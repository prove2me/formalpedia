-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:35:50.160481+00:00
-- url     : https://prove2.me/submissions/c74d6790-0c7c-4fa9-92fd-2f902dad212b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1294_e

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

theorem canonical1302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1302 raw1302Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw1302 raw1302Labels = mixedMoment B raw1302step0 raw1302step0Labels := by
      have ha : raw1302step0 = (fun i j => raw1302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1302step0 raw1302; decide +kernel
      have hl : raw1302step0Labels = raw1302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1302 raw1302Labels permutation8 permutation4
    mixedMoment B raw1302step0 raw1302step0Labels = mixedMoment B raw1302step1 raw1302step1Labels := by
      have ha : raw1302step1 = raw1302step0 := by apply Matrix.ext; unfold raw1302step1 raw1302step0; decide +kernel
      have hl : raw1302step0Labels = labelEmbedding7 ∘ raw1302step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1302step0 raw1302step0Labels raw1302step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical1303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1303 raw1303Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw1303 raw1303Labels = mixedMoment B raw1303step0 raw1303step0Labels := by
      have ha : raw1303step0 = (fun i j => raw1303 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1303step0 raw1303; decide +kernel
      have hl : raw1303step0Labels = raw1303Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1303 raw1303Labels permutation8 permutation4
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical1304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1304 raw1304Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw1304 raw1304Labels = mixedMoment B raw1304step0 raw1304step0Labels := by
      have ha : raw1304step0 = (fun i j => raw1304 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1304step0 raw1304; decide +kernel
      have hl : raw1304step0Labels = raw1304Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1304 raw1304Labels permutation12 permutation6
    mixedMoment B raw1304step0 raw1304step0Labels = mixedMoment B raw1304step1 raw1304step1Labels := by
      have ha : raw1304step1 = -raw1304step0 := by apply Matrix.ext; change ∀ i j, raw1304step1 i j = -(raw1304step0 i j); unfold raw1304step1 raw1304step0; decide +kernel
      have hl : raw1304step1Labels = raw1304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1304step1 raw1304step1Labels = mixedMoment B raw1304step2 raw1304step2Labels := by
      have ha : raw1304step2 = raw1304step1 := by apply Matrix.ext; unfold raw1304step2 raw1304step1; decide +kernel
      have hl : raw1304step1Labels = labelEmbedding1 ∘ raw1304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1304step1 raw1304step1Labels raw1304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

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

theorem canonical1806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1806 raw1806Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw1806 raw1806Labels = mixedMoment B raw1806step0 raw1806step0Labels := by
      have ha : raw1806step0 = (fun i j => raw1806 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1806step0 raw1806; decide +kernel
      have hl : raw1806step0Labels = raw1806Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1806 raw1806Labels permutation8 permutation4
    mixedMoment B raw1806step0 raw1806step0Labels = mixedMoment B raw1806step1 raw1806step1Labels := by
      have ha : raw1806step1 = raw1806step0 := by apply Matrix.ext; unfold raw1806step1 raw1806step0; decide +kernel
      have hl : raw1806step0Labels = labelEmbedding7 ∘ raw1806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1806step0 raw1806step0Labels raw1806step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1807 raw1807Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw1807 raw1807Labels = mixedMoment B raw1807step0 raw1807step0Labels := by
      have ha : raw1807step0 = (fun i j => raw1807 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1807step0 raw1807; decide +kernel
      have hl : raw1807step0Labels = raw1807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1807 raw1807Labels permutation8 permutation4
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical1808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1808 raw1808Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw1808 raw1808Labels = mixedMoment B raw1808step0 raw1808step0Labels := by
      have ha : raw1808step0 = (fun i j => raw1808 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1808step0 raw1808; decide +kernel
      have hl : raw1808step0Labels = raw1808Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1808 raw1808Labels permutation10 permutation6
    mixedMoment B raw1808step0 raw1808step0Labels = mixedMoment B raw1808step1 raw1808step1Labels := by
      have ha : raw1808step1 = -raw1808step0 := by apply Matrix.ext; change ∀ i j, raw1808step1 i j = -(raw1808step0 i j); unfold raw1808step1 raw1808step0; decide +kernel
      have hl : raw1808step1Labels = raw1808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1808step1 raw1808step1Labels = mixedMoment B raw1808step2 raw1808step2Labels := by
      have ha : raw1808step2 = raw1808step1 := by apply Matrix.ext; unfold raw1808step2 raw1808step1; decide +kernel
      have hl : raw1808step1Labels = labelEmbedding1 ∘ raw1808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1808step1 raw1808step1Labels raw1808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1824 raw1824Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw1824 raw1824Labels = mixedMoment B raw1824step0 raw1824step0Labels := by
      have ha : raw1824step0 = (fun i j => raw1824 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1824step0 raw1824; decide +kernel
      have hl : raw1824step0Labels = raw1824Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1824 raw1824Labels permutation8 permutation4
    mixedMoment B raw1824step0 raw1824step0Labels = mixedMoment B raw1824step1 raw1824step1Labels := by
      have ha : raw1824step1 = raw1824step0 := by apply Matrix.ext; unfold raw1824step1 raw1824step0; decide +kernel
      have hl : raw1824step0Labels = labelEmbedding7 ∘ raw1824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1824step0 raw1824step0Labels raw1824step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1825 raw1825Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw1825 raw1825Labels = mixedMoment B raw1825step0 raw1825step0Labels := by
      have ha : raw1825step0 = (fun i j => raw1825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1825step0 raw1825; decide +kernel
      have hl : raw1825step0Labels = raw1825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1825 raw1825Labels permutation8 permutation4
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1826 raw1826Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw1826 raw1826Labels = mixedMoment B raw1826step0 raw1826step0Labels := by
      have ha : raw1826step0 = (fun i j => raw1826 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1826step0 raw1826; decide +kernel
      have hl : raw1826step0Labels = raw1826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1826 raw1826Labels permutation12 permutation6
    mixedMoment B raw1826step0 raw1826step0Labels = mixedMoment B raw1826step1 raw1826step1Labels := by
      have ha : raw1826step1 = -raw1826step0 := by apply Matrix.ext; change ∀ i j, raw1826step1 i j = -(raw1826step0 i j); unfold raw1826step1 raw1826step0; decide +kernel
      have hl : raw1826step1Labels = raw1826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1826step1 raw1826step1Labels = mixedMoment B raw1826step2 raw1826step2Labels := by
      have ha : raw1826step2 = raw1826step1 := by apply Matrix.ext; unfold raw1826step2 raw1826step1; decide +kernel
      have hl : raw1826step1Labels = labelEmbedding1 ∘ raw1826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1826step1 raw1826step1Labels raw1826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21007 raw21007Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw21007 raw21007Labels = mixedMoment B raw21007step0 raw21007step0Labels := by
      have hz : ∀ j, raw21007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21007step0 = (fun i j => raw21007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21007step0 raw21007; decide +kernel
      have hl : raw21007step0Labels = raw21007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21007 raw21007Labels permutation346 hz
    mixedMoment B raw21007step0 raw21007step0Labels = mixedMoment B raw21007step1 raw21007step1Labels := by
      have hz : ∀ j, raw21007step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21007step1 = (fun i j => raw21007step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21007step1 raw21007step0; decide +kernel
      have hl : raw21007step1Labels = raw21007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21007step0 raw21007step0Labels permutation56 hz
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical21008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21008 raw21008Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw21008 raw21008Labels = mixedMoment B raw21008step0 raw21008step0Labels := by
      have hz : ∀ j, raw21008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21008step0 = (fun i j => raw21008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21008step0 raw21008; decide +kernel
      have hl : raw21008step0Labels = raw21008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21008 raw21008Labels permutation346 hz
    mixedMoment B raw21008step0 raw21008step0Labels = mixedMoment B raw21008step1 raw21008step1Labels := by
      have hz : ∀ j, raw21008step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21008step1 = (fun i j => raw21008step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21008step1 raw21008step0; decide +kernel
      have hl : raw21008step1Labels = raw21008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21008step0 raw21008step0Labels permutation56 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

theorem canonical21012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21012 raw21012Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw21012 raw21012Labels = mixedMoment B raw21012step0 raw21012step0Labels := by
      have hz : ∀ j, raw21012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21012step0 = (fun i j => raw21012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21012step0 raw21012; decide +kernel
      have hl : raw21012step0Labels = raw21012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21012 raw21012Labels permutation346 hz
    mixedMoment B raw21012step0 raw21012step0Labels = mixedMoment B raw21012step1 raw21012step1Labels := by
      have hz : ∀ j, raw21012step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21012step1 = (fun i j => raw21012step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21012step1 raw21012step0; decide +kernel
      have hl : raw21012step1Labels = raw21012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21012step0 raw21012step0Labels permutation56 hz
    _ = mixedMoment B node1193 node1193Labels := by rfl

theorem canonical21045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21045 raw21045Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw21045 raw21045Labels = mixedMoment B raw21045step0 raw21045step0Labels := by
      have hz : ∀ j, raw21045 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21045step0 = (fun i j => raw21045 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21045step0 raw21045; decide +kernel
      have hl : raw21045step0Labels = raw21045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21045 raw21045Labels permutation265 hz
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical21046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21046 raw21046Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw21046 raw21046Labels = mixedMoment B raw21046step0 raw21046step0Labels := by
      have hz : ∀ j, raw21046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21046step0 = (fun i j => raw21046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21046step0 raw21046; decide +kernel
      have hl : raw21046step0Labels = raw21046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21046 raw21046Labels permutation265 hz
    mixedMoment B raw21046step0 raw21046step0Labels = mixedMoment B raw21046step1 raw21046step1Labels := by
      have ha : raw21046step1 = (fun i j => raw21046step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21046step1 raw21046step0; decide +kernel
      have hl : raw21046step1Labels = raw21046step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21046step0 raw21046step0Labels permutation125 permutation0
    mixedMoment B raw21046step1 raw21046step1Labels = mixedMoment B raw21046step2 raw21046step2Labels := by
      have ha : raw21046step2 = -raw21046step1 := by apply Matrix.ext; change ∀ i j, raw21046step2 i j = -(raw21046step1 i j); unfold raw21046step2 raw21046step1; decide +kernel
      have hl : raw21046step2Labels = raw21046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical21050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21050 raw21050Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw21050 raw21050Labels = mixedMoment B raw21050step0 raw21050step0Labels := by
      have hz : ∀ j, raw21050 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21050step0 = (fun i j => raw21050 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21050step0 raw21050; decide +kernel
      have hl : raw21050step0Labels = raw21050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21050 raw21050Labels permutation265 hz
    _ = mixedMoment B node1205 node1205Labels := by rfl

theorem canonical21094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21094 raw21094Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw21094 raw21094Labels = mixedMoment B raw21094step0 raw21094step0Labels := by
      have hz : ∀ j, raw21094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21094step0 = (fun i j => raw21094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21094step0 raw21094; decide +kernel
      have hl : raw21094step0Labels = raw21094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21094 raw21094Labels permutation346 hz
    mixedMoment B raw21094step0 raw21094step0Labels = mixedMoment B raw21094step1 raw21094step1Labels := by
      have ha : raw21094step1 = (fun i j => raw21094step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21094step1 raw21094step0; decide +kernel
      have hl : raw21094step1Labels = raw21094step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21094step0 raw21094step0Labels permutation38 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical21095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21095 raw21095Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21095 raw21095Labels = mixedMoment B raw21095step0 raw21095step0Labels := by
      have hz : ∀ j, raw21095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21095step0 = (fun i j => raw21095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21095step0 raw21095; decide +kernel
      have hl : raw21095step0Labels = raw21095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21095 raw21095Labels permutation346 hz
    mixedMoment B raw21095step0 raw21095step0Labels = mixedMoment B raw21095step1 raw21095step1Labels := by
      have ha : raw21095step1 = (fun i j => raw21095step0 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21095step1 raw21095step0; decide +kernel
      have hl : raw21095step1Labels = raw21095step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21095step0 raw21095step0Labels permutation41 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical21099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21099 raw21099Labels = mixedMoment B node993 node993Labels := by
  calc
    mixedMoment B raw21099 raw21099Labels = mixedMoment B raw21099step0 raw21099step0Labels := by
      have hz : ∀ j, raw21099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21099step0 = (fun i j => raw21099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21099step0 raw21099; decide +kernel
      have hl : raw21099step0Labels = raw21099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21099 raw21099Labels permutation346 hz
    mixedMoment B raw21099step0 raw21099step0Labels = mixedMoment B raw21099step1 raw21099step1Labels := by
      have ha : raw21099step1 = (fun i j => raw21099step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21099step1 raw21099step0; decide +kernel
      have hl : raw21099step1Labels = raw21099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21099step0 raw21099step0Labels permutation38 permutation2
    _ = mixedMoment B node993 node993Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21127 raw21127Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw21127 raw21127Labels = mixedMoment B raw21127step0 raw21127step0Labels := by
      have ha : raw21127step0 = (fun i j => raw21127 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21127step0 raw21127; decide +kernel
      have hl : raw21127step0Labels = raw21127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21127 raw21127Labels permutation200 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical21128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21128 raw21128Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw21128 raw21128Labels = mixedMoment B raw21128step0 raw21128step0Labels := by
      have ha : raw21128step0 = (fun i j => raw21128 (permutation200 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21128step0 raw21128; decide +kernel
      have hl : raw21128step0Labels = raw21128Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21128 raw21128Labels permutation200 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical21132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21132 raw21132Labels = mixedMoment B node974 node974Labels := by
  calc
    mixedMoment B raw21132 raw21132Labels = mixedMoment B raw21132step0 raw21132step0Labels := by
      have ha : raw21132step0 = (fun i j => raw21132 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21132step0 raw21132; decide +kernel
      have hl : raw21132step0Labels = raw21132Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21132 raw21132Labels permutation200 permutation2
    _ = mixedMoment B node974 node974Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22843 raw22843Labels = mixedMoment B node1192 node1192Labels := by
  calc
    mixedMoment B raw22843 raw22843Labels = mixedMoment B raw22843step0 raw22843step0Labels := by
      have hz : ∀ j, raw22843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22843step0 = (fun i j => raw22843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22843step0 raw22843; decide +kernel
      have hl : raw22843step0Labels = raw22843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22843 raw22843Labels permutation346 hz
    mixedMoment B raw22843step0 raw22843step0Labels = mixedMoment B raw22843step1 raw22843step1Labels := by
      have hz : ∀ j, raw22843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22843step1 = (fun i j => raw22843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22843step1 raw22843step0; decide +kernel
      have hl : raw22843step1Labels = raw22843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22843step0 raw22843step0Labels permutation56 hz
    mixedMoment B raw22843step1 raw22843step1Labels = mixedMoment B raw22843step2 raw22843step2Labels := by
      have ha : raw22843step2 = (fun i j => raw22843step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22843step2 raw22843step1; decide +kernel
      have hl : raw22843step2Labels = raw22843step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22843step1 raw22843step1Labels permutation9 permutation2
    _ = mixedMoment B node1192 node1192Labels := by rfl

theorem canonical22844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22844 raw22844Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw22844 raw22844Labels = mixedMoment B raw22844step0 raw22844step0Labels := by
      have hz : ∀ j, raw22844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22844step0 = (fun i j => raw22844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22844step0 raw22844; decide +kernel
      have hl : raw22844step0Labels = raw22844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22844 raw22844Labels permutation346 hz
    mixedMoment B raw22844step0 raw22844step0Labels = mixedMoment B raw22844step1 raw22844step1Labels := by
      have ha : raw22844step1 = (fun i j => raw22844step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22844step1 raw22844step0; decide +kernel
      have hl : raw22844step1Labels = raw22844step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22844step0 raw22844step0Labels permutation33 permutation2
    _ = mixedMoment B node2538 node2538Labels := by rfl

theorem canonical22845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22845 raw22845Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw22845 raw22845Labels = mixedMoment B raw22845step0 raw22845step0Labels := by
      have hz : ∀ j, raw22845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22845step0 = (fun i j => raw22845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22845step0 raw22845; decide +kernel
      have hl : raw22845step0Labels = raw22845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22845 raw22845Labels permutation265 hz
    mixedMoment B raw22845step0 raw22845step0Labels = mixedMoment B raw22845step1 raw22845step1Labels := by
      have ha : raw22845step1 = (fun i j => raw22845step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22845step1 raw22845step0; decide +kernel
      have hl : raw22845step1Labels = raw22845step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22845step0 raw22845step0Labels permutation33 permutation2
    _ = mixedMoment B node2538 node2538Labels := by rfl

theorem canonical22846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22846 raw22846Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw22846 raw22846Labels = mixedMoment B raw22846step0 raw22846step0Labels := by
      have hz : ∀ j, raw22846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22846step0 = (fun i j => raw22846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22846step0 raw22846; decide +kernel
      have hl : raw22846step0Labels = raw22846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22846 raw22846Labels permutation346 hz
    mixedMoment B raw22846step0 raw22846step0Labels = mixedMoment B raw22846step1 raw22846step1Labels := by
      have hz : ∀ j, raw22846step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22846step1 = (fun i j => raw22846step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22846step1 raw22846step0; decide +kernel
      have hl : raw22846step1Labels = raw22846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22846step0 raw22846step0Labels permutation56 hz
    mixedMoment B raw22846step1 raw22846step1Labels = mixedMoment B raw22846step2 raw22846step2Labels := by
      have ha : raw22846step2 = (fun i j => raw22846step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22846step2 raw22846step1; decide +kernel
      have hl : raw22846step2Labels = raw22846step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22846step1 raw22846step1Labels permutation9 permutation2
    _ = mixedMoment B node2410 node2410Labels := by rfl

theorem canonical22847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22847 raw22847Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw22847 raw22847Labels = mixedMoment B raw22847step0 raw22847step0Labels := by
      have hz : ∀ j, raw22847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22847step0 = (fun i j => raw22847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22847step0 raw22847; decide +kernel
      have hl : raw22847step0Labels = raw22847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22847 raw22847Labels permutation346 hz
    mixedMoment B raw22847step0 raw22847step0Labels = mixedMoment B raw22847step1 raw22847step1Labels := by
      have hz : ∀ j, raw22847step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22847step1 = (fun i j => raw22847step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22847step1 raw22847step0; decide +kernel
      have hl : raw22847step1Labels = raw22847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22847step0 raw22847step0Labels permutation56 hz
    _ = mixedMoment B node2687 node2687Labels := by rfl

theorem canonical22848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22848 raw22848Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw22848 raw22848Labels = mixedMoment B raw22848step0 raw22848step0Labels := by
      have hz : ∀ j, raw22848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22848step0 = (fun i j => raw22848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22848step0 raw22848; decide +kernel
      have hl : raw22848step0Labels = raw22848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22848 raw22848Labels permutation346 hz
    mixedMoment B raw22848step0 raw22848step0Labels = mixedMoment B raw22848step1 raw22848step1Labels := by
      have hz : ∀ j, raw22848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22848step1 = (fun i j => raw22848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22848step1 raw22848step0; decide +kernel
      have hl : raw22848step1Labels = raw22848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22848step0 raw22848step0Labels permutation56 hz
    mixedMoment B raw22848step1 raw22848step1Labels = mixedMoment B raw22848step2 raw22848step2Labels := by
      have ha : raw22848step2 = (fun i j => raw22848step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22848step2 raw22848step1; decide +kernel
      have hl : raw22848step2Labels = raw22848step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22848step1 raw22848step1Labels permutation9 permutation2
    _ = mixedMoment B node2685 node2685Labels := by rfl

theorem canonical22849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22849 raw22849Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw22849 raw22849Labels = mixedMoment B raw22849step0 raw22849step0Labels := by
      have hz : ∀ j, raw22849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22849step0 = (fun i j => raw22849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22849step0 raw22849; decide +kernel
      have hl : raw22849step0Labels = raw22849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22849 raw22849Labels permutation346 hz
    mixedMoment B raw22849step0 raw22849step0Labels = mixedMoment B raw22849step1 raw22849step1Labels := by
      have hz : ∀ j, raw22849step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22849step1 = (fun i j => raw22849step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22849step1 raw22849step0; decide +kernel
      have hl : raw22849step1Labels = raw22849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22849step0 raw22849step0Labels permutation56 hz
    mixedMoment B raw22849step1 raw22849step1Labels = mixedMoment B raw22849step2 raw22849step2Labels := by
      have ha : raw22849step2 = (fun i j => raw22849step1 (permutation24 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22849step2 raw22849step1; decide +kernel
      have hl : raw22849step2Labels = raw22849step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22849step1 raw22849step1Labels permutation24 permutation0
    mixedMoment B raw22849step2 raw22849step2Labels = mixedMoment B raw22849step3 raw22849step3Labels := by
      have ha : raw22849step3 = -raw22849step2 := by apply Matrix.ext; change ∀ i j, raw22849step3 i j = -(raw22849step2 i j); unfold raw22849step3 raw22849step2; decide +kernel
      have hl : raw22849step3Labels = raw22849step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical22850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22850 raw22850Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw22850 raw22850Labels = mixedMoment B raw22850step0 raw22850step0Labels := by
      have hz : ∀ j, raw22850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22850step0 = (fun i j => raw22850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22850step0 raw22850; decide +kernel
      have hl : raw22850step0Labels = raw22850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22850 raw22850Labels permutation346 hz
    _ = mixedMoment B node2539 node2539Labels := by rfl

theorem canonical22851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22851 raw22851Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw22851 raw22851Labels = mixedMoment B raw22851step0 raw22851step0Labels := by
      have hz : ∀ j, raw22851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22851step0 = (fun i j => raw22851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22851step0 raw22851; decide +kernel
      have hl : raw22851step0Labels = raw22851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22851 raw22851Labels permutation265 hz
    _ = mixedMoment B node2539 node2539Labels := by rfl

theorem canonical22852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22852 raw22852Labels = mixedMoment B node2411 node2411Labels := by
  calc
    mixedMoment B raw22852 raw22852Labels = mixedMoment B raw22852step0 raw22852step0Labels := by
      have hz : ∀ j, raw22852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22852step0 = (fun i j => raw22852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22852step0 raw22852; decide +kernel
      have hl : raw22852step0Labels = raw22852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22852 raw22852Labels permutation346 hz
    mixedMoment B raw22852step0 raw22852step0Labels = mixedMoment B raw22852step1 raw22852step1Labels := by
      have hz : ∀ j, raw22852step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22852step1 = (fun i j => raw22852step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22852step1 raw22852step0; decide +kernel
      have hl : raw22852step1Labels = raw22852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22852step0 raw22852step0Labels permutation56 hz
    _ = mixedMoment B node2411 node2411Labels := by rfl

theorem canonical22853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22853 raw22853Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw22853 raw22853Labels = mixedMoment B raw22853step0 raw22853step0Labels := by
      have hz : ∀ j, raw22853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22853step0 = (fun i j => raw22853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22853step0 raw22853; decide +kernel
      have hl : raw22853step0Labels = raw22853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22853 raw22853Labels permutation346 hz
    mixedMoment B raw22853step0 raw22853step0Labels = mixedMoment B raw22853step1 raw22853step1Labels := by
      have hz : ∀ j, raw22853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22853step1 = (fun i j => raw22853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22853step1 raw22853step0; decide +kernel
      have hl : raw22853step1Labels = raw22853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22853step0 raw22853step0Labels permutation56 hz
    mixedMoment B raw22853step1 raw22853step1Labels = mixedMoment B raw22853step2 raw22853step2Labels := by
      have ha : raw22853step2 = (fun i j => raw22853step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22853step2 raw22853step1; decide +kernel
      have hl : raw22853step2Labels = raw22853step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22853step1 raw22853step1Labels permutation9 permutation2
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical22854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22854 raw22854Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw22854 raw22854Labels = mixedMoment B raw22854step0 raw22854step0Labels := by
      have hz : ∀ j, raw22854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22854step0 = (fun i j => raw22854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22854step0 raw22854; decide +kernel
      have hl : raw22854step0Labels = raw22854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22854 raw22854Labels permutation346 hz
    mixedMoment B raw22854step0 raw22854step0Labels = mixedMoment B raw22854step1 raw22854step1Labels := by
      have ha : raw22854step1 = (fun i j => raw22854step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22854step1 raw22854step0; decide +kernel
      have hl : raw22854step1Labels = raw22854step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22854step0 raw22854step0Labels permutation38 permutation2
    _ = mixedMoment B node1099 node1099Labels := by rfl

theorem canonical22855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22855 raw22855Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw22855 raw22855Labels = mixedMoment B raw22855step0 raw22855step0Labels := by
      have hz : ∀ j, raw22855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22855step0 = (fun i j => raw22855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22855step0 raw22855; decide +kernel
      have hl : raw22855step0Labels = raw22855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22855 raw22855Labels permutation265 hz
    mixedMoment B raw22855step0 raw22855step0Labels = mixedMoment B raw22855step1 raw22855step1Labels := by
      have ha : raw22855step1 = (fun i j => raw22855step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22855step1 raw22855step0; decide +kernel
      have hl : raw22855step1Labels = raw22855step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22855step0 raw22855step0Labels permutation38 permutation2
    _ = mixedMoment B node1099 node1099Labels := by rfl

theorem canonical22856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22856 raw22856Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw22856 raw22856Labels = mixedMoment B raw22856step0 raw22856step0Labels := by
      have hz : ∀ j, raw22856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22856step0 = (fun i j => raw22856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22856step0 raw22856; decide +kernel
      have hl : raw22856step0Labels = raw22856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22856 raw22856Labels permutation346 hz
    mixedMoment B raw22856step0 raw22856step0Labels = mixedMoment B raw22856step1 raw22856step1Labels := by
      have hz : ∀ j, raw22856step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22856step1 = (fun i j => raw22856step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22856step1 raw22856step0; decide +kernel
      have hl : raw22856step1Labels = raw22856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22856step0 raw22856step0Labels permutation56 hz
    mixedMoment B raw22856step1 raw22856step1Labels = mixedMoment B raw22856step2 raw22856step2Labels := by
      have ha : raw22856step2 = (fun i j => raw22856step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22856step2 raw22856step1; decide +kernel
      have hl : raw22856step2Labels = raw22856step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22856step1 raw22856step1Labels permutation9 permutation2
    _ = mixedMoment B node1104 node1104Labels := by rfl

theorem canonical22857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22857 raw22857Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw22857 raw22857Labels = mixedMoment B raw22857step0 raw22857step0Labels := by
      have hz : ∀ j, raw22857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22857step0 = (fun i j => raw22857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22857step0 raw22857; decide +kernel
      have hl : raw22857step0Labels = raw22857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22857 raw22857Labels permutation346 hz
    mixedMoment B raw22857step0 raw22857step0Labels = mixedMoment B raw22857step1 raw22857step1Labels := by
      have hz : ∀ j, raw22857step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22857step1 = (fun i j => raw22857step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22857step1 raw22857step0; decide +kernel
      have hl : raw22857step1Labels = raw22857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22857step0 raw22857step0Labels permutation56 hz
    _ = mixedMoment B node1104 node1104Labels := by rfl

theorem canonical22864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22864 raw22864Labels = mixedMoment B node1204 node1204Labels := by
  calc
    mixedMoment B raw22864 raw22864Labels = mixedMoment B raw22864step0 raw22864step0Labels := by
      have hz : ∀ j, raw22864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22864step0 = (fun i j => raw22864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22864step0 raw22864; decide +kernel
      have hl : raw22864step0Labels = raw22864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22864 raw22864Labels permutation265 hz
    mixedMoment B raw22864step0 raw22864step0Labels = mixedMoment B raw22864step1 raw22864step1Labels := by
      have ha : raw22864step1 = (fun i j => raw22864step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22864step1 raw22864step0; decide +kernel
      have hl : raw22864step1Labels = raw22864step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22864step0 raw22864step0Labels permutation33 permutation2
    _ = mixedMoment B node1204 node1204Labels := by rfl

theorem canonical22865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22865 raw22865Labels = mixedMoment B node2540 node2540Labels := by
  calc
    mixedMoment B raw22865 raw22865Labels = mixedMoment B raw22865step0 raw22865step0Labels := by
      have ha : raw22865step0 = (fun i j => raw22865 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22865step0 raw22865; decide +kernel
      have hl : raw22865step0Labels = raw22865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22865 raw22865Labels permutation153 permutation2
    _ = mixedMoment B node2540 node2540Labels := by rfl

theorem canonical22866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22866 raw22866Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw22866 raw22866Labels = mixedMoment B raw22866step0 raw22866step0Labels := by
      have hz : ∀ j, raw22866 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22866step0 = (fun i j => raw22866 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22866step0 raw22866; decide +kernel
      have hl : raw22866step0Labels = raw22866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22866 raw22866Labels permutation265 hz
    mixedMoment B raw22866step0 raw22866step0Labels = mixedMoment B raw22866step1 raw22866step1Labels := by
      have ha : raw22866step1 = (fun i j => raw22866step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22866step1 raw22866step0; decide +kernel
      have hl : raw22866step1Labels = raw22866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22866step0 raw22866step0Labels permutation33 permutation2
    _ = mixedMoment B node2467 node2467Labels := by rfl

theorem canonical22867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22867 raw22867Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw22867 raw22867Labels = mixedMoment B raw22867step0 raw22867step0Labels := by
      have hz : ∀ j, raw22867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22867step0 = (fun i j => raw22867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22867step0 raw22867; decide +kernel
      have hl : raw22867step0Labels = raw22867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22867 raw22867Labels permutation265 hz
    mixedMoment B raw22867step0 raw22867step0Labels = mixedMoment B raw22867step1 raw22867step1Labels := by
      have ha : raw22867step1 = (fun i j => raw22867step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22867step1 raw22867step0; decide +kernel
      have hl : raw22867step1Labels = raw22867step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22867step0 raw22867step0Labels permutation39 permutation2
    _ = mixedMoment B node2467 node2467Labels := by rfl

theorem canonical22868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22868 raw22868Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw22868 raw22868Labels = mixedMoment B raw22868step0 raw22868step0Labels := by
      have hz : ∀ j, raw22868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22868step0 = (fun i j => raw22868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22868step0 raw22868; decide +kernel
      have hl : raw22868step0Labels = raw22868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22868 raw22868Labels permutation265 hz
    _ = mixedMoment B node2706 node2706Labels := by rfl

theorem canonical22869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22869 raw22869Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw22869 raw22869Labels = mixedMoment B raw22869step0 raw22869step0Labels := by
      have hz : ∀ j, raw22869 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22869step0 = (fun i j => raw22869 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22869step0 raw22869; decide +kernel
      have hl : raw22869step0Labels = raw22869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22869 raw22869Labels permutation265 hz
    mixedMoment B raw22869step0 raw22869step0Labels = mixedMoment B raw22869step1 raw22869step1Labels := by
      have ha : raw22869step1 = (fun i j => raw22869step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22869step1 raw22869step0; decide +kernel
      have hl : raw22869step1Labels = raw22869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22869step0 raw22869step0Labels permutation33 permutation2
    _ = mixedMoment B node2704 node2704Labels := by rfl

theorem canonical22870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22870 raw22870Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw22870 raw22870Labels = mixedMoment B raw22870step0 raw22870step0Labels := by
      have hz : ∀ j, raw22870 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22870step0 = (fun i j => raw22870 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22870step0 raw22870; decide +kernel
      have hl : raw22870step0Labels = raw22870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22870 raw22870Labels permutation265 hz
    mixedMoment B raw22870step0 raw22870step0Labels = mixedMoment B raw22870step1 raw22870step1Labels := by
      have ha : raw22870step1 = (fun i j => raw22870step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22870step1 raw22870step0; decide +kernel
      have hl : raw22870step1Labels = raw22870step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22870step0 raw22870step0Labels permutation125 permutation0
    mixedMoment B raw22870step1 raw22870step1Labels = mixedMoment B raw22870step2 raw22870step2Labels := by
      have ha : raw22870step2 = -raw22870step1 := by apply Matrix.ext; change ∀ i j, raw22870step2 i j = -(raw22870step1 i j); unfold raw22870step2 raw22870step1; decide +kernel
      have hl : raw22870step2Labels = raw22870step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical22871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22871 raw22871Labels = mixedMoment B node2541 node2541Labels := by
  calc
    _ = mixedMoment B node2541 node2541Labels := by rfl

theorem canonical22872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22872 raw22872Labels = mixedMoment B node2468 node2468Labels := by
  calc
    mixedMoment B raw22872 raw22872Labels = mixedMoment B raw22872step0 raw22872step0Labels := by
      have hz : ∀ j, raw22872 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22872step0 = (fun i j => raw22872 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22872step0 raw22872; decide +kernel
      have hl : raw22872step0Labels = raw22872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22872 raw22872Labels permutation265 hz
    _ = mixedMoment B node2468 node2468Labels := by rfl

theorem canonical22873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22873 raw22873Labels = mixedMoment B node2468 node2468Labels := by
  calc
    mixedMoment B raw22873 raw22873Labels = mixedMoment B raw22873step0 raw22873step0Labels := by
      have hz : ∀ j, raw22873 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22873step0 = (fun i j => raw22873 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22873step0 raw22873; decide +kernel
      have hl : raw22873step0Labels = raw22873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22873 raw22873Labels permutation265 hz
    mixedMoment B raw22873step0 raw22873step0Labels = mixedMoment B raw22873step1 raw22873step1Labels := by
      have ha : raw22873step1 = (fun i j => raw22873step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22873step1 raw22873step0; decide +kernel
      have hl : raw22873step1Labels = raw22873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22873step0 raw22873step0Labels permutation38 permutation2
    _ = mixedMoment B node2468 node2468Labels := by rfl

theorem canonical22874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22874 raw22874Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw22874 raw22874Labels = mixedMoment B raw22874step0 raw22874step0Labels := by
      have hz : ∀ j, raw22874 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22874step0 = (fun i j => raw22874 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22874step0 raw22874; decide +kernel
      have hl : raw22874step0Labels = raw22874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22874 raw22874Labels permutation265 hz
    mixedMoment B raw22874step0 raw22874step0Labels = mixedMoment B raw22874step1 raw22874step1Labels := by
      have ha : raw22874step1 = (fun i j => raw22874step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22874step1 raw22874step0; decide +kernel
      have hl : raw22874step1Labels = raw22874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22874step0 raw22874step0Labels permutation33 permutation2
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical22875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22875 raw22875Labels = mixedMoment B node1106 node1106Labels := by
  calc
    mixedMoment B raw22875 raw22875Labels = mixedMoment B raw22875step0 raw22875step0Labels := by
      have ha : raw22875step0 = (fun i j => raw22875 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22875step0 raw22875; decide +kernel
      have hl : raw22875step0Labels = raw22875Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22875 raw22875Labels permutation182 permutation2
    _ = mixedMoment B node1106 node1106Labels := by rfl

theorem canonical22876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22876 raw22876Labels = mixedMoment B node1124 node1124Labels := by
  calc
    mixedMoment B raw22876 raw22876Labels = mixedMoment B raw22876step0 raw22876step0Labels := by
      have hz : ∀ j, raw22876 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22876step0 = (fun i j => raw22876 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22876step0 raw22876; decide +kernel
      have hl : raw22876step0Labels = raw22876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22876 raw22876Labels permutation265 hz
    _ = mixedMoment B node1124 node1124Labels := by rfl

theorem canonical22877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22877 raw22877Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw22877 raw22877Labels = mixedMoment B raw22877step0 raw22877step0Labels := by
      have hz : ∀ j, raw22877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22877step0 = (fun i j => raw22877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22877step0 raw22877; decide +kernel
      have hl : raw22877step0Labels = raw22877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22877 raw22877Labels permutation265 hz
    mixedMoment B raw22877step0 raw22877step0Labels = mixedMoment B raw22877step1 raw22877step1Labels := by
      have ha : raw22877step1 = (fun i j => raw22877step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22877step1 raw22877step0; decide +kernel
      have hl : raw22877step1Labels = raw22877step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22877step0 raw22877step0Labels permutation33 permutation2
    _ = mixedMoment B node1110 node1110Labels := by rfl

theorem canonical22878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22878 raw22878Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw22878 raw22878Labels = mixedMoment B raw22878step0 raw22878step0Labels := by
      have hz : ∀ j, raw22878 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22878step0 = (fun i j => raw22878 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22878step0 raw22878; decide +kernel
      have hl : raw22878step0Labels = raw22878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22878 raw22878Labels permutation265 hz
    _ = mixedMoment B node1110 node1110Labels := by rfl

theorem canonical22884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22884 raw22884Labels = mixedMoment B node1062 node1062Labels := by
  calc
    mixedMoment B raw22884 raw22884Labels = mixedMoment B raw22884step0 raw22884step0Labels := by
      have hz : ∀ j, raw22884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22884step0 = (fun i j => raw22884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22884step0 raw22884; decide +kernel
      have hl : raw22884step0Labels = raw22884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22884 raw22884Labels permutation434 hz
    mixedMoment B raw22884step0 raw22884step0Labels = mixedMoment B raw22884step1 raw22884step1Labels := by
      have hz : ∀ j, raw22884step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22884step1 = (fun i j => raw22884step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22884step1 raw22884step0; decide +kernel
      have hl : raw22884step1Labels = raw22884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22884step0 raw22884step0Labels permutation80 hz
    mixedMoment B raw22884step1 raw22884step1Labels = mixedMoment B raw22884step2 raw22884step2Labels := by
      have ha : raw22884step2 = (fun i j => raw22884step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22884step2 raw22884step1; decide +kernel
      have hl : raw22884step2Labels = raw22884step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22884step1 raw22884step1Labels permutation9 permutation2
    _ = mixedMoment B node1062 node1062Labels := by rfl

theorem canonical22885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22885 raw22885Labels = mixedMoment B node2137 node2137Labels := by
  calc
    mixedMoment B raw22885 raw22885Labels = mixedMoment B raw22885step0 raw22885step0Labels := by
      have hz : ∀ j, raw22885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22885step0 = (fun i j => raw22885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22885step0 raw22885; decide +kernel
      have hl : raw22885step0Labels = raw22885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22885 raw22885Labels permutation434 hz
    mixedMoment B raw22885step0 raw22885step0Labels = mixedMoment B raw22885step1 raw22885step1Labels := by
      have hz : ∀ j, raw22885step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22885step1 = (fun i j => raw22885step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22885step1 raw22885step0; decide +kernel
      have hl : raw22885step1Labels = raw22885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22885step0 raw22885step0Labels permutation80 hz
    mixedMoment B raw22885step1 raw22885step1Labels = mixedMoment B raw22885step2 raw22885step2Labels := by
      have ha : raw22885step2 = (fun i j => raw22885step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22885step2 raw22885step1; decide +kernel
      have hl : raw22885step2Labels = raw22885step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22885step1 raw22885step1Labels permutation9 permutation2
    _ = mixedMoment B node2137 node2137Labels := by rfl

theorem canonical22886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22886 raw22886Labels = mixedMoment B node2038 node2038Labels := by
  calc
    mixedMoment B raw22886 raw22886Labels = mixedMoment B raw22886step0 raw22886step0Labels := by
      have hz : ∀ j, raw22886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22886step0 = (fun i j => raw22886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22886step0 raw22886; decide +kernel
      have hl : raw22886step0Labels = raw22886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22886 raw22886Labels permutation434 hz
    mixedMoment B raw22886step0 raw22886step0Labels = mixedMoment B raw22886step1 raw22886step1Labels := by
      have ha : raw22886step1 = (fun i j => raw22886step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22886step1 raw22886step0; decide +kernel
      have hl : raw22886step1Labels = raw22886step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22886step0 raw22886step0Labels permutation39 permutation2
    _ = mixedMoment B node2038 node2038Labels := by rfl

theorem canonical22887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22887 raw22887Labels = mixedMoment B node2038 node2038Labels := by
  calc
    mixedMoment B raw22887 raw22887Labels = mixedMoment B raw22887step0 raw22887step0Labels := by
      have hz : ∀ j, raw22887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22887step0 = (fun i j => raw22887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22887step0 raw22887; decide +kernel
      have hl : raw22887step0Labels = raw22887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22887 raw22887Labels permutation346 hz
    mixedMoment B raw22887step0 raw22887step0Labels = mixedMoment B raw22887step1 raw22887step1Labels := by
      have ha : raw22887step1 = (fun i j => raw22887step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22887step1 raw22887step0; decide +kernel
      have hl : raw22887step1Labels = raw22887step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22887step0 raw22887step0Labels permutation39 permutation2
    _ = mixedMoment B node2038 node2038Labels := by rfl

theorem canonical22888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22888 raw22888Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw22888 raw22888Labels = mixedMoment B raw22888step0 raw22888step0Labels := by
      have hz : ∀ j, raw22888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22888step0 = (fun i j => raw22888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22888step0 raw22888; decide +kernel
      have hl : raw22888step0Labels = raw22888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22888 raw22888Labels permutation434 hz
    mixedMoment B raw22888step0 raw22888step0Labels = mixedMoment B raw22888step1 raw22888step1Labels := by
      have hz : ∀ j, raw22888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22888step1 = (fun i j => raw22888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22888step1 raw22888step0; decide +kernel
      have hl : raw22888step1Labels = raw22888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22888step0 raw22888step0Labels permutation80 hz
    _ = mixedMoment B node2280 node2280Labels := by rfl

theorem canonical22889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22889 raw22889Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw22889 raw22889Labels = mixedMoment B raw22889step0 raw22889step0Labels := by
      have hz : ∀ j, raw22889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22889step0 = (fun i j => raw22889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22889step0 raw22889; decide +kernel
      have hl : raw22889step0Labels = raw22889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22889 raw22889Labels permutation434 hz
    mixedMoment B raw22889step0 raw22889step0Labels = mixedMoment B raw22889step1 raw22889step1Labels := by
      have hz : ∀ j, raw22889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22889step1 = (fun i j => raw22889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22889step1 raw22889step0; decide +kernel
      have hl : raw22889step1Labels = raw22889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22889step0 raw22889step0Labels permutation80 hz
    mixedMoment B raw22889step1 raw22889step1Labels = mixedMoment B raw22889step2 raw22889step2Labels := by
      have ha : raw22889step2 = (fun i j => raw22889step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22889step2 raw22889step1; decide +kernel
      have hl : raw22889step2Labels = raw22889step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22889step1 raw22889step1Labels permutation9 permutation2
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical22890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22890 raw22890Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw22890 raw22890Labels = mixedMoment B raw22890step0 raw22890step0Labels := by
      have hz : ∀ j, raw22890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22890step0 = (fun i j => raw22890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22890step0 raw22890; decide +kernel
      have hl : raw22890step0Labels = raw22890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22890 raw22890Labels permutation434 hz
    mixedMoment B raw22890step0 raw22890step0Labels = mixedMoment B raw22890step1 raw22890step1Labels := by
      have hz : ∀ j, raw22890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22890step1 = (fun i j => raw22890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22890step1 raw22890step0; decide +kernel
      have hl : raw22890step1Labels = raw22890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22890step0 raw22890step0Labels permutation80 hz
    mixedMoment B raw22890step1 raw22890step1Labels = mixedMoment B raw22890step2 raw22890step2Labels := by
      have ha : raw22890step2 = (fun i j => raw22890step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22890step2 raw22890step1; decide +kernel
      have hl : raw22890step2Labels = raw22890step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22890step1 raw22890step1Labels permutation12 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical22891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22891 raw22891Labels = mixedMoment B node992 node992Labels := by
  calc
    mixedMoment B raw22891 raw22891Labels = mixedMoment B raw22891step0 raw22891step0Labels := by
      have hz : ∀ j, raw22891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22891step0 = (fun i j => raw22891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22891step0 raw22891; decide +kernel
      have hl : raw22891step0Labels = raw22891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22891 raw22891Labels permutation346 hz
    mixedMoment B raw22891step0 raw22891step0Labels = mixedMoment B raw22891step1 raw22891step1Labels := by
      have ha : raw22891step1 = (fun i j => raw22891step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22891step1 raw22891step0; decide +kernel
      have hl : raw22891step1Labels = raw22891step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22891step0 raw22891step0Labels permutation39 permutation2
    _ = mixedMoment B node992 node992Labels := by rfl

theorem canonical22892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22892 raw22892Labels = mixedMoment B node2122 node2122Labels := by
  calc
    mixedMoment B raw22892 raw22892Labels = mixedMoment B raw22892step0 raw22892step0Labels := by
      have hz : ∀ j, raw22892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22892step0 = (fun i j => raw22892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22892step0 raw22892; decide +kernel
      have hl : raw22892step0Labels = raw22892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22892 raw22892Labels permutation346 hz
    mixedMoment B raw22892step0 raw22892step0Labels = mixedMoment B raw22892step1 raw22892step1Labels := by
      have ha : raw22892step1 = (fun i j => raw22892step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22892step1 raw22892step0; decide +kernel
      have hl : raw22892step1Labels = raw22892step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22892step0 raw22892step0Labels permutation33 permutation2
    _ = mixedMoment B node2122 node2122Labels := by rfl

theorem canonical22893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22893 raw22893Labels = mixedMoment B node1993 node1993Labels := by
  calc
    mixedMoment B raw22893 raw22893Labels = mixedMoment B raw22893step0 raw22893step0Labels := by
      have ha : raw22893step0 = (fun i j => raw22893 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22893step0 raw22893; decide +kernel
      have hl : raw22893step0Labels = raw22893Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22893 raw22893Labels permutation183 permutation2
    _ = mixedMoment B node1993 node1993Labels := by rfl

theorem canonical22894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22894 raw22894Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw22894 raw22894Labels = mixedMoment B raw22894step0 raw22894step0Labels := by
      have hz : ∀ j, raw22894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22894step0 = (fun i j => raw22894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22894step0 raw22894; decide +kernel
      have hl : raw22894step0Labels = raw22894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22894 raw22894Labels permutation346 hz
    mixedMoment B raw22894step0 raw22894step0Labels = mixedMoment B raw22894step1 raw22894step1Labels := by
      have ha : raw22894step1 = (fun i j => raw22894step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22894step1 raw22894step0; decide +kernel
      have hl : raw22894step1Labels = raw22894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22894step0 raw22894step0Labels permutation39 permutation2
    _ = mixedMoment B node1928 node1928Labels := by rfl

theorem canonical22895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22895 raw22895Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw22895 raw22895Labels = mixedMoment B raw22895step0 raw22895step0Labels := by
      have hz : ∀ j, raw22895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22895step0 = (fun i j => raw22895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22895step0 raw22895; decide +kernel
      have hl : raw22895step0Labels = raw22895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22895 raw22895Labels permutation346 hz
    mixedMoment B raw22895step0 raw22895step0Labels = mixedMoment B raw22895step1 raw22895step1Labels := by
      have ha : raw22895step1 = (fun i j => raw22895step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22895step1 raw22895step0; decide +kernel
      have hl : raw22895step1Labels = raw22895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22895step0 raw22895step0Labels permutation38 permutation2
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical22896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22896 raw22896Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw22896 raw22896Labels = mixedMoment B raw22896step0 raw22896step0Labels := by
      have hz : ∀ j, raw22896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22896step0 = (fun i j => raw22896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22896step0 raw22896; decide +kernel
      have hl : raw22896step0Labels = raw22896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22896 raw22896Labels permutation346 hz
    mixedMoment B raw22896step0 raw22896step0Labels = mixedMoment B raw22896step1 raw22896step1Labels := by
      have ha : raw22896step1 = (fun i j => raw22896step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22896step1 raw22896step0; decide +kernel
      have hl : raw22896step1Labels = raw22896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22896step0 raw22896step0Labels permutation39 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical22897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22897 raw22897Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw22897 raw22897Labels = mixedMoment B raw22897step0 raw22897step0Labels := by
      have hz : ∀ j, raw22897 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22897step0 = (fun i j => raw22897 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22897step0 raw22897; decide +kernel
      have hl : raw22897step0Labels = raw22897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22897 raw22897Labels permutation590 hz
    mixedMoment B raw22897step0 raw22897step0Labels = mixedMoment B raw22897step1 raw22897step1Labels := by
      have hz : ∀ j, raw22897step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22897step1 = (fun i j => raw22897step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22897step1 raw22897step0; decide +kernel
      have hl : raw22897step1Labels = raw22897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22897step0 raw22897step0Labels permutation80 hz
    mixedMoment B raw22897step1 raw22897step1Labels = mixedMoment B raw22897step2 raw22897step2Labels := by
      have ha : raw22897step2 = (fun i j => raw22897step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22897step2 raw22897step1; decide +kernel
      have hl : raw22897step2Labels = raw22897step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22897step1 raw22897step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical22898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22898 raw22898Labels = mixedMoment B node2123 node2123Labels := by
  calc
    mixedMoment B raw22898 raw22898Labels = mixedMoment B raw22898step0 raw22898step0Labels := by
      have hz : ∀ j, raw22898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22898step0 = (fun i j => raw22898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22898step0 raw22898; decide +kernel
      have hl : raw22898step0Labels = raw22898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22898 raw22898Labels permutation346 hz
    _ = mixedMoment B node2123 node2123Labels := by rfl

theorem canonical22899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22899 raw22899Labels = mixedMoment B node1994 node1994Labels := by
  calc
    mixedMoment B raw22899 raw22899Labels = mixedMoment B raw22899step0 raw22899step0Labels := by
      have ha : raw22899step0 = (fun i j => raw22899 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22899step0 raw22899; decide +kernel
      have hl : raw22899step0Labels = raw22899Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22899 raw22899Labels permutation182 permutation2
    _ = mixedMoment B node1994 node1994Labels := by rfl

theorem canonical22900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22900 raw22900Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw22900 raw22900Labels = mixedMoment B raw22900step0 raw22900step0Labels := by
      have hz : ∀ j, raw22900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22900step0 = (fun i j => raw22900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22900step0 raw22900; decide +kernel
      have hl : raw22900step0Labels = raw22900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22900 raw22900Labels permutation346 hz
    mixedMoment B raw22900step0 raw22900step0Labels = mixedMoment B raw22900step1 raw22900step1Labels := by
      have ha : raw22900step1 = (fun i j => raw22900step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22900step1 raw22900step0; decide +kernel
      have hl : raw22900step1Labels = raw22900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22900step0 raw22900step0Labels permutation38 permutation2
    _ = mixedMoment B node1929 node1929Labels := by rfl

theorem canonical22901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22901 raw22901Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw22901 raw22901Labels = mixedMoment B raw22901step0 raw22901step0Labels := by
      have hz : ∀ j, raw22901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22901step0 = (fun i j => raw22901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22901step0 raw22901; decide +kernel
      have hl : raw22901step0Labels = raw22901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22901 raw22901Labels permutation346 hz
    mixedMoment B raw22901step0 raw22901step0Labels = mixedMoment B raw22901step1 raw22901step1Labels := by
      have ha : raw22901step1 = (fun i j => raw22901step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22901step1 raw22901step0; decide +kernel
      have hl : raw22901step1Labels = raw22901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22901step0 raw22901step0Labels permutation39 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical22902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22902 raw22902Labels = mixedMoment B node1025 node1025Labels := by
  calc
    mixedMoment B raw22902 raw22902Labels = mixedMoment B raw22902step0 raw22902step0Labels := by
      have hz : ∀ j, raw22902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22902step0 = (fun i j => raw22902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22902step0 raw22902; decide +kernel
      have hl : raw22902step0Labels = raw22902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22902 raw22902Labels permutation434 hz
    mixedMoment B raw22902step0 raw22902step0Labels = mixedMoment B raw22902step1 raw22902step1Labels := by
      have ha : raw22902step1 = (fun i j => raw22902step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22902step1 raw22902step0; decide +kernel
      have hl : raw22902step1Labels = raw22902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22902step0 raw22902step0Labels permutation33 permutation2
    _ = mixedMoment B node1025 node1025Labels := by rfl

theorem canonical22903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22903 raw22903Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw22903 raw22903Labels = mixedMoment B raw22903step0 raw22903step0Labels := by
      have hz : ∀ j, raw22903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22903step0 = (fun i j => raw22903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22903step0 raw22903; decide +kernel
      have hl : raw22903step0Labels = raw22903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22903 raw22903Labels permutation434 hz
    mixedMoment B raw22903step0 raw22903step0Labels = mixedMoment B raw22903step1 raw22903step1Labels := by
      have ha : raw22903step1 = (fun i j => raw22903step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22903step1 raw22903step0; decide +kernel
      have hl : raw22903step1Labels = raw22903step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22903step0 raw22903step0Labels permutation33 permutation2
    _ = mixedMoment B node2093 node2093Labels := by rfl

theorem canonical22904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22904 raw22904Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw22904 raw22904Labels = mixedMoment B raw22904step0 raw22904step0Labels := by
      have hz : ∀ j, raw22904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22904step0 = (fun i j => raw22904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22904step0 raw22904; decide +kernel
      have hl : raw22904step0Labels = raw22904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22904 raw22904Labels permutation434 hz
    mixedMoment B raw22904step0 raw22904step0Labels = mixedMoment B raw22904step1 raw22904step1Labels := by
      have ha : raw22904step1 = (fun i j => raw22904step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22904step1 raw22904step0; decide +kernel
      have hl : raw22904step1Labels = raw22904step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22904step0 raw22904step0Labels permutation39 permutation2
    _ = mixedMoment B node2093 node2093Labels := by rfl

theorem canonical22905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22905 raw22905Labels = mixedMoment B node2011 node2011Labels := by
  calc
    mixedMoment B raw22905 raw22905Labels = mixedMoment B raw22905step0 raw22905step0Labels := by
      have ha : raw22905step0 = (fun i j => raw22905 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22905step0 raw22905; decide +kernel
      have hl : raw22905step0Labels = raw22905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22905 raw22905Labels permutation201 permutation2
    _ = mixedMoment B node2011 node2011Labels := by rfl

theorem canonical22906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22906 raw22906Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw22906 raw22906Labels = mixedMoment B raw22906step0 raw22906step0Labels := by
      have hz : ∀ j, raw22906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22906step0 = (fun i j => raw22906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22906step0 raw22906; decide +kernel
      have hl : raw22906step0Labels = raw22906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22906 raw22906Labels permutation434 hz
    _ = mixedMoment B node2246 node2246Labels := by rfl

theorem canonical22907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22907 raw22907Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw22907 raw22907Labels = mixedMoment B raw22907step0 raw22907step0Labels := by
      have hz : ∀ j, raw22907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22907step0 = (fun i j => raw22907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22907step0 raw22907; decide +kernel
      have hl : raw22907step0Labels = raw22907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22907 raw22907Labels permutation434 hz
    mixedMoment B raw22907step0 raw22907step0Labels = mixedMoment B raw22907step1 raw22907step1Labels := by
      have ha : raw22907step1 = (fun i j => raw22907step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22907step1 raw22907step0; decide +kernel
      have hl : raw22907step1Labels = raw22907step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22907step0 raw22907step0Labels permutation33 permutation2
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical22908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22908 raw22908Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw22908 raw22908Labels = mixedMoment B raw22908step0 raw22908step0Labels := by
      have hz : ∀ j, raw22908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22908step0 = (fun i j => raw22908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22908step0 raw22908; decide +kernel
      have hl : raw22908step0Labels = raw22908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22908 raw22908Labels permutation434 hz
    mixedMoment B raw22908step0 raw22908step0Labels = mixedMoment B raw22908step1 raw22908step1Labels := by
      have ha : raw22908step1 = (fun i j => raw22908step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22908step1 raw22908step0; decide +kernel
      have hl : raw22908step1Labels = raw22908step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22908step0 raw22908step0Labels permutation50 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical22909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22909 raw22909Labels = mixedMoment B node973 node973Labels := by
  calc
    mixedMoment B raw22909 raw22909Labels = mixedMoment B raw22909step0 raw22909step0Labels := by
      have ha : raw22909step0 = (fun i j => raw22909 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22909step0 raw22909; decide +kernel
      have hl : raw22909step0Labels = raw22909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22909 raw22909Labels permutation201 permutation2
    _ = mixedMoment B node973 node973Labels := by rfl

theorem canonical22910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22910 raw22910Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw22910 raw22910Labels = mixedMoment B raw22910step0 raw22910step0Labels := by
      have ha : raw22910step0 = (fun i j => raw22910 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22910step0 raw22910; decide +kernel
      have hl : raw22910step0Labels = raw22910Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22910 raw22910Labels permutation159 permutation2
    _ = mixedMoment B node2072 node2072Labels := by rfl

theorem canonical22911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22911 raw22911Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw22911 raw22911Labels = mixedMoment B raw22911step0 raw22911step0Labels := by
      have ha : raw22911step0 = (fun i j => raw22911 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22911step0 raw22911; decide +kernel
      have hl : raw22911step0Labels = raw22911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22911 raw22911Labels permutation183 permutation2
    _ = mixedMoment B node2072 node2072Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22912 raw22912Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw22912 raw22912Labels = mixedMoment B raw22912step0 raw22912step0Labels := by
      have ha : raw22912step0 = (fun i j => raw22912 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22912step0 raw22912; decide +kernel
      have hl : raw22912step0Labels = raw22912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22912 raw22912Labels permutation201 permutation2
    _ = mixedMoment B node1900 node1900Labels := by rfl

theorem canonical22913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22913 raw22913Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw22913 raw22913Labels = mixedMoment B raw22913step0 raw22913step0Labels := by
      have ha : raw22913step0 = (fun i j => raw22913 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22913step0 raw22913; decide +kernel
      have hl : raw22913step0Labels = raw22913Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22913 raw22913Labels permutation200 permutation2
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical22914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22914 raw22914Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw22914 raw22914Labels = mixedMoment B raw22914step0 raw22914step0Labels := by
      have ha : raw22914step0 = (fun i j => raw22914 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22914step0 raw22914; decide +kernel
      have hl : raw22914step0Labels = raw22914Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22914 raw22914Labels permutation201 permutation2
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical22915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22915 raw22915Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw22915 raw22915Labels = mixedMoment B raw22915step0 raw22915step0Labels := by
      have hz : ∀ j, raw22915 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22915step0 = (fun i j => raw22915 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22915step0 raw22915; decide +kernel
      have hl : raw22915step0Labels = raw22915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22915 raw22915Labels permutation590 hz
    mixedMoment B raw22915step0 raw22915step0Labels = mixedMoment B raw22915step1 raw22915step1Labels := by
      have ha : raw22915step1 = (fun i j => raw22915step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22915step1 raw22915step0; decide +kernel
      have hl : raw22915step1Labels = raw22915step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22915step0 raw22915step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical22916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22916 raw22916Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw22916 raw22916Labels = mixedMoment B raw22916step0 raw22916step0Labels := by
      have ha : raw22916step0 = (fun i j => raw22916 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22916step0 raw22916; decide +kernel
      have hl : raw22916step0Labels = raw22916Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22916 raw22916Labels permutation158 permutation2
    _ = mixedMoment B node2073 node2073Labels := by rfl

theorem canonical22917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22917 raw22917Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw22917 raw22917Labels = mixedMoment B raw22917step0 raw22917step0Labels := by
      have ha : raw22917step0 = (fun i j => raw22917 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22917step0 raw22917; decide +kernel
      have hl : raw22917step0Labels = raw22917Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22917 raw22917Labels permutation182 permutation2
    _ = mixedMoment B node2073 node2073Labels := by rfl

theorem canonical22918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22918 raw22918Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw22918 raw22918Labels = mixedMoment B raw22918step0 raw22918step0Labels := by
      have ha : raw22918step0 = (fun i j => raw22918 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22918step0 raw22918; decide +kernel
      have hl : raw22918step0Labels = raw22918Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22918 raw22918Labels permutation200 permutation2
    _ = mixedMoment B node1901 node1901Labels := by rfl

theorem canonical22919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22919 raw22919Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw22919 raw22919Labels = mixedMoment B raw22919step0 raw22919step0Labels := by
      have ha : raw22919step0 = (fun i j => raw22919 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22919step0 raw22919; decide +kernel
      have hl : raw22919step0Labels = raw22919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22919 raw22919Labels permutation201 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical22920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22920 raw22920Labels = mixedMoment B node1048 node1048Labels := by
  calc
    mixedMoment B raw22920 raw22920Labels = mixedMoment B raw22920step0 raw22920step0Labels := by
      have hz : ∀ j, raw22920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22920step0 = (fun i j => raw22920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22920step0 raw22920; decide +kernel
      have hl : raw22920step0Labels = raw22920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22920 raw22920Labels permutation434 hz
    mixedMoment B raw22920step0 raw22920step0Labels = mixedMoment B raw22920step1 raw22920step1Labels := by
      have hz : ∀ j, raw22920step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22920step1 = (fun i j => raw22920step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22920step1 raw22920step0; decide +kernel
      have hl : raw22920step1Labels = raw22920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22920step0 raw22920step0Labels permutation80 hz
    mixedMoment B raw22920step1 raw22920step1Labels = mixedMoment B raw22920step2 raw22920step2Labels := by
      have ha : raw22920step2 = (fun i j => raw22920step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22920step2 raw22920step1; decide +kernel
      have hl : raw22920step2Labels = raw22920step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22920step1 raw22920step1Labels permutation9 permutation2
    _ = mixedMoment B node1048 node1048Labels := by rfl

theorem canonical22921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22921 raw22921Labels = mixedMoment B node2114 node2114Labels := by
  calc
    mixedMoment B raw22921 raw22921Labels = mixedMoment B raw22921step0 raw22921step0Labels := by
      have hz : ∀ j, raw22921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22921step0 = (fun i j => raw22921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22921step0 raw22921; decide +kernel
      have hl : raw22921step0Labels = raw22921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22921 raw22921Labels permutation434 hz
    mixedMoment B raw22921step0 raw22921step0Labels = mixedMoment B raw22921step1 raw22921step1Labels := by
      have hz : ∀ j, raw22921step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22921step1 = (fun i j => raw22921step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22921step1 raw22921step0; decide +kernel
      have hl : raw22921step1Labels = raw22921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22921step0 raw22921step0Labels permutation80 hz
    mixedMoment B raw22921step1 raw22921step1Labels = mixedMoment B raw22921step2 raw22921step2Labels := by
      have ha : raw22921step2 = (fun i j => raw22921step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22921step2 raw22921step1; decide +kernel
      have hl : raw22921step2Labels = raw22921step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22921step1 raw22921step1Labels permutation9 permutation2
    _ = mixedMoment B node2114 node2114Labels := by rfl

theorem canonical22922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22922 raw22922Labels = mixedMoment B node2027 node2027Labels := by
  calc
    mixedMoment B raw22922 raw22922Labels = mixedMoment B raw22922step0 raw22922step0Labels := by
      have hz : ∀ j, raw22922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22922step0 = (fun i j => raw22922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22922step0 raw22922; decide +kernel
      have hl : raw22922step0Labels = raw22922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22922 raw22922Labels permutation434 hz
    mixedMoment B raw22922step0 raw22922step0Labels = mixedMoment B raw22922step1 raw22922step1Labels := by
      have ha : raw22922step1 = (fun i j => raw22922step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22922step1 raw22922step0; decide +kernel
      have hl : raw22922step1Labels = raw22922step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22922step0 raw22922step0Labels permutation39 permutation2
    _ = mixedMoment B node2027 node2027Labels := by rfl

theorem canonical22923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22923 raw22923Labels = mixedMoment B node2027 node2027Labels := by
  calc
    mixedMoment B raw22923 raw22923Labels = mixedMoment B raw22923step0 raw22923step0Labels := by
      have hz : ∀ j, raw22923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22923step0 = (fun i j => raw22923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22923step0 raw22923; decide +kernel
      have hl : raw22923step0Labels = raw22923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22923 raw22923Labels permutation346 hz
    mixedMoment B raw22923step0 raw22923step0Labels = mixedMoment B raw22923step1 raw22923step1Labels := by
      have ha : raw22923step1 = (fun i j => raw22923step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22923step1 raw22923step0; decide +kernel
      have hl : raw22923step1Labels = raw22923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22923step0 raw22923step0Labels permutation39 permutation2
    _ = mixedMoment B node2027 node2027Labels := by rfl

theorem canonical22924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22924 raw22924Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw22924 raw22924Labels = mixedMoment B raw22924step0 raw22924step0Labels := by
      have hz : ∀ j, raw22924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22924step0 = (fun i j => raw22924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22924step0 raw22924; decide +kernel
      have hl : raw22924step0Labels = raw22924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22924 raw22924Labels permutation434 hz
    mixedMoment B raw22924step0 raw22924step0Labels = mixedMoment B raw22924step1 raw22924step1Labels := by
      have hz : ∀ j, raw22924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22924step1 = (fun i j => raw22924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22924step1 raw22924step0; decide +kernel
      have hl : raw22924step1Labels = raw22924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22924step0 raw22924step0Labels permutation80 hz
    _ = mixedMoment B node2267 node2267Labels := by rfl

theorem canonical22925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22925 raw22925Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw22925 raw22925Labels = mixedMoment B raw22925step0 raw22925step0Labels := by
      have hz : ∀ j, raw22925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22925step0 = (fun i j => raw22925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22925step0 raw22925; decide +kernel
      have hl : raw22925step0Labels = raw22925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22925 raw22925Labels permutation434 hz
    mixedMoment B raw22925step0 raw22925step0Labels = mixedMoment B raw22925step1 raw22925step1Labels := by
      have hz : ∀ j, raw22925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22925step1 = (fun i j => raw22925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22925step1 raw22925step0; decide +kernel
      have hl : raw22925step1Labels = raw22925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22925step0 raw22925step0Labels permutation80 hz
    mixedMoment B raw22925step1 raw22925step1Labels = mixedMoment B raw22925step2 raw22925step2Labels := by
      have ha : raw22925step2 = (fun i j => raw22925step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22925step2 raw22925step1; decide +kernel
      have hl : raw22925step2Labels = raw22925step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22925step1 raw22925step1Labels permutation9 permutation2
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical22926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22926 raw22926Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw22926 raw22926Labels = mixedMoment B raw22926step0 raw22926step0Labels := by
      have hz : ∀ j, raw22926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22926step0 = (fun i j => raw22926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22926step0 raw22926; decide +kernel
      have hl : raw22926step0Labels = raw22926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22926 raw22926Labels permutation434 hz
    mixedMoment B raw22926step0 raw22926step0Labels = mixedMoment B raw22926step1 raw22926step1Labels := by
      have hz : ∀ j, raw22926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22926step1 = (fun i j => raw22926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22926step1 raw22926step0; decide +kernel
      have hl : raw22926step1Labels = raw22926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22926step0 raw22926step0Labels permutation80 hz
    mixedMoment B raw22926step1 raw22926step1Labels = mixedMoment B raw22926step2 raw22926step2Labels := by
      have ha : raw22926step2 = (fun i j => raw22926step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22926step2 raw22926step1; decide +kernel
      have hl : raw22926step2Labels = raw22926step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22926step1 raw22926step1Labels permutation12 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical22927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22927 raw22927Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw22927 raw22927Labels = mixedMoment B raw22927step0 raw22927step0Labels := by
      have hz : ∀ j, raw22927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22927step0 = (fun i j => raw22927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22927step0 raw22927; decide +kernel
      have hl : raw22927step0Labels = raw22927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22927 raw22927Labels permutation434 hz
    mixedMoment B raw22927step0 raw22927step0Labels = mixedMoment B raw22927step1 raw22927step1Labels := by
      have hz : ∀ j, raw22927step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22927step1 = (fun i j => raw22927step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22927step1 raw22927step0; decide +kernel
      have hl : raw22927step1Labels = raw22927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22927step0 raw22927step0Labels permutation80 hz
    mixedMoment B raw22927step1 raw22927step1Labels = mixedMoment B raw22927step2 raw22927step2Labels := by
      have ha : raw22927step2 = (fun i j => raw22927step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22927step2 raw22927step1; decide +kernel
      have hl : raw22927step2Labels = raw22927step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22927step1 raw22927step1Labels permutation9 permutation2
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical22928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22928 raw22928Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw22928 raw22928Labels = mixedMoment B raw22928step0 raw22928step0Labels := by
      have hz : ∀ j, raw22928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22928step0 = (fun i j => raw22928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22928step0 raw22928; decide +kernel
      have hl : raw22928step0Labels = raw22928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22928 raw22928Labels permutation434 hz
    mixedMoment B raw22928step0 raw22928step0Labels = mixedMoment B raw22928step1 raw22928step1Labels := by
      have ha : raw22928step1 = (fun i j => raw22928step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22928step1 raw22928step0; decide +kernel
      have hl : raw22928step1Labels = raw22928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22928step0 raw22928step0Labels permutation39 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical22929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22929 raw22929Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw22929 raw22929Labels = mixedMoment B raw22929step0 raw22929step0Labels := by
      have hz : ∀ j, raw22929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22929step0 = (fun i j => raw22929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22929step0 raw22929; decide +kernel
      have hl : raw22929step0Labels = raw22929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22929 raw22929Labels permutation346 hz
    mixedMoment B raw22929step0 raw22929step0Labels = mixedMoment B raw22929step1 raw22929step1Labels := by
      have ha : raw22929step1 = (fun i j => raw22929step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22929step1 raw22929step0; decide +kernel
      have hl : raw22929step1Labels = raw22929step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22929step0 raw22929step0Labels permutation39 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical22930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22930 raw22930Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw22930 raw22930Labels = mixedMoment B raw22930step0 raw22930step0Labels := by
      have hz : ∀ j, raw22930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22930step0 = (fun i j => raw22930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22930step0 raw22930; decide +kernel
      have hl : raw22930step0Labels = raw22930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22930 raw22930Labels permutation434 hz
    mixedMoment B raw22930step0 raw22930step0Labels = mixedMoment B raw22930step1 raw22930step1Labels := by
      have hz : ∀ j, raw22930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22930step1 = (fun i j => raw22930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22930step1 raw22930step0; decide +kernel
      have hl : raw22930step1Labels = raw22930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22930step0 raw22930step0Labels permutation80 hz
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical22931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22931 raw22931Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw22931 raw22931Labels = mixedMoment B raw22931step0 raw22931step0Labels := by
      have hz : ∀ j, raw22931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22931step0 = (fun i j => raw22931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22931step0 raw22931; decide +kernel
      have hl : raw22931step0Labels = raw22931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22931 raw22931Labels permutation434 hz
    mixedMoment B raw22931step0 raw22931step0Labels = mixedMoment B raw22931step1 raw22931step1Labels := by
      have hz : ∀ j, raw22931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22931step1 = (fun i j => raw22931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22931step1 raw22931step0; decide +kernel
      have hl : raw22931step1Labels = raw22931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22931step0 raw22931step0Labels permutation80 hz
    mixedMoment B raw22931step1 raw22931step1Labels = mixedMoment B raw22931step2 raw22931step2Labels := by
      have ha : raw22931step2 = (fun i j => raw22931step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22931step2 raw22931step1; decide +kernel
      have hl : raw22931step2Labels = raw22931step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22931step1 raw22931step1Labels permutation9 permutation2
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical22932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22932 raw22932Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw22932 raw22932Labels = mixedMoment B raw22932step0 raw22932step0Labels := by
      have hz : ∀ j, raw22932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22932step0 = (fun i j => raw22932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22932step0 raw22932; decide +kernel
      have hl : raw22932step0Labels = raw22932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22932 raw22932Labels permutation434 hz
    mixedMoment B raw22932step0 raw22932step0Labels = mixedMoment B raw22932step1 raw22932step1Labels := by
      have hz : ∀ j, raw22932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22932step1 = (fun i j => raw22932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22932step1 raw22932step0; decide +kernel
      have hl : raw22932step1Labels = raw22932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22932step0 raw22932step0Labels permutation80 hz
    mixedMoment B raw22932step1 raw22932step1Labels = mixedMoment B raw22932step2 raw22932step2Labels := by
      have ha : raw22932step2 = (fun i j => raw22932step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22932step2 raw22932step1; decide +kernel
      have hl : raw22932step2Labels = raw22932step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22932step1 raw22932step1Labels permutation9 permutation2
    _ = mixedMoment B node4185 node4185Labels := by rfl

theorem canonical22933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22933 raw22933Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw22933 raw22933Labels = mixedMoment B raw22933step0 raw22933step0Labels := by
      have hz : ∀ j, raw22933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22933step0 = (fun i j => raw22933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22933step0 raw22933; decide +kernel
      have hl : raw22933step0Labels = raw22933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22933 raw22933Labels permutation434 hz
    mixedMoment B raw22933step0 raw22933step0Labels = mixedMoment B raw22933step1 raw22933step1Labels := by
      have ha : raw22933step1 = (fun i j => raw22933step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22933step1 raw22933step0; decide +kernel
      have hl : raw22933step1Labels = raw22933step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22933step0 raw22933step0Labels permutation39 permutation2
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical22934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22934 raw22934Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw22934 raw22934Labels = mixedMoment B raw22934step0 raw22934step0Labels := by
      have hz : ∀ j, raw22934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22934step0 = (fun i j => raw22934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22934step0 raw22934; decide +kernel
      have hl : raw22934step0Labels = raw22934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22934 raw22934Labels permutation346 hz
    mixedMoment B raw22934step0 raw22934step0Labels = mixedMoment B raw22934step1 raw22934step1Labels := by
      have ha : raw22934step1 = (fun i j => raw22934step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22934step1 raw22934step0; decide +kernel
      have hl : raw22934step1Labels = raw22934step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22934step0 raw22934step0Labels permutation39 permutation2
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical22935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22935 raw22935Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw22935 raw22935Labels = mixedMoment B raw22935step0 raw22935step0Labels := by
      have hz : ∀ j, raw22935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22935step0 = (fun i j => raw22935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22935step0 raw22935; decide +kernel
      have hl : raw22935step0Labels = raw22935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22935 raw22935Labels permutation434 hz
    mixedMoment B raw22935step0 raw22935step0Labels = mixedMoment B raw22935step1 raw22935step1Labels := by
      have hz : ∀ j, raw22935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22935step1 = (fun i j => raw22935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22935step1 raw22935step0; decide +kernel
      have hl : raw22935step1Labels = raw22935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22935step0 raw22935step0Labels permutation80 hz
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical22936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22936 raw22936Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw22936 raw22936Labels = mixedMoment B raw22936step0 raw22936step0Labels := by
      have hz : ∀ j, raw22936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22936step0 = (fun i j => raw22936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22936step0 raw22936; decide +kernel
      have hl : raw22936step0Labels = raw22936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22936 raw22936Labels permutation434 hz
    mixedMoment B raw22936step0 raw22936step0Labels = mixedMoment B raw22936step1 raw22936step1Labels := by
      have hz : ∀ j, raw22936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22936step1 = (fun i j => raw22936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22936step1 raw22936step0; decide +kernel
      have hl : raw22936step1Labels = raw22936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22936step0 raw22936step0Labels permutation80 hz
    mixedMoment B raw22936step1 raw22936step1Labels = mixedMoment B raw22936step2 raw22936step2Labels := by
      have ha : raw22936step2 = (fun i j => raw22936step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22936step2 raw22936step1; decide +kernel
      have hl : raw22936step2Labels = raw22936step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22936step1 raw22936step1Labels permutation12 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical22937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22937 raw22937Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw22937 raw22937Labels = mixedMoment B raw22937step0 raw22937step0Labels := by
      have hz : ∀ j, raw22937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22937step0 = (fun i j => raw22937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22937step0 raw22937; decide +kernel
      have hl : raw22937step0Labels = raw22937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22937 raw22937Labels permutation434 hz
    mixedMoment B raw22937step0 raw22937step0Labels = mixedMoment B raw22937step1 raw22937step1Labels := by
      have ha : raw22937step1 = (fun i j => raw22937step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22937step1 raw22937step0; decide +kernel
      have hl : raw22937step1Labels = raw22937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22937step0 raw22937step0Labels permutation33 permutation2
    _ = mixedMoment B node4154 node4154Labels := by rfl

theorem canonical22938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22938 raw22938Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw22938 raw22938Labels = mixedMoment B raw22938step0 raw22938step0Labels := by
      have hz : ∀ j, raw22938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22938step0 = (fun i j => raw22938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22938step0 raw22938; decide +kernel
      have hl : raw22938step0Labels = raw22938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22938 raw22938Labels permutation434 hz
    mixedMoment B raw22938step0 raw22938step0Labels = mixedMoment B raw22938step1 raw22938step1Labels := by
      have ha : raw22938step1 = (fun i j => raw22938step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22938step1 raw22938step0; decide +kernel
      have hl : raw22938step1Labels = raw22938step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22938step0 raw22938step0Labels permutation33 permutation2
    _ = mixedMoment B node4368 node4368Labels := by rfl

theorem canonical22939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22939 raw22939Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw22939 raw22939Labels = mixedMoment B raw22939step0 raw22939step0Labels := by
      have ha : raw22939step0 = (fun i j => raw22939 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22939step0 raw22939; decide +kernel
      have hl : raw22939step0Labels = raw22939Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22939 raw22939Labels permutation201 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

theorem canonical22940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22940 raw22940Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw22940 raw22940Labels = mixedMoment B raw22940step0 raw22940step0Labels := by
      have hz : ∀ j, raw22940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22940step0 = (fun i j => raw22940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22940step0 raw22940; decide +kernel
      have hl : raw22940step0Labels = raw22940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22940 raw22940Labels permutation434 hz
    _ = mixedMoment B node4459 node4459Labels := by rfl

theorem canonical22941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22941 raw22941Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw22941 raw22941Labels = mixedMoment B raw22941step0 raw22941step0Labels := by
      have hz : ∀ j, raw22941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22941step0 = (fun i j => raw22941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22941step0 raw22941; decide +kernel
      have hl : raw22941step0Labels = raw22941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22941 raw22941Labels permutation434 hz
    mixedMoment B raw22941step0 raw22941step0Labels = mixedMoment B raw22941step1 raw22941step1Labels := by
      have ha : raw22941step1 = (fun i j => raw22941step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22941step1 raw22941step0; decide +kernel
      have hl : raw22941step1Labels = raw22941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22941step0 raw22941step0Labels permutation33 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical22942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22942 raw22942Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw22942 raw22942Labels = mixedMoment B raw22942step0 raw22942step0Labels := by
      have hz : ∀ j, raw22942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22942step0 = (fun i j => raw22942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22942step0 raw22942; decide +kernel
      have hl : raw22942step0Labels = raw22942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22942 raw22942Labels permutation346 hz
    mixedMoment B raw22942step0 raw22942step0Labels = mixedMoment B raw22942step1 raw22942step1Labels := by
      have ha : raw22942step1 = (fun i j => raw22942step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22942step1 raw22942step0; decide +kernel
      have hl : raw22942step1Labels = raw22942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22942step0 raw22942step0Labels permutation33 permutation2
    _ = mixedMoment B node4154 node4154Labels := by rfl

theorem canonical22943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22943 raw22943Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw22943 raw22943Labels = mixedMoment B raw22943step0 raw22943step0Labels := by
      have hz : ∀ j, raw22943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22943step0 = (fun i j => raw22943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22943step0 raw22943; decide +kernel
      have hl : raw22943step0Labels = raw22943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22943 raw22943Labels permutation346 hz
    mixedMoment B raw22943step0 raw22943step0Labels = mixedMoment B raw22943step1 raw22943step1Labels := by
      have ha : raw22943step1 = (fun i j => raw22943step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22943step1 raw22943step0; decide +kernel
      have hl : raw22943step1Labels = raw22943step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22943step0 raw22943step0Labels permutation33 permutation2
    _ = mixedMoment B node4368 node4368Labels := by rfl

theorem canonical22944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22944 raw22944Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw22944 raw22944Labels = mixedMoment B raw22944step0 raw22944step0Labels := by
      have ha : raw22944step0 = (fun i j => raw22944 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22944step0 raw22944; decide +kernel
      have hl : raw22944step0Labels = raw22944Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22944 raw22944Labels permutation177 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

theorem canonical22945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22945 raw22945Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw22945 raw22945Labels = mixedMoment B raw22945step0 raw22945step0Labels := by
      have hz : ∀ j, raw22945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22945step0 = (fun i j => raw22945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22945step0 raw22945; decide +kernel
      have hl : raw22945step0Labels = raw22945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22945 raw22945Labels permutation346 hz
    _ = mixedMoment B node4459 node4459Labels := by rfl

theorem canonical22946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22946 raw22946Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw22946 raw22946Labels = mixedMoment B raw22946step0 raw22946step0Labels := by
      have hz : ∀ j, raw22946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22946step0 = (fun i j => raw22946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22946step0 raw22946; decide +kernel
      have hl : raw22946step0Labels = raw22946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22946 raw22946Labels permutation346 hz
    mixedMoment B raw22946step0 raw22946step0Labels = mixedMoment B raw22946step1 raw22946step1Labels := by
      have ha : raw22946step1 = (fun i j => raw22946step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22946step1 raw22946step0; decide +kernel
      have hl : raw22946step1Labels = raw22946step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22946step0 raw22946step0Labels permutation33 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical22947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22947 raw22947Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw22947 raw22947Labels = mixedMoment B raw22947step0 raw22947step0Labels := by
      have hz : ∀ j, raw22947 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22947step0 = (fun i j => raw22947 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22947step0 raw22947; decide +kernel
      have hl : raw22947step0Labels = raw22947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22947 raw22947Labels permutation434 hz
    mixedMoment B raw22947step0 raw22947step0Labels = mixedMoment B raw22947step1 raw22947step1Labels := by
      have hz : ∀ j, raw22947step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22947step1 = (fun i j => raw22947step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22947step1 raw22947step0; decide +kernel
      have hl : raw22947step1Labels = raw22947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22947step0 raw22947step0Labels permutation80 hz
    mixedMoment B raw22947step1 raw22947step1Labels = mixedMoment B raw22947step2 raw22947step2Labels := by
      have ha : raw22947step2 = (fun i j => raw22947step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22947step2 raw22947step1; decide +kernel
      have hl : raw22947step2Labels = raw22947step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22947step1 raw22947step1Labels permutation9 permutation2
    _ = mixedMoment B node4160 node4160Labels := by rfl

theorem canonical22948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22948 raw22948Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw22948 raw22948Labels = mixedMoment B raw22948step0 raw22948step0Labels := by
      have hz : ∀ j, raw22948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22948step0 = (fun i j => raw22948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22948step0 raw22948; decide +kernel
      have hl : raw22948step0Labels = raw22948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22948 raw22948Labels permutation434 hz
    mixedMoment B raw22948step0 raw22948step0Labels = mixedMoment B raw22948step1 raw22948step1Labels := by
      have hz : ∀ j, raw22948step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22948step1 = (fun i j => raw22948step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22948step1 raw22948step0; decide +kernel
      have hl : raw22948step1Labels = raw22948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22948step0 raw22948step0Labels permutation80 hz
    mixedMoment B raw22948step1 raw22948step1Labels = mixedMoment B raw22948step2 raw22948step2Labels := by
      have ha : raw22948step2 = (fun i j => raw22948step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22948step2 raw22948step1; decide +kernel
      have hl : raw22948step2Labels = raw22948step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22948step1 raw22948step1Labels permutation9 permutation2
    _ = mixedMoment B node4373 node4373Labels := by rfl

theorem canonical22949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22949 raw22949Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw22949 raw22949Labels = mixedMoment B raw22949step0 raw22949step0Labels := by
      have hz : ∀ j, raw22949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22949step0 = (fun i j => raw22949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22949step0 raw22949; decide +kernel
      have hl : raw22949step0Labels = raw22949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22949 raw22949Labels permutation434 hz
    mixedMoment B raw22949step0 raw22949step0Labels = mixedMoment B raw22949step1 raw22949step1Labels := by
      have ha : raw22949step1 = (fun i j => raw22949step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22949step1 raw22949step0; decide +kernel
      have hl : raw22949step1Labels = raw22949step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22949step0 raw22949step0Labels permutation39 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

theorem canonical22950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22950 raw22950Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw22950 raw22950Labels = mixedMoment B raw22950step0 raw22950step0Labels := by
      have hz : ∀ j, raw22950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22950step0 = (fun i j => raw22950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22950step0 raw22950; decide +kernel
      have hl : raw22950step0Labels = raw22950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22950 raw22950Labels permutation346 hz
    mixedMoment B raw22950step0 raw22950step0Labels = mixedMoment B raw22950step1 raw22950step1Labels := by
      have ha : raw22950step1 = (fun i j => raw22950step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22950step1 raw22950step0; decide +kernel
      have hl : raw22950step1Labels = raw22950step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22950step0 raw22950step0Labels permutation39 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

theorem canonical22951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22951 raw22951Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw22951 raw22951Labels = mixedMoment B raw22951step0 raw22951step0Labels := by
      have hz : ∀ j, raw22951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22951step0 = (fun i j => raw22951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22951step0 raw22951; decide +kernel
      have hl : raw22951step0Labels = raw22951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22951 raw22951Labels permutation434 hz
    mixedMoment B raw22951step0 raw22951step0Labels = mixedMoment B raw22951step1 raw22951step1Labels := by
      have hz : ∀ j, raw22951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22951step1 = (fun i j => raw22951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22951step1 raw22951step0; decide +kernel
      have hl : raw22951step1Labels = raw22951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22951step0 raw22951step0Labels permutation80 hz
    mixedMoment B raw22951step1 raw22951step1Labels = mixedMoment B raw22951step2 raw22951step2Labels := by
      have ha : raw22951step2 = (fun i j => raw22951step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22951step2 raw22951step1; decide +kernel
      have hl : raw22951step2Labels = raw22951step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22951step1 raw22951step1Labels permutation9 permutation2
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical22952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22952 raw22952Labels = mixedMoment B node4162 node4162Labels := by
  calc
    mixedMoment B raw22952 raw22952Labels = mixedMoment B raw22952step0 raw22952step0Labels := by
      have hz : ∀ j, raw22952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22952step0 = (fun i j => raw22952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22952step0 raw22952; decide +kernel
      have hl : raw22952step0Labels = raw22952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22952 raw22952Labels permutation434 hz
    mixedMoment B raw22952step0 raw22952step0Labels = mixedMoment B raw22952step1 raw22952step1Labels := by
      have hz : ∀ j, raw22952step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22952step1 = (fun i j => raw22952step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22952step1 raw22952step0; decide +kernel
      have hl : raw22952step1Labels = raw22952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22952step0 raw22952step0Labels permutation80 hz
    _ = mixedMoment B node4162 node4162Labels := by rfl

theorem canonical22953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22953 raw22953Labels = mixedMoment B node4375 node4375Labels := by
  calc
    mixedMoment B raw22953 raw22953Labels = mixedMoment B raw22953step0 raw22953step0Labels := by
      have hz : ∀ j, raw22953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22953step0 = (fun i j => raw22953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22953step0 raw22953; decide +kernel
      have hl : raw22953step0Labels = raw22953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22953 raw22953Labels permutation434 hz
    mixedMoment B raw22953step0 raw22953step0Labels = mixedMoment B raw22953step1 raw22953step1Labels := by
      have hz : ∀ j, raw22953step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22953step1 = (fun i j => raw22953step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22953step1 raw22953step0; decide +kernel
      have hl : raw22953step1Labels = raw22953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22953step0 raw22953step0Labels permutation80 hz
    _ = mixedMoment B node4375 node4375Labels := by rfl

theorem canonical22954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22954 raw22954Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw22954 raw22954Labels = mixedMoment B raw22954step0 raw22954step0Labels := by
      have hz : ∀ j, raw22954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22954step0 = (fun i j => raw22954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22954step0 raw22954; decide +kernel
      have hl : raw22954step0Labels = raw22954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22954 raw22954Labels permutation434 hz
    mixedMoment B raw22954step0 raw22954step0Labels = mixedMoment B raw22954step1 raw22954step1Labels := by
      have ha : raw22954step1 = (fun i j => raw22954step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22954step1 raw22954step0; decide +kernel
      have hl : raw22954step1Labels = raw22954step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22954step0 raw22954step0Labels permutation38 permutation2
    _ = mixedMoment B node4336 node4336Labels := by rfl

theorem canonical22955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22955 raw22955Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw22955 raw22955Labels = mixedMoment B raw22955step0 raw22955step0Labels := by
      have hz : ∀ j, raw22955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22955step0 = (fun i j => raw22955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22955step0 raw22955; decide +kernel
      have hl : raw22955step0Labels = raw22955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22955 raw22955Labels permutation346 hz
    mixedMoment B raw22955step0 raw22955step0Labels = mixedMoment B raw22955step1 raw22955step1Labels := by
      have ha : raw22955step1 = (fun i j => raw22955step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22955step1 raw22955step0; decide +kernel
      have hl : raw22955step1Labels = raw22955step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22955step0 raw22955step0Labels permutation38 permutation2
    _ = mixedMoment B node4336 node4336Labels := by rfl

theorem canonical22956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22956 raw22956Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw22956 raw22956Labels = mixedMoment B raw22956step0 raw22956step0Labels := by
      have hz : ∀ j, raw22956 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22956step0 = (fun i j => raw22956 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22956step0 raw22956; decide +kernel
      have hl : raw22956step0Labels = raw22956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22956 raw22956Labels permutation434 hz
    mixedMoment B raw22956step0 raw22956step0Labels = mixedMoment B raw22956step1 raw22956step1Labels := by
      have hz : ∀ j, raw22956step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22956step1 = (fun i j => raw22956step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22956step1 raw22956step0; decide +kernel
      have hl : raw22956step1Labels = raw22956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22956step0 raw22956step0Labels permutation80 hz
    _ = mixedMoment B node4464 node4464Labels := by rfl

theorem canonical22987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22987 raw22987Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw22987 raw22987Labels = mixedMoment B raw22987step0 raw22987step0Labels := by
      have hz : ∀ j, raw22987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22987step0 = (fun i j => raw22987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22987step0 raw22987; decide +kernel
      have hl : raw22987step0Labels = raw22987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22987 raw22987Labels permutation434 hz
    mixedMoment B raw22987step0 raw22987step0Labels = mixedMoment B raw22987step1 raw22987step1Labels := by
      have hz : ∀ j, raw22987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22987step1 = (fun i j => raw22987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22987step1 raw22987step0; decide +kernel
      have hl : raw22987step1Labels = raw22987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22987step0 raw22987step0Labels permutation80 hz
    mixedMoment B raw22987step1 raw22987step1Labels = mixedMoment B raw22987step2 raw22987step2Labels := by
      have ha : raw22987step2 = (fun i j => raw22987step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22987step2 raw22987step1; decide +kernel
      have hl : raw22987step2Labels = raw22987step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22987step1 raw22987step1Labels permutation12 permutation7
    mixedMoment B raw22987step2 raw22987step2Labels = mixedMoment B raw22987step3 raw22987step3Labels := by
      have ha : raw22987step3 = -raw22987step2 := by apply Matrix.ext; change ∀ i j, raw22987step3 i j = -(raw22987step2 i j); unfold raw22987step3 raw22987step2; decide +kernel
      have hl : raw22987step3Labels = raw22987step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22987step3 raw22987step3Labels = mixedMoment B raw22987step4 raw22987step4Labels := by
      have ha : raw22987step4 = raw22987step3 := by apply Matrix.ext; unfold raw22987step4 raw22987step3; decide +kernel
      have hl : raw22987step3Labels = labelEmbedding1 ∘ raw22987step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22987step3 raw22987step3Labels raw22987step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical22988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22988 raw22988Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw22988 raw22988Labels = mixedMoment B raw22988step0 raw22988step0Labels := by
      have hz : ∀ j, raw22988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22988step0 = (fun i j => raw22988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22988step0 raw22988; decide +kernel
      have hl : raw22988step0Labels = raw22988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22988 raw22988Labels permutation434 hz
    mixedMoment B raw22988step0 raw22988step0Labels = mixedMoment B raw22988step1 raw22988step1Labels := by
      have ha : raw22988step1 = (fun i j => raw22988step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22988step1 raw22988step0; decide +kernel
      have hl : raw22988step1Labels = raw22988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22988step0 raw22988step0Labels permutation42 permutation7
    mixedMoment B raw22988step1 raw22988step1Labels = mixedMoment B raw22988step2 raw22988step2Labels := by
      have ha : raw22988step2 = -raw22988step1 := by apply Matrix.ext; change ∀ i j, raw22988step2 i j = -(raw22988step1 i j); unfold raw22988step2 raw22988step1; decide +kernel
      have hl : raw22988step2Labels = raw22988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22988step2 raw22988step2Labels = mixedMoment B raw22988step3 raw22988step3Labels := by
      have ha : raw22988step3 = raw22988step2 := by apply Matrix.ext; unfold raw22988step3 raw22988step2; decide +kernel
      have hl : raw22988step2Labels = labelEmbedding1 ∘ raw22988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22988step2 raw22988step2Labels raw22988step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical22989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22989 raw22989Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw22989 raw22989Labels = mixedMoment B raw22989step0 raw22989step0Labels := by
      have hz : ∀ j, raw22989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22989step0 = (fun i j => raw22989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22989step0 raw22989; decide +kernel
      have hl : raw22989step0Labels = raw22989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22989 raw22989Labels permutation346 hz
    mixedMoment B raw22989step0 raw22989step0Labels = mixedMoment B raw22989step1 raw22989step1Labels := by
      have ha : raw22989step1 = (fun i j => raw22989step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22989step1 raw22989step0; decide +kernel
      have hl : raw22989step1Labels = raw22989step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22989step0 raw22989step0Labels permutation42 permutation7
    mixedMoment B raw22989step1 raw22989step1Labels = mixedMoment B raw22989step2 raw22989step2Labels := by
      have ha : raw22989step2 = -raw22989step1 := by apply Matrix.ext; change ∀ i j, raw22989step2 i j = -(raw22989step1 i j); unfold raw22989step2 raw22989step1; decide +kernel
      have hl : raw22989step2Labels = raw22989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22989step2 raw22989step2Labels = mixedMoment B raw22989step3 raw22989step3Labels := by
      have ha : raw22989step3 = raw22989step2 := by apply Matrix.ext; unfold raw22989step3 raw22989step2; decide +kernel
      have hl : raw22989step2Labels = labelEmbedding1 ∘ raw22989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22989step2 raw22989step2Labels raw22989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical22990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22990 raw22990Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw22990 raw22990Labels = mixedMoment B raw22990step0 raw22990step0Labels := by
      have hz : ∀ j, raw22990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22990step0 = (fun i j => raw22990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22990step0 raw22990; decide +kernel
      have hl : raw22990step0Labels = raw22990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22990 raw22990Labels permutation434 hz
    mixedMoment B raw22990step0 raw22990step0Labels = mixedMoment B raw22990step1 raw22990step1Labels := by
      have hz : ∀ j, raw22990step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22990step1 = (fun i j => raw22990step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22990step1 raw22990step0; decide +kernel
      have hl : raw22990step1Labels = raw22990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22990step0 raw22990step0Labels permutation80 hz
    mixedMoment B raw22990step1 raw22990step1Labels = mixedMoment B raw22990step2 raw22990step2Labels := by
      have ha : raw22990step2 = (fun i j => raw22990step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22990step2 raw22990step1; decide +kernel
      have hl : raw22990step2Labels = raw22990step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22990step1 raw22990step1Labels permutation12 permutation7
    mixedMoment B raw22990step2 raw22990step2Labels = mixedMoment B raw22990step3 raw22990step3Labels := by
      have ha : raw22990step3 = -raw22990step2 := by apply Matrix.ext; change ∀ i j, raw22990step3 i j = -(raw22990step2 i j); unfold raw22990step3 raw22990step2; decide +kernel
      have hl : raw22990step3Labels = raw22990step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22990step3 raw22990step3Labels = mixedMoment B raw22990step4 raw22990step4Labels := by
      have ha : raw22990step4 = raw22990step3 := by apply Matrix.ext; unfold raw22990step4 raw22990step3; decide +kernel
      have hl : raw22990step3Labels = labelEmbedding1 ∘ raw22990step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22990step3 raw22990step3Labels raw22990step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical22991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22991 raw22991Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw22991 raw22991Labels = mixedMoment B raw22991step0 raw22991step0Labels := by
      have hz : ∀ j, raw22991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22991step0 = (fun i j => raw22991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22991step0 raw22991; decide +kernel
      have hl : raw22991step0Labels = raw22991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22991 raw22991Labels permutation434 hz
    mixedMoment B raw22991step0 raw22991step0Labels = mixedMoment B raw22991step1 raw22991step1Labels := by
      have hz : ∀ j, raw22991step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22991step1 = (fun i j => raw22991step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22991step1 raw22991step0; decide +kernel
      have hl : raw22991step1Labels = raw22991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22991step0 raw22991step0Labels permutation80 hz
    mixedMoment B raw22991step1 raw22991step1Labels = mixedMoment B raw22991step2 raw22991step2Labels := by
      have ha : raw22991step2 = (fun i j => raw22991step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22991step2 raw22991step1; decide +kernel
      have hl : raw22991step2Labels = raw22991step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22991step1 raw22991step1Labels permutation12 permutation7
    mixedMoment B raw22991step2 raw22991step2Labels = mixedMoment B raw22991step3 raw22991step3Labels := by
      have ha : raw22991step3 = -raw22991step2 := by apply Matrix.ext; change ∀ i j, raw22991step3 i j = -(raw22991step2 i j); unfold raw22991step3 raw22991step2; decide +kernel
      have hl : raw22991step3Labels = raw22991step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22991step3 raw22991step3Labels = mixedMoment B raw22991step4 raw22991step4Labels := by
      have ha : raw22991step4 = raw22991step3 := by apply Matrix.ext; unfold raw22991step4 raw22991step3; decide +kernel
      have hl : raw22991step3Labels = labelEmbedding1 ∘ raw22991step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22991step3 raw22991step3Labels raw22991step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical22992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22992 raw22992Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw22992 raw22992Labels = mixedMoment B raw22992step0 raw22992step0Labels := by
      have hz : ∀ j, raw22992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22992step0 = (fun i j => raw22992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22992step0 raw22992; decide +kernel
      have hl : raw22992step0Labels = raw22992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22992 raw22992Labels permutation434 hz
    mixedMoment B raw22992step0 raw22992step0Labels = mixedMoment B raw22992step1 raw22992step1Labels := by
      have hz : ∀ j, raw22992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22992step1 = (fun i j => raw22992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22992step1 raw22992step0; decide +kernel
      have hl : raw22992step1Labels = raw22992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22992step0 raw22992step0Labels permutation80 hz
    mixedMoment B raw22992step1 raw22992step1Labels = mixedMoment B raw22992step2 raw22992step2Labels := by
      have ha : raw22992step2 = (fun i j => raw22992step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22992step2 raw22992step1; decide +kernel
      have hl : raw22992step2Labels = raw22992step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22992step1 raw22992step1Labels permutation12 permutation7
    mixedMoment B raw22992step2 raw22992step2Labels = mixedMoment B raw22992step3 raw22992step3Labels := by
      have ha : raw22992step3 = -raw22992step2 := by apply Matrix.ext; change ∀ i j, raw22992step3 i j = -(raw22992step2 i j); unfold raw22992step3 raw22992step2; decide +kernel
      have hl : raw22992step3Labels = raw22992step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22992step3 raw22992step3Labels = mixedMoment B raw22992step4 raw22992step4Labels := by
      have ha : raw22992step4 = raw22992step3 := by apply Matrix.ext; unfold raw22992step4 raw22992step3; decide +kernel
      have hl : raw22992step3Labels = labelEmbedding1 ∘ raw22992step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22992step3 raw22992step3Labels raw22992step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1525 node1525Labels := by rfl

theorem canonical22993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22993 raw22993Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw22993 raw22993Labels = mixedMoment B raw22993step0 raw22993step0Labels := by
      have hz : ∀ j, raw22993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22993step0 = (fun i j => raw22993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22993step0 raw22993; decide +kernel
      have hl : raw22993step0Labels = raw22993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22993 raw22993Labels permutation434 hz
    mixedMoment B raw22993step0 raw22993step0Labels = mixedMoment B raw22993step1 raw22993step1Labels := by
      have ha : raw22993step1 = (fun i j => raw22993step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22993step1 raw22993step0; decide +kernel
      have hl : raw22993step1Labels = raw22993step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22993step0 raw22993step0Labels permutation42 permutation7
    mixedMoment B raw22993step1 raw22993step1Labels = mixedMoment B raw22993step2 raw22993step2Labels := by
      have ha : raw22993step2 = -raw22993step1 := by apply Matrix.ext; change ∀ i j, raw22993step2 i j = -(raw22993step1 i j); unfold raw22993step2 raw22993step1; decide +kernel
      have hl : raw22993step2Labels = raw22993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22993step2 raw22993step2Labels = mixedMoment B raw22993step3 raw22993step3Labels := by
      have ha : raw22993step3 = raw22993step2 := by apply Matrix.ext; unfold raw22993step3 raw22993step2; decide +kernel
      have hl : raw22993step2Labels = labelEmbedding1 ∘ raw22993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22993step2 raw22993step2Labels raw22993step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

theorem canonical22994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22994 raw22994Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw22994 raw22994Labels = mixedMoment B raw22994step0 raw22994step0Labels := by
      have hz : ∀ j, raw22994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22994step0 = (fun i j => raw22994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22994step0 raw22994; decide +kernel
      have hl : raw22994step0Labels = raw22994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22994 raw22994Labels permutation346 hz
    mixedMoment B raw22994step0 raw22994step0Labels = mixedMoment B raw22994step1 raw22994step1Labels := by
      have ha : raw22994step1 = (fun i j => raw22994step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22994step1 raw22994step0; decide +kernel
      have hl : raw22994step1Labels = raw22994step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22994step0 raw22994step0Labels permutation42 permutation7
    mixedMoment B raw22994step1 raw22994step1Labels = mixedMoment B raw22994step2 raw22994step2Labels := by
      have ha : raw22994step2 = -raw22994step1 := by apply Matrix.ext; change ∀ i j, raw22994step2 i j = -(raw22994step1 i j); unfold raw22994step2 raw22994step1; decide +kernel
      have hl : raw22994step2Labels = raw22994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22994step2 raw22994step2Labels = mixedMoment B raw22994step3 raw22994step3Labels := by
      have ha : raw22994step3 = raw22994step2 := by apply Matrix.ext; unfold raw22994step3 raw22994step2; decide +kernel
      have hl : raw22994step2Labels = labelEmbedding1 ∘ raw22994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22994step2 raw22994step2Labels raw22994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

theorem canonical22995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22995 raw22995Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw22995 raw22995Labels = mixedMoment B raw22995step0 raw22995step0Labels := by
      have hz : ∀ j, raw22995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22995step0 = (fun i j => raw22995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22995step0 raw22995; decide +kernel
      have hl : raw22995step0Labels = raw22995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22995 raw22995Labels permutation434 hz
    mixedMoment B raw22995step0 raw22995step0Labels = mixedMoment B raw22995step1 raw22995step1Labels := by
      have hz : ∀ j, raw22995step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22995step1 = (fun i j => raw22995step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22995step1 raw22995step0; decide +kernel
      have hl : raw22995step1Labels = raw22995step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22995step0 raw22995step0Labels permutation80 hz
    mixedMoment B raw22995step1 raw22995step1Labels = mixedMoment B raw22995step2 raw22995step2Labels := by
      have ha : raw22995step2 = (fun i j => raw22995step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22995step2 raw22995step1; decide +kernel
      have hl : raw22995step2Labels = raw22995step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22995step1 raw22995step1Labels permutation12 permutation7
    mixedMoment B raw22995step2 raw22995step2Labels = mixedMoment B raw22995step3 raw22995step3Labels := by
      have ha : raw22995step3 = -raw22995step2 := by apply Matrix.ext; change ∀ i j, raw22995step3 i j = -(raw22995step2 i j); unfold raw22995step3 raw22995step2; decide +kernel
      have hl : raw22995step3Labels = raw22995step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22995step3 raw22995step3Labels = mixedMoment B raw22995step4 raw22995step4Labels := by
      have ha : raw22995step4 = raw22995step3 := by apply Matrix.ext; unfold raw22995step4 raw22995step3; decide +kernel
      have hl : raw22995step3Labels = labelEmbedding1 ∘ raw22995step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22995step3 raw22995step3Labels raw22995step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical22996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22996 raw22996Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw22996 raw22996Labels = mixedMoment B raw22996step0 raw22996step0Labels := by
      have hz : ∀ j, raw22996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22996step0 = (fun i j => raw22996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22996step0 raw22996; decide +kernel
      have hl : raw22996step0Labels = raw22996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22996 raw22996Labels permutation434 hz
    mixedMoment B raw22996step0 raw22996step0Labels = mixedMoment B raw22996step1 raw22996step1Labels := by
      have hz : ∀ j, raw22996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22996step1 = (fun i j => raw22996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22996step1 raw22996step0; decide +kernel
      have hl : raw22996step1Labels = raw22996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22996step0 raw22996step0Labels permutation80 hz
    mixedMoment B raw22996step1 raw22996step1Labels = mixedMoment B raw22996step2 raw22996step2Labels := by
      have ha : raw22996step2 = (fun i j => raw22996step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22996step2 raw22996step1; decide +kernel
      have hl : raw22996step2Labels = raw22996step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22996step1 raw22996step1Labels permutation12 permutation7
    mixedMoment B raw22996step2 raw22996step2Labels = mixedMoment B raw22996step3 raw22996step3Labels := by
      have ha : raw22996step3 = -raw22996step2 := by apply Matrix.ext; change ∀ i j, raw22996step3 i j = -(raw22996step2 i j); unfold raw22996step3 raw22996step2; decide +kernel
      have hl : raw22996step3Labels = raw22996step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22996step3 raw22996step3Labels = mixedMoment B raw22996step4 raw22996step4Labels := by
      have ha : raw22996step4 = raw22996step3 := by apply Matrix.ext; unfold raw22996step4 raw22996step3; decide +kernel
      have hl : raw22996step3Labels = labelEmbedding1 ∘ raw22996step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22996step3 raw22996step3Labels raw22996step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical22997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22997 raw22997Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw22997 raw22997Labels = mixedMoment B raw22997step0 raw22997step0Labels := by
      have hz : ∀ j, raw22997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22997step0 = (fun i j => raw22997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22997step0 raw22997; decide +kernel
      have hl : raw22997step0Labels = raw22997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22997 raw22997Labels permutation434 hz
    mixedMoment B raw22997step0 raw22997step0Labels = mixedMoment B raw22997step1 raw22997step1Labels := by
      have ha : raw22997step1 = (fun i j => raw22997step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22997step1 raw22997step0; decide +kernel
      have hl : raw22997step1Labels = raw22997step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22997step0 raw22997step0Labels permutation42 permutation7
    mixedMoment B raw22997step1 raw22997step1Labels = mixedMoment B raw22997step2 raw22997step2Labels := by
      have ha : raw22997step2 = -raw22997step1 := by apply Matrix.ext; change ∀ i j, raw22997step2 i j = -(raw22997step1 i j); unfold raw22997step2 raw22997step1; decide +kernel
      have hl : raw22997step2Labels = raw22997step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22997step2 raw22997step2Labels = mixedMoment B raw22997step3 raw22997step3Labels := by
      have ha : raw22997step3 = raw22997step2 := by apply Matrix.ext; unfold raw22997step3 raw22997step2; decide +kernel
      have hl : raw22997step2Labels = labelEmbedding1 ∘ raw22997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22997step2 raw22997step2Labels raw22997step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical22998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22998 raw22998Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw22998 raw22998Labels = mixedMoment B raw22998step0 raw22998step0Labels := by
      have hz : ∀ j, raw22998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22998step0 = (fun i j => raw22998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22998step0 raw22998; decide +kernel
      have hl : raw22998step0Labels = raw22998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22998 raw22998Labels permutation434 hz
    mixedMoment B raw22998step0 raw22998step0Labels = mixedMoment B raw22998step1 raw22998step1Labels := by
      have ha : raw22998step1 = (fun i j => raw22998step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22998step1 raw22998step0; decide +kernel
      have hl : raw22998step1Labels = raw22998step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22998step0 raw22998step0Labels permutation42 permutation7
    mixedMoment B raw22998step1 raw22998step1Labels = mixedMoment B raw22998step2 raw22998step2Labels := by
      have ha : raw22998step2 = -raw22998step1 := by apply Matrix.ext; change ∀ i j, raw22998step2 i j = -(raw22998step1 i j); unfold raw22998step2 raw22998step1; decide +kernel
      have hl : raw22998step2Labels = raw22998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22998step2 raw22998step2Labels = mixedMoment B raw22998step3 raw22998step3Labels := by
      have ha : raw22998step3 = raw22998step2 := by apply Matrix.ext; unfold raw22998step3 raw22998step2; decide +kernel
      have hl : raw22998step2Labels = labelEmbedding1 ∘ raw22998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22998step2 raw22998step2Labels raw22998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical22999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22999 raw22999Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw22999 raw22999Labels = mixedMoment B raw22999step0 raw22999step0Labels := by
      have ha : raw22999step0 = (fun i j => raw22999 (permutation210 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22999step0 raw22999; decide +kernel
      have hl : raw22999step0Labels = raw22999Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22999 raw22999Labels permutation210 permutation7
    mixedMoment B raw22999step0 raw22999step0Labels = mixedMoment B raw22999step1 raw22999step1Labels := by
      have ha : raw22999step1 = -raw22999step0 := by apply Matrix.ext; change ∀ i j, raw22999step1 i j = -(raw22999step0 i j); unfold raw22999step1 raw22999step0; decide +kernel
      have hl : raw22999step1Labels = raw22999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22999step1 raw22999step1Labels = mixedMoment B raw22999step2 raw22999step2Labels := by
      have ha : raw22999step2 = raw22999step1 := by apply Matrix.ext; unfold raw22999step2 raw22999step1; decide +kernel
      have hl : raw22999step1Labels = labelEmbedding1 ∘ raw22999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22999step1 raw22999step1Labels raw22999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical23000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23000 raw23000Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23000 raw23000Labels = mixedMoment B raw23000step0 raw23000step0Labels := by
      have hz : ∀ j, raw23000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23000step0 = (fun i j => raw23000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23000step0 raw23000; decide +kernel
      have hl : raw23000step0Labels = raw23000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23000 raw23000Labels permutation434 hz
    mixedMoment B raw23000step0 raw23000step0Labels = mixedMoment B raw23000step1 raw23000step1Labels := by
      have ha : raw23000step1 = (fun i j => raw23000step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23000step1 raw23000step0; decide +kernel
      have hl : raw23000step1Labels = raw23000step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23000step0 raw23000step0Labels permutation42 permutation7
    mixedMoment B raw23000step1 raw23000step1Labels = mixedMoment B raw23000step2 raw23000step2Labels := by
      have ha : raw23000step2 = -raw23000step1 := by apply Matrix.ext; change ∀ i j, raw23000step2 i j = -(raw23000step1 i j); unfold raw23000step2 raw23000step1; decide +kernel
      have hl : raw23000step2Labels = raw23000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23000step2 raw23000step2Labels = mixedMoment B raw23000step3 raw23000step3Labels := by
      have ha : raw23000step3 = raw23000step2 := by apply Matrix.ext; unfold raw23000step3 raw23000step2; decide +kernel
      have hl : raw23000step2Labels = labelEmbedding1 ∘ raw23000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23000step2 raw23000step2Labels raw23000step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical23001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23001 raw23001Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23001 raw23001Labels = mixedMoment B raw23001step0 raw23001step0Labels := by
      have hz : ∀ j, raw23001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23001step0 = (fun i j => raw23001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23001step0 raw23001; decide +kernel
      have hl : raw23001step0Labels = raw23001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23001 raw23001Labels permutation434 hz
    mixedMoment B raw23001step0 raw23001step0Labels = mixedMoment B raw23001step1 raw23001step1Labels := by
      have ha : raw23001step1 = (fun i j => raw23001step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23001step1 raw23001step0; decide +kernel
      have hl : raw23001step1Labels = raw23001step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23001step0 raw23001step0Labels permutation42 permutation7
    mixedMoment B raw23001step1 raw23001step1Labels = mixedMoment B raw23001step2 raw23001step2Labels := by
      have ha : raw23001step2 = -raw23001step1 := by apply Matrix.ext; change ∀ i j, raw23001step2 i j = -(raw23001step1 i j); unfold raw23001step2 raw23001step1; decide +kernel
      have hl : raw23001step2Labels = raw23001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23001step2 raw23001step2Labels = mixedMoment B raw23001step3 raw23001step3Labels := by
      have ha : raw23001step3 = raw23001step2 := by apply Matrix.ext; unfold raw23001step3 raw23001step2; decide +kernel
      have hl : raw23001step2Labels = labelEmbedding1 ∘ raw23001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23001step2 raw23001step2Labels raw23001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical23002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23002 raw23002Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw23002 raw23002Labels = mixedMoment B raw23002step0 raw23002step0Labels := by
      have hz : ∀ j, raw23002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23002step0 = (fun i j => raw23002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23002step0 raw23002; decide +kernel
      have hl : raw23002step0Labels = raw23002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23002 raw23002Labels permutation346 hz
    mixedMoment B raw23002step0 raw23002step0Labels = mixedMoment B raw23002step1 raw23002step1Labels := by
      have ha : raw23002step1 = (fun i j => raw23002step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23002step1 raw23002step0; decide +kernel
      have hl : raw23002step1Labels = raw23002step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23002step0 raw23002step0Labels permutation42 permutation7
    mixedMoment B raw23002step1 raw23002step1Labels = mixedMoment B raw23002step2 raw23002step2Labels := by
      have ha : raw23002step2 = -raw23002step1 := by apply Matrix.ext; change ∀ i j, raw23002step2 i j = -(raw23002step1 i j); unfold raw23002step2 raw23002step1; decide +kernel
      have hl : raw23002step2Labels = raw23002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23002step2 raw23002step2Labels = mixedMoment B raw23002step3 raw23002step3Labels := by
      have ha : raw23002step3 = raw23002step2 := by apply Matrix.ext; unfold raw23002step3 raw23002step2; decide +kernel
      have hl : raw23002step2Labels = labelEmbedding1 ∘ raw23002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23002step2 raw23002step2Labels raw23002step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical23003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23003 raw23003Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw23003 raw23003Labels = mixedMoment B raw23003step0 raw23003step0Labels := by
      have hz : ∀ j, raw23003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23003step0 = (fun i j => raw23003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23003step0 raw23003; decide +kernel
      have hl : raw23003step0Labels = raw23003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23003 raw23003Labels permutation346 hz
    mixedMoment B raw23003step0 raw23003step0Labels = mixedMoment B raw23003step1 raw23003step1Labels := by
      have ha : raw23003step1 = (fun i j => raw23003step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23003step1 raw23003step0; decide +kernel
      have hl : raw23003step1Labels = raw23003step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23003step0 raw23003step0Labels permutation42 permutation7
    mixedMoment B raw23003step1 raw23003step1Labels = mixedMoment B raw23003step2 raw23003step2Labels := by
      have ha : raw23003step2 = -raw23003step1 := by apply Matrix.ext; change ∀ i j, raw23003step2 i j = -(raw23003step1 i j); unfold raw23003step2 raw23003step1; decide +kernel
      have hl : raw23003step2Labels = raw23003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23003step2 raw23003step2Labels = mixedMoment B raw23003step3 raw23003step3Labels := by
      have ha : raw23003step3 = raw23003step2 := by apply Matrix.ext; unfold raw23003step3 raw23003step2; decide +kernel
      have hl : raw23003step2Labels = labelEmbedding1 ∘ raw23003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23003step2 raw23003step2Labels raw23003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical23004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23004 raw23004Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw23004 raw23004Labels = mixedMoment B raw23004step0 raw23004step0Labels := by
      have ha : raw23004step0 = (fun i j => raw23004 (permutation186 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23004step0 raw23004; decide +kernel
      have hl : raw23004step0Labels = raw23004Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23004 raw23004Labels permutation186 permutation7
    mixedMoment B raw23004step0 raw23004step0Labels = mixedMoment B raw23004step1 raw23004step1Labels := by
      have ha : raw23004step1 = -raw23004step0 := by apply Matrix.ext; change ∀ i j, raw23004step1 i j = -(raw23004step0 i j); unfold raw23004step1 raw23004step0; decide +kernel
      have hl : raw23004step1Labels = raw23004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23004step1 raw23004step1Labels = mixedMoment B raw23004step2 raw23004step2Labels := by
      have ha : raw23004step2 = raw23004step1 := by apply Matrix.ext; unfold raw23004step2 raw23004step1; decide +kernel
      have hl : raw23004step1Labels = labelEmbedding1 ∘ raw23004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23004step1 raw23004step1Labels raw23004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical23005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23005 raw23005Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23005 raw23005Labels = mixedMoment B raw23005step0 raw23005step0Labels := by
      have hz : ∀ j, raw23005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23005step0 = (fun i j => raw23005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23005step0 raw23005; decide +kernel
      have hl : raw23005step0Labels = raw23005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23005 raw23005Labels permutation346 hz
    mixedMoment B raw23005step0 raw23005step0Labels = mixedMoment B raw23005step1 raw23005step1Labels := by
      have ha : raw23005step1 = (fun i j => raw23005step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23005step1 raw23005step0; decide +kernel
      have hl : raw23005step1Labels = raw23005step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23005step0 raw23005step0Labels permutation42 permutation7
    mixedMoment B raw23005step1 raw23005step1Labels = mixedMoment B raw23005step2 raw23005step2Labels := by
      have ha : raw23005step2 = -raw23005step1 := by apply Matrix.ext; change ∀ i j, raw23005step2 i j = -(raw23005step1 i j); unfold raw23005step2 raw23005step1; decide +kernel
      have hl : raw23005step2Labels = raw23005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23005step2 raw23005step2Labels = mixedMoment B raw23005step3 raw23005step3Labels := by
      have ha : raw23005step3 = raw23005step2 := by apply Matrix.ext; unfold raw23005step3 raw23005step2; decide +kernel
      have hl : raw23005step2Labels = labelEmbedding1 ∘ raw23005step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23005step2 raw23005step2Labels raw23005step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical23006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23006 raw23006Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23006 raw23006Labels = mixedMoment B raw23006step0 raw23006step0Labels := by
      have hz : ∀ j, raw23006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23006step0 = (fun i j => raw23006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23006step0 raw23006; decide +kernel
      have hl : raw23006step0Labels = raw23006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23006 raw23006Labels permutation346 hz
    mixedMoment B raw23006step0 raw23006step0Labels = mixedMoment B raw23006step1 raw23006step1Labels := by
      have ha : raw23006step1 = (fun i j => raw23006step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23006step1 raw23006step0; decide +kernel
      have hl : raw23006step1Labels = raw23006step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23006step0 raw23006step0Labels permutation42 permutation7
    mixedMoment B raw23006step1 raw23006step1Labels = mixedMoment B raw23006step2 raw23006step2Labels := by
      have ha : raw23006step2 = -raw23006step1 := by apply Matrix.ext; change ∀ i j, raw23006step2 i j = -(raw23006step1 i j); unfold raw23006step2 raw23006step1; decide +kernel
      have hl : raw23006step2Labels = raw23006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23006step2 raw23006step2Labels = mixedMoment B raw23006step3 raw23006step3Labels := by
      have ha : raw23006step3 = raw23006step2 := by apply Matrix.ext; unfold raw23006step3 raw23006step2; decide +kernel
      have hl : raw23006step2Labels = labelEmbedding1 ∘ raw23006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23006step2 raw23006step2Labels raw23006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical23007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23007 raw23007Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw23007 raw23007Labels = mixedMoment B raw23007step0 raw23007step0Labels := by
      have hz : ∀ j, raw23007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23007step0 = (fun i j => raw23007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23007step0 raw23007; decide +kernel
      have hl : raw23007step0Labels = raw23007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23007 raw23007Labels permutation434 hz
    mixedMoment B raw23007step0 raw23007step0Labels = mixedMoment B raw23007step1 raw23007step1Labels := by
      have hz : ∀ j, raw23007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23007step1 = (fun i j => raw23007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23007step1 raw23007step0; decide +kernel
      have hl : raw23007step1Labels = raw23007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23007step0 raw23007step0Labels permutation80 hz
    mixedMoment B raw23007step1 raw23007step1Labels = mixedMoment B raw23007step2 raw23007step2Labels := by
      have ha : raw23007step2 = (fun i j => raw23007step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23007step2 raw23007step1; decide +kernel
      have hl : raw23007step2Labels = raw23007step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23007step1 raw23007step1Labels permutation12 permutation7
    mixedMoment B raw23007step2 raw23007step2Labels = mixedMoment B raw23007step3 raw23007step3Labels := by
      have ha : raw23007step3 = -raw23007step2 := by apply Matrix.ext; change ∀ i j, raw23007step3 i j = -(raw23007step2 i j); unfold raw23007step3 raw23007step2; decide +kernel
      have hl : raw23007step3Labels = raw23007step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23007step3 raw23007step3Labels = mixedMoment B raw23007step4 raw23007step4Labels := by
      have ha : raw23007step4 = raw23007step3 := by apply Matrix.ext; unfold raw23007step4 raw23007step3; decide +kernel
      have hl : raw23007step3Labels = labelEmbedding1 ∘ raw23007step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23007step3 raw23007step3Labels raw23007step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

theorem canonical23008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23008 raw23008Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw23008 raw23008Labels = mixedMoment B raw23008step0 raw23008step0Labels := by
      have hz : ∀ j, raw23008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23008step0 = (fun i j => raw23008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23008step0 raw23008; decide +kernel
      have hl : raw23008step0Labels = raw23008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23008 raw23008Labels permutation434 hz
    mixedMoment B raw23008step0 raw23008step0Labels = mixedMoment B raw23008step1 raw23008step1Labels := by
      have hz : ∀ j, raw23008step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23008step1 = (fun i j => raw23008step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23008step1 raw23008step0; decide +kernel
      have hl : raw23008step1Labels = raw23008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23008step0 raw23008step0Labels permutation80 hz
    mixedMoment B raw23008step1 raw23008step1Labels = mixedMoment B raw23008step2 raw23008step2Labels := by
      have ha : raw23008step2 = (fun i j => raw23008step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23008step2 raw23008step1; decide +kernel
      have hl : raw23008step2Labels = raw23008step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23008step1 raw23008step1Labels permutation12 permutation7
    mixedMoment B raw23008step2 raw23008step2Labels = mixedMoment B raw23008step3 raw23008step3Labels := by
      have ha : raw23008step3 = -raw23008step2 := by apply Matrix.ext; change ∀ i j, raw23008step3 i j = -(raw23008step2 i j); unfold raw23008step3 raw23008step2; decide +kernel
      have hl : raw23008step3Labels = raw23008step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23008step3 raw23008step3Labels = mixedMoment B raw23008step4 raw23008step4Labels := by
      have ha : raw23008step4 = raw23008step3 := by apply Matrix.ext; unfold raw23008step4 raw23008step3; decide +kernel
      have hl : raw23008step3Labels = labelEmbedding1 ∘ raw23008step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23008step3 raw23008step3Labels raw23008step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

theorem canonical23009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23009 raw23009Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw23009 raw23009Labels = mixedMoment B raw23009step0 raw23009step0Labels := by
      have hz : ∀ j, raw23009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23009step0 = (fun i j => raw23009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23009step0 raw23009; decide +kernel
      have hl : raw23009step0Labels = raw23009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23009 raw23009Labels permutation434 hz
    mixedMoment B raw23009step0 raw23009step0Labels = mixedMoment B raw23009step1 raw23009step1Labels := by
      have ha : raw23009step1 = (fun i j => raw23009step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23009step1 raw23009step0; decide +kernel
      have hl : raw23009step1Labels = raw23009step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23009step0 raw23009step0Labels permutation42 permutation7
    mixedMoment B raw23009step1 raw23009step1Labels = mixedMoment B raw23009step2 raw23009step2Labels := by
      have ha : raw23009step2 = -raw23009step1 := by apply Matrix.ext; change ∀ i j, raw23009step2 i j = -(raw23009step1 i j); unfold raw23009step2 raw23009step1; decide +kernel
      have hl : raw23009step2Labels = raw23009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23009step2 raw23009step2Labels = mixedMoment B raw23009step3 raw23009step3Labels := by
      have ha : raw23009step3 = raw23009step2 := by apply Matrix.ext; unfold raw23009step3 raw23009step2; decide +kernel
      have hl : raw23009step2Labels = labelEmbedding1 ∘ raw23009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23009step2 raw23009step2Labels raw23009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical23010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23010 raw23010Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw23010 raw23010Labels = mixedMoment B raw23010step0 raw23010step0Labels := by
      have hz : ∀ j, raw23010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23010step0 = (fun i j => raw23010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23010step0 raw23010; decide +kernel
      have hl : raw23010step0Labels = raw23010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23010 raw23010Labels permutation346 hz
    mixedMoment B raw23010step0 raw23010step0Labels = mixedMoment B raw23010step1 raw23010step1Labels := by
      have ha : raw23010step1 = (fun i j => raw23010step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23010step1 raw23010step0; decide +kernel
      have hl : raw23010step1Labels = raw23010step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23010step0 raw23010step0Labels permutation42 permutation7
    mixedMoment B raw23010step1 raw23010step1Labels = mixedMoment B raw23010step2 raw23010step2Labels := by
      have ha : raw23010step2 = -raw23010step1 := by apply Matrix.ext; change ∀ i j, raw23010step2 i j = -(raw23010step1 i j); unfold raw23010step2 raw23010step1; decide +kernel
      have hl : raw23010step2Labels = raw23010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23010step2 raw23010step2Labels = mixedMoment B raw23010step3 raw23010step3Labels := by
      have ha : raw23010step3 = raw23010step2 := by apply Matrix.ext; unfold raw23010step3 raw23010step2; decide +kernel
      have hl : raw23010step2Labels = labelEmbedding1 ∘ raw23010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23010step2 raw23010step2Labels raw23010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical23011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23011 raw23011Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw23011 raw23011Labels = mixedMoment B raw23011step0 raw23011step0Labels := by
      have hz : ∀ j, raw23011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23011step0 = (fun i j => raw23011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23011step0 raw23011; decide +kernel
      have hl : raw23011step0Labels = raw23011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23011 raw23011Labels permutation434 hz
    mixedMoment B raw23011step0 raw23011step0Labels = mixedMoment B raw23011step1 raw23011step1Labels := by
      have hz : ∀ j, raw23011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23011step1 = (fun i j => raw23011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23011step1 raw23011step0; decide +kernel
      have hl : raw23011step1Labels = raw23011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23011step0 raw23011step0Labels permutation80 hz
    mixedMoment B raw23011step1 raw23011step1Labels = mixedMoment B raw23011step2 raw23011step2Labels := by
      have ha : raw23011step2 = (fun i j => raw23011step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23011step2 raw23011step1; decide +kernel
      have hl : raw23011step2Labels = raw23011step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23011step1 raw23011step1Labels permutation12 permutation7
    mixedMoment B raw23011step2 raw23011step2Labels = mixedMoment B raw23011step3 raw23011step3Labels := by
      have ha : raw23011step3 = -raw23011step2 := by apply Matrix.ext; change ∀ i j, raw23011step3 i j = -(raw23011step2 i j); unfold raw23011step3 raw23011step2; decide +kernel
      have hl : raw23011step3Labels = raw23011step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23011step3 raw23011step3Labels = mixedMoment B raw23011step4 raw23011step4Labels := by
      have ha : raw23011step4 = raw23011step3 := by apply Matrix.ext; unfold raw23011step4 raw23011step3; decide +kernel
      have hl : raw23011step3Labels = labelEmbedding1 ∘ raw23011step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23011step3 raw23011step3Labels raw23011step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical23012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23012 raw23012Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw23012 raw23012Labels = mixedMoment B raw23012step0 raw23012step0Labels := by
      have hz : ∀ j, raw23012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23012step0 = (fun i j => raw23012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23012step0 raw23012; decide +kernel
      have hl : raw23012step0Labels = raw23012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23012 raw23012Labels permutation434 hz
    mixedMoment B raw23012step0 raw23012step0Labels = mixedMoment B raw23012step1 raw23012step1Labels := by
      have hz : ∀ j, raw23012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23012step1 = (fun i j => raw23012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23012step1 raw23012step0; decide +kernel
      have hl : raw23012step1Labels = raw23012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23012step0 raw23012step0Labels permutation80 hz
    mixedMoment B raw23012step1 raw23012step1Labels = mixedMoment B raw23012step2 raw23012step2Labels := by
      have ha : raw23012step2 = (fun i j => raw23012step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23012step2 raw23012step1; decide +kernel
      have hl : raw23012step2Labels = raw23012step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23012step1 raw23012step1Labels permutation12 permutation7
    mixedMoment B raw23012step2 raw23012step2Labels = mixedMoment B raw23012step3 raw23012step3Labels := by
      have ha : raw23012step3 = -raw23012step2 := by apply Matrix.ext; change ∀ i j, raw23012step3 i j = -(raw23012step2 i j); unfold raw23012step3 raw23012step2; decide +kernel
      have hl : raw23012step3Labels = raw23012step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23012step3 raw23012step3Labels = mixedMoment B raw23012step4 raw23012step4Labels := by
      have ha : raw23012step4 = raw23012step3 := by apply Matrix.ext; unfold raw23012step4 raw23012step3; decide +kernel
      have hl : raw23012step3Labels = labelEmbedding1 ∘ raw23012step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23012step3 raw23012step3Labels raw23012step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1529 node1529Labels := by rfl

theorem canonical23013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23013 raw23013Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw23013 raw23013Labels = mixedMoment B raw23013step0 raw23013step0Labels := by
      have hz : ∀ j, raw23013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23013step0 = (fun i j => raw23013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23013step0 raw23013; decide +kernel
      have hl : raw23013step0Labels = raw23013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23013 raw23013Labels permutation434 hz
    mixedMoment B raw23013step0 raw23013step0Labels = mixedMoment B raw23013step1 raw23013step1Labels := by
      have hz : ∀ j, raw23013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23013step1 = (fun i j => raw23013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23013step1 raw23013step0; decide +kernel
      have hl : raw23013step1Labels = raw23013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23013step0 raw23013step0Labels permutation80 hz
    mixedMoment B raw23013step1 raw23013step1Labels = mixedMoment B raw23013step2 raw23013step2Labels := by
      have ha : raw23013step2 = (fun i j => raw23013step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23013step2 raw23013step1; decide +kernel
      have hl : raw23013step2Labels = raw23013step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23013step1 raw23013step1Labels permutation12 permutation7
    mixedMoment B raw23013step2 raw23013step2Labels = mixedMoment B raw23013step3 raw23013step3Labels := by
      have ha : raw23013step3 = -raw23013step2 := by apply Matrix.ext; change ∀ i j, raw23013step3 i j = -(raw23013step2 i j); unfold raw23013step3 raw23013step2; decide +kernel
      have hl : raw23013step3Labels = raw23013step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23013step3 raw23013step3Labels = mixedMoment B raw23013step4 raw23013step4Labels := by
      have ha : raw23013step4 = raw23013step3 := by apply Matrix.ext; unfold raw23013step4 raw23013step3; decide +kernel
      have hl : raw23013step3Labels = labelEmbedding1 ∘ raw23013step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23013step3 raw23013step3Labels raw23013step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1743 node1743Labels := by rfl

theorem canonical23014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23014 raw23014Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw23014 raw23014Labels = mixedMoment B raw23014step0 raw23014step0Labels := by
      have hz : ∀ j, raw23014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23014step0 = (fun i j => raw23014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23014step0 raw23014; decide +kernel
      have hl : raw23014step0Labels = raw23014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23014 raw23014Labels permutation434 hz
    mixedMoment B raw23014step0 raw23014step0Labels = mixedMoment B raw23014step1 raw23014step1Labels := by
      have ha : raw23014step1 = (fun i j => raw23014step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23014step1 raw23014step0; decide +kernel
      have hl : raw23014step1Labels = raw23014step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23014step0 raw23014step0Labels permutation42 permutation7
    mixedMoment B raw23014step1 raw23014step1Labels = mixedMoment B raw23014step2 raw23014step2Labels := by
      have ha : raw23014step2 = -raw23014step1 := by apply Matrix.ext; change ∀ i j, raw23014step2 i j = -(raw23014step1 i j); unfold raw23014step2 raw23014step1; decide +kernel
      have hl : raw23014step2Labels = raw23014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23014step2 raw23014step2Labels = mixedMoment B raw23014step3 raw23014step3Labels := by
      have ha : raw23014step3 = raw23014step2 := by apply Matrix.ext; unfold raw23014step3 raw23014step2; decide +kernel
      have hl : raw23014step2Labels = labelEmbedding1 ∘ raw23014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23014step2 raw23014step2Labels raw23014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

theorem canonical23015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23015 raw23015Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw23015 raw23015Labels = mixedMoment B raw23015step0 raw23015step0Labels := by
      have hz : ∀ j, raw23015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23015step0 = (fun i j => raw23015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23015step0 raw23015; decide +kernel
      have hl : raw23015step0Labels = raw23015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23015 raw23015Labels permutation346 hz
    mixedMoment B raw23015step0 raw23015step0Labels = mixedMoment B raw23015step1 raw23015step1Labels := by
      have ha : raw23015step1 = (fun i j => raw23015step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23015step1 raw23015step0; decide +kernel
      have hl : raw23015step1Labels = raw23015step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23015step0 raw23015step0Labels permutation42 permutation7
    mixedMoment B raw23015step1 raw23015step1Labels = mixedMoment B raw23015step2 raw23015step2Labels := by
      have ha : raw23015step2 = -raw23015step1 := by apply Matrix.ext; change ∀ i j, raw23015step2 i j = -(raw23015step1 i j); unfold raw23015step2 raw23015step1; decide +kernel
      have hl : raw23015step2Labels = raw23015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23015step2 raw23015step2Labels = mixedMoment B raw23015step3 raw23015step3Labels := by
      have ha : raw23015step3 = raw23015step2 := by apply Matrix.ext; unfold raw23015step3 raw23015step2; decide +kernel
      have hl : raw23015step2Labels = labelEmbedding1 ∘ raw23015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23015step2 raw23015step2Labels raw23015step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

theorem canonical23016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23016 raw23016Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw23016 raw23016Labels = mixedMoment B raw23016step0 raw23016step0Labels := by
      have hz : ∀ j, raw23016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23016step0 = (fun i j => raw23016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23016step0 raw23016; decide +kernel
      have hl : raw23016step0Labels = raw23016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23016 raw23016Labels permutation434 hz
    mixedMoment B raw23016step0 raw23016step0Labels = mixedMoment B raw23016step1 raw23016step1Labels := by
      have hz : ∀ j, raw23016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23016step1 = (fun i j => raw23016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23016step1 raw23016step0; decide +kernel
      have hl : raw23016step1Labels = raw23016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23016step0 raw23016step0Labels permutation80 hz
    mixedMoment B raw23016step1 raw23016step1Labels = mixedMoment B raw23016step2 raw23016step2Labels := by
      have ha : raw23016step2 = (fun i j => raw23016step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23016step2 raw23016step1; decide +kernel
      have hl : raw23016step2Labels = raw23016step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23016step1 raw23016step1Labels permutation12 permutation7
    mixedMoment B raw23016step2 raw23016step2Labels = mixedMoment B raw23016step3 raw23016step3Labels := by
      have ha : raw23016step3 = -raw23016step2 := by apply Matrix.ext; change ∀ i j, raw23016step3 i j = -(raw23016step2 i j); unfold raw23016step3 raw23016step2; decide +kernel
      have hl : raw23016step3Labels = raw23016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23016step3 raw23016step3Labels = mixedMoment B raw23016step4 raw23016step4Labels := by
      have ha : raw23016step4 = raw23016step3 := by apply Matrix.ext; unfold raw23016step4 raw23016step3; decide +kernel
      have hl : raw23016step3Labels = labelEmbedding1 ∘ raw23016step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23016step3 raw23016step3Labels raw23016step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

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

theorem canonical828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw828 raw828Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw828 raw828Labels = mixedMoment B raw828step0 raw828step0Labels := by
      have ha : raw828step0 = (fun i j => raw828 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw828step0 raw828; decide +kernel
      have hl : raw828step0Labels = raw828Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw828 raw828Labels permutation8 permutation4
    mixedMoment B raw828step0 raw828step0Labels = mixedMoment B raw828step1 raw828step1Labels := by
      have ha : raw828step1 = raw828step0 := by apply Matrix.ext; unfold raw828step1 raw828step0; decide +kernel
      have hl : raw828step0Labels = labelEmbedding7 ∘ raw828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw828step0 raw828step0Labels raw828step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4185 node4185Labels := by rfl

theorem canonical829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw829 raw829Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw829 raw829Labels = mixedMoment B raw829step0 raw829step0Labels := by
      have ha : raw829step0 = (fun i j => raw829 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw829step0 raw829; decide +kernel
      have hl : raw829step0Labels = raw829Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw829 raw829Labels permutation8 permutation4
    _ = mixedMoment B node613 node613Labels := by rfl

theorem canonical830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw830 raw830Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw830 raw830Labels = mixedMoment B raw830step0 raw830step0Labels := by
      have ha : raw830step0 = (fun i j => raw830 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw830step0 raw830; decide +kernel
      have hl : raw830step0Labels = raw830Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw830 raw830Labels permutation10 permutation6
    mixedMoment B raw830step0 raw830step0Labels = mixedMoment B raw830step1 raw830step1Labels := by
      have ha : raw830step1 = -raw830step0 := by apply Matrix.ext; change ∀ i j, raw830step1 i j = -(raw830step0 i j); unfold raw830step1 raw830step0; decide +kernel
      have hl : raw830step1Labels = raw830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw830step1 raw830step1Labels = mixedMoment B raw830step2 raw830step2Labels := by
      have ha : raw830step2 = raw830step1 := by apply Matrix.ext; unfold raw830step2 raw830step1; decide +kernel
      have hl : raw830step1Labels = labelEmbedding1 ∘ raw830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw830step1 raw830step1Labels raw830step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1525 node1525Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1257 raw1257Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw1257 raw1257Labels = mixedMoment B raw1257step0 raw1257step0Labels := by
      have ha : raw1257step0 = (fun i j => raw1257 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1257step0 raw1257; decide +kernel
      have hl : raw1257step0Labels = raw1257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1257 raw1257Labels permutation32 permutation4
    mixedMoment B raw1257step0 raw1257step0Labels = mixedMoment B raw1257step1 raw1257step1Labels := by
      have ha : raw1257step1 = raw1257step0 := by apply Matrix.ext; unfold raw1257step1 raw1257step0; decide +kernel
      have hl : raw1257step0Labels = labelEmbedding7 ∘ raw1257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1257step0 raw1257step0Labels raw1257step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1258 raw1258Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw1258 raw1258Labels = mixedMoment B raw1258step0 raw1258step0Labels := by
      have ha : raw1258step0 = (fun i j => raw1258 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1258step0 raw1258; decide +kernel
      have hl : raw1258step0Labels = raw1258Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1258 raw1258Labels permutation32 permutation4
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1259 raw1259Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw1259 raw1259Labels = mixedMoment B raw1259step0 raw1259step0Labels := by
      have ha : raw1259step0 = (fun i j => raw1259 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1259step0 raw1259; decide +kernel
      have hl : raw1259step0Labels = raw1259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1259 raw1259Labels permutation40 permutation6
    mixedMoment B raw1259step0 raw1259step0Labels = mixedMoment B raw1259step1 raw1259step1Labels := by
      have ha : raw1259step1 = -raw1259step0 := by apply Matrix.ext; change ∀ i j, raw1259step1 i j = -(raw1259step0 i j); unfold raw1259step1 raw1259step0; decide +kernel
      have hl : raw1259step1Labels = raw1259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1259step1 raw1259step1Labels = mixedMoment B raw1259step2 raw1259step2Labels := by
      have ha : raw1259step2 = raw1259step1 := by apply Matrix.ext; unfold raw1259step2 raw1259step1; decide +kernel
      have hl : raw1259step1Labels = labelEmbedding1 ∘ raw1259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1259step1 raw1259step1Labels raw1259step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4185 node4185Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node613 node613Labels + mixedMoment B node1525 node1525Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw828 singletonSmall4185
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4185) = raw828Labels := by decide +kernel
  rw [hl, canonical828 B hB] at h
  have hc0 : mixedMoment B raw828 (Fin.cases (0 : Fin 2) singletonSmall4185) =
      mixedMoment B node613 node613Labels := by
    have ha : raw828 = raw829 := by apply Matrix.ext; unfold raw828 raw829; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4185 = raw829Labels := by decide +kernel
    rw [ha, hj, canonical829 B hB]
  have hc1 : mixedMoment B raw828 (Fin.cases (1 : Fin 2) singletonSmall4185) =
      mixedMoment B node1525 node1525Labels := by
    have ha : raw828 = raw830 := by apply Matrix.ext; unfold raw828 raw830; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4185 = raw830Labels := by decide +kernel
    rw [ha, hj, canonical830 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4457 node4457Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1040 node1040Labels + mixedMoment B node1707 node1707Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1257 singletonSmall4457
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4457) = raw1257Labels := by decide +kernel
  rw [hl, canonical1257 B hB] at h
  have hc0 : mixedMoment B raw1257 (Fin.cases (0 : Fin 2) singletonSmall4457) =
      mixedMoment B node1040 node1040Labels := by
    have ha : raw1257 = raw1258 := by apply Matrix.ext; unfold raw1257 raw1258; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4457 = raw1258Labels := by decide +kernel
    rw [ha, hj, canonical1258 B hB]
  have hc1 : mixedMoment B raw1257 (Fin.cases (1 : Fin 2) singletonSmall4457) =
      mixedMoment B node1707 node1707Labels := by
    have ha : raw1257 = raw1259 := by apply Matrix.ext; unfold raw1257 raw1259; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4457 = raw1259Labels := by decide +kernel
    rw [ha, hj, canonical1259 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4503 node4503Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1087 node1087Labels + mixedMoment B node1739 node1739Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1302 singletonSmall4503
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4503) = raw1302Labels := by decide +kernel
  rw [hl, canonical1302 B hB] at h
  have hc0 : mixedMoment B raw1302 (Fin.cases (0 : Fin 2) singletonSmall4503) =
      mixedMoment B node1087 node1087Labels := by
    have ha : raw1302 = raw1303 := by apply Matrix.ext; unfold raw1302 raw1303; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4503 = raw1303Labels := by decide +kernel
    rw [ha, hj, canonical1303 B hB]
  have hc1 : mixedMoment B raw1302 (Fin.cases (1 : Fin 2) singletonSmall4503) =
      mixedMoment B node1739 node1739Labels := by
    have ha : raw1302 = raw1304 := by apply Matrix.ext; unfold raw1302 raw1304; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4503 = raw1304Labels := by decide +kernel
    rw [ha, hj, canonical1304 B hB]
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

theorem singleton4874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4874 node4874Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2115 node2115Labels + mixedMoment B node2276 node2276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1806 singletonSmall4874
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4874) = raw1806Labels := by decide +kernel
  rw [hl, canonical1806 B hB] at h
  have hc0 : mixedMoment B raw1806 (Fin.cases (0 : Fin 2) singletonSmall4874) =
      mixedMoment B node2115 node2115Labels := by
    have ha : raw1806 = raw1807 := by apply Matrix.ext; unfold raw1806 raw1807; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4874 = raw1807Labels := by decide +kernel
    rw [ha, hj, canonical1807 B hB]
  have hc1 : mixedMoment B raw1806 (Fin.cases (1 : Fin 2) singletonSmall4874) =
      mixedMoment B node2276 node2276Labels := by
    have ha : raw1806 = raw1808 := by apply Matrix.ext; unfold raw1806 raw1808; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4874 = raw1808Labels := by decide +kernel
    rw [ha, hj, canonical1808 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4896 node4896Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2266 node2266Labels + mixedMoment B node2278 node2278Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1824 singletonSmall4896
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4896) = raw1824Labels := by decide +kernel
  rw [hl, canonical1824 B hB] at h
  have hc0 : mixedMoment B raw1824 (Fin.cases (0 : Fin 2) singletonSmall4896) =
      mixedMoment B node2266 node2266Labels := by
    have ha : raw1824 = raw1825 := by apply Matrix.ext; unfold raw1824 raw1825; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4896 = raw1825Labels := by decide +kernel
    rw [ha, hj, canonical1825 B hB]
  have hc1 : mixedMoment B raw1824 (Fin.cases (1 : Fin 2) singletonSmall4896) =
      mixedMoment B node2278 node2278Labels := by
    have ha : raw1824 = raw1826 := by apply Matrix.ext; unfold raw1824 raw1826; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4896 = raw1826Labels := by decide +kernel
    rw [ha, hj, canonical1826 B hB]
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

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

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

theorem zero974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node974 node974Labels = 0 := by
  exact mixedMoment_alpha B hF node974 node974Labels 1 permutation200
    (by decide +kernel)

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

theorem sound973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node973 node973Labels = Sparse.eval nodeValue973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 973) = mixedMoment B node973 node973Labels := rfl
  simpa [nodeValue973, Sparse.eval] using hc.symm

theorem sound974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node974 node974Labels = Sparse.eval nodeValue974 (mixedVector B) := by
  simpa only [nodeValue974, Sparse.eval_nil] using zero974 B _hB _hF

theorem sound992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node992 node992Labels = Sparse.eval nodeValue992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 992) = mixedMoment B node992 node992Labels := rfl
  simpa [nodeValue992, Sparse.eval] using hc.symm

theorem sound993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node993 node993Labels = Sparse.eval nodeValue993 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 993) = mixedMoment B node993 node993Labels := rfl
  simpa [nodeValue993, Sparse.eval] using hc.symm

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

theorem sound1025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1025 node1025Labels = Sparse.eval nodeValue1025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1025) = mixedMoment B node1025 node1025Labels := rfl
  simpa [nodeValue1025, Sparse.eval] using hc.symm

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1048 node1048Labels = Sparse.eval nodeValue1048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1048) = mixedMoment B node1048 node1048Labels := rfl
  simpa [nodeValue1048, Sparse.eval] using hc.symm

theorem sound1062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1062 node1062Labels = Sparse.eval nodeValue1062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1062) = mixedMoment B node1062 node1062Labels := rfl
  simpa [nodeValue1062, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

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

theorem sound1192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1192 node1192Labels = Sparse.eval nodeValue1192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1192) = mixedMoment B node1192 node1192Labels := rfl
  simpa [nodeValue1192, Sparse.eval] using hc.symm

theorem sound1193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1193 node1193Labels = Sparse.eval nodeValue1193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1193) = mixedMoment B node1193 node1193Labels := rfl
  simpa [nodeValue1193, Sparse.eval] using hc.symm

theorem sound1204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1204 node1204Labels = Sparse.eval nodeValue1204 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1204) = mixedMoment B node1204 node1204Labels := rfl
  simpa [nodeValue1204, Sparse.eval] using hc.symm

theorem sound1205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1205 node1205Labels = Sparse.eval nodeValue1205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1205) = mixedMoment B node1205 node1205Labels := rfl
  simpa [nodeValue1205, Sparse.eval] using hc.symm

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

theorem sound1511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1511 node1511Labels = Sparse.eval nodeValue1511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1511) = mixedMoment B node1511 node1511Labels := rfl
  simpa [nodeValue1511, Sparse.eval] using hc.symm

theorem sound1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1523 node1523Labels = Sparse.eval nodeValue1523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1523) = mixedMoment B node1523 node1523Labels := rfl
  simpa [nodeValue1523, Sparse.eval] using hc.symm

theorem sound1525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1525 node1525Labels = Sparse.eval nodeValue1525 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1525) = mixedMoment B node1525 node1525Labels := rfl
  simpa [nodeValue1525, Sparse.eval] using hc.symm

theorem sound1529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1529 node1529Labels = Sparse.eval nodeValue1529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1529) = mixedMoment B node1529 node1529Labels := rfl
  simpa [nodeValue1529, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = 0 := by
  exact mixedMoment_order_one B hB node1727 node1727Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1667 node1667Labels = Sparse.eval nodeValue1667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1667) = mixedMoment B node1667 node1667Labels := rfl
  simpa [nodeValue1667, Sparse.eval] using hc.symm

theorem sound1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1679 node1679Labels = Sparse.eval nodeValue1679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1679) = mixedMoment B node1679 node1679Labels := rfl
  simpa [nodeValue1679, Sparse.eval] using hc.symm

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

theorem sound1685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1685 node1685Labels = Sparse.eval nodeValue1685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1685) = mixedMoment B node1685 node1685Labels := rfl
  simpa [nodeValue1685, Sparse.eval] using hc.symm

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1712 node1712Labels = Sparse.eval nodeValue1712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1712) = mixedMoment B node1712 node1712Labels := rfl
  simpa [nodeValue1712, Sparse.eval] using hc.symm

theorem sound1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1714 node1714Labels = Sparse.eval nodeValue1714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1714) = mixedMoment B node1714 node1714Labels := rfl
  simpa [nodeValue1714, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

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

theorem sound1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1735 node1735Labels = Sparse.eval nodeValue1735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1735) = mixedMoment B node1735 node1735Labels := rfl
  simpa [nodeValue1735, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1743 node1743Labels = Sparse.eval nodeValue1743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1743) = mixedMoment B node1743 node1743Labels := rfl
  simpa [nodeValue1743, Sparse.eval] using hc.symm

theorem sound1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1745 node1745Labels = Sparse.eval nodeValue1745 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1745) = mixedMoment B node1745 node1745Labels := rfl
  simpa [nodeValue1745, Sparse.eval] using hc.symm

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

theorem sound1900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1900 node1900Labels = Sparse.eval nodeValue1900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1900) = mixedMoment B node1900 node1900Labels := rfl
  simpa [nodeValue1900, Sparse.eval] using hc.symm

theorem sound1901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1901 node1901Labels = Sparse.eval nodeValue1901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1901) = mixedMoment B node1901 node1901Labels := rfl
  simpa [nodeValue1901, Sparse.eval] using hc.symm

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

theorem sound1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1928 node1928Labels = Sparse.eval nodeValue1928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1928) = mixedMoment B node1928 node1928Labels := rfl
  simpa [nodeValue1928, Sparse.eval] using hc.symm

theorem sound1929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1929 node1929Labels = Sparse.eval nodeValue1929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1929) = mixedMoment B node1929 node1929Labels := rfl
  simpa [nodeValue1929, Sparse.eval] using hc.symm

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

theorem sound1993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1993 node1993Labels = Sparse.eval nodeValue1993 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1993) = mixedMoment B node1993 node1993Labels := rfl
  simpa [nodeValue1993, Sparse.eval] using hc.symm

theorem sound1994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1994 node1994Labels = Sparse.eval nodeValue1994 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1994) = mixedMoment B node1994 node1994Labels := rfl
  simpa [nodeValue1994, Sparse.eval] using hc.symm

theorem sound2011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2011 node2011Labels = Sparse.eval nodeValue2011 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2011) = mixedMoment B node2011 node2011Labels := rfl
  simpa [nodeValue2011, Sparse.eval] using hc.symm

theorem sound2027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2027 node2027Labels = Sparse.eval nodeValue2027 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2027) = mixedMoment B node2027 node2027Labels := rfl
  simpa [nodeValue2027, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

theorem sound2038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2038 node2038Labels = Sparse.eval nodeValue2038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2038) = mixedMoment B node2038 node2038Labels := rfl
  simpa [nodeValue2038, Sparse.eval] using hc.symm

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

theorem sound2072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2072 node2072Labels = Sparse.eval nodeValue2072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2072) = mixedMoment B node2072 node2072Labels := rfl
  simpa [nodeValue2072, Sparse.eval] using hc.symm

theorem sound2073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2073 node2073Labels = Sparse.eval nodeValue2073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2073) = mixedMoment B node2073 node2073Labels := rfl
  simpa [nodeValue2073, Sparse.eval] using hc.symm

theorem sound2093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2093 node2093Labels = Sparse.eval nodeValue2093 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2093) = mixedMoment B node2093 node2093Labels := rfl
  simpa [nodeValue2093, Sparse.eval] using hc.symm

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

theorem sound2114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2114 node2114Labels = Sparse.eval nodeValue2114 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2114) = mixedMoment B node2114 node2114Labels := rfl
  simpa [nodeValue2114, Sparse.eval] using hc.symm

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

theorem sound2122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2122 node2122Labels = Sparse.eval nodeValue2122 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2122) = mixedMoment B node2122 node2122Labels := rfl
  simpa [nodeValue2122, Sparse.eval] using hc.symm

theorem sound2123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2123 node2123Labels = Sparse.eval nodeValue2123 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2123) = mixedMoment B node2123 node2123Labels := rfl
  simpa [nodeValue2123, Sparse.eval] using hc.symm

theorem sound2137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2137 node2137Labels = Sparse.eval nodeValue2137 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2137) = mixedMoment B node2137 node2137Labels := rfl
  simpa [nodeValue2137, Sparse.eval] using hc.symm

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

theorem sound2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2192 node2192Labels = Sparse.eval nodeValue2192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2192) = mixedMoment B node2192 node2192Labels := rfl
  simpa [nodeValue2192, Sparse.eval] using hc.symm

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

theorem sound2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2217 node2217Labels = Sparse.eval nodeValue2217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2217) = mixedMoment B node2217 node2217Labels := rfl
  simpa [nodeValue2217, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2246 node2246Labels = Sparse.eval nodeValue2246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2246) = mixedMoment B node2246 node2246Labels := rfl
  simpa [nodeValue2246, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2267 node2267Labels = Sparse.eval nodeValue2267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2267) = mixedMoment B node2267 node2267Labels := rfl
  simpa [nodeValue2267, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2280 node2280Labels = Sparse.eval nodeValue2280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2280) = mixedMoment B node2280 node2280Labels := rfl
  simpa [nodeValue2280, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2411 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2411 node2411Labels = 0 := by
  exact mixedMoment_order_one B hB node2411 node2411Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2410 node2410Labels = Sparse.eval nodeValue2410 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2410) = mixedMoment B node2410 node2410Labels := rfl
  simpa [nodeValue2410, Sparse.eval] using hc.symm

theorem sound2411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2411 node2411Labels = Sparse.eval nodeValue2411 (mixedVector B) := by
  simpa only [nodeValue2411, Sparse.eval_nil] using zero2411 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2468 node2468Labels = 0 := by
  exact mixedMoment_order_one B hB node2468 node2468Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2467 node2467Labels = Sparse.eval nodeValue2467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2467) = mixedMoment B node2467 node2467Labels := rfl
  simpa [nodeValue2467, Sparse.eval] using hc.symm

theorem sound2468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2468 node2468Labels = Sparse.eval nodeValue2468 (mixedVector B) := by
  simpa only [nodeValue2468, Sparse.eval_nil] using zero2468 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2540 node2540Labels = 0 := by
  exact mixedMoment_alpha B hF node2540 node2540Labels 1 permutation161
    (by decide +kernel)

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

theorem sound2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2538 node2538Labels = Sparse.eval nodeValue2538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2538) = mixedMoment B node2538 node2538Labels := rfl
  simpa [nodeValue2538, Sparse.eval] using hc.symm

theorem sound2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2539 node2539Labels = Sparse.eval nodeValue2539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2539) = mixedMoment B node2539 node2539Labels := rfl
  simpa [nodeValue2539, Sparse.eval] using hc.symm

theorem sound2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2540 node2540Labels = Sparse.eval nodeValue2540 (mixedVector B) := by
  simpa only [nodeValue2540, Sparse.eval_nil] using zero2540 B _hB _hF

theorem sound2541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2541 node2541Labels = Sparse.eval nodeValue2541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2541) = mixedMoment B node2541 node2541Labels := rfl
  simpa [nodeValue2541, Sparse.eval] using hc.symm

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

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

theorem sound2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2687 node2687Labels = Sparse.eval nodeValue2687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2687) = mixedMoment B node2687 node2687Labels := rfl
  simpa [nodeValue2687, Sparse.eval] using hc.symm

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

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

theorem sound2706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2706 node2706Labels = Sparse.eval nodeValue2706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2706) = mixedMoment B node2706 node2706Labels := rfl
  simpa [nodeValue2706, Sparse.eval] using hc.symm

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

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

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

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

theorem sound4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4089 node4089Labels = Sparse.eval nodeValue4089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4089) = mixedMoment B node4089 node4089Labels := rfl
  simpa [nodeValue4089, Sparse.eval] using hc.symm

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

theorem sound613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node613 node613Labels = Sparse.eval nodeValue613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 613) = mixedMoment B node613 node613Labels := rfl
  simpa [nodeValue613, Sparse.eval] using hc.symm

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

theorem sound4154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4154 node4154Labels = Sparse.eval nodeValue4154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4154) = mixedMoment B node4154 node4154Labels := rfl
  simpa [nodeValue4154, Sparse.eval] using hc.symm

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

theorem sound4160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4160 node4160Labels = Sparse.eval nodeValue4160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4160) = mixedMoment B node4160 node4160Labels := rfl
  simpa [nodeValue4160, Sparse.eval] using hc.symm

theorem sound4162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4162 node4162Labels = Sparse.eval nodeValue4162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4162) = mixedMoment B node4162 node4162Labels := rfl
  simpa [nodeValue4162, Sparse.eval] using hc.symm

theorem sound4185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4185 node4185Labels = Sparse.eval nodeValue4185 (mixedVector B) := by
  have h := singleton4185 B _hB
  rw [sound613 B _hB _hF, sound1525 B _hB _hF] at h
  norm_num [nodeValue4185, nodeValue613, nodeValue1525, Sparse.eval] at h ⊢
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

theorem sound4328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4328 node4328Labels = Sparse.eval nodeValue4328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4328) = mixedMoment B node4328 node4328Labels := rfl
  simpa [nodeValue4328, Sparse.eval] using hc.symm

theorem sound4334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4334 node4334Labels = Sparse.eval nodeValue4334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4334) = mixedMoment B node4334 node4334Labels := rfl
  simpa [nodeValue4334, Sparse.eval] using hc.symm

theorem sound4336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4336 node4336Labels = Sparse.eval nodeValue4336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4336) = mixedMoment B node4336 node4336Labels := rfl
  simpa [nodeValue4336, Sparse.eval] using hc.symm

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

theorem sound4368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4368 node4368Labels = Sparse.eval nodeValue4368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4368) = mixedMoment B node4368 node4368Labels := rfl
  simpa [nodeValue4368, Sparse.eval] using hc.symm

theorem sound4373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4373 node4373Labels = Sparse.eval nodeValue4373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4373) = mixedMoment B node4373 node4373Labels := rfl
  simpa [nodeValue4373, Sparse.eval] using hc.symm

theorem sound4375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4375 node4375Labels = Sparse.eval nodeValue4375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4375) = mixedMoment B node4375 node4375Labels := rfl
  simpa [nodeValue4375, Sparse.eval] using hc.symm

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

theorem sound4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4457 node4457Labels = Sparse.eval nodeValue4457 (mixedVector B) := by
  have h := singleton4457 B _hB
  rw [sound1040 B _hB _hF, sound1707 B _hB _hF] at h
  norm_num [nodeValue4457, nodeValue1040, nodeValue1707, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4459 node4459Labels = Sparse.eval nodeValue4459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4459) = mixedMoment B node4459 node4459Labels := rfl
  simpa [nodeValue4459, Sparse.eval] using hc.symm

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4464 node4464Labels = Sparse.eval nodeValue4464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4464) = mixedMoment B node4464 node4464Labels := rfl
  simpa [nodeValue4464, Sparse.eval] using hc.symm

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

theorem sound4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4503 node4503Labels = Sparse.eval nodeValue4503 (mixedVector B) := by
  have h := singleton4503 B _hB
  rw [sound1087 B _hB _hF, sound1739 B _hB _hF] at h
  norm_num [nodeValue4503, nodeValue1087, nodeValue1739, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
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

theorem zero4894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = 0 := by
  exact mixedMoment_order_one B hB node4894 node4894Labels 1
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

theorem sound4874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4874 node4874Labels = Sparse.eval nodeValue4874 (mixedVector B) := by
  have h := singleton4874 B _hB
  rw [sound2115 B _hB _hF, sound2276 B _hB _hF] at h
  norm_num [nodeValue4874, nodeValue2115, nodeValue2276, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

theorem sound4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4896 node4896Labels = Sparse.eval nodeValue4896 (mixedVector B) := by
  have h := singleton4896 B _hB
  rw [sound2266 B _hB _hF, sound2278 B _hB _hF] at h
  norm_num [nodeValue4896, nodeValue2266, nodeValue2278, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources46
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1495 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 0) (sourceB1495 + difference 0 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1192) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 0) (sourceB1495 + difference 0 0) sourceC1495) = raw22843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22843; decide +kernel
    rw [ha]
    exact (canonical22843 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 1) (sourceB1495 + difference 1 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 1) (sourceB1495 + difference 1 0) sourceC1495) = raw22844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22844; decide +kernel
    rw [ha]
    exact (canonical22844 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 2) (sourceB1495 + difference 2 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 2) (sourceB1495 + difference 2 0) sourceC1495) = raw22845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22845; decide +kernel
    rw [ha]
    exact (canonical22845 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 3) (sourceB1495 + difference 3 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2410) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 3) (sourceB1495 + difference 3 0) sourceC1495) = raw22846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22846; decide +kernel
    rw [ha]
    exact (canonical22846 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 4) (sourceB1495 + difference 4 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 4) (sourceB1495 + difference 4 0) sourceC1495) = raw22847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22847; decide +kernel
    rw [ha]
    exact (canonical22847 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1495 + difference 0 5) (sourceB1495 + difference 5 0) sourceC1495) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1495 + difference 0 5) (sourceB1495 + difference 5 0) sourceC1495) = raw22848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1495 sourceB1495 sourceC1495 difference raw22848; decide +kernel
    rw [ha]
    exact (canonical22848 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1495 + sourceB1495) sourceC1495) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1495 + sourceB1495) sourceC1495) = raw22849 := by
      apply Matrix.ext; unfold doubleCharges sourceA1495 sourceB1495 sourceC1495 raw22849; decide +kernel
    rw [ha]
    exact (canonical22849 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1495 sourceB1495 sourceC1495
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1495, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1496 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 0) (sourceB1496 + difference 0 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 0) (sourceB1496 + difference 0 0) sourceC1496) = raw21012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw21012; decide +kernel
    rw [ha]
    exact (canonical21012 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 1) (sourceB1496 + difference 1 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 1) (sourceB1496 + difference 1 0) sourceC1496) = raw22850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw22850; decide +kernel
    rw [ha]
    exact (canonical22850 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 2) (sourceB1496 + difference 2 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 2) (sourceB1496 + difference 2 0) sourceC1496) = raw22851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw22851; decide +kernel
    rw [ha]
    exact (canonical22851 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 3) (sourceB1496 + difference 3 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2411) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 3) (sourceB1496 + difference 3 0) sourceC1496) = raw22852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw22852; decide +kernel
    rw [ha]
    exact (canonical22852 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 4) (sourceB1496 + difference 4 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 4) (sourceB1496 + difference 4 0) sourceC1496) = raw21007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw21007; decide +kernel
    rw [ha]
    exact (canonical21007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1496 + difference 0 5) (sourceB1496 + difference 5 0) sourceC1496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1496 + difference 0 5) (sourceB1496 + difference 5 0) sourceC1496) = raw22853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1496 sourceB1496 sourceC1496 difference raw22853; decide +kernel
    rw [ha]
    exact (canonical22853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1496 + sourceB1496) sourceC1496) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1496 + sourceB1496) sourceC1496) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1496 sourceB1496 sourceC1496 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1496 sourceB1496 sourceC1496
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1496, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1497 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1497 + difference 0 3) (sourceB1497 + difference 3 0) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2411) := by
    have ha : (tripleCharges (sourceA1497 + difference 0 3) (sourceB1497 + difference 3 0) sourceC1497) = raw22852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22852; decide +kernel
    rw [ha]
    exact (canonical22852 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1497 + difference 1 3) (sourceB1497 + difference 3 1) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1099) := by
    have ha : (tripleCharges (sourceA1497 + difference 1 3) (sourceB1497 + difference 3 1) sourceC1497) = raw22854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22854; decide +kernel
    rw [ha]
    exact (canonical22854 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1497 + difference 2 3) (sourceB1497 + difference 3 2) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1099) := by
    have ha : (tripleCharges (sourceA1497 + difference 2 3) (sourceB1497 + difference 3 2) sourceC1497) = raw22855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22855; decide +kernel
    rw [ha]
    exact (canonical22855 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1497 + difference 3 3) (sourceB1497 + difference 3 3) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA1497 + difference 3 3) (sourceB1497 + difference 3 3) sourceC1497) = raw21012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw21012; decide +kernel
    rw [ha]
    exact (canonical21012 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1497 + difference 4 3) (sourceB1497 + difference 3 4) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1104) := by
    have ha : (tripleCharges (sourceA1497 + difference 4 3) (sourceB1497 + difference 3 4) sourceC1497) = raw22856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22856; decide +kernel
    rw [ha]
    exact (canonical22856 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1497 + difference 5 3) (sourceB1497 + difference 3 5) sourceC1497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1104) := by
    have ha : (tripleCharges (sourceA1497 + difference 5 3) (sourceB1497 + difference 3 5) sourceC1497) = raw22857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1497 sourceB1497 sourceC1497 difference raw22857; decide +kernel
    rw [ha]
    exact (canonical22857 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1497 + sourceB1497) sourceC1497) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1497 + sourceB1497) sourceC1497) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1497 sourceB1497 sourceC1497 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1497 sourceB1497 sourceC1497
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1497, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1499 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 0) (sourceB1499 + difference 0 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1204) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 0) (sourceB1499 + difference 0 0) sourceC1499) = raw22864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22864; decide +kernel
    rw [ha]
    exact (canonical22864 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 1) (sourceB1499 + difference 1 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2540) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 1) (sourceB1499 + difference 1 0) sourceC1499) = raw22865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22865; decide +kernel
    rw [ha]
    exact (canonical22865 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 2) (sourceB1499 + difference 2 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 2) (sourceB1499 + difference 2 0) sourceC1499) = raw22866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22866; decide +kernel
    rw [ha]
    exact (canonical22866 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 3) (sourceB1499 + difference 3 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 3) (sourceB1499 + difference 3 0) sourceC1499) = raw22867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22867; decide +kernel
    rw [ha]
    exact (canonical22867 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 4) (sourceB1499 + difference 4 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 4) (sourceB1499 + difference 4 0) sourceC1499) = raw22868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22868; decide +kernel
    rw [ha]
    exact (canonical22868 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1499 + difference 0 5) (sourceB1499 + difference 5 0) sourceC1499) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1499 + difference 0 5) (sourceB1499 + difference 5 0) sourceC1499) = raw22869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1499 sourceB1499 sourceC1499 difference raw22869; decide +kernel
    rw [ha]
    exact (canonical22869 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1499 + sourceB1499) sourceC1499) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1499 + sourceB1499) sourceC1499) = raw22870 := by
      apply Matrix.ext; unfold doubleCharges sourceA1499 sourceB1499 sourceC1499 raw22870; decide +kernel
    rw [ha]
    exact (canonical22870 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1499 sourceB1499 sourceC1499
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1499, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1500 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 0) (sourceB1500 + difference 0 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 0) (sourceB1500 + difference 0 0) sourceC1500) = raw21050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw21050; decide +kernel
    rw [ha]
    exact (canonical21050 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 1) (sourceB1500 + difference 1 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2541) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 1) (sourceB1500 + difference 1 0) sourceC1500) = raw22871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw22871; decide +kernel
    rw [ha]
    exact (canonical22871 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 2) (sourceB1500 + difference 2 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 2) (sourceB1500 + difference 2 0) sourceC1500) = raw22872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw22872; decide +kernel
    rw [ha]
    exact (canonical22872 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 3) (sourceB1500 + difference 3 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 3) (sourceB1500 + difference 3 0) sourceC1500) = raw22873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw22873; decide +kernel
    rw [ha]
    exact (canonical22873 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 4) (sourceB1500 + difference 4 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 4) (sourceB1500 + difference 4 0) sourceC1500) = raw21045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw21045; decide +kernel
    rw [ha]
    exact (canonical21045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1500 + difference 0 5) (sourceB1500 + difference 5 0) sourceC1500) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1500 + difference 0 5) (sourceB1500 + difference 5 0) sourceC1500) = raw22874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1500 sourceB1500 sourceC1500 difference raw22874; decide +kernel
    rw [ha]
    exact (canonical22874 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1500 + sourceB1500) sourceC1500) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1500 + sourceB1500) sourceC1500) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1500 sourceB1500 sourceC1500 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1500 sourceB1500 sourceC1500
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1500, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1501 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1501 + difference 0 2) (sourceB1501 + difference 2 0) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA1501 + difference 0 2) (sourceB1501 + difference 2 0) sourceC1501) = raw22872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22872; decide +kernel
    rw [ha]
    exact (canonical22872 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1501 + difference 1 2) (sourceB1501 + difference 2 1) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1106) := by
    have ha : (tripleCharges (sourceA1501 + difference 1 2) (sourceB1501 + difference 2 1) sourceC1501) = raw22875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22875; decide +kernel
    rw [ha]
    exact (canonical22875 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1501 + difference 2 2) (sourceB1501 + difference 2 2) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1501 + difference 2 2) (sourceB1501 + difference 2 2) sourceC1501) = raw21050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw21050; decide +kernel
    rw [ha]
    exact (canonical21050 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1501 + difference 3 2) (sourceB1501 + difference 2 3) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1124) := by
    have ha : (tripleCharges (sourceA1501 + difference 3 2) (sourceB1501 + difference 2 3) sourceC1501) = raw22876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22876; decide +kernel
    rw [ha]
    exact (canonical22876 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1501 + difference 4 2) (sourceB1501 + difference 2 4) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1501 + difference 4 2) (sourceB1501 + difference 2 4) sourceC1501) = raw22877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22877; decide +kernel
    rw [ha]
    exact (canonical22877 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1501 + difference 5 2) (sourceB1501 + difference 2 5) sourceC1501) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA1501 + difference 5 2) (sourceB1501 + difference 2 5) sourceC1501) = raw22878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1501 sourceB1501 sourceC1501 difference raw22878; decide +kernel
    rw [ha]
    exact (canonical22878 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1501 + sourceB1501) sourceC1501) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1501 + sourceB1501) sourceC1501) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1501 sourceB1501 sourceC1501 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1501 sourceB1501 sourceC1501
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1501, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1503 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 0) (sourceB1503 + difference 0 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1062) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 0) (sourceB1503 + difference 0 0) sourceC1503) = raw22884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22884; decide +kernel
    rw [ha]
    exact (canonical22884 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 1) (sourceB1503 + difference 1 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2137) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 1) (sourceB1503 + difference 1 0) sourceC1503) = raw22885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22885; decide +kernel
    rw [ha]
    exact (canonical22885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 2) (sourceB1503 + difference 2 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2038) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 2) (sourceB1503 + difference 2 0) sourceC1503) = raw22886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22886; decide +kernel
    rw [ha]
    exact (canonical22886 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 3) (sourceB1503 + difference 3 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2038) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 3) (sourceB1503 + difference 3 0) sourceC1503) = raw22887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22887; decide +kernel
    rw [ha]
    exact (canonical22887 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 4) (sourceB1503 + difference 4 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 4) (sourceB1503 + difference 4 0) sourceC1503) = raw22888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22888; decide +kernel
    rw [ha]
    exact (canonical22888 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1503 + difference 0 5) (sourceB1503 + difference 5 0) sourceC1503) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1503 + difference 0 5) (sourceB1503 + difference 5 0) sourceC1503) = raw22889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1503 sourceB1503 sourceC1503 difference raw22889; decide +kernel
    rw [ha]
    exact (canonical22889 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1503 + sourceB1503) sourceC1503) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1503 + sourceB1503) sourceC1503) = raw22890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1503 sourceB1503 sourceC1503 raw22890; decide +kernel
    rw [ha]
    exact (canonical22890 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1503 sourceB1503 sourceC1503
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1503, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources47
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1504 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 0) (sourceB1504 + difference 0 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 992) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 0) (sourceB1504 + difference 0 0) sourceC1504) = raw22891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22891; decide +kernel
    rw [ha]
    exact (canonical22891 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 1) (sourceB1504 + difference 1 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2122) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 1) (sourceB1504 + difference 1 0) sourceC1504) = raw22892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22892; decide +kernel
    rw [ha]
    exact (canonical22892 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 2) (sourceB1504 + difference 2 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1993) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 2) (sourceB1504 + difference 2 0) sourceC1504) = raw22893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22893; decide +kernel
    rw [ha]
    exact (canonical22893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 3) (sourceB1504 + difference 3 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 3) (sourceB1504 + difference 3 0) sourceC1504) = raw22894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22894; decide +kernel
    rw [ha]
    exact (canonical22894 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 4) (sourceB1504 + difference 4 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 4) (sourceB1504 + difference 4 0) sourceC1504) = raw22895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22895; decide +kernel
    rw [ha]
    exact (canonical22895 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1504 + difference 0 5) (sourceB1504 + difference 5 0) sourceC1504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1504 + difference 0 5) (sourceB1504 + difference 5 0) sourceC1504) = raw22896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1504 sourceB1504 sourceC1504 difference raw22896; decide +kernel
    rw [ha]
    exact (canonical22896 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1504 + sourceB1504) sourceC1504) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1504 + sourceB1504) sourceC1504) = raw22897 := by
      apply Matrix.ext; unfold doubleCharges sourceA1504 sourceB1504 sourceC1504 raw22897; decide +kernel
    rw [ha]
    exact (canonical22897 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1504 sourceB1504 sourceC1504
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1504, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1505 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 0) (sourceB1505 + difference 0 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 993) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 0) (sourceB1505 + difference 0 0) sourceC1505) = raw21099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw21099; decide +kernel
    rw [ha]
    exact (canonical21099 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 1) (sourceB1505 + difference 1 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2123) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 1) (sourceB1505 + difference 1 0) sourceC1505) = raw22898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw22898; decide +kernel
    rw [ha]
    exact (canonical22898 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 2) (sourceB1505 + difference 2 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1994) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 2) (sourceB1505 + difference 2 0) sourceC1505) = raw22899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw22899; decide +kernel
    rw [ha]
    exact (canonical22899 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 3) (sourceB1505 + difference 3 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 3) (sourceB1505 + difference 3 0) sourceC1505) = raw22900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw22900; decide +kernel
    rw [ha]
    exact (canonical22900 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 4) (sourceB1505 + difference 4 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 4) (sourceB1505 + difference 4 0) sourceC1505) = raw21094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw21094; decide +kernel
    rw [ha]
    exact (canonical21094 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1505 + difference 0 5) (sourceB1505 + difference 5 0) sourceC1505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1505 + difference 0 5) (sourceB1505 + difference 5 0) sourceC1505) = raw22901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1505 sourceB1505 sourceC1505 difference raw22901; decide +kernel
    rw [ha]
    exact (canonical22901 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1505 + sourceB1505) sourceC1505) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1505 + sourceB1505) sourceC1505) = raw21095 := by
      apply Matrix.ext; unfold doubleCharges sourceA1505 sourceB1505 sourceC1505 raw21095; decide +kernel
    rw [ha]
    exact (canonical21095 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1505 sourceB1505 sourceC1505
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1505, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1506 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 0) (sourceB1506 + difference 0 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1025) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 0) (sourceB1506 + difference 0 0) sourceC1506) = raw22902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22902; decide +kernel
    rw [ha]
    exact (canonical22902 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 1) (sourceB1506 + difference 1 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 1) (sourceB1506 + difference 1 0) sourceC1506) = raw22903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22903; decide +kernel
    rw [ha]
    exact (canonical22903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 2) (sourceB1506 + difference 2 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 2) (sourceB1506 + difference 2 0) sourceC1506) = raw22904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22904; decide +kernel
    rw [ha]
    exact (canonical22904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 3) (sourceB1506 + difference 3 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2011) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 3) (sourceB1506 + difference 3 0) sourceC1506) = raw22905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22905; decide +kernel
    rw [ha]
    exact (canonical22905 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 4) (sourceB1506 + difference 4 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 4) (sourceB1506 + difference 4 0) sourceC1506) = raw22906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22906; decide +kernel
    rw [ha]
    exact (canonical22906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1506 + difference 0 5) (sourceB1506 + difference 5 0) sourceC1506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1506 + difference 0 5) (sourceB1506 + difference 5 0) sourceC1506) = raw22907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1506 sourceB1506 sourceC1506 difference raw22907; decide +kernel
    rw [ha]
    exact (canonical22907 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1506 + sourceB1506) sourceC1506) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1506 + sourceB1506) sourceC1506) = raw22908 := by
      apply Matrix.ext; unfold doubleCharges sourceA1506 sourceB1506 sourceC1506 raw22908; decide +kernel
    rw [ha]
    exact (canonical22908 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1506 sourceB1506 sourceC1506
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1506, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1507 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 0) (sourceB1507 + difference 0 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 973) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 0) (sourceB1507 + difference 0 0) sourceC1507) = raw22909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22909; decide +kernel
    rw [ha]
    exact (canonical22909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 1) (sourceB1507 + difference 1 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 1) (sourceB1507 + difference 1 0) sourceC1507) = raw22910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22910; decide +kernel
    rw [ha]
    exact (canonical22910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 2) (sourceB1507 + difference 2 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 2) (sourceB1507 + difference 2 0) sourceC1507) = raw22911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22911; decide +kernel
    rw [ha]
    exact (canonical22911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 3) (sourceB1507 + difference 3 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1900) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 3) (sourceB1507 + difference 3 0) sourceC1507) = raw22912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22912; decide +kernel
    rw [ha]
    exact (canonical22912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 4) (sourceB1507 + difference 4 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 4) (sourceB1507 + difference 4 0) sourceC1507) = raw22913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22913; decide +kernel
    rw [ha]
    exact (canonical22913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1507 + difference 0 5) (sourceB1507 + difference 5 0) sourceC1507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1507 + difference 0 5) (sourceB1507 + difference 5 0) sourceC1507) = raw22914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1507 sourceB1507 sourceC1507 difference raw22914; decide +kernel
    rw [ha]
    exact (canonical22914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1507 + sourceB1507) sourceC1507) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1507 + sourceB1507) sourceC1507) = raw22915 := by
      apply Matrix.ext; unfold doubleCharges sourceA1507 sourceB1507 sourceC1507 raw22915; decide +kernel
    rw [ha]
    exact (canonical22915 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1507 sourceB1507 sourceC1507
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1507, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1508 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 0) (sourceB1508 + difference 0 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 974) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 0) (sourceB1508 + difference 0 0) sourceC1508) = raw21132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw21132; decide +kernel
    rw [ha]
    exact (canonical21132 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 1) (sourceB1508 + difference 1 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 1) (sourceB1508 + difference 1 0) sourceC1508) = raw22916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw22916; decide +kernel
    rw [ha]
    exact (canonical22916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 2) (sourceB1508 + difference 2 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 2) (sourceB1508 + difference 2 0) sourceC1508) = raw22917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw22917; decide +kernel
    rw [ha]
    exact (canonical22917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 3) (sourceB1508 + difference 3 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1901) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 3) (sourceB1508 + difference 3 0) sourceC1508) = raw22918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw22918; decide +kernel
    rw [ha]
    exact (canonical22918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 4) (sourceB1508 + difference 4 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 4) (sourceB1508 + difference 4 0) sourceC1508) = raw21127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw21127; decide +kernel
    rw [ha]
    exact (canonical21127 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1508 + difference 0 5) (sourceB1508 + difference 5 0) sourceC1508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1508 + difference 0 5) (sourceB1508 + difference 5 0) sourceC1508) = raw22919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1508 sourceB1508 sourceC1508 difference raw22919; decide +kernel
    rw [ha]
    exact (canonical22919 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1508 + sourceB1508) sourceC1508) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1508 + sourceB1508) sourceC1508) = raw21128 := by
      apply Matrix.ext; unfold doubleCharges sourceA1508 sourceB1508 sourceC1508 raw21128; decide +kernel
    rw [ha]
    exact (canonical21128 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1508 sourceB1508 sourceC1508
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1508, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1509 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 0) (sourceB1509 + difference 0 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 0) (sourceB1509 + difference 0 0) sourceC1509) = raw22920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22920; decide +kernel
    rw [ha]
    exact (canonical22920 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 1) (sourceB1509 + difference 1 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2114) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 1) (sourceB1509 + difference 1 0) sourceC1509) = raw22921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22921; decide +kernel
    rw [ha]
    exact (canonical22921 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 2) (sourceB1509 + difference 2 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2027) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 2) (sourceB1509 + difference 2 0) sourceC1509) = raw22922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22922; decide +kernel
    rw [ha]
    exact (canonical22922 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 3) (sourceB1509 + difference 3 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2027) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 3) (sourceB1509 + difference 3 0) sourceC1509) = raw22923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22923; decide +kernel
    rw [ha]
    exact (canonical22923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 4) (sourceB1509 + difference 4 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 4) (sourceB1509 + difference 4 0) sourceC1509) = raw22924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22924; decide +kernel
    rw [ha]
    exact (canonical22924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1509 + difference 0 5) (sourceB1509 + difference 5 0) sourceC1509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1509 + difference 0 5) (sourceB1509 + difference 5 0) sourceC1509) = raw22925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1509 sourceB1509 sourceC1509 difference raw22925; decide +kernel
    rw [ha]
    exact (canonical22925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1509 + sourceB1509) sourceC1509) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1509 + sourceB1509) sourceC1509) = raw22926 := by
      apply Matrix.ext; unfold doubleCharges sourceA1509 sourceB1509 sourceC1509 raw22926; decide +kernel
    rw [ha]
    exact (canonical22926 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1509 sourceB1509 sourceC1509
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1509, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1510 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 1) (sourceB1510 + difference 1 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 1) (sourceB1510 + difference 1 0) sourceC1510) = raw22927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22927; decide +kernel
    rw [ha]
    exact (canonical22927 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 2) (sourceB1510 + difference 2 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 2) (sourceB1510 + difference 2 0) sourceC1510) = raw22928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22928; decide +kernel
    rw [ha]
    exact (canonical22928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 3) (sourceB1510 + difference 3 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 3) (sourceB1510 + difference 3 0) sourceC1510) = raw22929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22929; decide +kernel
    rw [ha]
    exact (canonical22929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 4) (sourceB1510 + difference 4 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 4) (sourceB1510 + difference 4 0) sourceC1510) = raw22930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22930; decide +kernel
    rw [ha]
    exact (canonical22930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1510 + difference 0 5) (sourceB1510 + difference 5 0) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1510 + difference 0 5) (sourceB1510 + difference 5 0) sourceC1510) = raw22931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22931; decide +kernel
    rw [ha]
    exact (canonical22931 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 0) (sourceB1510 + difference 0 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 0) (sourceB1510 + difference 0 1) sourceC1510) = raw22932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22932; decide +kernel
    rw [ha]
    exact (canonical22932 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 2) (sourceB1510 + difference 2 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 2) (sourceB1510 + difference 2 1) sourceC1510) = raw22933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22933; decide +kernel
    rw [ha]
    exact (canonical22933 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 3) (sourceB1510 + difference 3 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 3) (sourceB1510 + difference 3 1) sourceC1510) = raw22934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22934; decide +kernel
    rw [ha]
    exact (canonical22934 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 4) (sourceB1510 + difference 4 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 4) (sourceB1510 + difference 4 1) sourceC1510) = raw22935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22935; decide +kernel
    rw [ha]
    exact (canonical22935 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1510 + difference 1 5) (sourceB1510 + difference 5 1) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1510 + difference 1 5) (sourceB1510 + difference 5 1) sourceC1510) = raw22936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22936; decide +kernel
    rw [ha]
    exact (canonical22936 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 0) (sourceB1510 + difference 0 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 0) (sourceB1510 + difference 0 2) sourceC1510) = raw22937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22937; decide +kernel
    rw [ha]
    exact (canonical22937 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 1) (sourceB1510 + difference 1 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 1) (sourceB1510 + difference 1 2) sourceC1510) = raw22938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22938; decide +kernel
    rw [ha]
    exact (canonical22938 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 3) (sourceB1510 + difference 3 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 3) (sourceB1510 + difference 3 2) sourceC1510) = raw22939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22939; decide +kernel
    rw [ha]
    exact (canonical22939 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 4) (sourceB1510 + difference 4 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 4) (sourceB1510 + difference 4 2) sourceC1510) = raw22940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22940; decide +kernel
    rw [ha]
    exact (canonical22940 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1510 + difference 2 5) (sourceB1510 + difference 5 2) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1510 + difference 2 5) (sourceB1510 + difference 5 2) sourceC1510) = raw22941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22941; decide +kernel
    rw [ha]
    exact (canonical22941 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 0) (sourceB1510 + difference 0 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 0) (sourceB1510 + difference 0 3) sourceC1510) = raw22942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22942; decide +kernel
    rw [ha]
    exact (canonical22942 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 1) (sourceB1510 + difference 1 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 1) (sourceB1510 + difference 1 3) sourceC1510) = raw22943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22943; decide +kernel
    rw [ha]
    exact (canonical22943 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 2) (sourceB1510 + difference 2 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 2) (sourceB1510 + difference 2 3) sourceC1510) = raw22944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22944; decide +kernel
    rw [ha]
    exact (canonical22944 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 4) (sourceB1510 + difference 4 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 4) (sourceB1510 + difference 4 3) sourceC1510) = raw22945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22945; decide +kernel
    rw [ha]
    exact (canonical22945 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1510 + difference 3 5) (sourceB1510 + difference 5 3) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1510 + difference 3 5) (sourceB1510 + difference 5 3) sourceC1510) = raw22946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22946; decide +kernel
    rw [ha]
    exact (canonical22946 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 0) (sourceB1510 + difference 0 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4160) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 0) (sourceB1510 + difference 0 4) sourceC1510) = raw22947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22947; decide +kernel
    rw [ha]
    exact (canonical22947 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 1) (sourceB1510 + difference 1 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 1) (sourceB1510 + difference 1 4) sourceC1510) = raw22948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22948; decide +kernel
    rw [ha]
    exact (canonical22948 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 2) (sourceB1510 + difference 2 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 2) (sourceB1510 + difference 2 4) sourceC1510) = raw22949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22949; decide +kernel
    rw [ha]
    exact (canonical22949 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 3) (sourceB1510 + difference 3 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 3) (sourceB1510 + difference 3 4) sourceC1510) = raw22950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22950; decide +kernel
    rw [ha]
    exact (canonical22950 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1510 + difference 4 5) (sourceB1510 + difference 5 4) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1510 + difference 4 5) (sourceB1510 + difference 5 4) sourceC1510) = raw22951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22951; decide +kernel
    rw [ha]
    exact (canonical22951 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 0) (sourceB1510 + difference 0 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4162) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 0) (sourceB1510 + difference 0 5) sourceC1510) = raw22952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22952; decide +kernel
    rw [ha]
    exact (canonical22952 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 1) (sourceB1510 + difference 1 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4375) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 1) (sourceB1510 + difference 1 5) sourceC1510) = raw22953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22953; decide +kernel
    rw [ha]
    exact (canonical22953 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 2) (sourceB1510 + difference 2 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4336) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 2) (sourceB1510 + difference 2 5) sourceC1510) = raw22954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22954; decide +kernel
    rw [ha]
    exact (canonical22954 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 3) (sourceB1510 + difference 3 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4336) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 3) (sourceB1510 + difference 3 5) sourceC1510) = raw22955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22955; decide +kernel
    rw [ha]
    exact (canonical22955 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1510 + difference 5 4) (sourceB1510 + difference 4 5) sourceC1510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1510 + difference 5 4) (sourceB1510 + difference 4 5) sourceC1510) = raw22956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1510 sourceB1510 sourceC1510 difference raw22956; decide +kernel
    rw [ha]
    exact (canonical22956 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1510 sourceB1510 sourceC1510
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1510, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1512 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 1) (sourceB1512 + difference 1 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 1) (sourceB1512 + difference 1 0) sourceC1512) = raw22987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22987; decide +kernel
    rw [ha]
    exact (canonical22987 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 2) (sourceB1512 + difference 2 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 2) (sourceB1512 + difference 2 0) sourceC1512) = raw22988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22988; decide +kernel
    rw [ha]
    exact (canonical22988 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 3) (sourceB1512 + difference 3 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 3) (sourceB1512 + difference 3 0) sourceC1512) = raw22989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22989; decide +kernel
    rw [ha]
    exact (canonical22989 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 4) (sourceB1512 + difference 4 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 4) (sourceB1512 + difference 4 0) sourceC1512) = raw22990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22990; decide +kernel
    rw [ha]
    exact (canonical22990 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1512 + difference 0 5) (sourceB1512 + difference 5 0) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA1512 + difference 0 5) (sourceB1512 + difference 5 0) sourceC1512) = raw22991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22991; decide +kernel
    rw [ha]
    exact (canonical22991 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 0) (sourceB1512 + difference 0 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 0) (sourceB1512 + difference 0 1) sourceC1512) = raw22992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22992; decide +kernel
    rw [ha]
    exact (canonical22992 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 2) (sourceB1512 + difference 2 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 2) (sourceB1512 + difference 2 1) sourceC1512) = raw22993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22993; decide +kernel
    rw [ha]
    exact (canonical22993 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 3) (sourceB1512 + difference 3 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 3) (sourceB1512 + difference 3 1) sourceC1512) = raw22994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22994; decide +kernel
    rw [ha]
    exact (canonical22994 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 4) (sourceB1512 + difference 4 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 4) (sourceB1512 + difference 4 1) sourceC1512) = raw22995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22995; decide +kernel
    rw [ha]
    exact (canonical22995 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1512 + difference 1 5) (sourceB1512 + difference 5 1) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1512 + difference 1 5) (sourceB1512 + difference 5 1) sourceC1512) = raw22996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22996; decide +kernel
    rw [ha]
    exact (canonical22996 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 0) (sourceB1512 + difference 0 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 0) (sourceB1512 + difference 0 2) sourceC1512) = raw22997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22997; decide +kernel
    rw [ha]
    exact (canonical22997 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 1) (sourceB1512 + difference 1 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 1) (sourceB1512 + difference 1 2) sourceC1512) = raw22998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22998; decide +kernel
    rw [ha]
    exact (canonical22998 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 3) (sourceB1512 + difference 3 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 3) (sourceB1512 + difference 3 2) sourceC1512) = raw22999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw22999; decide +kernel
    rw [ha]
    exact (canonical22999 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 4) (sourceB1512 + difference 4 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 4) (sourceB1512 + difference 4 2) sourceC1512) = raw23000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23000; decide +kernel
    rw [ha]
    exact (canonical23000 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1512 + difference 2 5) (sourceB1512 + difference 5 2) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1512 + difference 2 5) (sourceB1512 + difference 5 2) sourceC1512) = raw23001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23001; decide +kernel
    rw [ha]
    exact (canonical23001 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 0) (sourceB1512 + difference 0 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 0) (sourceB1512 + difference 0 3) sourceC1512) = raw23002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23002; decide +kernel
    rw [ha]
    exact (canonical23002 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 1) (sourceB1512 + difference 1 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 1) (sourceB1512 + difference 1 3) sourceC1512) = raw23003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23003; decide +kernel
    rw [ha]
    exact (canonical23003 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 2) (sourceB1512 + difference 2 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 2) (sourceB1512 + difference 2 3) sourceC1512) = raw23004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23004; decide +kernel
    rw [ha]
    exact (canonical23004 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 4) (sourceB1512 + difference 4 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 4) (sourceB1512 + difference 4 3) sourceC1512) = raw23005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23005; decide +kernel
    rw [ha]
    exact (canonical23005 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1512 + difference 3 5) (sourceB1512 + difference 5 3) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1512 + difference 3 5) (sourceB1512 + difference 5 3) sourceC1512) = raw23006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23006; decide +kernel
    rw [ha]
    exact (canonical23006 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 0) (sourceB1512 + difference 0 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 0) (sourceB1512 + difference 0 4) sourceC1512) = raw23007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23007; decide +kernel
    rw [ha]
    exact (canonical23007 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 1) (sourceB1512 + difference 1 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 1) (sourceB1512 + difference 1 4) sourceC1512) = raw23008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23008; decide +kernel
    rw [ha]
    exact (canonical23008 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 2) (sourceB1512 + difference 2 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 2) (sourceB1512 + difference 2 4) sourceC1512) = raw23009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23009; decide +kernel
    rw [ha]
    exact (canonical23009 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 3) (sourceB1512 + difference 3 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 3) (sourceB1512 + difference 3 4) sourceC1512) = raw23010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23010; decide +kernel
    rw [ha]
    exact (canonical23010 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1512 + difference 4 5) (sourceB1512 + difference 5 4) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1512 + difference 4 5) (sourceB1512 + difference 5 4) sourceC1512) = raw23011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23011; decide +kernel
    rw [ha]
    exact (canonical23011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 0) (sourceB1512 + difference 0 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 0) (sourceB1512 + difference 0 5) sourceC1512) = raw23012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23012; decide +kernel
    rw [ha]
    exact (canonical23012 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 1) (sourceB1512 + difference 1 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1743) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 1) (sourceB1512 + difference 1 5) sourceC1512) = raw23013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23013; decide +kernel
    rw [ha]
    exact (canonical23013 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 2) (sourceB1512 + difference 2 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 2) (sourceB1512 + difference 2 5) sourceC1512) = raw23014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23014; decide +kernel
    rw [ha]
    exact (canonical23014 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 3) (sourceB1512 + difference 3 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 3) (sourceB1512 + difference 3 5) sourceC1512) = raw23015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23015; decide +kernel
    rw [ha]
    exact (canonical23015 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1512 + difference 5 4) (sourceB1512 + difference 4 5) sourceC1512) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1512 + difference 5 4) (sourceB1512 + difference 4 5) sourceC1512) = raw23016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1512 sourceB1512 sourceC1512 difference raw23016; decide +kernel
    rw [ha]
    exact (canonical23016 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1512 sourceB1512 sourceC1512
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1512, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1280 : Integer.Sparse.reindex keyMap MixedData.row1280 = numericRow1280 := by decide +kernel

theorem numericCheck1280 (x : Master → ℝ) : Integer.Sparse.eval numericRow1280 x =
    (1 : ℝ) * reducedSource1280 x := by
  norm_num [numericRow1280, reducedSource1280, Integer.Sparse.eval, Sparse.eval, nodeValue1192, nodeValue2410, nodeValue2538, nodeValue2685, nodeValue2687, nodeValue4082]

theorem reindexCheck1281 : Integer.Sparse.reindex keyMap MixedData.row1281 = numericRow1281 := by decide +kernel

theorem numericCheck1281 (x : Master → ℝ) : Integer.Sparse.eval numericRow1281 x =
    (1 : ℝ) * reducedSource1281 x := by
  norm_num [numericRow1281, reducedSource1281, Integer.Sparse.eval, Sparse.eval, nodeValue1193, nodeValue2411, nodeValue2539, nodeValue2686, nodeValue4089]

theorem reindexCheck1282 : Integer.Sparse.reindex keyMap MixedData.row1282 = numericRow1282 := by decide +kernel

theorem numericCheck1282 (x : Master → ℝ) : Integer.Sparse.eval numericRow1282 x =
    (1 : ℝ) * reducedSource1282 x := by
  norm_num [numericRow1282, reducedSource1282, Integer.Sparse.eval, Sparse.eval, nodeValue1099, nodeValue1104, nodeValue1193, nodeValue2411, nodeValue4089]

theorem reindexCheck1283 : Integer.Sparse.reindex keyMap MixedData.row1283 = numericRow1283 := by decide +kernel

theorem numericCheck1283 (x : Master → ℝ) : Integer.Sparse.eval numericRow1283 x =
    (1 : ℝ) * reducedSource1283 x := by
  norm_num [numericRow1283, reducedSource1283, Integer.Sparse.eval, Sparse.eval, nodeValue1204, nodeValue2467, nodeValue2540, nodeValue2704, nodeValue2706, nodeValue4080]

theorem reindexCheck1284 : Integer.Sparse.reindex keyMap MixedData.row1284 = numericRow1284 := by decide +kernel

theorem numericCheck1284 (x : Master → ℝ) : Integer.Sparse.eval numericRow1284 x =
    (1 : ℝ) * reducedSource1284 x := by
  norm_num [numericRow1284, reducedSource1284, Integer.Sparse.eval, Sparse.eval, nodeValue1205, nodeValue2468, nodeValue2541, nodeValue2705, nodeValue4088]

theorem reindexCheck1285 : Integer.Sparse.reindex keyMap MixedData.row1285 = numericRow1285 := by decide +kernel

theorem numericCheck1285 (x : Master → ℝ) : Integer.Sparse.eval numericRow1285 x =
    (1 : ℝ) * reducedSource1285 x := by
  norm_num [numericRow1285, reducedSource1285, Integer.Sparse.eval, Sparse.eval, nodeValue1106, nodeValue1110, nodeValue1124, nodeValue1205, nodeValue2468, nodeValue4088]

theorem reindexCheck1286 : Integer.Sparse.reindex keyMap MixedData.row1286 = numericRow1286 := by decide +kernel

theorem numericCheck1286 (x : Master → ℝ) : Integer.Sparse.eval numericRow1286 x =
    (1 : ℝ) * reducedSource1286 x := by
  norm_num [numericRow1286, reducedSource1286, Integer.Sparse.eval, Sparse.eval, nodeValue1062, nodeValue2038, nodeValue2137, nodeValue2276, nodeValue2280, nodeValue4082]

theorem reindexCheck1287 : Integer.Sparse.reindex keyMap MixedData.row1287 = numericRow1287 := by decide +kernel

theorem numericCheck1287 (x : Master → ℝ) : Integer.Sparse.eval numericRow1287 x =
    (1 : ℝ) * reducedSource1287 x := by
  norm_num [numericRow1287, reducedSource1287, Integer.Sparse.eval, Sparse.eval, nodeValue992, nodeValue1928, nodeValue1993, nodeValue2122, nodeValue2215, nodeValue2217, nodeValue4082]

theorem reindexCheck1288 : Integer.Sparse.reindex keyMap MixedData.row1288 = numericRow1288 := by decide +kernel

theorem numericCheck1288 (x : Master → ℝ) : Integer.Sparse.eval numericRow1288 x =
    (1 : ℝ) * reducedSource1288 x := by
  norm_num [numericRow1288, reducedSource1288, Integer.Sparse.eval, Sparse.eval, nodeValue993, nodeValue1929, nodeValue1994, nodeValue2123, nodeValue2216, nodeValue4080]

theorem reindexCheck1289 : Integer.Sparse.reindex keyMap MixedData.row1289 = numericRow1289 := by decide +kernel

theorem numericCheck1289 (x : Master → ℝ) : Integer.Sparse.eval numericRow1289 x =
    (1 : ℝ) * reducedSource1289 x := by
  norm_num [numericRow1289, reducedSource1289, Integer.Sparse.eval, Sparse.eval, nodeValue1025, nodeValue2011, nodeValue2093, nodeValue2242, nodeValue2246, nodeValue4080]

theorem reindexCheck1290 : Integer.Sparse.reindex keyMap MixedData.row1290 = numericRow1290 := by decide +kernel

theorem numericCheck1290 (x : Master → ℝ) : Integer.Sparse.eval numericRow1290 x =
    (1 : ℝ) * reducedSource1290 x := by
  norm_num [numericRow1290, reducedSource1290, Integer.Sparse.eval, Sparse.eval, nodeValue973, nodeValue1900, nodeValue2072, nodeValue2190, nodeValue2192, nodeValue4080]

theorem reindexCheck1291 : Integer.Sparse.reindex keyMap MixedData.row1291 = numericRow1291 := by decide +kernel

theorem numericCheck1291 (x : Master → ℝ) : Integer.Sparse.eval numericRow1291 x =
    (1 : ℝ) * reducedSource1291 x := by
  norm_num [numericRow1291, reducedSource1291, Integer.Sparse.eval, Sparse.eval, nodeValue974, nodeValue1901, nodeValue2073, nodeValue2191, nodeValue4079]

theorem reindexCheck1292 : Integer.Sparse.reindex keyMap MixedData.row1292 = numericRow1292 := by decide +kernel

theorem numericCheck1292 (x : Master → ℝ) : Integer.Sparse.eval numericRow1292 x =
    (1 : ℝ) * reducedSource1292 x := by
  norm_num [numericRow1292, reducedSource1292, Integer.Sparse.eval, Sparse.eval, nodeValue1048, nodeValue2027, nodeValue2114, nodeValue2261, nodeValue2267, nodeValue4081]

theorem reindexCheck1293 : Integer.Sparse.reindex keyMap MixedData.row1293 = numericRow1293 := by decide +kernel

theorem numericCheck1293 (x : Master → ℝ) : Integer.Sparse.eval numericRow1293 x =
    (4 : ℝ) * reducedSource1293 x := by
  norm_num [numericRow1293, reducedSource1293, Integer.Sparse.eval, Sparse.eval, nodeValue4154, nodeValue4160, nodeValue4162, nodeValue4185, nodeValue4328, nodeValue4334, nodeValue4336, nodeValue4354, nodeValue4368, nodeValue4373, nodeValue4375, nodeValue4457, nodeValue4459, nodeValue4460, nodeValue4464, nodeValue4498, nodeValue4503, nodeValue4810, nodeValue4874, nodeValue4894, nodeValue4896]
  ring

theorem reindexCheck1295 : Integer.Sparse.reindex keyMap MixedData.row1295 = numericRow1295 := by decide +kernel

theorem numericCheck1295 (x : Master → ℝ) : Integer.Sparse.eval numericRow1295 x =
    (1 : ℝ) * reducedSource1295 x := by
  norm_num [numericRow1295, reducedSource1295, Integer.Sparse.eval, Sparse.eval, nodeValue1511, nodeValue1523, nodeValue1525, nodeValue1529, nodeValue1667, nodeValue1679, nodeValue1681, nodeValue1685, nodeValue1707, nodeValue1712, nodeValue1714, nodeValue1725, nodeValue1727, nodeValue1735, nodeValue1739, nodeValue1743, nodeValue1745, nodeValue2215, nodeValue2264, nodeValue2276, nodeValue2278]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1280 (mixedVector B) = 0 := by
  have h1192 : mixedVector B (Sum.inr 1192) = Sparse.eval nodeValue1192 (mixedVector B) := by
    change mixedMoment B node1192 node1192Labels = _
    exact sound1192 B hB hF
  have h2410 : mixedVector B (Sum.inr 2410) = Sparse.eval nodeValue2410 (mixedVector B) := by
    change mixedMoment B node2410 node2410Labels = _
    exact sound2410 B hB hF
  have h2538 : mixedVector B (Sum.inr 2538) = Sparse.eval nodeValue2538 (mixedVector B) := by
    change mixedMoment B node2538 node2538Labels = _
    exact sound2538 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1495, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1192, h2410, h2538, h2685, h2687, h4082, reducedSource1280] using sourceEq1495 B hB

theorem rowSound1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1280 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1280, numericCheck1280, reducedZero1280 B hB hF, mul_zero]

theorem reducedZero1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1281 (mixedVector B) = 0 := by
  have h1193 : mixedVector B (Sum.inr 1193) = Sparse.eval nodeValue1193 (mixedVector B) := by
    change mixedMoment B node1193 node1193Labels = _
    exact sound1193 B hB hF
  have h2411 : mixedVector B (Sum.inr 2411) = Sparse.eval nodeValue2411 (mixedVector B) := by
    change mixedMoment B node2411 node2411Labels = _
    exact sound2411 B hB hF
  have h2539 : mixedVector B (Sum.inr 2539) = Sparse.eval nodeValue2539 (mixedVector B) := by
    change mixedMoment B node2539 node2539Labels = _
    exact sound2539 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1496, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1193, h2411, h2539, h2686, h4089, reducedSource1281] using sourceEq1496 B hB

theorem rowSound1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1281 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1281, numericCheck1281, reducedZero1281 B hB hF, mul_zero]

theorem reducedZero1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1282 (mixedVector B) = 0 := by
  have h1099 : mixedVector B (Sum.inr 1099) = Sparse.eval nodeValue1099 (mixedVector B) := by
    change mixedMoment B node1099 node1099Labels = _
    exact sound1099 B hB hF
  have h1104 : mixedVector B (Sum.inr 1104) = Sparse.eval nodeValue1104 (mixedVector B) := by
    change mixedMoment B node1104 node1104Labels = _
    exact sound1104 B hB hF
  have h1193 : mixedVector B (Sum.inr 1193) = Sparse.eval nodeValue1193 (mixedVector B) := by
    change mixedMoment B node1193 node1193Labels = _
    exact sound1193 B hB hF
  have h2411 : mixedVector B (Sum.inr 2411) = Sparse.eval nodeValue2411 (mixedVector B) := by
    change mixedMoment B node2411 node2411Labels = _
    exact sound2411 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1497, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1099, h1104, h1193, h2411, h4089, reducedSource1282] using sourceEq1497 B hB

theorem rowSound1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1282 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1282, numericCheck1282, reducedZero1282 B hB hF, mul_zero]

theorem reducedZero1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1283 (mixedVector B) = 0 := by
  have h1204 : mixedVector B (Sum.inr 1204) = Sparse.eval nodeValue1204 (mixedVector B) := by
    change mixedMoment B node1204 node1204Labels = _
    exact sound1204 B hB hF
  have h2467 : mixedVector B (Sum.inr 2467) = Sparse.eval nodeValue2467 (mixedVector B) := by
    change mixedMoment B node2467 node2467Labels = _
    exact sound2467 B hB hF
  have h2540 : mixedVector B (Sum.inr 2540) = Sparse.eval nodeValue2540 (mixedVector B) := by
    change mixedMoment B node2540 node2540Labels = _
    exact sound2540 B hB hF
  have h2704 : mixedVector B (Sum.inr 2704) = Sparse.eval nodeValue2704 (mixedVector B) := by
    change mixedMoment B node2704 node2704Labels = _
    exact sound2704 B hB hF
  have h2706 : mixedVector B (Sum.inr 2706) = Sparse.eval nodeValue2706 (mixedVector B) := by
    change mixedMoment B node2706 node2706Labels = _
    exact sound2706 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1499, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1204, h2467, h2540, h2704, h2706, h4080, reducedSource1283] using sourceEq1499 B hB

theorem rowSound1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1283 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1283, numericCheck1283, reducedZero1283 B hB hF, mul_zero]

theorem reducedZero1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1284 (mixedVector B) = 0 := by
  have h1205 : mixedVector B (Sum.inr 1205) = Sparse.eval nodeValue1205 (mixedVector B) := by
    change mixedMoment B node1205 node1205Labels = _
    exact sound1205 B hB hF
  have h2468 : mixedVector B (Sum.inr 2468) = Sparse.eval nodeValue2468 (mixedVector B) := by
    change mixedMoment B node2468 node2468Labels = _
    exact sound2468 B hB hF
  have h2541 : mixedVector B (Sum.inr 2541) = Sparse.eval nodeValue2541 (mixedVector B) := by
    change mixedMoment B node2541 node2541Labels = _
    exact sound2541 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1500, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1205, h2468, h2541, h2705, h4088, reducedSource1284] using sourceEq1500 B hB

theorem rowSound1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1284 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1284, numericCheck1284, reducedZero1284 B hB hF, mul_zero]

theorem reducedZero1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1285 (mixedVector B) = 0 := by
  have h1106 : mixedVector B (Sum.inr 1106) = Sparse.eval nodeValue1106 (mixedVector B) := by
    change mixedMoment B node1106 node1106Labels = _
    exact sound1106 B hB hF
  have h1110 : mixedVector B (Sum.inr 1110) = Sparse.eval nodeValue1110 (mixedVector B) := by
    change mixedMoment B node1110 node1110Labels = _
    exact sound1110 B hB hF
  have h1124 : mixedVector B (Sum.inr 1124) = Sparse.eval nodeValue1124 (mixedVector B) := by
    change mixedMoment B node1124 node1124Labels = _
    exact sound1124 B hB hF
  have h1205 : mixedVector B (Sum.inr 1205) = Sparse.eval nodeValue1205 (mixedVector B) := by
    change mixedMoment B node1205 node1205Labels = _
    exact sound1205 B hB hF
  have h2468 : mixedVector B (Sum.inr 2468) = Sparse.eval nodeValue2468 (mixedVector B) := by
    change mixedMoment B node2468 node2468Labels = _
    exact sound2468 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1501, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1106, h1110, h1124, h1205, h2468, h4088, reducedSource1285] using sourceEq1501 B hB

theorem rowSound1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1285 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1285, numericCheck1285, reducedZero1285 B hB hF, mul_zero]

theorem reducedZero1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1286 (mixedVector B) = 0 := by
  have h1062 : mixedVector B (Sum.inr 1062) = Sparse.eval nodeValue1062 (mixedVector B) := by
    change mixedMoment B node1062 node1062Labels = _
    exact sound1062 B hB hF
  have h2038 : mixedVector B (Sum.inr 2038) = Sparse.eval nodeValue2038 (mixedVector B) := by
    change mixedMoment B node2038 node2038Labels = _
    exact sound2038 B hB hF
  have h2137 : mixedVector B (Sum.inr 2137) = Sparse.eval nodeValue2137 (mixedVector B) := by
    change mixedMoment B node2137 node2137Labels = _
    exact sound2137 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2280 : mixedVector B (Sum.inr 2280) = Sparse.eval nodeValue2280 (mixedVector B) := by
    change mixedMoment B node2280 node2280Labels = _
    exact sound2280 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1503, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1062, h2038, h2137, h2276, h2280, h4082, reducedSource1286] using sourceEq1503 B hB

theorem rowSound1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1286 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1286, numericCheck1286, reducedZero1286 B hB hF, mul_zero]

theorem reducedZero1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1287 (mixedVector B) = 0 := by
  have h992 : mixedVector B (Sum.inr 992) = Sparse.eval nodeValue992 (mixedVector B) := by
    change mixedMoment B node992 node992Labels = _
    exact sound992 B hB hF
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h1993 : mixedVector B (Sum.inr 1993) = Sparse.eval nodeValue1993 (mixedVector B) := by
    change mixedMoment B node1993 node1993Labels = _
    exact sound1993 B hB hF
  have h2122 : mixedVector B (Sum.inr 2122) = Sparse.eval nodeValue2122 (mixedVector B) := by
    change mixedMoment B node2122 node2122Labels = _
    exact sound2122 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2217 : mixedVector B (Sum.inr 2217) = Sparse.eval nodeValue2217 (mixedVector B) := by
    change mixedMoment B node2217 node2217Labels = _
    exact sound2217 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1504, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h992, h1928, h1993, h2122, h2215, h2217, h4082, reducedSource1287] using sourceEq1504 B hB

theorem rowSound1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1287 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1287, numericCheck1287, reducedZero1287 B hB hF, mul_zero]

theorem reducedZero1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1288 (mixedVector B) = 0 := by
  have h993 : mixedVector B (Sum.inr 993) = Sparse.eval nodeValue993 (mixedVector B) := by
    change mixedMoment B node993 node993Labels = _
    exact sound993 B hB hF
  have h1929 : mixedVector B (Sum.inr 1929) = Sparse.eval nodeValue1929 (mixedVector B) := by
    change mixedMoment B node1929 node1929Labels = _
    exact sound1929 B hB hF
  have h1994 : mixedVector B (Sum.inr 1994) = Sparse.eval nodeValue1994 (mixedVector B) := by
    change mixedMoment B node1994 node1994Labels = _
    exact sound1994 B hB hF
  have h2123 : mixedVector B (Sum.inr 2123) = Sparse.eval nodeValue2123 (mixedVector B) := by
    change mixedMoment B node2123 node2123Labels = _
    exact sound2123 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1505, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h993, h1929, h1994, h2123, h2216, h4080, reducedSource1288] using sourceEq1505 B hB

theorem rowSound1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1288 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1288, numericCheck1288, reducedZero1288 B hB hF, mul_zero]

theorem reducedZero1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1289 (mixedVector B) = 0 := by
  have h1025 : mixedVector B (Sum.inr 1025) = Sparse.eval nodeValue1025 (mixedVector B) := by
    change mixedMoment B node1025 node1025Labels = _
    exact sound1025 B hB hF
  have h2011 : mixedVector B (Sum.inr 2011) = Sparse.eval nodeValue2011 (mixedVector B) := by
    change mixedMoment B node2011 node2011Labels = _
    exact sound2011 B hB hF
  have h2093 : mixedVector B (Sum.inr 2093) = Sparse.eval nodeValue2093 (mixedVector B) := by
    change mixedMoment B node2093 node2093Labels = _
    exact sound2093 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2246 : mixedVector B (Sum.inr 2246) = Sparse.eval nodeValue2246 (mixedVector B) := by
    change mixedMoment B node2246 node2246Labels = _
    exact sound2246 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1506, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1025, h2011, h2093, h2242, h2246, h4080, reducedSource1289] using sourceEq1506 B hB

theorem rowSound1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1289 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1289, numericCheck1289, reducedZero1289 B hB hF, mul_zero]

theorem reducedZero1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1290 (mixedVector B) = 0 := by
  have h973 : mixedVector B (Sum.inr 973) = Sparse.eval nodeValue973 (mixedVector B) := by
    change mixedMoment B node973 node973Labels = _
    exact sound973 B hB hF
  have h1900 : mixedVector B (Sum.inr 1900) = Sparse.eval nodeValue1900 (mixedVector B) := by
    change mixedMoment B node1900 node1900Labels = _
    exact sound1900 B hB hF
  have h2072 : mixedVector B (Sum.inr 2072) = Sparse.eval nodeValue2072 (mixedVector B) := by
    change mixedMoment B node2072 node2072Labels = _
    exact sound2072 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1507, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h973, h1900, h2072, h2190, h2192, h4080, reducedSource1290] using sourceEq1507 B hB

theorem rowSound1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1290 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1290, numericCheck1290, reducedZero1290 B hB hF, mul_zero]

theorem reducedZero1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1291 (mixedVector B) = 0 := by
  have h974 : mixedVector B (Sum.inr 974) = Sparse.eval nodeValue974 (mixedVector B) := by
    change mixedMoment B node974 node974Labels = _
    exact sound974 B hB hF
  have h1901 : mixedVector B (Sum.inr 1901) = Sparse.eval nodeValue1901 (mixedVector B) := by
    change mixedMoment B node1901 node1901Labels = _
    exact sound1901 B hB hF
  have h2073 : mixedVector B (Sum.inr 2073) = Sparse.eval nodeValue2073 (mixedVector B) := by
    change mixedMoment B node2073 node2073Labels = _
    exact sound2073 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1508, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h974, h1901, h2073, h2191, h4079, reducedSource1291] using sourceEq1508 B hB

theorem rowSound1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1291 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1291, numericCheck1291, reducedZero1291 B hB hF, mul_zero]

theorem reducedZero1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1292 (mixedVector B) = 0 := by
  have h1048 : mixedVector B (Sum.inr 1048) = Sparse.eval nodeValue1048 (mixedVector B) := by
    change mixedMoment B node1048 node1048Labels = _
    exact sound1048 B hB hF
  have h2027 : mixedVector B (Sum.inr 2027) = Sparse.eval nodeValue2027 (mixedVector B) := by
    change mixedMoment B node2027 node2027Labels = _
    exact sound2027 B hB hF
  have h2114 : mixedVector B (Sum.inr 2114) = Sparse.eval nodeValue2114 (mixedVector B) := by
    change mixedMoment B node2114 node2114Labels = _
    exact sound2114 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1509, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1048, h2027, h2114, h2261, h2267, h4081, reducedSource1292] using sourceEq1509 B hB

theorem rowSound1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1292 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1292, numericCheck1292, reducedZero1292 B hB hF, mul_zero]

theorem reducedZero1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1293 (mixedVector B) = 0 := by
  have h4154 : mixedVector B (Sum.inr 4154) = Sparse.eval nodeValue4154 (mixedVector B) := by
    change mixedMoment B node4154 node4154Labels = _
    exact sound4154 B hB hF
  have h4160 : mixedVector B (Sum.inr 4160) = Sparse.eval nodeValue4160 (mixedVector B) := by
    change mixedMoment B node4160 node4160Labels = _
    exact sound4160 B hB hF
  have h4162 : mixedVector B (Sum.inr 4162) = Sparse.eval nodeValue4162 (mixedVector B) := by
    change mixedMoment B node4162 node4162Labels = _
    exact sound4162 B hB hF
  have h4185 : mixedVector B (Sum.inr 4185) = Sparse.eval nodeValue4185 (mixedVector B) := by
    change mixedMoment B node4185 node4185Labels = _
    exact sound4185 B hB hF
  have h4328 : mixedVector B (Sum.inr 4328) = Sparse.eval nodeValue4328 (mixedVector B) := by
    change mixedMoment B node4328 node4328Labels = _
    exact sound4328 B hB hF
  have h4334 : mixedVector B (Sum.inr 4334) = Sparse.eval nodeValue4334 (mixedVector B) := by
    change mixedMoment B node4334 node4334Labels = _
    exact sound4334 B hB hF
  have h4336 : mixedVector B (Sum.inr 4336) = Sparse.eval nodeValue4336 (mixedVector B) := by
    change mixedMoment B node4336 node4336Labels = _
    exact sound4336 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4368 : mixedVector B (Sum.inr 4368) = Sparse.eval nodeValue4368 (mixedVector B) := by
    change mixedMoment B node4368 node4368Labels = _
    exact sound4368 B hB hF
  have h4373 : mixedVector B (Sum.inr 4373) = Sparse.eval nodeValue4373 (mixedVector B) := by
    change mixedMoment B node4373 node4373Labels = _
    exact sound4373 B hB hF
  have h4375 : mixedVector B (Sum.inr 4375) = Sparse.eval nodeValue4375 (mixedVector B) := by
    change mixedMoment B node4375 node4375Labels = _
    exact sound4375 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4464 : mixedVector B (Sum.inr 4464) = Sparse.eval nodeValue4464 (mixedVector B) := by
    change mixedMoment B node4464 node4464Labels = _
    exact sound4464 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  simpa only [sourceForm1510, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4154, h4160, h4162, h4185, h4328, h4334, h4336, h4354, h4368, h4373, h4375, h4457, h4459, h4460, h4464, h4498, h4503, h4810, h4874, h4894, h4896, reducedSource1293] using sourceEq1510 B hB

theorem rowSound1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1293 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1293, numericCheck1293, reducedZero1293 B hB hF, mul_zero]

theorem reducedZero1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1295 (mixedVector B) = 0 := by
  have h1511 : mixedVector B (Sum.inr 1511) = Sparse.eval nodeValue1511 (mixedVector B) := by
    change mixedMoment B node1511 node1511Labels = _
    exact sound1511 B hB hF
  have h1523 : mixedVector B (Sum.inr 1523) = Sparse.eval nodeValue1523 (mixedVector B) := by
    change mixedMoment B node1523 node1523Labels = _
    exact sound1523 B hB hF
  have h1525 : mixedVector B (Sum.inr 1525) = Sparse.eval nodeValue1525 (mixedVector B) := by
    change mixedMoment B node1525 node1525Labels = _
    exact sound1525 B hB hF
  have h1529 : mixedVector B (Sum.inr 1529) = Sparse.eval nodeValue1529 (mixedVector B) := by
    change mixedMoment B node1529 node1529Labels = _
    exact sound1529 B hB hF
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1681 : mixedVector B (Sum.inr 1681) = Sparse.eval nodeValue1681 (mixedVector B) := by
    change mixedMoment B node1681 node1681Labels = _
    exact sound1681 B hB hF
  have h1685 : mixedVector B (Sum.inr 1685) = Sparse.eval nodeValue1685 (mixedVector B) := by
    change mixedMoment B node1685 node1685Labels = _
    exact sound1685 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h1743 : mixedVector B (Sum.inr 1743) = Sparse.eval nodeValue1743 (mixedVector B) := by
    change mixedMoment B node1743 node1743Labels = _
    exact sound1743 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  simpa only [sourceForm1512, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1511, h1523, h1525, h1529, h1667, h1679, h1681, h1685, h1707, h1712, h1714, h1725, h1727, h1735, h1739, h1743, h1745, h2215, h2264, h2276, h2278, reducedSource1295] using sourceEq1512 B hB

theorem rowSound1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1295 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1295, numericCheck1295, reducedZero1295 B hB hF, mul_zero]

theorem sourceRowsAt1280 : MixedData.sourceRows (1280 : Fin 2425) =
    MixedData.row1280 := by decide +kernel

theorem sourceRowsAt1281 : MixedData.sourceRows (1281 : Fin 2425) =
    MixedData.row1281 := by decide +kernel

theorem sourceRowsAt1282 : MixedData.sourceRows (1282 : Fin 2425) =
    MixedData.row1282 := by decide +kernel

theorem sourceRowsAt1283 : MixedData.sourceRows (1283 : Fin 2425) =
    MixedData.row1283 := by decide +kernel

theorem sourceRowsAt1284 : MixedData.sourceRows (1284 : Fin 2425) =
    MixedData.row1284 := by decide +kernel

theorem sourceRowsAt1285 : MixedData.sourceRows (1285 : Fin 2425) =
    MixedData.row1285 := by decide +kernel

theorem sourceRowsAt1286 : MixedData.sourceRows (1286 : Fin 2425) =
    MixedData.row1286 := by decide +kernel

theorem sourceRowsAt1287 : MixedData.sourceRows (1287 : Fin 2425) =
    MixedData.row1287 := by decide +kernel

theorem sourceRowsAt1288 : MixedData.sourceRows (1288 : Fin 2425) =
    MixedData.row1288 := by decide +kernel

theorem sourceRowsAt1289 : MixedData.sourceRows (1289 : Fin 2425) =
    MixedData.row1289 := by decide +kernel

theorem sourceRowsAt1290 : MixedData.sourceRows (1290 : Fin 2425) =
    MixedData.row1290 := by decide +kernel

theorem sourceRowsAt1291 : MixedData.sourceRows (1291 : Fin 2425) =
    MixedData.row1291 := by decide +kernel

theorem sourceRowsAt1292 : MixedData.sourceRows (1292 : Fin 2425) =
    MixedData.row1292 := by decide +kernel

theorem sourceRowsAt1293 : MixedData.sourceRows (1293 : Fin 2425) =
    MixedData.row1293 := by decide +kernel

theorem sourceRowsAt1294 : MixedData.sourceRows (1294 : Fin 2425) =
    MixedData.row1294 := by decide +kernel

theorem sourceRowsAt1295 : MixedData.sourceRows (1295 : Fin 2425) =
    MixedData.row1295 := by decide +kernel

theorem chunkSound80_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 80) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1280 ∨ k.val = 1281 ∨ k.val = 1282 ∨ k.val = 1283 ∨ k.val = 1284 ∨ k.val = 1285 ∨ k.val = 1286 ∨ k.val = 1287 ∨ k.val = 1288 ∨ k.val = 1289 ∨ k.val = 1290 ∨ k.val = 1291 ∨ k.val = 1292 ∨ k.val = 1293 ∨ k.val = 1294 ∨ k.val = 1295 := by omega
  rcases heq with h1280 | h1281 | h1282 | h1283 | h1284 | h1285 | h1286 | h1287 | h1288 | h1289 | h1290 | h1291 | h1292 | h1293 | h1294 | h1295
  · have he : k = (1280 : Fin 2425) := Fin.ext h1280
    subst k
    rw [sourceRowsAt1280]
    exact rowSound1280 B hB hF
  · have he : k = (1281 : Fin 2425) := Fin.ext h1281
    subst k
    rw [sourceRowsAt1281]
    exact rowSound1281 B hB hF
  · have he : k = (1282 : Fin 2425) := Fin.ext h1282
    subst k
    rw [sourceRowsAt1282]
    exact rowSound1282 B hB hF
  · have he : k = (1283 : Fin 2425) := Fin.ext h1283
    subst k
    rw [sourceRowsAt1283]
    exact rowSound1283 B hB hF
  · have he : k = (1284 : Fin 2425) := Fin.ext h1284
    subst k
    rw [sourceRowsAt1284]
    exact rowSound1284 B hB hF
  · have he : k = (1285 : Fin 2425) := Fin.ext h1285
    subst k
    rw [sourceRowsAt1285]
    exact rowSound1285 B hB hF
  · have he : k = (1286 : Fin 2425) := Fin.ext h1286
    subst k
    rw [sourceRowsAt1286]
    exact rowSound1286 B hB hF
  · have he : k = (1287 : Fin 2425) := Fin.ext h1287
    subst k
    rw [sourceRowsAt1287]
    exact rowSound1287 B hB hF
  · have he : k = (1288 : Fin 2425) := Fin.ext h1288
    subst k
    rw [sourceRowsAt1288]
    exact rowSound1288 B hB hF
  · have he : k = (1289 : Fin 2425) := Fin.ext h1289
    subst k
    rw [sourceRowsAt1289]
    exact rowSound1289 B hB hF
  · have he : k = (1290 : Fin 2425) := Fin.ext h1290
    subst k
    rw [sourceRowsAt1290]
    exact rowSound1290 B hB hF
  · have he : k = (1291 : Fin 2425) := Fin.ext h1291
    subst k
    rw [sourceRowsAt1291]
    exact rowSound1291 B hB hF
  · have he : k = (1292 : Fin 2425) := Fin.ext h1292
    subst k
    rw [sourceRowsAt1292]
    exact rowSound1292 B hB hF
  · have he : k = (1293 : Fin 2425) := Fin.ext h1293
    subst k
    rw [sourceRowsAt1293]
    exact rowSound1293 B hB hF
  · have he : k = (1294 : Fin 2425) := Fin.ext h1294
    subst k
    rw [sourceRowsAt1294]
    exact rowSound1294_e B hB hF
  · have he : k = (1295 : Fin 2425) := Fin.ext h1295
    subst k
    rw [sourceRowsAt1295]
    exact rowSound1295 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e_oai
