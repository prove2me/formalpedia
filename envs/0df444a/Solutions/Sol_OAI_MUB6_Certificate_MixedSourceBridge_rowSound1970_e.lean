-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:29:44.352338+00:00
-- url     : https://prove2.me/submissions/32161107-05ee-43fa-a78d-e679cb117c3d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5169_e

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

theorem canonical1281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1281 raw1281Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw1281 raw1281Labels = mixedMoment B raw1281step0 raw1281step0Labels := by
      have ha : raw1281step0 = (fun i j => raw1281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1281step0 raw1281; decide +kernel
      have hl : raw1281step0Labels = raw1281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1281 raw1281Labels permutation32 permutation4
    mixedMoment B raw1281step0 raw1281step0Labels = mixedMoment B raw1281step1 raw1281step1Labels := by
      have ha : raw1281step1 = raw1281step0 := by apply Matrix.ext; unfold raw1281step1 raw1281step0; decide +kernel
      have hl : raw1281step0Labels = labelEmbedding7 ∘ raw1281step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1281step0 raw1281step0Labels raw1281step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

theorem canonical1282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1282 raw1282Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw1282 raw1282Labels = mixedMoment B raw1282step0 raw1282step0Labels := by
      have ha : raw1282step0 = (fun i j => raw1282 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1282step0 raw1282; decide +kernel
      have hl : raw1282step0Labels = raw1282Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1282 raw1282Labels permutation32 permutation4
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical1283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1283 raw1283Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw1283 raw1283Labels = mixedMoment B raw1283step0 raw1283step0Labels := by
      have ha : raw1283step0 = (fun i j => raw1283 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1283step0 raw1283; decide +kernel
      have hl : raw1283step0Labels = raw1283Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1283 raw1283Labels permutation32 permutation6
    mixedMoment B raw1283step0 raw1283step0Labels = mixedMoment B raw1283step1 raw1283step1Labels := by
      have ha : raw1283step1 = -raw1283step0 := by apply Matrix.ext; change ∀ i j, raw1283step1 i j = -(raw1283step0 i j); unfold raw1283step1 raw1283step0; decide +kernel
      have hl : raw1283step1Labels = raw1283step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1283step1 raw1283step1Labels = mixedMoment B raw1283step2 raw1283step2Labels := by
      have ha : raw1283step2 = raw1283step1 := by apply Matrix.ext; unfold raw1283step2 raw1283step1; decide +kernel
      have hl : raw1283step1Labels = labelEmbedding1 ∘ raw1283step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1283step1 raw1283step1Labels raw1283step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1648 node1648Labels := by rfl

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

theorem canonical1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1725 raw1725Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw1725 raw1725Labels = mixedMoment B raw1725step0 raw1725step0Labels := by
      have ha : raw1725step0 = (fun i j => raw1725 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1725step0 raw1725; decide +kernel
      have hl : raw1725step0Labels = raw1725Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1725 raw1725Labels permutation152 permutation4
    mixedMoment B raw1725step0 raw1725step0Labels = mixedMoment B raw1725step1 raw1725step1Labels := by
      have ha : raw1725step1 = raw1725step0 := by apply Matrix.ext; unfold raw1725step1 raw1725step0; decide +kernel
      have hl : raw1725step0Labels = labelEmbedding7 ∘ raw1725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1725step0 raw1725step0Labels raw1725step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1726 raw1726Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw1726 raw1726Labels = mixedMoment B raw1726step0 raw1726step0Labels := by
      have ha : raw1726step0 = (fun i j => raw1726 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1726step0 raw1726; decide +kernel
      have hl : raw1726step0Labels = raw1726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1726 raw1726Labels permutation152 permutation4
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1727 raw1727Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw1727 raw1727Labels = mixedMoment B raw1727step0 raw1727step0Labels := by
      have ha : raw1727step0 = (fun i j => raw1727 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1727step0 raw1727; decide +kernel
      have hl : raw1727step0Labels = raw1727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1727 raw1727Labels permutation200 permutation6
    mixedMoment B raw1727step0 raw1727step0Labels = mixedMoment B raw1727step1 raw1727step1Labels := by
      have ha : raw1727step1 = -raw1727step0 := by apply Matrix.ext; change ∀ i j, raw1727step1 i j = -(raw1727step0 i j); unfold raw1727step1 raw1727step0; decide +kernel
      have hl : raw1727step1Labels = raw1727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1727step1 raw1727step1Labels = mixedMoment B raw1727step2 raw1727step2Labels := by
      have ha : raw1727step2 = raw1727step1 := by apply Matrix.ext; unfold raw1727step2 raw1727step1; decide +kernel
      have hl : raw1727step1Labels = labelEmbedding1 ∘ raw1727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1727step1 raw1727step1Labels raw1727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2075 node2075Labels := by rfl

theorem canonical1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1734 raw1734Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw1734 raw1734Labels = mixedMoment B raw1734step0 raw1734step0Labels := by
      have ha : raw1734step0 = (fun i j => raw1734 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1734step0 raw1734; decide +kernel
      have hl : raw1734step0Labels = raw1734Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1734 raw1734Labels permutation152 permutation4
    mixedMoment B raw1734step0 raw1734step0Labels = mixedMoment B raw1734step1 raw1734step1Labels := by
      have ha : raw1734step1 = raw1734step0 := by apply Matrix.ext; unfold raw1734step1 raw1734step0; decide +kernel
      have hl : raw1734step0Labels = labelEmbedding7 ∘ raw1734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1734step0 raw1734step0Labels raw1734step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1735 raw1735Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw1735 raw1735Labels = mixedMoment B raw1735step0 raw1735step0Labels := by
      have ha : raw1735step0 = (fun i j => raw1735 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1735step0 raw1735; decide +kernel
      have hl : raw1735step0Labels = raw1735Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1735 raw1735Labels permutation152 permutation4
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1736 raw1736Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw1736 raw1736Labels = mixedMoment B raw1736step0 raw1736step0Labels := by
      have ha : raw1736step0 = (fun i j => raw1736 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1736step0 raw1736; decide +kernel
      have hl : raw1736step0Labels = raw1736Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1736 raw1736Labels permutation158 permutation6
    mixedMoment B raw1736step0 raw1736step0Labels = mixedMoment B raw1736step1 raw1736step1Labels := by
      have ha : raw1736step1 = -raw1736step0 := by apply Matrix.ext; change ∀ i j, raw1736step1 i j = -(raw1736step0 i j); unfold raw1736step1 raw1736step0; decide +kernel
      have hl : raw1736step1Labels = raw1736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1736step1 raw1736step1Labels = mixedMoment B raw1736step2 raw1736step2Labels := by
      have ha : raw1736step2 = raw1736step1 := by apply Matrix.ext; unfold raw1736step2 raw1736step1; decide +kernel
      have hl : raw1736step1Labels = labelEmbedding1 ∘ raw1736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1736step1 raw1736step1Labels raw1736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1752 raw1752Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw1752 raw1752Labels = mixedMoment B raw1752step0 raw1752step0Labels := by
      have ha : raw1752step0 = (fun i j => raw1752 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1752step0 raw1752; decide +kernel
      have hl : raw1752step0Labels = raw1752Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1752 raw1752Labels permutation152 permutation4
    mixedMoment B raw1752step0 raw1752step0Labels = mixedMoment B raw1752step1 raw1752step1Labels := by
      have ha : raw1752step1 = raw1752step0 := by apply Matrix.ext; unfold raw1752step1 raw1752step0; decide +kernel
      have hl : raw1752step0Labels = labelEmbedding7 ∘ raw1752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1752step0 raw1752step0Labels raw1752step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1753 raw1753Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw1753 raw1753Labels = mixedMoment B raw1753step0 raw1753step0Labels := by
      have ha : raw1753step0 = (fun i j => raw1753 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1753step0 raw1753; decide +kernel
      have hl : raw1753step0Labels = raw1753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1753 raw1753Labels permutation152 permutation4
    _ = mixedMoment B node2046 node2046Labels := by rfl

theorem canonical1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1754 raw1754Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw1754 raw1754Labels = mixedMoment B raw1754step0 raw1754step0Labels := by
      have ha : raw1754step0 = (fun i j => raw1754 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1754step0 raw1754; decide +kernel
      have hl : raw1754step0Labels = raw1754Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1754 raw1754Labels permutation176 permutation6
    mixedMoment B raw1754step0 raw1754step0Labels = mixedMoment B raw1754step1 raw1754step1Labels := by
      have ha : raw1754step1 = -raw1754step0 := by apply Matrix.ext; change ∀ i j, raw1754step1 i j = -(raw1754step0 i j); unfold raw1754step1 raw1754step0; decide +kernel
      have hl : raw1754step1Labels = raw1754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1754step1 raw1754step1Labels = mixedMoment B raw1754step2 raw1754step2Labels := by
      have ha : raw1754step2 = raw1754step1 := by apply Matrix.ext; unfold raw1754step2 raw1754step1; decide +kernel
      have hl : raw1754step1Labels = labelEmbedding1 ∘ raw1754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1754step1 raw1754step1Labels raw1754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2077 node2077Labels := by rfl

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

theorem canonical1782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1782 raw1782Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw1782 raw1782Labels = mixedMoment B raw1782step0 raw1782step0Labels := by
      have ha : raw1782step0 = (fun i j => raw1782 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1782step0 raw1782; decide +kernel
      have hl : raw1782step0Labels = raw1782Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1782 raw1782Labels permutation32 permutation4
    mixedMoment B raw1782step0 raw1782step0Labels = mixedMoment B raw1782step1 raw1782step1Labels := by
      have ha : raw1782step1 = raw1782step0 := by apply Matrix.ext; unfold raw1782step1 raw1782step0; decide +kernel
      have hl : raw1782step0Labels = labelEmbedding7 ∘ raw1782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1782step0 raw1782step0Labels raw1782step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

theorem canonical1783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1783 raw1783Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw1783 raw1783Labels = mixedMoment B raw1783step0 raw1783step0Labels := by
      have ha : raw1783step0 = (fun i j => raw1783 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1783step0 raw1783; decide +kernel
      have hl : raw1783step0Labels = raw1783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1783 raw1783Labels permutation32 permutation4
    _ = mixedMoment B node2101 node2101Labels := by rfl

theorem canonical1784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1784 raw1784Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw1784 raw1784Labels = mixedMoment B raw1784step0 raw1784step0Labels := by
      have ha : raw1784step0 = (fun i j => raw1784 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1784step0 raw1784; decide +kernel
      have hl : raw1784step0Labels = raw1784Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1784 raw1784Labels permutation38 permutation6
    mixedMoment B raw1784step0 raw1784step0Labels = mixedMoment B raw1784step1 raw1784step1Labels := by
      have ha : raw1784step1 = -raw1784step0 := by apply Matrix.ext; change ∀ i j, raw1784step1 i j = -(raw1784step0 i j); unfold raw1784step1 raw1784step0; decide +kernel
      have hl : raw1784step1Labels = raw1784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1784step1 raw1784step1Labels = mixedMoment B raw1784step2 raw1784step2Labels := by
      have ha : raw1784step2 = raw1784step1 := by apply Matrix.ext; unfold raw1784step2 raw1784step1; decide +kernel
      have hl : raw1784step1Labels = labelEmbedding1 ∘ raw1784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1784step1 raw1784step1Labels raw1784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2101 node2101Labels := by rfl

theorem canonical1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1791 raw1791Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw1791 raw1791Labels = mixedMoment B raw1791step0 raw1791step0Labels := by
      have ha : raw1791step0 = (fun i j => raw1791 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1791step0 raw1791; decide +kernel
      have hl : raw1791step0Labels = raw1791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1791 raw1791Labels permutation32 permutation4
    mixedMoment B raw1791step0 raw1791step0Labels = mixedMoment B raw1791step1 raw1791step1Labels := by
      have ha : raw1791step1 = raw1791step0 := by apply Matrix.ext; unfold raw1791step1 raw1791step0; decide +kernel
      have hl : raw1791step0Labels = labelEmbedding7 ∘ raw1791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1791step0 raw1791step0Labels raw1791step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

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

theorem canonical1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1792 raw1792Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw1792 raw1792Labels = mixedMoment B raw1792step0 raw1792step0Labels := by
      have ha : raw1792step0 = (fun i j => raw1792 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1792step0 raw1792; decide +kernel
      have hl : raw1792step0Labels = raw1792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1792 raw1792Labels permutation32 permutation4
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1793 raw1793Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw1793 raw1793Labels = mixedMoment B raw1793step0 raw1793step0Labels := by
      have ha : raw1793step0 = (fun i j => raw1793 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1793step0 raw1793; decide +kernel
      have hl : raw1793step0Labels = raw1793Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1793 raw1793Labels permutation40 permutation6
    mixedMoment B raw1793step0 raw1793step0Labels = mixedMoment B raw1793step1 raw1793step1Labels := by
      have ha : raw1793step1 = -raw1793step0 := by apply Matrix.ext; change ∀ i j, raw1793step1 i j = -(raw1793step0 i j); unfold raw1793step1 raw1793step0; decide +kernel
      have hl : raw1793step1Labels = raw1793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1793step1 raw1793step1Labels = mixedMoment B raw1793step2 raw1793step2Labels := by
      have ha : raw1793step2 = raw1793step1 := by apply Matrix.ext; unfold raw1793step2 raw1793step1; decide +kernel
      have hl : raw1793step1Labels = labelEmbedding1 ∘ raw1793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1793step1 raw1793step1Labels raw1793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1794 raw1794Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw1794 raw1794Labels = mixedMoment B raw1794step0 raw1794step0Labels := by
      have ha : raw1794step0 = (fun i j => raw1794 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1794step0 raw1794; decide +kernel
      have hl : raw1794step0Labels = raw1794Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1794 raw1794Labels permutation32 permutation4
    mixedMoment B raw1794step0 raw1794step0Labels = mixedMoment B raw1794step1 raw1794step1Labels := by
      have ha : raw1794step1 = raw1794step0 := by apply Matrix.ext; unfold raw1794step1 raw1794step0; decide +kernel
      have hl : raw1794step0Labels = labelEmbedding7 ∘ raw1794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1794step0 raw1794step0Labels raw1794step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1795 raw1795Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw1795 raw1795Labels = mixedMoment B raw1795step0 raw1795step0Labels := by
      have ha : raw1795step0 = (fun i j => raw1795 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1795step0 raw1795; decide +kernel
      have hl : raw1795step0Labels = raw1795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1795 raw1795Labels permutation32 permutation4
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1796 raw1796Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw1796 raw1796Labels = mixedMoment B raw1796step0 raw1796step0Labels := by
      have ha : raw1796step0 = (fun i j => raw1796 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1796step0 raw1796; decide +kernel
      have hl : raw1796step0Labels = raw1796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1796 raw1796Labels permutation38 permutation6
    mixedMoment B raw1796step0 raw1796step0Labels = mixedMoment B raw1796step1 raw1796step1Labels := by
      have ha : raw1796step1 = -raw1796step0 := by apply Matrix.ext; change ∀ i j, raw1796step1 i j = -(raw1796step0 i j); unfold raw1796step1 raw1796step0; decide +kernel
      have hl : raw1796step1Labels = raw1796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1796step1 raw1796step1Labels = mixedMoment B raw1796step2 raw1796step2Labels := by
      have ha : raw1796step2 = raw1796step1 := by apply Matrix.ext; unfold raw1796step2 raw1796step1; decide +kernel
      have hl : raw1796step1Labels = labelEmbedding1 ∘ raw1796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1796step1 raw1796step1Labels raw1796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical1800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1800 raw1800Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw1800 raw1800Labels = mixedMoment B raw1800step0 raw1800step0Labels := by
      have ha : raw1800step0 = (fun i j => raw1800 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1800step0 raw1800; decide +kernel
      have hl : raw1800step0Labels = raw1800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1800 raw1800Labels permutation32 permutation4
    mixedMoment B raw1800step0 raw1800step0Labels = mixedMoment B raw1800step1 raw1800step1Labels := by
      have ha : raw1800step1 = raw1800step0 := by apply Matrix.ext; unfold raw1800step1 raw1800step0; decide +kernel
      have hl : raw1800step0Labels = labelEmbedding7 ∘ raw1800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1800step0 raw1800step0Labels raw1800step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1801 raw1801Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw1801 raw1801Labels = mixedMoment B raw1801step0 raw1801step0Labels := by
      have ha : raw1801step0 = (fun i j => raw1801 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1801step0 raw1801; decide +kernel
      have hl : raw1801step0Labels = raw1801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1801 raw1801Labels permutation32 permutation4
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1802 raw1802Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw1802 raw1802Labels = mixedMoment B raw1802step0 raw1802step0Labels := by
      have ha : raw1802step0 = (fun i j => raw1802 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1802step0 raw1802; decide +kernel
      have hl : raw1802step0Labels = raw1802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1802 raw1802Labels permutation50 permutation6
    mixedMoment B raw1802step0 raw1802step0Labels = mixedMoment B raw1802step1 raw1802step1Labels := by
      have ha : raw1802step1 = -raw1802step0 := by apply Matrix.ext; change ∀ i j, raw1802step1 i j = -(raw1802step0 i j); unfold raw1802step1 raw1802step0; decide +kernel
      have hl : raw1802step1Labels = raw1802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1802step1 raw1802step1Labels = mixedMoment B raw1802step2 raw1802step2Labels := by
      have ha : raw1802step2 = raw1802step1 := by apply Matrix.ext; unfold raw1802step2 raw1802step1; decide +kernel
      have hl : raw1802step1Labels = labelEmbedding1 ∘ raw1802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1802step1 raw1802step1Labels raw1802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

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

theorem canonical2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2232 raw2232Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw2232 raw2232Labels = mixedMoment B raw2232step0 raw2232step0Labels := by
      have ha : raw2232step0 = (fun i j => raw2232 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2232step0 raw2232; decide +kernel
      have hl : raw2232step0Labels = raw2232Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2232 raw2232Labels permutation32 permutation5
    mixedMoment B raw2232step0 raw2232step0Labels = mixedMoment B raw2232step1 raw2232step1Labels := by
      have ha : raw2232step1 = raw2232step0 := by apply Matrix.ext; unfold raw2232step1 raw2232step0; decide +kernel
      have hl : raw2232step0Labels = labelEmbedding8 ∘ raw2232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2232step0 raw2232step0Labels raw2232step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical2233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2233 raw2233Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw2233 raw2233Labels = mixedMoment B raw2233step0 raw2233step0Labels := by
      have ha : raw2233step0 = (fun i j => raw2233 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2233step0 raw2233; decide +kernel
      have hl : raw2233step0Labels = raw2233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2233 raw2233Labels permutation34 permutation4
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2234 raw2234Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw2234 raw2234Labels = mixedMoment B raw2234step0 raw2234step0Labels := by
      have ha : raw2234step0 = (fun i j => raw2234 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2234step0 raw2234; decide +kernel
      have hl : raw2234step0Labels = raw2234Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2234 raw2234Labels permutation42 permutation3
    mixedMoment B raw2234step0 raw2234step0Labels = mixedMoment B raw2234step1 raw2234step1Labels := by
      have ha : raw2234step1 = -raw2234step0 := by apply Matrix.ext; change ∀ i j, raw2234step1 i j = -(raw2234step0 i j); unfold raw2234step1 raw2234step0; decide +kernel
      have hl : raw2234step1Labels = raw2234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2234step1 raw2234step1Labels = mixedMoment B raw2234step2 raw2234step2Labels := by
      have ha : raw2234step2 = raw2234step1 := by apply Matrix.ext; unfold raw2234step2 raw2234step1; decide +kernel
      have hl : raw2234step1Labels = labelEmbedding1 ∘ raw2234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2234step1 raw2234step1Labels raw2234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32230 raw32230Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw32230 raw32230Labels = mixedMoment B raw32230step0 raw32230step0Labels := by
      have hz : ∀ j, raw32230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32230step0 = (fun i j => raw32230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32230step0 raw32230; decide +kernel
      have hl : raw32230step0Labels = raw32230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32230 raw32230Labels permutation346 hz
    mixedMoment B raw32230step0 raw32230step0Labels = mixedMoment B raw32230step1 raw32230step1Labels := by
      have ha : raw32230step1 = (fun i j => raw32230step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32230step1 raw32230step0; decide +kernel
      have hl : raw32230step1Labels = raw32230step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32230step0 raw32230step0Labels permutation32 permutation6
    mixedMoment B raw32230step1 raw32230step1Labels = mixedMoment B raw32230step2 raw32230step2Labels := by
      have ha : raw32230step2 = raw32230step1 := by apply Matrix.ext; unfold raw32230step2 raw32230step1; decide +kernel
      have hl : raw32230step1Labels = labelEmbedding9 ∘ raw32230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32230step1 raw32230step1Labels raw32230step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical32233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32233 raw32233Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32233 raw32233Labels = mixedMoment B raw32233step0 raw32233step0Labels := by
      have hz : ∀ j, raw32233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32233step0 = (fun i j => raw32233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32233step0 raw32233; decide +kernel
      have hl : raw32233step0Labels = raw32233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32233 raw32233Labels permutation346 hz
    mixedMoment B raw32233step0 raw32233step0Labels = mixedMoment B raw32233step1 raw32233step1Labels := by
      have ha : raw32233step1 = (fun i j => raw32233step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32233step1 raw32233step0; decide +kernel
      have hl : raw32233step1Labels = raw32233step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32233step0 raw32233step0Labels permutation34 permutation6
    mixedMoment B raw32233step1 raw32233step1Labels = mixedMoment B raw32233step2 raw32233step2Labels := by
      have ha : raw32233step2 = raw32233step1 := by apply Matrix.ext; unfold raw32233step2 raw32233step1; decide +kernel
      have hl : raw32233step1Labels = labelEmbedding9 ∘ raw32233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32233step1 raw32233step1Labels raw32233step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical32250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32250 raw32250Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw32250 raw32250Labels = mixedMoment B raw32250step0 raw32250step0Labels := by
      have hz : ∀ j, raw32250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32250step0 = (fun i j => raw32250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32250step0 raw32250; decide +kernel
      have hl : raw32250step0Labels = raw32250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32250 raw32250Labels permutation346 hz
    mixedMoment B raw32250step0 raw32250step0Labels = mixedMoment B raw32250step1 raw32250step1Labels := by
      have ha : raw32250step1 = (fun i j => raw32250step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32250step1 raw32250step0; decide +kernel
      have hl : raw32250step1Labels = raw32250step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32250step0 raw32250step0Labels permutation32 permutation6
    mixedMoment B raw32250step1 raw32250step1Labels = mixedMoment B raw32250step2 raw32250step2Labels := by
      have ha : raw32250step2 = raw32250step1 := by apply Matrix.ext; unfold raw32250step2 raw32250step1; decide +kernel
      have hl : raw32250step1Labels = labelEmbedding9 ∘ raw32250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32250step1 raw32250step1Labels raw32250step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical32254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32254 raw32254Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32254 raw32254Labels = mixedMoment B raw32254step0 raw32254step0Labels := by
      have hz : ∀ j, raw32254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32254step0 = (fun i j => raw32254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32254step0 raw32254; decide +kernel
      have hl : raw32254step0Labels = raw32254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32254 raw32254Labels permutation346 hz
    mixedMoment B raw32254step0 raw32254step0Labels = mixedMoment B raw32254step1 raw32254step1Labels := by
      have ha : raw32254step1 = (fun i j => raw32254step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32254step1 raw32254step0; decide +kernel
      have hl : raw32254step1Labels = raw32254step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32254step0 raw32254step0Labels permutation34 permutation6
    mixedMoment B raw32254step1 raw32254step1Labels = mixedMoment B raw32254step2 raw32254step2Labels := by
      have ha : raw32254step2 = raw32254step1 := by apply Matrix.ext; unfold raw32254step2 raw32254step1; decide +kernel
      have hl : raw32254step1Labels = labelEmbedding9 ∘ raw32254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32254step1 raw32254step1Labels raw32254step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32317 raw32317Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw32317 raw32317Labels = mixedMoment B raw32317step0 raw32317step0Labels := by
      have ha : raw32317step0 = (fun i j => raw32317 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32317step0 raw32317; decide +kernel
      have hl : raw32317step0Labels = raw32317Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32317 raw32317Labels permutation152 permutation6
    mixedMoment B raw32317step0 raw32317step0Labels = mixedMoment B raw32317step1 raw32317step1Labels := by
      have ha : raw32317step1 = raw32317step0 := by apply Matrix.ext; unfold raw32317step1 raw32317step0; decide +kernel
      have hl : raw32317step0Labels = labelEmbedding9 ∘ raw32317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32317step0 raw32317step0Labels raw32317step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical32318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32318 raw32318Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32318 raw32318Labels = mixedMoment B raw32318step0 raw32318step0Labels := by
      have hz : ∀ j, raw32318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32318step0 = (fun i j => raw32318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32318step0 raw32318; decide +kernel
      have hl : raw32318step0Labels = raw32318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32318 raw32318Labels permutation346 hz
    mixedMoment B raw32318step0 raw32318step0Labels = mixedMoment B raw32318step1 raw32318step1Labels := by
      have ha : raw32318step1 = (fun i j => raw32318step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32318step1 raw32318step0; decide +kernel
      have hl : raw32318step1Labels = raw32318step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32318step0 raw32318step0Labels permutation32 permutation6
    mixedMoment B raw32318step1 raw32318step1Labels = mixedMoment B raw32318step2 raw32318step2Labels := by
      have ha : raw32318step2 = raw32318step1 := by apply Matrix.ext; unfold raw32318step2 raw32318step1; decide +kernel
      have hl : raw32318step1Labels = labelEmbedding9 ∘ raw32318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32318step1 raw32318step1Labels raw32318step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical32327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32327 raw32327Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw32327 raw32327Labels = mixedMoment B raw32327step0 raw32327step0Labels := by
      have ha : raw32327step0 = (fun i j => raw32327 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32327step0 raw32327; decide +kernel
      have hl : raw32327step0Labels = raw32327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32327 raw32327Labels permutation154 permutation6
    mixedMoment B raw32327step0 raw32327step0Labels = mixedMoment B raw32327step1 raw32327step1Labels := by
      have ha : raw32327step1 = raw32327step0 := by apply Matrix.ext; unfold raw32327step1 raw32327step0; decide +kernel
      have hl : raw32327step0Labels = labelEmbedding9 ∘ raw32327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32327step0 raw32327step0Labels raw32327step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32822 raw32822Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw32822 raw32822Labels = mixedMoment B raw32822step0 raw32822step0Labels := by
      have hz : ∀ j, raw32822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32822step0 = (fun i j => raw32822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32822step0 raw32822; decide +kernel
      have hl : raw32822step0Labels = raw32822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32822 raw32822Labels permutation346 hz
    mixedMoment B raw32822step0 raw32822step0Labels = mixedMoment B raw32822step1 raw32822step1Labels := by
      have ha : raw32822step1 = (fun i j => raw32822step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32822step1 raw32822step0; decide +kernel
      have hl : raw32822step1Labels = raw32822step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32822step0 raw32822step0Labels permutation44 permutation4
    mixedMoment B raw32822step1 raw32822step1Labels = mixedMoment B raw32822step2 raw32822step2Labels := by
      have ha : raw32822step2 = -raw32822step1 := by apply Matrix.ext; change ∀ i j, raw32822step2 i j = -(raw32822step1 i j); unfold raw32822step2 raw32822step1; decide +kernel
      have hl : raw32822step2Labels = raw32822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32822step2 raw32822step2Labels = mixedMoment B raw32822step3 raw32822step3Labels := by
      have ha : raw32822step3 = raw32822step2 := by apply Matrix.ext; unfold raw32822step3 raw32822step2; decide +kernel
      have hl : raw32822step2Labels = labelEmbedding7 ∘ raw32822step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32822step2 raw32822step2Labels raw32822step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

theorem canonical32826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32826 raw32826Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw32826 raw32826Labels = mixedMoment B raw32826step0 raw32826step0Labels := by
      have hz : ∀ j, raw32826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32826step0 = (fun i j => raw32826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32826step0 raw32826; decide +kernel
      have hl : raw32826step0Labels = raw32826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32826 raw32826Labels permutation346 hz
    mixedMoment B raw32826step0 raw32826step0Labels = mixedMoment B raw32826step1 raw32826step1Labels := by
      have ha : raw32826step1 = (fun i j => raw32826step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32826step1 raw32826step0; decide +kernel
      have hl : raw32826step1Labels = raw32826step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32826step0 raw32826step0Labels permutation34 permutation6
    mixedMoment B raw32826step1 raw32826step1Labels = mixedMoment B raw32826step2 raw32826step2Labels := by
      have ha : raw32826step2 = raw32826step1 := by apply Matrix.ext; unfold raw32826step2 raw32826step1; decide +kernel
      have hl : raw32826step1Labels = labelEmbedding9 ∘ raw32826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32826step1 raw32826step1Labels raw32826step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

theorem canonical32835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32835 raw32835Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw32835 raw32835Labels = mixedMoment B raw32835step0 raw32835step0Labels := by
      have hz : ∀ j, raw32835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32835step0 = (fun i j => raw32835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32835step0 raw32835; decide +kernel
      have hl : raw32835step0Labels = raw32835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32835 raw32835Labels permutation346 hz
    mixedMoment B raw32835step0 raw32835step0Labels = mixedMoment B raw32835step1 raw32835step1Labels := by
      have ha : raw32835step1 = (fun i j => raw32835step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32835step1 raw32835step0; decide +kernel
      have hl : raw32835step1Labels = raw32835step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32835step0 raw32835step0Labels permutation34 permutation6
    mixedMoment B raw32835step1 raw32835step1Labels = mixedMoment B raw32835step2 raw32835step2Labels := by
      have ha : raw32835step2 = raw32835step1 := by apply Matrix.ext; unfold raw32835step2 raw32835step1; decide +kernel
      have hl : raw32835step1Labels = labelEmbedding9 ∘ raw32835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32835step1 raw32835step1Labels raw32835step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32902 raw32902Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw32902 raw32902Labels = mixedMoment B raw32902step0 raw32902step0Labels := by
      have ha : raw32902step0 = (fun i j => raw32902 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32902step0 raw32902; decide +kernel
      have hl : raw32902step0Labels = raw32902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32902 raw32902Labels permutation176 permutation4
    mixedMoment B raw32902step0 raw32902step0Labels = mixedMoment B raw32902step1 raw32902step1Labels := by
      have ha : raw32902step1 = -raw32902step0 := by apply Matrix.ext; change ∀ i j, raw32902step1 i j = -(raw32902step0 i j); unfold raw32902step1 raw32902step0; decide +kernel
      have hl : raw32902step1Labels = raw32902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32902step1 raw32902step1Labels = mixedMoment B raw32902step2 raw32902step2Labels := by
      have ha : raw32902step2 = raw32902step1 := by apply Matrix.ext; unfold raw32902step2 raw32902step1; decide +kernel
      have hl : raw32902step1Labels = labelEmbedding7 ∘ raw32902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32902step1 raw32902step1Labels raw32902step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical32905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32905 raw32905Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw32905 raw32905Labels = mixedMoment B raw32905step0 raw32905step0Labels := by
      have ha : raw32905step0 = (fun i j => raw32905 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32905step0 raw32905; decide +kernel
      have hl : raw32905step0Labels = raw32905Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32905 raw32905Labels permutation154 permutation6
    mixedMoment B raw32905step0 raw32905step0Labels = mixedMoment B raw32905step1 raw32905step1Labels := by
      have ha : raw32905step1 = raw32905step0 := by apply Matrix.ext; unfold raw32905step1 raw32905step0; decide +kernel
      have hl : raw32905step0Labels = labelEmbedding9 ∘ raw32905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32905step0 raw32905step0Labels raw32905step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical32999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32999 raw32999Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw32999 raw32999Labels = mixedMoment B raw32999step0 raw32999step0Labels := by
      have ha : raw32999step0 = (fun i j => raw32999 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32999step0 raw32999; decide +kernel
      have hl : raw32999step0Labels = raw32999Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32999 raw32999Labels permutation188 permutation4
    mixedMoment B raw32999step0 raw32999step0Labels = mixedMoment B raw32999step1 raw32999step1Labels := by
      have ha : raw32999step1 = -raw32999step0 := by apply Matrix.ext; change ∀ i j, raw32999step1 i j = -(raw32999step0 i j); unfold raw32999step1 raw32999step0; decide +kernel
      have hl : raw32999step1Labels = raw32999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32999step1 raw32999step1Labels = mixedMoment B raw32999step2 raw32999step2Labels := by
      have ha : raw32999step2 = raw32999step1 := by apply Matrix.ext; unfold raw32999step2 raw32999step1; decide +kernel
      have hl : raw32999step1Labels = labelEmbedding7 ∘ raw32999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32999step1 raw32999step1Labels raw32999step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical262
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33553 raw33553Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw33553 raw33553Labels = mixedMoment B raw33553step0 raw33553step0Labels := by
      have hz : ∀ j, raw33553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33553step0 = (fun i j => raw33553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33553step0 raw33553; decide +kernel
      have hl : raw33553step0Labels = raw33553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33553 raw33553Labels permutation346 hz
    mixedMoment B raw33553step0 raw33553step0Labels = mixedMoment B raw33553step1 raw33553step1Labels := by
      have ha : raw33553step1 = (fun i j => raw33553step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33553step1 raw33553step0; decide +kernel
      have hl : raw33553step1Labels = raw33553step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33553step0 raw33553step0Labels permutation34 permutation6
    mixedMoment B raw33553step1 raw33553step1Labels = mixedMoment B raw33553step2 raw33553step2Labels := by
      have ha : raw33553step2 = raw33553step1 := by apply Matrix.ext; unfold raw33553step2 raw33553step1; decide +kernel
      have hl : raw33553step1Labels = labelEmbedding9 ∘ raw33553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33553step1 raw33553step1Labels raw33553step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

theorem canonical33556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33556 raw33556Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw33556 raw33556Labels = mixedMoment B raw33556step0 raw33556step0Labels := by
      have ha : raw33556step0 = (fun i j => raw33556 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33556step0 raw33556; decide +kernel
      have hl : raw33556step0Labels = raw33556Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33556 raw33556Labels permutation154 permutation6
    mixedMoment B raw33556step0 raw33556step0Labels = mixedMoment B raw33556step1 raw33556step1Labels := by
      have ha : raw33556step1 = raw33556step0 := by apply Matrix.ext; unfold raw33556step1 raw33556step0; decide +kernel
      have hl : raw33556step0Labels = labelEmbedding9 ∘ raw33556step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33556step0 raw33556step0Labels raw33556step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical33560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33560 raw33560Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw33560 raw33560Labels = mixedMoment B raw33560step0 raw33560step0Labels := by
      have hz : ∀ j, raw33560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33560step0 = (fun i j => raw33560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33560step0 raw33560; decide +kernel
      have hl : raw33560step0Labels = raw33560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33560 raw33560Labels permutation346 hz
    mixedMoment B raw33560step0 raw33560step0Labels = mixedMoment B raw33560step1 raw33560step1Labels := by
      have ha : raw33560step1 = (fun i j => raw33560step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33560step1 raw33560step0; decide +kernel
      have hl : raw33560step1Labels = raw33560step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33560step0 raw33560step0Labels permutation34 permutation6
    mixedMoment B raw33560step1 raw33560step1Labels = mixedMoment B raw33560step2 raw33560step2Labels := by
      have ha : raw33560step2 = raw33560step1 := by apply Matrix.ext; unfold raw33560step2 raw33560step1; decide +kernel
      have hl : raw33560step1Labels = labelEmbedding9 ∘ raw33560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33560step1 raw33560step1Labels raw33560step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

theorem canonical33566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33566 raw33566Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw33566 raw33566Labels = mixedMoment B raw33566step0 raw33566step0Labels := by
      have hz : ∀ j, raw33566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33566step0 = (fun i j => raw33566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33566step0 raw33566; decide +kernel
      have hl : raw33566step0Labels = raw33566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33566 raw33566Labels permutation346 hz
    mixedMoment B raw33566step0 raw33566step0Labels = mixedMoment B raw33566step1 raw33566step1Labels := by
      have ha : raw33566step1 = (fun i j => raw33566step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33566step1 raw33566step0; decide +kernel
      have hl : raw33566step1Labels = raw33566step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33566step0 raw33566step0Labels permutation32 permutation4
    mixedMoment B raw33566step1 raw33566step1Labels = mixedMoment B raw33566step2 raw33566step2Labels := by
      have ha : raw33566step2 = -raw33566step1 := by apply Matrix.ext; change ∀ i j, raw33566step2 i j = -(raw33566step1 i j); unfold raw33566step2 raw33566step1; decide +kernel
      have hl : raw33566step2Labels = raw33566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33566step2 raw33566step2Labels = mixedMoment B raw33566step3 raw33566step3Labels := by
      have ha : raw33566step3 = raw33566step2 := by apply Matrix.ext; unfold raw33566step3 raw33566step2; decide +kernel
      have hl : raw33566step2Labels = labelEmbedding7 ∘ raw33566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33566step2 raw33566step2Labels raw33566step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

theorem canonical33567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33567 raw33567Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw33567 raw33567Labels = mixedMoment B raw33567step0 raw33567step0Labels := by
      have hz : ∀ j, raw33567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33567step0 = (fun i j => raw33567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33567step0 raw33567; decide +kernel
      have hl : raw33567step0Labels = raw33567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33567 raw33567Labels permutation346 hz
    mixedMoment B raw33567step0 raw33567step0Labels = mixedMoment B raw33567step1 raw33567step1Labels := by
      have ha : raw33567step1 = (fun i j => raw33567step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33567step1 raw33567step0; decide +kernel
      have hl : raw33567step1Labels = raw33567step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33567step0 raw33567step0Labels permutation32 permutation6
    mixedMoment B raw33567step1 raw33567step1Labels = mixedMoment B raw33567step2 raw33567step2Labels := by
      have ha : raw33567step2 = raw33567step1 := by apply Matrix.ext; unfold raw33567step2 raw33567step1; decide +kernel
      have hl : raw33567step1Labels = labelEmbedding9 ∘ raw33567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33567step1 raw33567step1Labels raw33567step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical33642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33642 raw33642Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw33642 raw33642Labels = mixedMoment B raw33642step0 raw33642step0Labels := by
      have hz : ∀ j, raw33642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33642step0 = (fun i j => raw33642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33642step0 raw33642; decide +kernel
      have hl : raw33642step0Labels = raw33642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33642 raw33642Labels permutation346 hz
    mixedMoment B raw33642step0 raw33642step0Labels = mixedMoment B raw33642step1 raw33642step1Labels := by
      have ha : raw33642step1 = (fun i j => raw33642step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33642step1 raw33642step0; decide +kernel
      have hl : raw33642step1Labels = raw33642step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33642step0 raw33642step0Labels permutation47 permutation4
    mixedMoment B raw33642step1 raw33642step1Labels = mixedMoment B raw33642step2 raw33642step2Labels := by
      have ha : raw33642step2 = -raw33642step1 := by apply Matrix.ext; change ∀ i j, raw33642step2 i j = -(raw33642step1 i j); unfold raw33642step2 raw33642step1; decide +kernel
      have hl : raw33642step2Labels = raw33642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33642step2 raw33642step2Labels = mixedMoment B raw33642step3 raw33642step3Labels := by
      have ha : raw33642step3 = raw33642step2 := by apply Matrix.ext; unfold raw33642step3 raw33642step2; decide +kernel
      have hl : raw33642step2Labels = labelEmbedding7 ∘ raw33642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33642step2 raw33642step2Labels raw33642step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

theorem canonical33643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33643 raw33643Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw33643 raw33643Labels = mixedMoment B raw33643step0 raw33643step0Labels := by
      have ha : raw33643step0 = (fun i j => raw33643 (permutation191 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33643step0 raw33643; decide +kernel
      have hl : raw33643step0Labels = raw33643Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33643 raw33643Labels permutation191 permutation4
    mixedMoment B raw33643step0 raw33643step0Labels = mixedMoment B raw33643step1 raw33643step1Labels := by
      have ha : raw33643step1 = -raw33643step0 := by apply Matrix.ext; change ∀ i j, raw33643step1 i j = -(raw33643step0 i j); unfold raw33643step1 raw33643step0; decide +kernel
      have hl : raw33643step1Labels = raw33643step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33643step1 raw33643step1Labels = mixedMoment B raw33643step2 raw33643step2Labels := by
      have ha : raw33643step2 = raw33643step1 := by apply Matrix.ext; unfold raw33643step2 raw33643step1; decide +kernel
      have hl : raw33643step1Labels = labelEmbedding7 ∘ raw33643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33643step1 raw33643step1Labels raw33643step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

theorem canonical33644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33644 raw33644Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw33644 raw33644Labels = mixedMoment B raw33644step0 raw33644step0Labels := by
      have hz : ∀ j, raw33644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33644step0 = (fun i j => raw33644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33644step0 raw33644; decide +kernel
      have hl : raw33644step0Labels = raw33644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33644 raw33644Labels permutation346 hz
    mixedMoment B raw33644step0 raw33644step0Labels = mixedMoment B raw33644step1 raw33644step1Labels := by
      have ha : raw33644step1 = (fun i j => raw33644step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33644step1 raw33644step0; decide +kernel
      have hl : raw33644step1Labels = raw33644step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33644step0 raw33644step0Labels permutation32 permutation6
    mixedMoment B raw33644step1 raw33644step1Labels = mixedMoment B raw33644step2 raw33644step2Labels := by
      have ha : raw33644step2 = raw33644step1 := by apply Matrix.ext; unfold raw33644step2 raw33644step1; decide +kernel
      have hl : raw33644step1Labels = labelEmbedding9 ∘ raw33644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33644step1 raw33644step1Labels raw33644step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

theorem canonical33645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33645 raw33645Labels = mixedMoment B node4870 node4870Labels := by
  calc
    mixedMoment B raw33645 raw33645Labels = mixedMoment B raw33645step0 raw33645step0Labels := by
      have hz : ∀ j, raw33645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33645step0 = (fun i j => raw33645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33645step0 raw33645; decide +kernel
      have hl : raw33645step0Labels = raw33645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33645 raw33645Labels permutation346 hz
    mixedMoment B raw33645step0 raw33645step0Labels = mixedMoment B raw33645step1 raw33645step1Labels := by
      have ha : raw33645step1 = (fun i j => raw33645step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33645step1 raw33645step0; decide +kernel
      have hl : raw33645step1Labels = raw33645step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33645step0 raw33645step0Labels permutation47 permutation4
    mixedMoment B raw33645step1 raw33645step1Labels = mixedMoment B raw33645step2 raw33645step2Labels := by
      have ha : raw33645step2 = -raw33645step1 := by apply Matrix.ext; change ∀ i j, raw33645step2 i j = -(raw33645step1 i j); unfold raw33645step2 raw33645step1; decide +kernel
      have hl : raw33645step2Labels = raw33645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33645step2 raw33645step2Labels = mixedMoment B raw33645step3 raw33645step3Labels := by
      have ha : raw33645step3 = raw33645step2 := by apply Matrix.ext; unfold raw33645step3 raw33645step2; decide +kernel
      have hl : raw33645step2Labels = labelEmbedding7 ∘ raw33645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33645step2 raw33645step2Labels raw33645step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4870 node4870Labels := by rfl

theorem canonical33646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33646 raw33646Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw33646 raw33646Labels = mixedMoment B raw33646step0 raw33646step0Labels := by
      have ha : raw33646step0 = (fun i j => raw33646 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33646step0 raw33646; decide +kernel
      have hl : raw33646step0Labels = raw33646Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33646 raw33646Labels permutation224 permutation4
    mixedMoment B raw33646step0 raw33646step0Labels = mixedMoment B raw33646step1 raw33646step1Labels := by
      have ha : raw33646step1 = -raw33646step0 := by apply Matrix.ext; change ∀ i j, raw33646step1 i j = -(raw33646step0 i j); unfold raw33646step1 raw33646step0; decide +kernel
      have hl : raw33646step1Labels = raw33646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33646step1 raw33646step1Labels = mixedMoment B raw33646step2 raw33646step2Labels := by
      have ha : raw33646step2 = raw33646step1 := by apply Matrix.ext; unfold raw33646step2 raw33646step1; decide +kernel
      have hl : raw33646step1Labels = labelEmbedding7 ∘ raw33646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33646step1 raw33646step1Labels raw33646step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

theorem canonical33647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33647 raw33647Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw33647 raw33647Labels = mixedMoment B raw33647step0 raw33647step0Labels := by
      have ha : raw33647step0 = (fun i j => raw33647 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33647step0 raw33647; decide +kernel
      have hl : raw33647step0Labels = raw33647Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33647 raw33647Labels permutation154 permutation6
    mixedMoment B raw33647step0 raw33647step0Labels = mixedMoment B raw33647step1 raw33647step1Labels := by
      have ha : raw33647step1 = raw33647step0 := by apply Matrix.ext; unfold raw33647step1 raw33647step0; decide +kernel
      have hl : raw33647step0Labels = labelEmbedding9 ∘ raw33647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33647step0 raw33647step0Labels raw33647step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

theorem canonical33648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33648 raw33648Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw33648 raw33648Labels = mixedMoment B raw33648step0 raw33648step0Labels := by
      have hz : ∀ j, raw33648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33648step0 = (fun i j => raw33648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33648step0 raw33648; decide +kernel
      have hl : raw33648step0Labels = raw33648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33648 raw33648Labels permutation346 hz
    mixedMoment B raw33648step0 raw33648step0Labels = mixedMoment B raw33648step1 raw33648step1Labels := by
      have ha : raw33648step1 = (fun i j => raw33648step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33648step1 raw33648step0; decide +kernel
      have hl : raw33648step1Labels = raw33648step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33648step0 raw33648step0Labels permutation45 permutation4
    mixedMoment B raw33648step1 raw33648step1Labels = mixedMoment B raw33648step2 raw33648step2Labels := by
      have ha : raw33648step2 = -raw33648step1 := by apply Matrix.ext; change ∀ i j, raw33648step2 i j = -(raw33648step1 i j); unfold raw33648step2 raw33648step1; decide +kernel
      have hl : raw33648step2Labels = raw33648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33648step2 raw33648step2Labels = mixedMoment B raw33648step3 raw33648step3Labels := by
      have ha : raw33648step3 = raw33648step2 := by apply Matrix.ext; unfold raw33648step3 raw33648step2; decide +kernel
      have hl : raw33648step2Labels = labelEmbedding7 ∘ raw33648step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33648step2 raw33648step2Labels raw33648step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

theorem canonical33649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33649 raw33649Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw33649 raw33649Labels = mixedMoment B raw33649step0 raw33649step0Labels := by
      have hz : ∀ j, raw33649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33649step0 = (fun i j => raw33649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33649step0 raw33649; decide +kernel
      have hl : raw33649step0Labels = raw33649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33649 raw33649Labels permutation346 hz
    mixedMoment B raw33649step0 raw33649step0Labels = mixedMoment B raw33649step1 raw33649step1Labels := by
      have ha : raw33649step1 = (fun i j => raw33649step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33649step1 raw33649step0; decide +kernel
      have hl : raw33649step1Labels = raw33649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33649step0 raw33649step0Labels permutation34 permutation6
    mixedMoment B raw33649step1 raw33649step1Labels = mixedMoment B raw33649step2 raw33649step2Labels := by
      have ha : raw33649step2 = raw33649step1 := by apply Matrix.ext; unfold raw33649step2 raw33649step1; decide +kernel
      have hl : raw33649step1Labels = labelEmbedding9 ∘ raw33649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33649step1 raw33649step1Labels raw33649step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical33650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33650 raw33650Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw33650 raw33650Labels = mixedMoment B raw33650step0 raw33650step0Labels := by
      have ha : raw33650step0 = (fun i j => raw33650 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33650step0 raw33650; decide +kernel
      have hl : raw33650step0Labels = raw33650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33650 raw33650Labels permutation189 permutation4
    mixedMoment B raw33650step0 raw33650step0Labels = mixedMoment B raw33650step1 raw33650step1Labels := by
      have ha : raw33650step1 = -raw33650step0 := by apply Matrix.ext; change ∀ i j, raw33650step1 i j = -(raw33650step0 i j); unfold raw33650step1 raw33650step0; decide +kernel
      have hl : raw33650step1Labels = raw33650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33650step1 raw33650step1Labels = mixedMoment B raw33650step2 raw33650step2Labels := by
      have ha : raw33650step2 = raw33650step1 := by apply Matrix.ext; unfold raw33650step2 raw33650step1; decide +kernel
      have hl : raw33650step1Labels = labelEmbedding7 ∘ raw33650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33650step1 raw33650step1Labels raw33650step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

theorem canonical33651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33651 raw33651Labels = mixedMoment B node4861 node4861Labels := by
  calc
    mixedMoment B raw33651 raw33651Labels = mixedMoment B raw33651step0 raw33651step0Labels := by
      have hz : ∀ j, raw33651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33651step0 = (fun i j => raw33651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33651step0 raw33651; decide +kernel
      have hl : raw33651step0Labels = raw33651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33651 raw33651Labels permutation346 hz
    mixedMoment B raw33651step0 raw33651step0Labels = mixedMoment B raw33651step1 raw33651step1Labels := by
      have ha : raw33651step1 = (fun i j => raw33651step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33651step1 raw33651step0; decide +kernel
      have hl : raw33651step1Labels = raw33651step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33651step0 raw33651step0Labels permutation45 permutation4
    mixedMoment B raw33651step1 raw33651step1Labels = mixedMoment B raw33651step2 raw33651step2Labels := by
      have ha : raw33651step2 = -raw33651step1 := by apply Matrix.ext; change ∀ i j, raw33651step2 i j = -(raw33651step1 i j); unfold raw33651step2 raw33651step1; decide +kernel
      have hl : raw33651step2Labels = raw33651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33651step2 raw33651step2Labels = mixedMoment B raw33651step3 raw33651step3Labels := by
      have ha : raw33651step3 = raw33651step2 := by apply Matrix.ext; unfold raw33651step3 raw33651step2; decide +kernel
      have hl : raw33651step2Labels = labelEmbedding7 ∘ raw33651step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33651step2 raw33651step2Labels raw33651step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4861 node4861Labels := by rfl

theorem canonical33652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33652 raw33652Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw33652 raw33652Labels = mixedMoment B raw33652step0 raw33652step0Labels := by
      have hz : ∀ j, raw33652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33652step0 = (fun i j => raw33652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33652step0 raw33652; decide +kernel
      have hl : raw33652step0Labels = raw33652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33652 raw33652Labels permutation346 hz
    mixedMoment B raw33652step0 raw33652step0Labels = mixedMoment B raw33652step1 raw33652step1Labels := by
      have ha : raw33652step1 = (fun i j => raw33652step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33652step1 raw33652step0; decide +kernel
      have hl : raw33652step1Labels = raw33652step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33652step0 raw33652step0Labels permutation44 permutation4
    mixedMoment B raw33652step1 raw33652step1Labels = mixedMoment B raw33652step2 raw33652step2Labels := by
      have ha : raw33652step2 = -raw33652step1 := by apply Matrix.ext; change ∀ i j, raw33652step2 i j = -(raw33652step1 i j); unfold raw33652step2 raw33652step1; decide +kernel
      have hl : raw33652step2Labels = raw33652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33652step2 raw33652step2Labels = mixedMoment B raw33652step3 raw33652step3Labels := by
      have ha : raw33652step3 = raw33652step2 := by apply Matrix.ext; unfold raw33652step3 raw33652step2; decide +kernel
      have hl : raw33652step2Labels = labelEmbedding7 ∘ raw33652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33652step2 raw33652step2Labels raw33652step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical33653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33653 raw33653Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw33653 raw33653Labels = mixedMoment B raw33653step0 raw33653step0Labels := by
      have hz : ∀ j, raw33653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33653step0 = (fun i j => raw33653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33653step0 raw33653; decide +kernel
      have hl : raw33653step0Labels = raw33653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33653 raw33653Labels permutation346 hz
    mixedMoment B raw33653step0 raw33653step0Labels = mixedMoment B raw33653step1 raw33653step1Labels := by
      have ha : raw33653step1 = (fun i j => raw33653step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33653step1 raw33653step0; decide +kernel
      have hl : raw33653step1Labels = raw33653step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33653step0 raw33653step0Labels permutation32 permutation6
    mixedMoment B raw33653step1 raw33653step1Labels = mixedMoment B raw33653step2 raw33653step2Labels := by
      have ha : raw33653step2 = raw33653step1 := by apply Matrix.ext; unfold raw33653step2 raw33653step1; decide +kernel
      have hl : raw33653step1Labels = labelEmbedding9 ∘ raw33653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33653step1 raw33653step1Labels raw33653step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

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

theorem canonical1248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1248 raw1248Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw1248 raw1248Labels = mixedMoment B raw1248step0 raw1248step0Labels := by
      have ha : raw1248step0 = (fun i j => raw1248 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1248step0 raw1248; decide +kernel
      have hl : raw1248step0Labels = raw1248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1248 raw1248Labels permutation32 permutation4
    mixedMoment B raw1248step0 raw1248step0Labels = mixedMoment B raw1248step1 raw1248step1Labels := by
      have ha : raw1248step1 = raw1248step0 := by apply Matrix.ext; unfold raw1248step1 raw1248step0; decide +kernel
      have hl : raw1248step0Labels = labelEmbedding7 ∘ raw1248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1248step0 raw1248step0Labels raw1248step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical1249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1249 raw1249Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw1249 raw1249Labels = mixedMoment B raw1249step0 raw1249step0Labels := by
      have ha : raw1249step0 = (fun i j => raw1249 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1249step0 raw1249; decide +kernel
      have hl : raw1249step0Labels = raw1249Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1249 raw1249Labels permutation32 permutation4
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical1250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1250 raw1250Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw1250 raw1250Labels = mixedMoment B raw1250step0 raw1250step0Labels := by
      have ha : raw1250step0 = (fun i j => raw1250 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1250step0 raw1250; decide +kernel
      have hl : raw1250step0Labels = raw1250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1250 raw1250Labels permutation38 permutation6
    mixedMoment B raw1250step0 raw1250step0Labels = mixedMoment B raw1250step1 raw1250step1Labels := by
      have ha : raw1250step1 = -raw1250step0 := by apply Matrix.ext; change ∀ i j, raw1250step1 i j = -(raw1250step0 i j); unfold raw1250step1 raw1250step0; decide +kernel
      have hl : raw1250step1Labels = raw1250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1250step1 raw1250step1Labels = mixedMoment B raw1250step2 raw1250step2Labels := by
      have ha : raw1250step2 = raw1250step1 := by apply Matrix.ext; unfold raw1250step2 raw1250step1; decide +kernel
      have hl : raw1250step1Labels = labelEmbedding1 ∘ raw1250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1250step1 raw1250step1Labels raw1250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1645 node1645Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4452 node4452Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1035 node1035Labels + mixedMoment B node1645 node1645Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1248 singletonSmall4452
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4452) = raw1248Labels := by decide +kernel
  rw [hl, canonical1248 B hB] at h
  have hc0 : mixedMoment B raw1248 (Fin.cases (0 : Fin 2) singletonSmall4452) =
      mixedMoment B node1035 node1035Labels := by
    have ha : raw1248 = raw1249 := by apply Matrix.ext; unfold raw1248 raw1249; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4452 = raw1249Labels := by decide +kernel
    rw [ha, hj, canonical1249 B hB]
  have hc1 : mixedMoment B raw1248 (Fin.cases (1 : Fin 2) singletonSmall4452) =
      mixedMoment B node1645 node1645Labels := by
    have ha : raw1248 = raw1250 := by apply Matrix.ext; unfold raw1248 raw1250; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4452 = raw1250Labels := by decide +kernel
    rw [ha, hj, canonical1250 B hB]
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

theorem singleton4489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4489 node4489Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1073 node1073Labels + mixedMoment B node1648 node1648Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1281 singletonSmall4489
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4489) = raw1281Labels := by decide +kernel
  rw [hl, canonical1281 B hB] at h
  have hc0 : mixedMoment B raw1281 (Fin.cases (0 : Fin 2) singletonSmall4489) =
      mixedMoment B node1073 node1073Labels := by
    have ha : raw1281 = raw1282 := by apply Matrix.ext; unfold raw1281 raw1282; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4489 = raw1282Labels := by decide +kernel
    rw [ha, hj, canonical1282 B hB]
  have hc1 : mixedMoment B raw1281 (Fin.cases (1 : Fin 2) singletonSmall4489) =
      mixedMoment B node1648 node1648Labels := by
    have ha : raw1281 = raw1283 := by apply Matrix.ext; unfold raw1281 raw1283; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4489 = raw1283Labels := by decide +kernel
    rw [ha, hj, canonical1283 B hB]
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

theorem singleton4798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4798 node4798Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2016 node2016Labels + mixedMoment B node2075 node2075Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1725 singletonSmall4798
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4798) = raw1725Labels := by decide +kernel
  rw [hl, canonical1725 B hB] at h
  have hc0 : mixedMoment B raw1725 (Fin.cases (0 : Fin 2) singletonSmall4798) =
      mixedMoment B node2016 node2016Labels := by
    have ha : raw1725 = raw1726 := by apply Matrix.ext; unfold raw1725 raw1726; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4798 = raw1726Labels := by decide +kernel
    rw [ha, hj, canonical1726 B hB]
  have hc1 : mixedMoment B raw1725 (Fin.cases (1 : Fin 2) singletonSmall4798) =
      mixedMoment B node2075 node2075Labels := by
    have ha : raw1725 = raw1727 := by apply Matrix.ext; unfold raw1725 raw1727; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4798 = raw1727Labels := by decide +kernel
    rw [ha, hj, canonical1727 B hB]
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

theorem singleton4802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4802 node4802Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2020 node2020Labels + mixedMoment B node2202 node2202Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1734 singletonSmall4802
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4802) = raw1734Labels := by decide +kernel
  rw [hl, canonical1734 B hB] at h
  have hc0 : mixedMoment B raw1734 (Fin.cases (0 : Fin 2) singletonSmall4802) =
      mixedMoment B node2020 node2020Labels := by
    have ha : raw1734 = raw1735 := by apply Matrix.ext; unfold raw1734 raw1735; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4802 = raw1735Labels := by decide +kernel
    rw [ha, hj, canonical1735 B hB]
  have hc1 : mixedMoment B raw1734 (Fin.cases (1 : Fin 2) singletonSmall4802) =
      mixedMoment B node2202 node2202Labels := by
    have ha : raw1734 = raw1736 := by apply Matrix.ext; unfold raw1734 raw1736; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4802 = raw1736Labels := by decide +kernel
    rw [ha, hj, canonical1736 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4826 node4826Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2046 node2046Labels + mixedMoment B node2077 node2077Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1752 singletonSmall4826
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4826) = raw1752Labels := by decide +kernel
  rw [hl, canonical1752 B hB] at h
  have hc0 : mixedMoment B raw1752 (Fin.cases (0 : Fin 2) singletonSmall4826) =
      mixedMoment B node2046 node2046Labels := by
    have ha : raw1752 = raw1753 := by apply Matrix.ext; unfold raw1752 raw1753; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4826 = raw1753Labels := by decide +kernel
    rw [ha, hj, canonical1753 B hB]
  have hc1 : mixedMoment B raw1752 (Fin.cases (1 : Fin 2) singletonSmall4826) =
      mixedMoment B node2077 node2077Labels := by
    have ha : raw1752 = raw1754 := by apply Matrix.ext; unfold raw1752 raw1754; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4826 = raw1754Labels := by decide +kernel
    rw [ha, hj, canonical1754 B hB]
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

theorem singleton4860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4860 node4860Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2101 node2101Labels + mixedMoment B node2101 node2101Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1782 singletonSmall4860
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4860) = raw1782Labels := by decide +kernel
  rw [hl, canonical1782 B hB] at h
  have hc0 : mixedMoment B raw1782 (Fin.cases (0 : Fin 2) singletonSmall4860) =
      mixedMoment B node2101 node2101Labels := by
    have ha : raw1782 = raw1783 := by apply Matrix.ext; unfold raw1782 raw1783; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4860 = raw1783Labels := by decide +kernel
    rw [ha, hj, canonical1783 B hB]
  have hc1 : mixedMoment B raw1782 (Fin.cases (1 : Fin 2) singletonSmall4860) =
      mixedMoment B node2101 node2101Labels := by
    have ha : raw1782 = raw1784 := by apply Matrix.ext; unfold raw1782 raw1784; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4860 = raw1784Labels := by decide +kernel
    rw [ha, hj, canonical1784 B hB]
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

theorem singleton4865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4865 node4865Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2106 node2106Labels + mixedMoment B node2242 node2242Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1791 singletonSmall4865
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4865) = raw1791Labels := by decide +kernel
  rw [hl, canonical1791 B hB] at h
  have hc0 : mixedMoment B raw1791 (Fin.cases (0 : Fin 2) singletonSmall4865) =
      mixedMoment B node2106 node2106Labels := by
    have ha : raw1791 = raw1792 := by apply Matrix.ext; unfold raw1791 raw1792; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4865 = raw1792Labels := by decide +kernel
    rw [ha, hj, canonical1792 B hB]
  have hc1 : mixedMoment B raw1791 (Fin.cases (1 : Fin 2) singletonSmall4865) =
      mixedMoment B node2242 node2242Labels := by
    have ha : raw1791 = raw1793 := by apply Matrix.ext; unfold raw1791 raw1793; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4865 = raw1793Labels := by decide +kernel
    rw [ha, hj, canonical1793 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4866 node4866Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2107 node2107Labels + mixedMoment B node2260 node2260Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1794 singletonSmall4866
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4866) = raw1794Labels := by decide +kernel
  rw [hl, canonical1794 B hB] at h
  have hc0 : mixedMoment B raw1794 (Fin.cases (0 : Fin 2) singletonSmall4866) =
      mixedMoment B node2107 node2107Labels := by
    have ha : raw1794 = raw1795 := by apply Matrix.ext; unfold raw1794 raw1795; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4866 = raw1795Labels := by decide +kernel
    rw [ha, hj, canonical1795 B hB]
  have hc1 : mixedMoment B raw1794 (Fin.cases (1 : Fin 2) singletonSmall4866) =
      mixedMoment B node2260 node2260Labels := by
    have ha : raw1794 = raw1796 := by apply Matrix.ext; unfold raw1794 raw1796; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4866 = raw1796Labels := by decide +kernel
    rw [ha, hj, canonical1796 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4869 node4869Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2110 node2110Labels + mixedMoment B node2275 node2275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1800 singletonSmall4869
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4869) = raw1800Labels := by decide +kernel
  rw [hl, canonical1800 B hB] at h
  have hc0 : mixedMoment B raw1800 (Fin.cases (0 : Fin 2) singletonSmall4869) =
      mixedMoment B node2110 node2110Labels := by
    have ha : raw1800 = raw1801 := by apply Matrix.ext; unfold raw1800 raw1801; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4869 = raw1801Labels := by decide +kernel
    rw [ha, hj, canonical1801 B hB]
  have hc1 : mixedMoment B raw1800 (Fin.cases (1 : Fin 2) singletonSmall4869) =
      mixedMoment B node2275 node2275Labels := by
    have ha : raw1800 = raw1802 := by apply Matrix.ext; unfold raw1800 raw1802; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4869 = raw1802Labels := by decide +kernel
    rw [ha, hj, canonical1802 B hB]
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

theorem singleton5204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5204 node5204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2881 node2881Labels + mixedMoment B node3624 node3624Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2232 singletonSmall5204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5204) = raw2232Labels := by decide +kernel
  rw [hl, canonical2232 B hB] at h
  have hc0 : mixedMoment B raw2232 (Fin.cases (0 : Fin 2) singletonSmall5204) =
      mixedMoment B node2881 node2881Labels := by
    have ha : raw2232 = raw2233 := by apply Matrix.ext; unfold raw2232 raw2233; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5204 = raw2233Labels := by decide +kernel
    rw [ha, hj, canonical2233 B hB]
  have hc1 : mixedMoment B raw2232 (Fin.cases (1 : Fin 2) singletonSmall5204) =
      mixedMoment B node3624 node3624Labels := by
    have ha : raw2232 = raw2234 := by apply Matrix.ext; unfold raw2232 raw2234; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5204 = raw2234Labels := by decide +kernel
    rw [ha, hj, canonical2234 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

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

theorem sound1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1645 node1645Labels = Sparse.eval nodeValue1645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1645) = mixedMoment B node1645 node1645Labels := rfl
  simpa [nodeValue1645, Sparse.eval] using hc.symm

theorem sound1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1648 node1648Labels = Sparse.eval nodeValue1648 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1648) = mixedMoment B node1648 node1648Labels := rfl
  simpa [nodeValue1648, Sparse.eval] using hc.symm

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

theorem sound2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2016 node2016Labels = Sparse.eval nodeValue2016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2016) = mixedMoment B node2016 node2016Labels := rfl
  simpa [nodeValue2016, Sparse.eval] using hc.symm

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2046 node2046Labels = Sparse.eval nodeValue2046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2046) = mixedMoment B node2046 node2046Labels := rfl
  simpa [nodeValue2046, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

theorem sound2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2101 node2101Labels = Sparse.eval nodeValue2101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2101) = mixedMoment B node2101 node2101Labels := rfl
  simpa [nodeValue2101, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

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

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

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

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

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

theorem sound3621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3621 node3621Labels = Sparse.eval nodeValue3621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3621) = mixedMoment B node3621 node3621Labels := rfl
  simpa [nodeValue3621, Sparse.eval] using hc.symm

theorem sound3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3624 node3624Labels = Sparse.eval nodeValue3624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3624) = mixedMoment B node3624 node3624Labels := rfl
  simpa [nodeValue3624, Sparse.eval] using hc.symm

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

theorem sound4449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4449 node4449Labels = Sparse.eval nodeValue4449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4449) = mixedMoment B node4449 node4449Labels := rfl
  simpa [nodeValue4449, Sparse.eval] using hc.symm

theorem sound4452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4452 node4452Labels = Sparse.eval nodeValue4452 (mixedVector B) := by
  have h := singleton4452 B _hB
  rw [sound1035 B _hB _hF, sound1645 B _hB _hF] at h
  norm_num [nodeValue4452, nodeValue1035, nodeValue1645, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4453 node4453Labels = Sparse.eval nodeValue4453 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4453) = mixedMoment B node4453 node4453Labels := rfl
  simpa [nodeValue4453, Sparse.eval] using hc.symm

theorem sound4462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4462 node4462Labels = Sparse.eval nodeValue4462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4462) = mixedMoment B node4462 node4462Labels := rfl
  simpa [nodeValue4462, Sparse.eval] using hc.symm

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

theorem sound4489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4489 node4489Labels = Sparse.eval nodeValue4489 (mixedVector B) := by
  have h := singleton4489 B _hB
  rw [sound1073 B _hB _hF, sound1648 B _hB _hF] at h
  norm_num [nodeValue4489, nodeValue1073, nodeValue1648, Sparse.eval] at h ⊢
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

theorem sound4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4798 node4798Labels = Sparse.eval nodeValue4798 (mixedVector B) := by
  have h := singleton4798 B _hB
  rw [sound2016 B _hB _hF, sound2075 B _hB _hF] at h
  norm_num [nodeValue4798, nodeValue2016, nodeValue2075, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4799 node4799Labels = Sparse.eval nodeValue4799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4799) = mixedMoment B node4799 node4799Labels := rfl
  simpa [nodeValue4799, Sparse.eval] using hc.symm

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

theorem zero4838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = 0 := by
  exact mixedMoment_order_one B hB node4838 node4838Labels 1
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

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4806 node4806Labels = Sparse.eval nodeValue4806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4806) = mixedMoment B node4806 node4806Labels := rfl
  simpa [nodeValue4806, Sparse.eval] using hc.symm

theorem sound4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4826 node4826Labels = Sparse.eval nodeValue4826 (mixedVector B) := by
  have h := singleton4826 B _hB
  rw [sound2046 B _hB _hF, sound2077 B _hB _hF] at h
  norm_num [nodeValue4826, nodeValue2046, nodeValue2077, Sparse.eval] at h ⊢
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

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

theorem sound4849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4849 node4849Labels = Sparse.eval nodeValue4849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4849) = mixedMoment B node4849 node4849Labels := rfl
  simpa [nodeValue4849, Sparse.eval] using hc.symm

theorem sound4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4851 node4851Labels = Sparse.eval nodeValue4851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4851) = mixedMoment B node4851 node4851Labels := rfl
  simpa [nodeValue4851, Sparse.eval] using hc.symm

theorem sound4852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4852 node4852Labels = Sparse.eval nodeValue4852 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4852) = mixedMoment B node4852 node4852Labels := rfl
  simpa [nodeValue4852, Sparse.eval] using hc.symm

theorem sound4860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4860 node4860Labels = Sparse.eval nodeValue4860 (mixedVector B) := by
  have h := singleton4860 B _hB
  rw [sound2101 B _hB _hF] at h
  norm_num [nodeValue4860, nodeValue2101, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4861 node4861Labels = Sparse.eval nodeValue4861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4861) = mixedMoment B node4861 node4861Labels := rfl
  simpa [nodeValue4861, Sparse.eval] using hc.symm

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

theorem sound4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4865 node4865Labels = Sparse.eval nodeValue4865 (mixedVector B) := by
  have h := singleton4865 B _hB
  rw [sound2106 B _hB _hF, sound2242 B _hB _hF] at h
  norm_num [nodeValue4865, nodeValue2106, nodeValue2242, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4866 node4866Labels = Sparse.eval nodeValue4866 (mixedVector B) := by
  have h := singleton4866 B _hB
  rw [sound2107 B _hB _hF, sound2260 B _hB _hF] at h
  norm_num [nodeValue4866, nodeValue2107, nodeValue2260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4867 node4867Labels = Sparse.eval nodeValue4867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4867) = mixedMoment B node4867 node4867Labels := rfl
  simpa [nodeValue4867, Sparse.eval] using hc.symm

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4870 node4870Labels = Sparse.eval nodeValue4870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4870) = mixedMoment B node4870 node4870Labels := rfl
  simpa [nodeValue4870, Sparse.eval] using hc.symm

theorem sound4879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4879 node4879Labels = Sparse.eval nodeValue4879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4879) = mixedMoment B node4879 node4879Labels := rfl
  simpa [nodeValue4879, Sparse.eval] using hc.symm

theorem sound4880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4880 node4880Labels = Sparse.eval nodeValue4880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4880) = mixedMoment B node4880 node4880Labels := rfl
  simpa [nodeValue4880, Sparse.eval] using hc.symm

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

theorem sound5199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5199 node5199Labels = Sparse.eval nodeValue5199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5199) = mixedMoment B node5199 node5199Labels := rfl
  simpa [nodeValue5199, Sparse.eval] using hc.symm

theorem sound5203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5203 node5203Labels = Sparse.eval nodeValue5203 (mixedVector B) := by
  have h := singleton5203 B _hB
  rw [sound2884 B _hB _hF, sound3621 B _hB _hF] at h
  norm_num [nodeValue5203, nodeValue2884, nodeValue3621, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5204 node5204Labels = Sparse.eval nodeValue5204 (mixedVector B) := by
  have h := singleton5204 B _hB
  rw [sound2881 B _hB _hF, sound3624 B _hB _hF] at h
  norm_num [nodeValue5204, nodeValue2881, nodeValue3624, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources76
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2450 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 1) (sourceB2450 + difference 1 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 1) (sourceB2450 + difference 1 0) sourceC2450) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 2) (sourceB2450 + difference 2 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 2) (sourceB2450 + difference 2 0) sourceC2450) = raw32905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32905; decide +kernel
    rw [ha]
    exact (canonical32905 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 3) (sourceB2450 + difference 3 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 3) (sourceB2450 + difference 3 0) sourceC2450) = raw32318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32318; decide +kernel
    rw [ha]
    exact (canonical32318 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 4) (sourceB2450 + difference 4 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 4) (sourceB2450 + difference 4 0) sourceC2450) = raw32826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32826; decide +kernel
    rw [ha]
    exact (canonical32826 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2450 + difference 0 5) (sourceB2450 + difference 5 0) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2450 + difference 0 5) (sourceB2450 + difference 5 0) sourceC2450) = raw32233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32233; decide +kernel
    rw [ha]
    exact (canonical32233 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 0) (sourceB2450 + difference 0 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 0) (sourceB2450 + difference 0 1) sourceC2450) = raw33642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33642; decide +kernel
    rw [ha]
    exact (canonical33642 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 2) (sourceB2450 + difference 2 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 2) (sourceB2450 + difference 2 1) sourceC2450) = raw33643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33643; decide +kernel
    rw [ha]
    exact (canonical33643 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 3) (sourceB2450 + difference 3 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 3) (sourceB2450 + difference 3 1) sourceC2450) = raw33644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33644; decide +kernel
    rw [ha]
    exact (canonical33644 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 4) (sourceB2450 + difference 4 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 4) (sourceB2450 + difference 4 1) sourceC2450) = raw33645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33645; decide +kernel
    rw [ha]
    exact (canonical33645 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2450 + difference 1 5) (sourceB2450 + difference 5 1) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA2450 + difference 1 5) (sourceB2450 + difference 5 1) sourceC2450) = raw33553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33553; decide +kernel
    rw [ha]
    exact (canonical33553 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 0) (sourceB2450 + difference 0 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 0) (sourceB2450 + difference 0 2) sourceC2450) = raw33646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33646; decide +kernel
    rw [ha]
    exact (canonical33646 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 1) (sourceB2450 + difference 1 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 1) (sourceB2450 + difference 1 2) sourceC2450) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 3) (sourceB2450 + difference 3 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 3) (sourceB2450 + difference 3 2) sourceC2450) = raw32317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32317; decide +kernel
    rw [ha]
    exact (canonical32317 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 4) (sourceB2450 + difference 4 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 4) (sourceB2450 + difference 4 2) sourceC2450) = raw33647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33647; decide +kernel
    rw [ha]
    exact (canonical33647 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2450 + difference 2 5) (sourceB2450 + difference 5 2) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2450 + difference 2 5) (sourceB2450 + difference 5 2) sourceC2450) = raw33556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33556; decide +kernel
    rw [ha]
    exact (canonical33556 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 0) (sourceB2450 + difference 0 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 0) (sourceB2450 + difference 0 3) sourceC2450) = raw33648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33648; decide +kernel
    rw [ha]
    exact (canonical33648 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 1) (sourceB2450 + difference 1 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 1) (sourceB2450 + difference 1 3) sourceC2450) = raw33649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33649; decide +kernel
    rw [ha]
    exact (canonical33649 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 2) (sourceB2450 + difference 2 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 2) (sourceB2450 + difference 2 3) sourceC2450) = raw33650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33650; decide +kernel
    rw [ha]
    exact (canonical33650 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 4) (sourceB2450 + difference 4 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4861) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 4) (sourceB2450 + difference 4 3) sourceC2450) = raw33651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33651; decide +kernel
    rw [ha]
    exact (canonical33651 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2450 + difference 3 5) (sourceB2450 + difference 5 3) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2450 + difference 3 5) (sourceB2450 + difference 5 3) sourceC2450) = raw33560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33560; decide +kernel
    rw [ha]
    exact (canonical33560 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 0) (sourceB2450 + difference 0 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 0) (sourceB2450 + difference 0 4) sourceC2450) = raw33566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33566; decide +kernel
    rw [ha]
    exact (canonical33566 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 1) (sourceB2450 + difference 1 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 1) (sourceB2450 + difference 1 4) sourceC2450) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 2) (sourceB2450 + difference 2 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 2) (sourceB2450 + difference 2 4) sourceC2450) = raw32902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32902; decide +kernel
    rw [ha]
    exact (canonical32902 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 3) (sourceB2450 + difference 3 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 3) (sourceB2450 + difference 3 4) sourceC2450) = raw33567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33567; decide +kernel
    rw [ha]
    exact (canonical33567 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2450 + difference 4 5) (sourceB2450 + difference 5 4) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2450 + difference 4 5) (sourceB2450 + difference 5 4) sourceC2450) = raw32230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32230; decide +kernel
    rw [ha]
    exact (canonical32230 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 0) (sourceB2450 + difference 0 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 0) (sourceB2450 + difference 0 5) sourceC2450) = raw33652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33652; decide +kernel
    rw [ha]
    exact (canonical33652 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 1) (sourceB2450 + difference 1 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 1) (sourceB2450 + difference 1 5) sourceC2450) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 2) (sourceB2450 + difference 2 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 2) (sourceB2450 + difference 2 5) sourceC2450) = raw32999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32999; decide +kernel
    rw [ha]
    exact (canonical32999 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 3) (sourceB2450 + difference 3 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 3) (sourceB2450 + difference 3 5) sourceC2450) = raw33653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw33653; decide +kernel
    rw [ha]
    exact (canonical33653 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2450 + difference 5 4) (sourceB2450 + difference 4 5) sourceC2450) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2450 + difference 5 4) (sourceB2450 + difference 4 5) sourceC2450) = raw32822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2450 sourceB2450 sourceC2450 difference raw32822; decide +kernel
    rw [ha]
    exact (canonical32822 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2450 sourceB2450 sourceC2450
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2450, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1970 : Integer.Sparse.reindex keyMap MixedData.row1970 = numericRow1970 := by decide +kernel

theorem numericCheck1970 (x : Master → ℝ) : Integer.Sparse.eval numericRow1970 x =
    (17280 : ℝ) * reducedSource1970 x := by
  norm_num [numericRow1970, reducedSource1970, Integer.Sparse.eval, Sparse.eval, nodeValue4449, nodeValue4452, nodeValue4453, nodeValue4462, nodeValue4489, nodeValue4798, nodeValue4799, nodeValue4802, nodeValue4806, nodeValue4826, nodeValue4834, nodeValue4835, nodeValue4838, nodeValue4849, nodeValue4851, nodeValue4852, nodeValue4860, nodeValue4861, nodeValue4865, nodeValue4866, nodeValue4867, nodeValue4869, nodeValue4870, nodeValue4879, nodeValue4880, nodeValue5169, nodeValue5185, nodeValue5199, nodeValue5203, nodeValue5204]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1970 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1970 (mixedVector B) = 0 := by
  have h4449 : mixedVector B (Sum.inr 4449) = Sparse.eval nodeValue4449 (mixedVector B) := by
    change mixedMoment B node4449 node4449Labels = _
    exact sound4449 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4453 : mixedVector B (Sum.inr 4453) = Sparse.eval nodeValue4453 (mixedVector B) := by
    change mixedMoment B node4453 node4453Labels = _
    exact sound4453 B hB hF
  have h4462 : mixedVector B (Sum.inr 4462) = Sparse.eval nodeValue4462 (mixedVector B) := by
    change mixedMoment B node4462 node4462Labels = _
    exact sound4462 B hB hF
  have h4489 : mixedVector B (Sum.inr 4489) = Sparse.eval nodeValue4489 (mixedVector B) := by
    change mixedMoment B node4489 node4489Labels = _
    exact sound4489 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4799 : mixedVector B (Sum.inr 4799) = Sparse.eval nodeValue4799 (mixedVector B) := by
    change mixedMoment B node4799 node4799Labels = _
    exact sound4799 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4806 : mixedVector B (Sum.inr 4806) = Sparse.eval nodeValue4806 (mixedVector B) := by
    change mixedMoment B node4806 node4806Labels = _
    exact sound4806 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4849 : mixedVector B (Sum.inr 4849) = Sparse.eval nodeValue4849 (mixedVector B) := by
    change mixedMoment B node4849 node4849Labels = _
    exact sound4849 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h4860 : mixedVector B (Sum.inr 4860) = Sparse.eval nodeValue4860 (mixedVector B) := by
    change mixedMoment B node4860 node4860Labels = _
    exact sound4860 B hB hF
  have h4861 : mixedVector B (Sum.inr 4861) = Sparse.eval nodeValue4861 (mixedVector B) := by
    change mixedMoment B node4861 node4861Labels = _
    exact sound4861 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4870 : mixedVector B (Sum.inr 4870) = Sparse.eval nodeValue4870 (mixedVector B) := by
    change mixedMoment B node4870 node4870Labels = _
    exact sound4870 B hB hF
  have h4879 : mixedVector B (Sum.inr 4879) = Sparse.eval nodeValue4879 (mixedVector B) := by
    change mixedMoment B node4879 node4879Labels = _
    exact sound4879 B hB hF
  have h4880 : mixedVector B (Sum.inr 4880) = Sparse.eval nodeValue4880 (mixedVector B) := by
    change mixedMoment B node4880 node4880Labels = _
    exact sound4880 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169_e B hB hF
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5199 : mixedVector B (Sum.inr 5199) = Sparse.eval nodeValue5199 (mixedVector B) := by
    change mixedMoment B node5199 node5199Labels = _
    exact sound5199 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  simpa only [sourceForm2450, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4449, h4452, h4453, h4462, h4489, h4798, h4799, h4802, h4806, h4826, h4834, h4835, h4838, h4849, h4851, h4852, h4860, h4861, h4865, h4866, h4867, h4869, h4870, h4879, h4880, h5169, h5185, h5199, h5203, h5204, reducedSource1970] using sourceEq2450 B hB

theorem rowSound1970_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1970 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1970, numericCheck1970, reducedZero1970 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e_oai
