-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:45:05.35121+00:00
-- url     : https://prove2.me/submissions/fc363f8c-df7a-4d4c-82a2-c8186d421353

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5387_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e

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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1482 raw1482Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw1482 raw1482Labels = mixedMoment B raw1482step0 raw1482step0Labels := by
      have ha : raw1482step0 = (fun i j => raw1482 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1482step0 raw1482; decide +kernel
      have hl : raw1482step0Labels = raw1482Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1482 raw1482Labels permutation152 permutation4
    mixedMoment B raw1482step0 raw1482step0Labels = mixedMoment B raw1482step1 raw1482step1Labels := by
      have ha : raw1482step1 = raw1482step0 := by apply Matrix.ext; unfold raw1482step1 raw1482step0; decide +kernel
      have hl : raw1482step0Labels = labelEmbedding7 ∘ raw1482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1482step0 raw1482step0Labels raw1482step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

theorem canonical1483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1483 raw1483Labels = mixedMoment B node1763 node1763Labels := by
  calc
    mixedMoment B raw1483 raw1483Labels = mixedMoment B raw1483step0 raw1483step0Labels := by
      have ha : raw1483step0 = (fun i j => raw1483 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1483step0 raw1483; decide +kernel
      have hl : raw1483step0Labels = raw1483Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1483 raw1483Labels permutation152 permutation4
    _ = mixedMoment B node1763 node1763Labels := by rfl

theorem canonical1484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1484 raw1484Labels = mixedMoment B node1842 node1842Labels := by
  calc
    mixedMoment B raw1484 raw1484Labels = mixedMoment B raw1484step0 raw1484step0Labels := by
      have ha : raw1484step0 = (fun i j => raw1484 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1484step0 raw1484; decide +kernel
      have hl : raw1484step0Labels = raw1484Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1484 raw1484Labels permutation164 permutation6
    mixedMoment B raw1484step0 raw1484step0Labels = mixedMoment B raw1484step1 raw1484step1Labels := by
      have ha : raw1484step1 = -raw1484step0 := by apply Matrix.ext; change ∀ i j, raw1484step1 i j = -(raw1484step0 i j); unfold raw1484step1 raw1484step0; decide +kernel
      have hl : raw1484step1Labels = raw1484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1484step1 raw1484step1Labels = mixedMoment B raw1484step2 raw1484step2Labels := by
      have ha : raw1484step2 = raw1484step1 := by apply Matrix.ext; unfold raw1484step2 raw1484step1; decide +kernel
      have hl : raw1484step1Labels = labelEmbedding1 ∘ raw1484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1484step1 raw1484step1Labels raw1484step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1842 node1842Labels := by rfl

theorem canonical1488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1488 raw1488Labels = mixedMoment B node4636 node4636Labels := by
  calc
    mixedMoment B raw1488 raw1488Labels = mixedMoment B raw1488step0 raw1488step0Labels := by
      have ha : raw1488step0 = (fun i j => raw1488 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1488step0 raw1488; decide +kernel
      have hl : raw1488step0Labels = raw1488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1488 raw1488Labels permutation32 permutation4
    mixedMoment B raw1488step0 raw1488step0Labels = mixedMoment B raw1488step1 raw1488step1Labels := by
      have ha : raw1488step1 = raw1488step0 := by apply Matrix.ext; unfold raw1488step1 raw1488step0; decide +kernel
      have hl : raw1488step0Labels = labelEmbedding7 ∘ raw1488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1488step0 raw1488step0Labels raw1488step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4636 node4636Labels := by rfl

theorem canonical1489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1489 raw1489Labels = mixedMoment B node1765 node1765Labels := by
  calc
    mixedMoment B raw1489 raw1489Labels = mixedMoment B raw1489step0 raw1489step0Labels := by
      have ha : raw1489step0 = (fun i j => raw1489 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1489step0 raw1489; decide +kernel
      have hl : raw1489step0Labels = raw1489Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1489 raw1489Labels permutation32 permutation4
    _ = mixedMoment B node1765 node1765Labels := by rfl

theorem canonical1490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1490 raw1490Labels = mixedMoment B node1843 node1843Labels := by
  calc
    mixedMoment B raw1490 raw1490Labels = mixedMoment B raw1490step0 raw1490step0Labels := by
      have ha : raw1490step0 = (fun i j => raw1490 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1490step0 raw1490; decide +kernel
      have hl : raw1490step0Labels = raw1490Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1490 raw1490Labels permutation34 permutation6
    mixedMoment B raw1490step0 raw1490step0Labels = mixedMoment B raw1490step1 raw1490step1Labels := by
      have ha : raw1490step1 = -raw1490step0 := by apply Matrix.ext; change ∀ i j, raw1490step1 i j = -(raw1490step0 i j); unfold raw1490step1 raw1490step0; decide +kernel
      have hl : raw1490step1Labels = raw1490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1490step1 raw1490step1Labels = mixedMoment B raw1490step2 raw1490step2Labels := by
      have ha : raw1490step2 = raw1490step1 := by apply Matrix.ext; unfold raw1490step2 raw1490step1; decide +kernel
      have hl : raw1490step1Labels = labelEmbedding1 ∘ raw1490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1490step1 raw1490step1Labels raw1490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1843 node1843Labels := by rfl

theorem canonical1494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1494 raw1494Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw1494 raw1494Labels = mixedMoment B raw1494step0 raw1494step0Labels := by
      have ha : raw1494step0 = (fun i j => raw1494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1494step0 raw1494; decide +kernel
      have hl : raw1494step0Labels = raw1494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1494 raw1494Labels permutation32 permutation4
    mixedMoment B raw1494step0 raw1494step0Labels = mixedMoment B raw1494step1 raw1494step1Labels := by
      have ha : raw1494step1 = raw1494step0 := by apply Matrix.ext; unfold raw1494step1 raw1494step0; decide +kernel
      have hl : raw1494step0Labels = labelEmbedding7 ∘ raw1494step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1494step0 raw1494step0Labels raw1494step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

theorem canonical1495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1495 raw1495Labels = mixedMoment B node1767 node1767Labels := by
  calc
    mixedMoment B raw1495 raw1495Labels = mixedMoment B raw1495step0 raw1495step0Labels := by
      have ha : raw1495step0 = (fun i j => raw1495 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1495step0 raw1495; decide +kernel
      have hl : raw1495step0Labels = raw1495Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1495 raw1495Labels permutation32 permutation4
    _ = mixedMoment B node1767 node1767Labels := by rfl

theorem canonical1496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1496 raw1496Labels = mixedMoment B node1851 node1851Labels := by
  calc
    mixedMoment B raw1496 raw1496Labels = mixedMoment B raw1496step0 raw1496step0Labels := by
      have ha : raw1496step0 = (fun i j => raw1496 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1496step0 raw1496; decide +kernel
      have hl : raw1496step0Labels = raw1496Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1496 raw1496Labels permutation33 permutation6
    mixedMoment B raw1496step0 raw1496step0Labels = mixedMoment B raw1496step1 raw1496step1Labels := by
      have ha : raw1496step1 = -raw1496step0 := by apply Matrix.ext; change ∀ i j, raw1496step1 i j = -(raw1496step0 i j); unfold raw1496step1 raw1496step0; decide +kernel
      have hl : raw1496step1Labels = raw1496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1496step1 raw1496step1Labels = mixedMoment B raw1496step2 raw1496step2Labels := by
      have ha : raw1496step2 = raw1496step1 := by apply Matrix.ext; unfold raw1496step2 raw1496step1; decide +kernel
      have hl : raw1496step1Labels = labelEmbedding1 ∘ raw1496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1496step1 raw1496step1Labels raw1496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1851 node1851Labels := by rfl

theorem canonical1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1521 raw1521Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw1521 raw1521Labels = mixedMoment B raw1521step0 raw1521step0Labels := by
      have ha : raw1521step0 = (fun i j => raw1521 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1521step0 raw1521; decide +kernel
      have hl : raw1521step0Labels = raw1521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1521 raw1521Labels permutation32 permutation4
    mixedMoment B raw1521step0 raw1521step0Labels = mixedMoment B raw1521step1 raw1521step1Labels := by
      have ha : raw1521step1 = raw1521step0 := by apply Matrix.ext; unfold raw1521step1 raw1521step0; decide +kernel
      have hl : raw1521step0Labels = labelEmbedding7 ∘ raw1521step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1521step0 raw1521step0Labels raw1521step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

theorem canonical1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1522 raw1522Labels = mixedMoment B node1781 node1781Labels := by
  calc
    mixedMoment B raw1522 raw1522Labels = mixedMoment B raw1522step0 raw1522step0Labels := by
      have ha : raw1522step0 = (fun i j => raw1522 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1522step0 raw1522; decide +kernel
      have hl : raw1522step0Labels = raw1522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1522 raw1522Labels permutation32 permutation4
    _ = mixedMoment B node1781 node1781Labels := by rfl

theorem canonical1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1523 raw1523Labels = mixedMoment B node1846 node1846Labels := by
  calc
    mixedMoment B raw1523 raw1523Labels = mixedMoment B raw1523step0 raw1523step0Labels := by
      have ha : raw1523step0 = (fun i j => raw1523 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1523step0 raw1523; decide +kernel
      have hl : raw1523step0Labels = raw1523Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1523 raw1523Labels permutation34 permutation6
    mixedMoment B raw1523step0 raw1523step0Labels = mixedMoment B raw1523step1 raw1523step1Labels := by
      have ha : raw1523step1 = -raw1523step0 := by apply Matrix.ext; change ∀ i j, raw1523step1 i j = -(raw1523step0 i j); unfold raw1523step1 raw1523step0; decide +kernel
      have hl : raw1523step1Labels = raw1523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1523step1 raw1523step1Labels = mixedMoment B raw1523step2 raw1523step2Labels := by
      have ha : raw1523step2 = raw1523step1 := by apply Matrix.ext; unfold raw1523step2 raw1523step1; decide +kernel
      have hl : raw1523step1Labels = labelEmbedding1 ∘ raw1523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1523step1 raw1523step1Labels raw1523step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1846 node1846Labels := by rfl

theorem canonical1530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1530 raw1530Labels = mixedMoment B node4658 node4658Labels := by
  calc
    mixedMoment B raw1530 raw1530Labels = mixedMoment B raw1530step0 raw1530step0Labels := by
      have ha : raw1530step0 = (fun i j => raw1530 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1530step0 raw1530; decide +kernel
      have hl : raw1530step0Labels = raw1530Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1530 raw1530Labels permutation152 permutation4
    mixedMoment B raw1530step0 raw1530step0Labels = mixedMoment B raw1530step1 raw1530step1Labels := by
      have ha : raw1530step1 = raw1530step0 := by apply Matrix.ext; unfold raw1530step1 raw1530step0; decide +kernel
      have hl : raw1530step0Labels = labelEmbedding7 ∘ raw1530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1530step0 raw1530step0Labels raw1530step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4658 node4658Labels := by rfl

theorem canonical1531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1531 raw1531Labels = mixedMoment B node1784 node1784Labels := by
  calc
    mixedMoment B raw1531 raw1531Labels = mixedMoment B raw1531step0 raw1531step0Labels := by
      have ha : raw1531step0 = (fun i j => raw1531 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1531step0 raw1531; decide +kernel
      have hl : raw1531step0Labels = raw1531Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1531 raw1531Labels permutation152 permutation4
    _ = mixedMoment B node1784 node1784Labels := by rfl

theorem canonical1532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1532 raw1532Labels = mixedMoment B node1884 node1884Labels := by
  calc
    mixedMoment B raw1532 raw1532Labels = mixedMoment B raw1532step0 raw1532step0Labels := by
      have ha : raw1532step0 = (fun i j => raw1532 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1532step0 raw1532; decide +kernel
      have hl : raw1532step0Labels = raw1532Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1532 raw1532Labels permutation686 permutation6
    mixedMoment B raw1532step0 raw1532step0Labels = mixedMoment B raw1532step1 raw1532step1Labels := by
      have ha : raw1532step1 = raw1532step0 := by apply Matrix.ext; unfold raw1532step1 raw1532step0; decide +kernel
      have hl : raw1532step0Labels = labelEmbedding1 ∘ raw1532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1532step0 raw1532step0Labels raw1532step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1884 node1884Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1557 raw1557Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw1557 raw1557Labels = mixedMoment B raw1557step0 raw1557step0Labels := by
      have ha : raw1557step0 = (fun i j => raw1557 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1557step0 raw1557; decide +kernel
      have hl : raw1557step0Labels = raw1557Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1557 raw1557Labels permutation32 permutation4
    mixedMoment B raw1557step0 raw1557step0Labels = mixedMoment B raw1557step1 raw1557step1Labels := by
      have ha : raw1557step1 = raw1557step0 := by apply Matrix.ext; unfold raw1557step1 raw1557step0; decide +kernel
      have hl : raw1557step0Labels = labelEmbedding7 ∘ raw1557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1557step0 raw1557step0Labels raw1557step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4678 node4678Labels := by rfl

theorem canonical1558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1558 raw1558Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw1558 raw1558Labels = mixedMoment B raw1558step0 raw1558step0Labels := by
      have ha : raw1558step0 = (fun i j => raw1558 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1558step0 raw1558; decide +kernel
      have hl : raw1558step0Labels = raw1558Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1558 raw1558Labels permutation32 permutation4
    _ = mixedMoment B node1804 node1804Labels := by rfl

theorem canonical1559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1559 raw1559Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw1559 raw1559Labels = mixedMoment B raw1559step0 raw1559step0Labels := by
      have ha : raw1559step0 = (fun i j => raw1559 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1559step0 raw1559; decide +kernel
      have hl : raw1559step0Labels = raw1559Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1559 raw1559Labels permutation32 permutation6
    mixedMoment B raw1559step0 raw1559step0Labels = mixedMoment B raw1559step1 raw1559step1Labels := by
      have ha : raw1559step1 = -raw1559step0 := by apply Matrix.ext; change ∀ i j, raw1559step1 i j = -(raw1559step0 i j); unfold raw1559step1 raw1559step0; decide +kernel
      have hl : raw1559step1Labels = raw1559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1559step1 raw1559step1Labels = mixedMoment B raw1559step2 raw1559step2Labels := by
      have ha : raw1559step2 = raw1559step1 := by apply Matrix.ext; unfold raw1559step2 raw1559step1; decide +kernel
      have hl : raw1559step1Labels = labelEmbedding1 ∘ raw1559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1559step1 raw1559step1Labels raw1559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

theorem canonical1593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1593 raw1593Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw1593 raw1593Labels = mixedMoment B raw1593step0 raw1593step0Labels := by
      have ha : raw1593step0 = (fun i j => raw1593 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1593step0 raw1593; decide +kernel
      have hl : raw1593step0Labels = raw1593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1593 raw1593Labels permutation152 permutation4
    mixedMoment B raw1593step0 raw1593step0Labels = mixedMoment B raw1593step1 raw1593step1Labels := by
      have ha : raw1593step1 = raw1593step0 := by apply Matrix.ext; unfold raw1593step1 raw1593step0; decide +kernel
      have hl : raw1593step0Labels = labelEmbedding7 ∘ raw1593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1593step0 raw1593step0Labels raw1593step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

theorem canonical1594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1594 raw1594Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw1594 raw1594Labels = mixedMoment B raw1594step0 raw1594step0Labels := by
      have ha : raw1594step0 = (fun i j => raw1594 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1594step0 raw1594; decide +kernel
      have hl : raw1594step0Labels = raw1594Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1594 raw1594Labels permutation152 permutation4
    _ = mixedMoment B node1861 node1861Labels := by rfl

theorem canonical1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1595 raw1595Labels = mixedMoment B node1889 node1889Labels := by
  calc
    mixedMoment B raw1595 raw1595Labels = mixedMoment B raw1595step0 raw1595step0Labels := by
      have ha : raw1595step0 = (fun i j => raw1595 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1595step0 raw1595; decide +kernel
      have hl : raw1595step0Labels = raw1595Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1595 raw1595Labels permutation153 permutation6
    mixedMoment B raw1595step0 raw1595step0Labels = mixedMoment B raw1595step1 raw1595step1Labels := by
      have ha : raw1595step1 = -raw1595step0 := by apply Matrix.ext; change ∀ i j, raw1595step1 i j = -(raw1595step0 i j); unfold raw1595step1 raw1595step0; decide +kernel
      have hl : raw1595step1Labels = raw1595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1595step1 raw1595step1Labels = mixedMoment B raw1595step2 raw1595step2Labels := by
      have ha : raw1595step2 = raw1595step1 := by apply Matrix.ext; unfold raw1595step2 raw1595step1; decide +kernel
      have hl : raw1595step1Labels = labelEmbedding1 ∘ raw1595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1595step1 raw1595step1Labels raw1595step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1889 node1889Labels := by rfl

theorem canonical1608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1608 raw1608Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw1608 raw1608Labels = mixedMoment B raw1608step0 raw1608step0Labels := by
      have ha : raw1608step0 = (fun i j => raw1608 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1608step0 raw1608; decide +kernel
      have hl : raw1608step0Labels = raw1608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1608 raw1608Labels permutation152 permutation4
    mixedMoment B raw1608step0 raw1608step0Labels = mixedMoment B raw1608step1 raw1608step1Labels := by
      have ha : raw1608step1 = raw1608step0 := by apply Matrix.ext; unfold raw1608step1 raw1608step0; decide +kernel
      have hl : raw1608step0Labels = labelEmbedding7 ∘ raw1608step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1608step0 raw1608step0Labels raw1608step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

theorem canonical1609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1609 raw1609Labels = mixedMoment B node1870 node1870Labels := by
  calc
    mixedMoment B raw1609 raw1609Labels = mixedMoment B raw1609step0 raw1609step0Labels := by
      have ha : raw1609step0 = (fun i j => raw1609 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1609step0 raw1609; decide +kernel
      have hl : raw1609step0Labels = raw1609Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1609 raw1609Labels permutation152 permutation4
    _ = mixedMoment B node1870 node1870Labels := by rfl

theorem canonical1610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1610 raw1610Labels = mixedMoment B node1886 node1886Labels := by
  calc
    mixedMoment B raw1610 raw1610Labels = mixedMoment B raw1610step0 raw1610step0Labels := by
      have ha : raw1610step0 = (fun i j => raw1610 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1610step0 raw1610; decide +kernel
      have hl : raw1610step0Labels = raw1610Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1610 raw1610Labels permutation154 permutation6
    mixedMoment B raw1610step0 raw1610step0Labels = mixedMoment B raw1610step1 raw1610step1Labels := by
      have ha : raw1610step1 = -raw1610step0 := by apply Matrix.ext; change ∀ i j, raw1610step1 i j = -(raw1610step0 i j); unfold raw1610step1 raw1610step0; decide +kernel
      have hl : raw1610step1Labels = raw1610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1610step1 raw1610step1Labels = mixedMoment B raw1610step2 raw1610step2Labels := by
      have ha : raw1610step2 = raw1610step1 := by apply Matrix.ext; unfold raw1610step2 raw1610step1; decide +kernel
      have hl : raw1610step1Labels = labelEmbedding1 ∘ raw1610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1610step1 raw1610step1Labels raw1610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1886 node1886Labels := by rfl

theorem canonical1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1647 raw1647Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw1647 raw1647Labels = mixedMoment B raw1647step0 raw1647step0Labels := by
      have ha : raw1647step0 = (fun i j => raw1647 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1647step0 raw1647; decide +kernel
      have hl : raw1647step0Labels = raw1647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1647 raw1647Labels permutation152 permutation4
    mixedMoment B raw1647step0 raw1647step0Labels = mixedMoment B raw1647step1 raw1647step1Labels := by
      have ha : raw1647step1 = raw1647step0 := by apply Matrix.ext; unfold raw1647step1 raw1647step0; decide +kernel
      have hl : raw1647step0Labels = labelEmbedding7 ∘ raw1647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1647step0 raw1647step0Labels raw1647step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

theorem canonical1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1648 raw1648Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw1648 raw1648Labels = mixedMoment B raw1648step0 raw1648step0Labels := by
      have ha : raw1648step0 = (fun i j => raw1648 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1648step0 raw1648; decide +kernel
      have hl : raw1648step0Labels = raw1648Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1648 raw1648Labels permutation152 permutation4
    _ = mixedMoment B node1900 node1900Labels := by rfl

theorem canonical1649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1649 raw1649Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw1649 raw1649Labels = mixedMoment B raw1649step0 raw1649step0Labels := by
      have ha : raw1649step0 = (fun i j => raw1649 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1649step0 raw1649; decide +kernel
      have hl : raw1649step0Labels = raw1649Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1649 raw1649Labels permutation164 permutation6
    mixedMoment B raw1649step0 raw1649step0Labels = mixedMoment B raw1649step1 raw1649step1Labels := by
      have ha : raw1649step1 = -raw1649step0 := by apply Matrix.ext; change ∀ i j, raw1649step1 i j = -(raw1649step0 i j); unfold raw1649step1 raw1649step0; decide +kernel
      have hl : raw1649step1Labels = raw1649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1649step1 raw1649step1Labels = mixedMoment B raw1649step2 raw1649step2Labels := by
      have ha : raw1649step2 = raw1649step1 := by apply Matrix.ext; unfold raw1649step2 raw1649step1; decide +kernel
      have hl : raw1649step1Labels = labelEmbedding1 ∘ raw1649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1649step1 raw1649step1Labels raw1649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1921 node1921Labels := by rfl

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

theorem canonical1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1707 raw1707Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw1707 raw1707Labels = mixedMoment B raw1707step0 raw1707step0Labels := by
      have ha : raw1707step0 = (fun i j => raw1707 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1707step0 raw1707; decide +kernel
      have hl : raw1707step0Labels = raw1707Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1707 raw1707Labels permutation32 permutation4
    mixedMoment B raw1707step0 raw1707step0Labels = mixedMoment B raw1707step1 raw1707step1Labels := by
      have ha : raw1707step1 = raw1707step0 := by apply Matrix.ext; unfold raw1707step1 raw1707step0; decide +kernel
      have hl : raw1707step0Labels = labelEmbedding7 ∘ raw1707step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1707step0 raw1707step0Labels raw1707step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1708 raw1708Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw1708 raw1708Labels = mixedMoment B raw1708step0 raw1708step0Labels := by
      have ha : raw1708step0 = (fun i j => raw1708 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1708step0 raw1708; decide +kernel
      have hl : raw1708step0Labels = raw1708Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1708 raw1708Labels permutation32 permutation4
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1709 raw1709Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw1709 raw1709Labels = mixedMoment B raw1709step0 raw1709step0Labels := by
      have ha : raw1709step0 = (fun i j => raw1709 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1709step0 raw1709; decide +kernel
      have hl : raw1709step0Labels = raw1709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1709 raw1709Labels permutation33 permutation6
    mixedMoment B raw1709step0 raw1709step0Labels = mixedMoment B raw1709step1 raw1709step1Labels := by
      have ha : raw1709step1 = -raw1709step0 := by apply Matrix.ext; change ∀ i j, raw1709step1 i j = -(raw1709step0 i j); unfold raw1709step1 raw1709step0; decide +kernel
      have hl : raw1709step1Labels = raw1709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1709step1 raw1709step1Labels = mixedMoment B raw1709step2 raw1709step2Labels := by
      have ha : raw1709step2 = raw1709step1 := by apply Matrix.ext; unfold raw1709step2 raw1709step1; decide +kernel
      have hl : raw1709step1Labels = labelEmbedding1 ∘ raw1709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1709step1 raw1709step1Labels raw1709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

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

theorem canonical1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1728 raw1728Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw1728 raw1728Labels = mixedMoment B raw1728step0 raw1728step0Labels := by
      have ha : raw1728step0 = (fun i j => raw1728 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1728step0 raw1728; decide +kernel
      have hl : raw1728step0Labels = raw1728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1728 raw1728Labels permutation32 permutation4
    mixedMoment B raw1728step0 raw1728step0Labels = mixedMoment B raw1728step1 raw1728step1Labels := by
      have ha : raw1728step1 = raw1728step0 := by apply Matrix.ext; unfold raw1728step1 raw1728step0; decide +kernel
      have hl : raw1728step0Labels = labelEmbedding7 ∘ raw1728step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1728step0 raw1728step0Labels raw1728step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

theorem canonical1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1729 raw1729Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw1729 raw1729Labels = mixedMoment B raw1729step0 raw1729step0Labels := by
      have ha : raw1729step0 = (fun i j => raw1729 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1729step0 raw1729; decide +kernel
      have hl : raw1729step0Labels = raw1729Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1729 raw1729Labels permutation32 permutation4
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1730 raw1730Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw1730 raw1730Labels = mixedMoment B raw1730step0 raw1730step0Labels := by
      have ha : raw1730step0 = (fun i j => raw1730 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1730step0 raw1730; decide +kernel
      have hl : raw1730step0Labels = raw1730Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1730 raw1730Labels permutation143 permutation6
    mixedMoment B raw1730step0 raw1730step0Labels = mixedMoment B raw1730step1 raw1730step1Labels := by
      have ha : raw1730step1 = raw1730step0 := by apply Matrix.ext; unfold raw1730step1 raw1730step0; decide +kernel
      have hl : raw1730step0Labels = labelEmbedding1 ∘ raw1730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1730step0 raw1730step0Labels raw1730step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1740 raw1740Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw1740 raw1740Labels = mixedMoment B raw1740step0 raw1740step0Labels := by
      have ha : raw1740step0 = (fun i j => raw1740 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1740step0 raw1740; decide +kernel
      have hl : raw1740step0Labels = raw1740Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1740 raw1740Labels permutation152 permutation4
    mixedMoment B raw1740step0 raw1740step0Labels = mixedMoment B raw1740step1 raw1740step1Labels := by
      have ha : raw1740step1 = raw1740step0 := by apply Matrix.ext; unfold raw1740step1 raw1740step0; decide +kernel
      have hl : raw1740step0Labels = labelEmbedding7 ∘ raw1740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1740step0 raw1740step0Labels raw1740step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1741 raw1741Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw1741 raw1741Labels = mixedMoment B raw1741step0 raw1741step0Labels := by
      have ha : raw1741step0 = (fun i j => raw1741 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1741step0 raw1741; decide +kernel
      have hl : raw1741step0Labels = raw1741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1741 raw1741Labels permutation152 permutation4
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1742 raw1742Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw1742 raw1742Labels = mixedMoment B raw1742step0 raw1742step0Labels := by
      have ha : raw1742step0 = (fun i j => raw1742 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1742step0 raw1742; decide +kernel
      have hl : raw1742step0Labels = raw1742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1742 raw1742Labels permutation170 permutation6
    mixedMoment B raw1742step0 raw1742step0Labels = mixedMoment B raw1742step1 raw1742step1Labels := by
      have ha : raw1742step1 = -raw1742step0 := by apply Matrix.ext; change ∀ i j, raw1742step1 i j = -(raw1742step0 i j); unfold raw1742step1 raw1742step0; decide +kernel
      have hl : raw1742step1Labels = raw1742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1742step1 raw1742step1Labels = mixedMoment B raw1742step2 raw1742step2Labels := by
      have ha : raw1742step2 = raw1742step1 := by apply Matrix.ext; unfold raw1742step2 raw1742step1; decide +kernel
      have hl : raw1742step1Labels = labelEmbedding1 ∘ raw1742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1742step1 raw1742step1Labels raw1742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

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

theorem canonical1758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1758 raw1758Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw1758 raw1758Labels = mixedMoment B raw1758step0 raw1758step0Labels := by
      have ha : raw1758step0 = (fun i j => raw1758 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1758step0 raw1758; decide +kernel
      have hl : raw1758step0Labels = raw1758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1758 raw1758Labels permutation32 permutation4
    mixedMoment B raw1758step0 raw1758step0Labels = mixedMoment B raw1758step1 raw1758step1Labels := by
      have ha : raw1758step1 = raw1758step0 := by apply Matrix.ext; unfold raw1758step1 raw1758step0; decide +kernel
      have hl : raw1758step0Labels = labelEmbedding7 ∘ raw1758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1758step0 raw1758step0Labels raw1758step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical1759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1759 raw1759Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw1759 raw1759Labels = mixedMoment B raw1759step0 raw1759step0Labels := by
      have ha : raw1759step0 = (fun i j => raw1759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1759step0 raw1759; decide +kernel
      have hl : raw1759step0Labels = raw1759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1759 raw1759Labels permutation32 permutation4
    _ = mixedMoment B node2048 node2048Labels := by rfl

theorem canonical1760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1760 raw1760Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw1760 raw1760Labels = mixedMoment B raw1760step0 raw1760step0Labels := by
      have ha : raw1760step0 = (fun i j => raw1760 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1760step0 raw1760; decide +kernel
      have hl : raw1760step0Labels = raw1760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1760 raw1760Labels permutation38 permutation6
    mixedMoment B raw1760step0 raw1760step0Labels = mixedMoment B raw1760step1 raw1760step1Labels := by
      have ha : raw1760step1 = -raw1760step0 := by apply Matrix.ext; change ∀ i j, raw1760step1 i j = -(raw1760step0 i j); unfold raw1760step1 raw1760step0; decide +kernel
      have hl : raw1760step1Labels = raw1760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1760step1 raw1760step1Labels = mixedMoment B raw1760step2 raw1760step2Labels := by
      have ha : raw1760step2 = raw1760step1 := by apply Matrix.ext; unfold raw1760step2 raw1760step1; decide +kernel
      have hl : raw1760step1Labels = labelEmbedding1 ∘ raw1760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1760step1 raw1760step1Labels raw1760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2082 node2082Labels := by rfl

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

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

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

theorem canonical2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2400 raw2400Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw2400 raw2400Labels = mixedMoment B raw2400step0 raw2400step0Labels := by
      have ha : raw2400step0 = (fun i j => raw2400 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2400step0 raw2400; decide +kernel
      have hl : raw2400step0Labels = raw2400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2400 raw2400Labels permutation32 permutation4
    mixedMoment B raw2400step0 raw2400step0Labels = mixedMoment B raw2400step1 raw2400step1Labels := by
      have ha : raw2400step1 = raw2400step0 := by apply Matrix.ext; unfold raw2400step1 raw2400step0; decide +kernel
      have hl : raw2400step0Labels = labelEmbedding7 ∘ raw2400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2400step0 raw2400step0Labels raw2400step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2401 raw2401Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw2401 raw2401Labels = mixedMoment B raw2401step0 raw2401step0Labels := by
      have ha : raw2401step0 = (fun i j => raw2401 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2401step0 raw2401; decide +kernel
      have hl : raw2401step0Labels = raw2401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2401 raw2401Labels permutation32 permutation4
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2402 raw2402Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw2402 raw2402Labels = mixedMoment B raw2402step0 raw2402step0Labels := by
      have ha : raw2402step0 = (fun i j => raw2402 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2402step0 raw2402; decide +kernel
      have hl : raw2402step0Labels = raw2402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2402 raw2402Labels permutation34 permutation6
    mixedMoment B raw2402step0 raw2402step0Labels = mixedMoment B raw2402step1 raw2402step1Labels := by
      have ha : raw2402step1 = -raw2402step0 := by apply Matrix.ext; change ∀ i j, raw2402step1 i j = -(raw2402step0 i j); unfold raw2402step1 raw2402step0; decide +kernel
      have hl : raw2402step1Labels = raw2402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2402step1 raw2402step1Labels = mixedMoment B raw2402step2 raw2402step2Labels := by
      have ha : raw2402step2 = raw2402step1 := by apply Matrix.ext; unfold raw2402step2 raw2402step1; decide +kernel
      have hl : raw2402step1Labels = labelEmbedding1 ∘ raw2402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2402step1 raw2402step1Labels raw2402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

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

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical2523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2523 raw2523Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw2523 raw2523Labels = mixedMoment B raw2523step0 raw2523step0Labels := by
      have ha : raw2523step0 = (fun i j => raw2523 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2523step0 raw2523; decide +kernel
      have hl : raw2523step0Labels = raw2523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2523 raw2523Labels permutation32 permutation4
    mixedMoment B raw2523step0 raw2523step0Labels = mixedMoment B raw2523step1 raw2523step1Labels := by
      have ha : raw2523step1 = raw2523step0 := by apply Matrix.ext; unfold raw2523step1 raw2523step0; decide +kernel
      have hl : raw2523step0Labels = labelEmbedding7 ∘ raw2523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2523step0 raw2523step0Labels raw2523step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2524 raw2524Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2524 raw2524Labels = mixedMoment B raw2524step0 raw2524step0Labels := by
      have ha : raw2524step0 = (fun i j => raw2524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2524step0 raw2524; decide +kernel
      have hl : raw2524step0Labels = raw2524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2524 raw2524Labels permutation32 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical2525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2525 raw2525Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2525 raw2525Labels = mixedMoment B raw2525step0 raw2525step0Labels := by
      have ha : raw2525step0 = (fun i j => raw2525 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2525step0 raw2525; decide +kernel
      have hl : raw2525step0Labels = raw2525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2525 raw2525Labels permutation143 permutation6
    mixedMoment B raw2525step0 raw2525step0Labels = mixedMoment B raw2525step1 raw2525step1Labels := by
      have ha : raw2525step1 = raw2525step0 := by apply Matrix.ext; unfold raw2525step1 raw2525step0; decide +kernel
      have hl : raw2525step0Labels = labelEmbedding1 ∘ raw2525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2525step0 raw2525step0Labels raw2525step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31380 raw31380Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw31380 raw31380Labels = mixedMoment B raw31380step0 raw31380step0Labels := by
      have hz : ∀ j, raw31380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31380step0 = (fun i j => raw31380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31380step0 raw31380; decide +kernel
      have hl : raw31380step0Labels = raw31380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31380 raw31380Labels permutation434 hz
    mixedMoment B raw31380step0 raw31380step0Labels = mixedMoment B raw31380step1 raw31380step1Labels := by
      have ha : raw31380step1 = (fun i j => raw31380step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31380step1 raw31380step0; decide +kernel
      have hl : raw31380step1Labels = raw31380step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31380step0 raw31380step0Labels permutation33 permutation3
    mixedMoment B raw31380step1 raw31380step1Labels = mixedMoment B raw31380step2 raw31380step2Labels := by
      have ha : raw31380step2 = raw31380step1 := by apply Matrix.ext; unfold raw31380step2 raw31380step1; decide +kernel
      have hl : raw31380step1Labels = labelEmbedding6 ∘ raw31380step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31380step1 raw31380step1Labels raw31380step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical31381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31381 raw31381Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw31381 raw31381Labels = mixedMoment B raw31381step0 raw31381step0Labels := by
      have hz : ∀ j, raw31381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31381step0 = (fun i j => raw31381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31381step0 raw31381; decide +kernel
      have hl : raw31381step0Labels = raw31381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31381 raw31381Labels permutation434 hz
    mixedMoment B raw31381step0 raw31381step0Labels = mixedMoment B raw31381step1 raw31381step1Labels := by
      have ha : raw31381step1 = (fun i j => raw31381step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31381step1 raw31381step0; decide +kernel
      have hl : raw31381step1Labels = raw31381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31381step0 raw31381step0Labels permutation125 permutation3
    mixedMoment B raw31381step1 raw31381step1Labels = mixedMoment B raw31381step2 raw31381step2Labels := by
      have ha : raw31381step2 = -raw31381step1 := by apply Matrix.ext; change ∀ i j, raw31381step2 i j = -(raw31381step1 i j); unfold raw31381step2 raw31381step1; decide +kernel
      have hl : raw31381step2Labels = raw31381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31381step2 raw31381step2Labels = mixedMoment B raw31381step3 raw31381step3Labels := by
      have ha : raw31381step3 = raw31381step2 := by apply Matrix.ext; unfold raw31381step3 raw31381step2; decide +kernel
      have hl : raw31381step2Labels = labelEmbedding6 ∘ raw31381step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31381step2 raw31381step2Labels raw31381step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

theorem canonical31382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31382 raw31382Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw31382 raw31382Labels = mixedMoment B raw31382step0 raw31382step0Labels := by
      have ha : raw31382step0 = (fun i j => raw31382 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31382step0 raw31382; decide +kernel
      have hl : raw31382step0Labels = raw31382Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31382 raw31382Labels permutation582 permutation3
    mixedMoment B raw31382step0 raw31382step0Labels = mixedMoment B raw31382step1 raw31382step1Labels := by
      have ha : raw31382step1 = -raw31382step0 := by apply Matrix.ext; change ∀ i j, raw31382step1 i j = -(raw31382step0 i j); unfold raw31382step1 raw31382step0; decide +kernel
      have hl : raw31382step1Labels = raw31382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31382step1 raw31382step1Labels = mixedMoment B raw31382step2 raw31382step2Labels := by
      have ha : raw31382step2 = raw31382step1 := by apply Matrix.ext; unfold raw31382step2 raw31382step1; decide +kernel
      have hl : raw31382step1Labels = labelEmbedding6 ∘ raw31382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31382step1 raw31382step1Labels raw31382step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical31383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31383 raw31383Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw31383 raw31383Labels = mixedMoment B raw31383step0 raw31383step0Labels := by
      have hz : ∀ j, raw31383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31383step0 = (fun i j => raw31383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31383step0 raw31383; decide +kernel
      have hl : raw31383step0Labels = raw31383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31383 raw31383Labels permutation434 hz
    mixedMoment B raw31383step0 raw31383step0Labels = mixedMoment B raw31383step1 raw31383step1Labels := by
      have ha : raw31383step1 = (fun i j => raw31383step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31383step1 raw31383step0; decide +kernel
      have hl : raw31383step1Labels = raw31383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31383step0 raw31383step0Labels permutation33 permutation3
    mixedMoment B raw31383step1 raw31383step1Labels = mixedMoment B raw31383step2 raw31383step2Labels := by
      have ha : raw31383step2 = raw31383step1 := by apply Matrix.ext; unfold raw31383step2 raw31383step1; decide +kernel
      have hl : raw31383step1Labels = labelEmbedding6 ∘ raw31383step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31383step1 raw31383step1Labels raw31383step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical31384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31384 raw31384Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw31384 raw31384Labels = mixedMoment B raw31384step0 raw31384step0Labels := by
      have hz : ∀ j, raw31384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31384step0 = (fun i j => raw31384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31384step0 raw31384; decide +kernel
      have hl : raw31384step0Labels = raw31384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31384 raw31384Labels permutation434 hz
    mixedMoment B raw31384step0 raw31384step0Labels = mixedMoment B raw31384step1 raw31384step1Labels := by
      have ha : raw31384step1 = (fun i j => raw31384step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31384step1 raw31384step0; decide +kernel
      have hl : raw31384step1Labels = raw31384step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31384step0 raw31384step0Labels permutation32 permutation3
    mixedMoment B raw31384step1 raw31384step1Labels = mixedMoment B raw31384step2 raw31384step2Labels := by
      have ha : raw31384step2 = raw31384step1 := by apply Matrix.ext; unfold raw31384step2 raw31384step1; decide +kernel
      have hl : raw31384step1Labels = labelEmbedding6 ∘ raw31384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31384step1 raw31384step1Labels raw31384step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical31385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31385 raw31385Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw31385 raw31385Labels = mixedMoment B raw31385step0 raw31385step0Labels := by
      have hz : ∀ j, raw31385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31385step0 = (fun i j => raw31385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31385step0 raw31385; decide +kernel
      have hl : raw31385step0Labels = raw31385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31385 raw31385Labels permutation434 hz
    mixedMoment B raw31385step0 raw31385step0Labels = mixedMoment B raw31385step1 raw31385step1Labels := by
      have ha : raw31385step1 = (fun i j => raw31385step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31385step1 raw31385step0; decide +kernel
      have hl : raw31385step1Labels = raw31385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31385step0 raw31385step0Labels permutation33 permutation3
    mixedMoment B raw31385step1 raw31385step1Labels = mixedMoment B raw31385step2 raw31385step2Labels := by
      have ha : raw31385step2 = raw31385step1 := by apply Matrix.ext; unfold raw31385step2 raw31385step1; decide +kernel
      have hl : raw31385step1Labels = labelEmbedding6 ∘ raw31385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31385step1 raw31385step1Labels raw31385step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

theorem canonical31386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31386 raw31386Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw31386 raw31386Labels = mixedMoment B raw31386step0 raw31386step0Labels := by
      have hz : ∀ j, raw31386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31386step0 = (fun i j => raw31386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31386step0 raw31386; decide +kernel
      have hl : raw31386step0Labels = raw31386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31386 raw31386Labels permutation434 hz
    mixedMoment B raw31386step0 raw31386step0Labels = mixedMoment B raw31386step1 raw31386step1Labels := by
      have ha : raw31386step1 = (fun i j => raw31386step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31386step1 raw31386step0; decide +kernel
      have hl : raw31386step1Labels = raw31386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31386step0 raw31386step0Labels permutation33 permutation3
    mixedMoment B raw31386step1 raw31386step1Labels = mixedMoment B raw31386step2 raw31386step2Labels := by
      have ha : raw31386step2 = raw31386step1 := by apply Matrix.ext; unfold raw31386step2 raw31386step1; decide +kernel
      have hl : raw31386step1Labels = labelEmbedding6 ∘ raw31386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31386step1 raw31386step1Labels raw31386step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

theorem canonical31387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31387 raw31387Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw31387 raw31387Labels = mixedMoment B raw31387step0 raw31387step0Labels := by
      have ha : raw31387step0 = (fun i j => raw31387 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31387step0 raw31387; decide +kernel
      have hl : raw31387step0Labels = raw31387Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31387 raw31387Labels permutation201 permutation3
    mixedMoment B raw31387step0 raw31387step0Labels = mixedMoment B raw31387step1 raw31387step1Labels := by
      have ha : raw31387step1 = raw31387step0 := by apply Matrix.ext; unfold raw31387step1 raw31387step0; decide +kernel
      have hl : raw31387step0Labels = labelEmbedding6 ∘ raw31387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31387step0 raw31387step0Labels raw31387step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

theorem canonical31388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31388 raw31388Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31388 raw31388Labels = mixedMoment B raw31388step0 raw31388step0Labels := by
      have hz : ∀ j, raw31388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31388step0 = (fun i j => raw31388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31388step0 raw31388; decide +kernel
      have hl : raw31388step0Labels = raw31388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31388 raw31388Labels permutation434 hz
    mixedMoment B raw31388step0 raw31388step0Labels = mixedMoment B raw31388step1 raw31388step1Labels := by
      have ha : raw31388step1 = (fun i j => raw31388step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31388step1 raw31388step0; decide +kernel
      have hl : raw31388step1Labels = raw31388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31388step0 raw31388step0Labels permutation36 permutation3
    mixedMoment B raw31388step1 raw31388step1Labels = mixedMoment B raw31388step2 raw31388step2Labels := by
      have ha : raw31388step2 = raw31388step1 := by apply Matrix.ext; unfold raw31388step2 raw31388step1; decide +kernel
      have hl : raw31388step1Labels = labelEmbedding6 ∘ raw31388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31388step1 raw31388step1Labels raw31388step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical31389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31389 raw31389Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw31389 raw31389Labels = mixedMoment B raw31389step0 raw31389step0Labels := by
      have ha : raw31389step0 = (fun i j => raw31389 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31389step0 raw31389; decide +kernel
      have hl : raw31389step0Labels = raw31389Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31389 raw31389Labels permutation153 permutation3
    mixedMoment B raw31389step0 raw31389step0Labels = mixedMoment B raw31389step1 raw31389step1Labels := by
      have ha : raw31389step1 = raw31389step0 := by apply Matrix.ext; unfold raw31389step1 raw31389step0; decide +kernel
      have hl : raw31389step0Labels = labelEmbedding6 ∘ raw31389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31389step0 raw31389step0Labels raw31389step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4200 node4200Labels := by rfl

theorem canonical31390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31390 raw31390Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw31390 raw31390Labels = mixedMoment B raw31390step0 raw31390step0Labels := by
      have ha : raw31390step0 = (fun i j => raw31390 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31390step0 raw31390; decide +kernel
      have hl : raw31390step0Labels = raw31390Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31390 raw31390Labels permutation153 permutation3
    mixedMoment B raw31390step0 raw31390step0Labels = mixedMoment B raw31390step1 raw31390step1Labels := by
      have ha : raw31390step1 = raw31390step0 := by apply Matrix.ext; unfold raw31390step1 raw31390step0; decide +kernel
      have hl : raw31390step0Labels = labelEmbedding6 ∘ raw31390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31390step0 raw31390step0Labels raw31390step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

theorem canonical31391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31391 raw31391Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw31391 raw31391Labels = mixedMoment B raw31391step0 raw31391step0Labels := by
      have ha : raw31391step0 = (fun i j => raw31391 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31391step0 raw31391; decide +kernel
      have hl : raw31391step0Labels = raw31391Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31391 raw31391Labels permutation153 permutation3
    mixedMoment B raw31391step0 raw31391step0Labels = mixedMoment B raw31391step1 raw31391step1Labels := by
      have ha : raw31391step1 = raw31391step0 := by apply Matrix.ext; unfold raw31391step1 raw31391step0; decide +kernel
      have hl : raw31391step0Labels = labelEmbedding6 ∘ raw31391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31391step0 raw31391step0Labels raw31391step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

theorem canonical31392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31392 raw31392Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw31392 raw31392Labels = mixedMoment B raw31392step0 raw31392step0Labels := by
      have ha : raw31392step0 = (fun i j => raw31392 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31392step0 raw31392; decide +kernel
      have hl : raw31392step0Labels = raw31392Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31392 raw31392Labels permutation156 permutation3
    mixedMoment B raw31392step0 raw31392step0Labels = mixedMoment B raw31392step1 raw31392step1Labels := by
      have ha : raw31392step1 = raw31392step0 := by apply Matrix.ext; unfold raw31392step1 raw31392step0; decide +kernel
      have hl : raw31392step0Labels = labelEmbedding6 ∘ raw31392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31392step0 raw31392step0Labels raw31392step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical31393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31393 raw31393Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw31393 raw31393Labels = mixedMoment B raw31393step0 raw31393step0Labels := by
      have hz : ∀ j, raw31393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31393step0 = (fun i j => raw31393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31393step0 raw31393; decide +kernel
      have hl : raw31393step0Labels = raw31393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31393 raw31393Labels permutation434 hz
    mixedMoment B raw31393step0 raw31393step0Labels = mixedMoment B raw31393step1 raw31393step1Labels := by
      have ha : raw31393step1 = (fun i j => raw31393step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31393step1 raw31393step0; decide +kernel
      have hl : raw31393step1Labels = raw31393step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31393step0 raw31393step0Labels permutation33 permutation3
    mixedMoment B raw31393step1 raw31393step1Labels = mixedMoment B raw31393step2 raw31393step2Labels := by
      have ha : raw31393step2 = raw31393step1 := by apply Matrix.ext; unfold raw31393step2 raw31393step1; decide +kernel
      have hl : raw31393step1Labels = labelEmbedding6 ∘ raw31393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31393step1 raw31393step1Labels raw31393step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4203 node4203Labels := by rfl

theorem canonical31394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31394 raw31394Labels = mixedMoment B node4636 node4636Labels := by
  calc
    mixedMoment B raw31394 raw31394Labels = mixedMoment B raw31394step0 raw31394step0Labels := by
      have hz : ∀ j, raw31394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31394step0 = (fun i j => raw31394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31394step0 raw31394; decide +kernel
      have hl : raw31394step0Labels = raw31394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31394 raw31394Labels permutation434 hz
    mixedMoment B raw31394step0 raw31394step0Labels = mixedMoment B raw31394step1 raw31394step1Labels := by
      have ha : raw31394step1 = (fun i j => raw31394step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31394step1 raw31394step0; decide +kernel
      have hl : raw31394step1Labels = raw31394step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31394step0 raw31394step0Labels permutation33 permutation3
    mixedMoment B raw31394step1 raw31394step1Labels = mixedMoment B raw31394step2 raw31394step2Labels := by
      have ha : raw31394step2 = raw31394step1 := by apply Matrix.ext; unfold raw31394step2 raw31394step1; decide +kernel
      have hl : raw31394step1Labels = labelEmbedding6 ∘ raw31394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31394step1 raw31394step1Labels raw31394step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4636 node4636Labels := by rfl

theorem canonical31395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31395 raw31395Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw31395 raw31395Labels = mixedMoment B raw31395step0 raw31395step0Labels := by
      have hz : ∀ j, raw31395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31395step0 = (fun i j => raw31395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31395step0 raw31395; decide +kernel
      have hl : raw31395step0Labels = raw31395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31395 raw31395Labels permutation434 hz
    mixedMoment B raw31395step0 raw31395step0Labels = mixedMoment B raw31395step1 raw31395step1Labels := by
      have ha : raw31395step1 = (fun i j => raw31395step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31395step1 raw31395step0; decide +kernel
      have hl : raw31395step1Labels = raw31395step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31395step0 raw31395step0Labels permutation125 permutation3
    mixedMoment B raw31395step1 raw31395step1Labels = mixedMoment B raw31395step2 raw31395step2Labels := by
      have ha : raw31395step2 = -raw31395step1 := by apply Matrix.ext; change ∀ i j, raw31395step2 i j = -(raw31395step1 i j); unfold raw31395step2 raw31395step1; decide +kernel
      have hl : raw31395step2Labels = raw31395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31395step2 raw31395step2Labels = mixedMoment B raw31395step3 raw31395step3Labels := by
      have ha : raw31395step3 = raw31395step2 := by apply Matrix.ext; unfold raw31395step3 raw31395step2; decide +kernel
      have hl : raw31395step2Labels = labelEmbedding6 ∘ raw31395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31395step2 raw31395step2Labels raw31395step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4678 node4678Labels := by rfl

theorem canonical31396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31396 raw31396Labels = mixedMoment B node4658 node4658Labels := by
  calc
    mixedMoment B raw31396 raw31396Labels = mixedMoment B raw31396step0 raw31396step0Labels := by
      have ha : raw31396step0 = (fun i j => raw31396 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31396step0 raw31396; decide +kernel
      have hl : raw31396step0Labels = raw31396Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31396 raw31396Labels permutation582 permutation3
    mixedMoment B raw31396step0 raw31396step0Labels = mixedMoment B raw31396step1 raw31396step1Labels := by
      have ha : raw31396step1 = -raw31396step0 := by apply Matrix.ext; change ∀ i j, raw31396step1 i j = -(raw31396step0 i j); unfold raw31396step1 raw31396step0; decide +kernel
      have hl : raw31396step1Labels = raw31396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31396step1 raw31396step1Labels = mixedMoment B raw31396step2 raw31396step2Labels := by
      have ha : raw31396step2 = raw31396step1 := by apply Matrix.ext; unfold raw31396step2 raw31396step1; decide +kernel
      have hl : raw31396step1Labels = labelEmbedding6 ∘ raw31396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31396step1 raw31396step1Labels raw31396step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4658 node4658Labels := by rfl

theorem canonical31397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31397 raw31397Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw31397 raw31397Labels = mixedMoment B raw31397step0 raw31397step0Labels := by
      have hz : ∀ j, raw31397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31397step0 = (fun i j => raw31397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31397step0 raw31397; decide +kernel
      have hl : raw31397step0Labels = raw31397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31397 raw31397Labels permutation434 hz
    mixedMoment B raw31397step0 raw31397step0Labels = mixedMoment B raw31397step1 raw31397step1Labels := by
      have ha : raw31397step1 = (fun i j => raw31397step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31397step1 raw31397step0; decide +kernel
      have hl : raw31397step1Labels = raw31397step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31397step0 raw31397step0Labels permutation33 permutation3
    mixedMoment B raw31397step1 raw31397step1Labels = mixedMoment B raw31397step2 raw31397step2Labels := by
      have ha : raw31397step2 = raw31397step1 := by apply Matrix.ext; unfold raw31397step2 raw31397step1; decide +kernel
      have hl : raw31397step1Labels = labelEmbedding6 ∘ raw31397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31397step1 raw31397step1Labels raw31397step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

theorem canonical31398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31398 raw31398Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw31398 raw31398Labels = mixedMoment B raw31398step0 raw31398step0Labels := by
      have hz : ∀ j, raw31398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31398step0 = (fun i j => raw31398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31398step0 raw31398; decide +kernel
      have hl : raw31398step0Labels = raw31398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31398 raw31398Labels permutation434 hz
    mixedMoment B raw31398step0 raw31398step0Labels = mixedMoment B raw31398step1 raw31398step1Labels := by
      have ha : raw31398step1 = (fun i j => raw31398step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31398step1 raw31398step0; decide +kernel
      have hl : raw31398step1Labels = raw31398step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31398step0 raw31398step0Labels permutation32 permutation3
    mixedMoment B raw31398step1 raw31398step1Labels = mixedMoment B raw31398step2 raw31398step2Labels := by
      have ha : raw31398step2 = raw31398step1 := by apply Matrix.ext; unfold raw31398step2 raw31398step1; decide +kernel
      have hl : raw31398step1Labels = labelEmbedding6 ∘ raw31398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31398step1 raw31398step1Labels raw31398step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4205 node4205Labels := by rfl

theorem canonical31399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31399 raw31399Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw31399 raw31399Labels = mixedMoment B raw31399step0 raw31399step0Labels := by
      have hz : ∀ j, raw31399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31399step0 = (fun i j => raw31399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31399step0 raw31399; decide +kernel
      have hl : raw31399step0Labels = raw31399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31399 raw31399Labels permutation434 hz
    mixedMoment B raw31399step0 raw31399step0Labels = mixedMoment B raw31399step1 raw31399step1Labels := by
      have ha : raw31399step1 = (fun i j => raw31399step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31399step1 raw31399step0; decide +kernel
      have hl : raw31399step1Labels = raw31399step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31399step0 raw31399step0Labels permutation32 permutation3
    mixedMoment B raw31399step1 raw31399step1Labels = mixedMoment B raw31399step2 raw31399step2Labels := by
      have ha : raw31399step2 = raw31399step1 := by apply Matrix.ext; unfold raw31399step2 raw31399step1; decide +kernel
      have hl : raw31399step1Labels = labelEmbedding6 ∘ raw31399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31399step1 raw31399step1Labels raw31399step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

theorem canonical31400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31400 raw31400Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw31400 raw31400Labels = mixedMoment B raw31400step0 raw31400step0Labels := by
      have hz : ∀ j, raw31400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31400step0 = (fun i j => raw31400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31400step0 raw31400; decide +kernel
      have hl : raw31400step0Labels = raw31400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31400 raw31400Labels permutation434 hz
    mixedMoment B raw31400step0 raw31400step0Labels = mixedMoment B raw31400step1 raw31400step1Labels := by
      have ha : raw31400step1 = (fun i j => raw31400step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31400step1 raw31400step0; decide +kernel
      have hl : raw31400step1Labels = raw31400step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31400step0 raw31400step0Labels permutation32 permutation3
    mixedMoment B raw31400step1 raw31400step1Labels = mixedMoment B raw31400step2 raw31400step2Labels := by
      have ha : raw31400step2 = raw31400step1 := by apply Matrix.ext; unfold raw31400step2 raw31400step1; decide +kernel
      have hl : raw31400step1Labels = labelEmbedding6 ∘ raw31400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31400step1 raw31400step1Labels raw31400step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical31401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31401 raw31401Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw31401 raw31401Labels = mixedMoment B raw31401step0 raw31401step0Labels := by
      have ha : raw31401step0 = (fun i j => raw31401 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31401step0 raw31401; decide +kernel
      have hl : raw31401step0Labels = raw31401Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31401 raw31401Labels permutation200 permutation3
    mixedMoment B raw31401step0 raw31401step0Labels = mixedMoment B raw31401step1 raw31401step1Labels := by
      have ha : raw31401step1 = raw31401step0 := by apply Matrix.ext; unfold raw31401step1 raw31401step0; decide +kernel
      have hl : raw31401step0Labels = labelEmbedding6 ∘ raw31401step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31401step0 raw31401step0Labels raw31401step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

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

theorem canonical864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw864 raw864Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw864 raw864Labels = mixedMoment B raw864step0 raw864step0Labels := by
      have ha : raw864step0 = (fun i j => raw864 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw864step0 raw864; decide +kernel
      have hl : raw864step0Labels = raw864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw864 raw864Labels permutation152 permutation4
    mixedMoment B raw864step0 raw864step0Labels = mixedMoment B raw864step1 raw864step1Labels := by
      have ha : raw864step1 = raw864step0 := by apply Matrix.ext; unfold raw864step1 raw864step0; decide +kernel
      have hl : raw864step0Labels = labelEmbedding7 ∘ raw864step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw864step0 raw864step0Labels raw864step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4200 node4200Labels := by rfl

theorem canonical865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw865 raw865Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw865 raw865Labels = mixedMoment B raw865step0 raw865step0Labels := by
      have ha : raw865step0 = (fun i j => raw865 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw865step0 raw865; decide +kernel
      have hl : raw865step0Labels = raw865Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw865 raw865Labels permutation152 permutation4
    _ = mixedMoment B node703 node703Labels := by rfl

theorem canonical866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw866 raw866Labels = mixedMoment B node754 node754Labels := by
  calc
    mixedMoment B raw866 raw866Labels = mixedMoment B raw866step0 raw866step0Labels := by
      have ha : raw866step0 = (fun i j => raw866 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw866step0 raw866; decide +kernel
      have hl : raw866step0Labels = raw866Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw866 raw866Labels permutation164 permutation6
    mixedMoment B raw866step0 raw866step0Labels = mixedMoment B raw866step1 raw866step1Labels := by
      have ha : raw866step1 = -raw866step0 := by apply Matrix.ext; change ∀ i j, raw866step1 i j = -(raw866step0 i j); unfold raw866step1 raw866step0; decide +kernel
      have hl : raw866step1Labels = raw866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw866step1 raw866step1Labels = mixedMoment B raw866step2 raw866step2Labels := by
      have ha : raw866step2 = raw866step1 := by apply Matrix.ext; unfold raw866step2 raw866step1; decide +kernel
      have hl : raw866step1Labels = labelEmbedding1 ∘ raw866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw866step1 raw866step1Labels raw866step2Labels labelEmbedding1 hl
    _ = mixedMoment B node754 node754Labels := by rfl

theorem canonical873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw873 raw873Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw873 raw873Labels = mixedMoment B raw873step0 raw873step0Labels := by
      have ha : raw873step0 = (fun i j => raw873 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw873step0 raw873; decide +kernel
      have hl : raw873step0Labels = raw873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw873 raw873Labels permutation32 permutation4
    mixedMoment B raw873step0 raw873step0Labels = mixedMoment B raw873step1 raw873step1Labels := by
      have ha : raw873step1 = raw873step0 := by apply Matrix.ext; unfold raw873step1 raw873step0; decide +kernel
      have hl : raw873step0Labels = labelEmbedding7 ∘ raw873step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw873step0 raw873step0Labels raw873step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4203 node4203Labels := by rfl

theorem canonical874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw874 raw874Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw874 raw874Labels = mixedMoment B raw874step0 raw874step0Labels := by
      have ha : raw874step0 = (fun i j => raw874 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw874step0 raw874; decide +kernel
      have hl : raw874step0Labels = raw874Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw874 raw874Labels permutation32 permutation4
    _ = mixedMoment B node706 node706Labels := by rfl

theorem canonical875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw875 raw875Labels = mixedMoment B node755 node755Labels := by
  calc
    mixedMoment B raw875 raw875Labels = mixedMoment B raw875step0 raw875step0Labels := by
      have ha : raw875step0 = (fun i j => raw875 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw875step0 raw875; decide +kernel
      have hl : raw875step0Labels = raw875Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw875 raw875Labels permutation34 permutation6
    mixedMoment B raw875step0 raw875step0Labels = mixedMoment B raw875step1 raw875step1Labels := by
      have ha : raw875step1 = -raw875step0 := by apply Matrix.ext; change ∀ i j, raw875step1 i j = -(raw875step0 i j); unfold raw875step1 raw875step0; decide +kernel
      have hl : raw875step1Labels = raw875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw875step1 raw875step1Labels = mixedMoment B raw875step2 raw875step2Labels := by
      have ha : raw875step2 = raw875step1 := by apply Matrix.ext; unfold raw875step2 raw875step1; decide +kernel
      have hl : raw875step1Labels = labelEmbedding1 ∘ raw875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw875step1 raw875step1Labels raw875step2Labels labelEmbedding1 hl
    _ = mixedMoment B node755 node755Labels := by rfl

theorem canonical879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw879 raw879Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw879 raw879Labels = mixedMoment B raw879step0 raw879step0Labels := by
      have ha : raw879step0 = (fun i j => raw879 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw879step0 raw879; decide +kernel
      have hl : raw879step0Labels = raw879Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw879 raw879Labels permutation32 permutation4
    mixedMoment B raw879step0 raw879step0Labels = mixedMoment B raw879step1 raw879step1Labels := by
      have ha : raw879step1 = raw879step0 := by apply Matrix.ext; unfold raw879step1 raw879step0; decide +kernel
      have hl : raw879step0Labels = labelEmbedding7 ∘ raw879step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw879step0 raw879step0Labels raw879step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4205 node4205Labels := by rfl

theorem canonical880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw880 raw880Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw880 raw880Labels = mixedMoment B raw880step0 raw880step0Labels := by
      have ha : raw880step0 = (fun i j => raw880 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw880step0 raw880; decide +kernel
      have hl : raw880step0Labels = raw880Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw880 raw880Labels permutation32 permutation4
    _ = mixedMoment B node708 node708Labels := by rfl

theorem canonical881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw881 raw881Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw881 raw881Labels = mixedMoment B raw881step0 raw881step0Labels := by
      have ha : raw881step0 = (fun i j => raw881 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw881step0 raw881; decide +kernel
      have hl : raw881step0Labels = raw881Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw881 raw881Labels permutation33 permutation6
    mixedMoment B raw881step0 raw881step0Labels = mixedMoment B raw881step1 raw881step1Labels := by
      have ha : raw881step1 = -raw881step0 := by apply Matrix.ext; change ∀ i j, raw881step1 i j = -(raw881step0 i j); unfold raw881step1 raw881step0; decide +kernel
      have hl : raw881step1Labels = raw881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw881step1 raw881step1Labels = mixedMoment B raw881step2 raw881step2Labels := by
      have ha : raw881step2 = raw881step1 := by apply Matrix.ext; unfold raw881step2 raw881step1; decide +kernel
      have hl : raw881step1Labels = labelEmbedding1 ∘ raw881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw881step1 raw881step1Labels raw881step2Labels labelEmbedding1 hl
    _ = mixedMoment B node764 node764Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw909 raw909Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw909 raw909Labels = mixedMoment B raw909step0 raw909step0Labels := by
      have ha : raw909step0 = (fun i j => raw909 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw909step0 raw909; decide +kernel
      have hl : raw909step0Labels = raw909Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw909 raw909Labels permutation32 permutation4
    mixedMoment B raw909step0 raw909step0Labels = mixedMoment B raw909step1 raw909step1Labels := by
      have ha : raw909step1 = raw909step0 := by apply Matrix.ext; unfold raw909step1 raw909step0; decide +kernel
      have hl : raw909step0Labels = labelEmbedding7 ∘ raw909step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw909step0 raw909step0Labels raw909step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

theorem canonical910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw910 raw910Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw910 raw910Labels = mixedMoment B raw910step0 raw910step0Labels := by
      have ha : raw910step0 = (fun i j => raw910 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw910step0 raw910; decide +kernel
      have hl : raw910step0Labels = raw910Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw910 raw910Labels permutation32 permutation4
    _ = mixedMoment B node724 node724Labels := by rfl

theorem canonical911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw911 raw911Labels = mixedMoment B node758 node758Labels := by
  calc
    mixedMoment B raw911 raw911Labels = mixedMoment B raw911step0 raw911step0Labels := by
      have ha : raw911step0 = (fun i j => raw911 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw911step0 raw911; decide +kernel
      have hl : raw911step0Labels = raw911Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw911 raw911Labels permutation34 permutation6
    mixedMoment B raw911step0 raw911step0Labels = mixedMoment B raw911step1 raw911step1Labels := by
      have ha : raw911step1 = -raw911step0 := by apply Matrix.ext; change ∀ i j, raw911step1 i j = -(raw911step0 i j); unfold raw911step1 raw911step0; decide +kernel
      have hl : raw911step1Labels = raw911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw911step1 raw911step1Labels = mixedMoment B raw911step2 raw911step2Labels := by
      have ha : raw911step2 = raw911step1 := by apply Matrix.ext; unfold raw911step2 raw911step1; decide +kernel
      have hl : raw911step1Labels = labelEmbedding1 ∘ raw911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw911step1 raw911step1Labels raw911step2Labels labelEmbedding1 hl
    _ = mixedMoment B node758 node758Labels := by rfl

theorem canonical981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw981 raw981Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw981 raw981Labels = mixedMoment B raw981step0 raw981step0Labels := by
      have ha : raw981step0 = (fun i j => raw981 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw981step0 raw981; decide +kernel
      have hl : raw981step0Labels = raw981Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw981 raw981Labels permutation32 permutation4
    mixedMoment B raw981step0 raw981step0Labels = mixedMoment B raw981step1 raw981step1Labels := by
      have ha : raw981step1 = raw981step0 := by apply Matrix.ext; unfold raw981step1 raw981step0; decide +kernel
      have hl : raw981step0Labels = labelEmbedding7 ∘ raw981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw981step0 raw981step0Labels raw981step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw982 raw982Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw982 raw982Labels = mixedMoment B raw982step0 raw982step0Labels := by
      have ha : raw982step0 = (fun i j => raw982 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw982step0 raw982; decide +kernel
      have hl : raw982step0Labels = raw982Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw982 raw982Labels permutation32 permutation4
    _ = mixedMoment B node789 node789Labels := by rfl

theorem canonical983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw983 raw983Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw983 raw983Labels = mixedMoment B raw983step0 raw983step0Labels := by
      have ha : raw983step0 = (fun i j => raw983 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw983step0 raw983; decide +kernel
      have hl : raw983step0Labels = raw983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw983 raw983Labels permutation44 permutation6
    mixedMoment B raw983step0 raw983step0Labels = mixedMoment B raw983step1 raw983step1Labels := by
      have ha : raw983step1 = -raw983step0 := by apply Matrix.ext; change ∀ i j, raw983step1 i j = -(raw983step0 i j); unfold raw983step1 raw983step0; decide +kernel
      have hl : raw983step1Labels = raw983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw983step1 raw983step1Labels = mixedMoment B raw983step2 raw983step2Labels := by
      have ha : raw983step2 = raw983step1 := by apply Matrix.ext; unfold raw983step2 raw983step1; decide +kernel
      have hl : raw983step1Labels = labelEmbedding1 ∘ raw983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw983step1 raw983step1Labels raw983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node823 node823Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11102 raw11102Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw11102 raw11102Labels = mixedMoment B raw11102step0 raw11102step0Labels := by
      have hz : ∀ j, raw11102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11102step0 = (fun i j => raw11102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11102step0 raw11102; decide +kernel
      have hl : raw11102step0Labels = raw11102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11102 raw11102Labels permutation434 hz
    mixedMoment B raw11102step0 raw11102step0Labels = mixedMoment B raw11102step1 raw11102step1Labels := by
      have ha : raw11102step1 = (fun i j => raw11102step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11102step1 raw11102step0; decide +kernel
      have hl : raw11102step1Labels = raw11102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11102step0 raw11102step0Labels permutation151 permutation2
    mixedMoment B raw11102step1 raw11102step1Labels = mixedMoment B raw11102step2 raw11102step2Labels := by
      have ha : raw11102step2 = -raw11102step1 := by apply Matrix.ext; change ∀ i j, raw11102step2 i j = -(raw11102step1 i j); unfold raw11102step2 raw11102step1; decide +kernel
      have hl : raw11102step2Labels = raw11102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical11113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11113 raw11113Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw11113 raw11113Labels = mixedMoment B raw11113step0 raw11113step0Labels := by
      have hz : ∀ j, raw11113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11113step0 = (fun i j => raw11113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11113step0 raw11113; decide +kernel
      have hl : raw11113step0Labels = raw11113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11113 raw11113Labels permutation434 hz
    mixedMoment B raw11113step0 raw11113step0Labels = mixedMoment B raw11113step1 raw11113step1Labels := by
      have ha : raw11113step1 = (fun i j => raw11113step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11113step1 raw11113step0; decide +kernel
      have hl : raw11113step1Labels = raw11113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11113step0 raw11113step0Labels permutation34 permutation3
    mixedMoment B raw11113step1 raw11113step1Labels = mixedMoment B raw11113step2 raw11113step2Labels := by
      have ha : raw11113step2 = raw11113step1 := by apply Matrix.ext; unfold raw11113step2 raw11113step1; decide +kernel
      have hl : raw11113step1Labels = labelEmbedding6 ∘ raw11113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11113step1 raw11113step1Labels raw11113step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical11118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11118 raw11118Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11118 raw11118Labels = mixedMoment B raw11118step0 raw11118step0Labels := by
      have ha : raw11118step0 = (fun i j => raw11118 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11118step0 raw11118; decide +kernel
      have hl : raw11118step0Labels = raw11118Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11118 raw11118Labels permutation152 permutation3
    mixedMoment B raw11118step0 raw11118step0Labels = mixedMoment B raw11118step1 raw11118step1Labels := by
      have ha : raw11118step1 = raw11118step0 := by apply Matrix.ext; unfold raw11118step1 raw11118step0; decide +kernel
      have hl : raw11118step0Labels = labelEmbedding6 ∘ raw11118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11118step0 raw11118step0Labels raw11118step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical11122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11122 raw11122Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw11122 raw11122Labels = mixedMoment B raw11122step0 raw11122step0Labels := by
      have hz : ∀ j, raw11122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11122step0 = (fun i j => raw11122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11122step0 raw11122; decide +kernel
      have hl : raw11122step0Labels = raw11122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11122 raw11122Labels permutation434 hz
    mixedMoment B raw11122step0 raw11122step0Labels = mixedMoment B raw11122step1 raw11122step1Labels := by
      have ha : raw11122step1 = (fun i j => raw11122step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11122step1 raw11122step0; decide +kernel
      have hl : raw11122step1Labels = raw11122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11122step0 raw11122step0Labels permutation33 permutation3
    mixedMoment B raw11122step1 raw11122step1Labels = mixedMoment B raw11122step2 raw11122step2Labels := by
      have ha : raw11122step2 = raw11122step1 := by apply Matrix.ext; unfold raw11122step2 raw11122step1; decide +kernel
      have hl : raw11122step1Labels = labelEmbedding6 ∘ raw11122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11122step1 raw11122step1Labels raw11122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical11124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11124 raw11124Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw11124 raw11124Labels = mixedMoment B raw11124step0 raw11124step0Labels := by
      have hz : ∀ j, raw11124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11124step0 = (fun i j => raw11124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11124step0 raw11124; decide +kernel
      have hl : raw11124step0Labels = raw11124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11124 raw11124Labels permutation434 hz
    mixedMoment B raw11124step0 raw11124step0Labels = mixedMoment B raw11124step1 raw11124step1Labels := by
      have ha : raw11124step1 = (fun i j => raw11124step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11124step1 raw11124step0; decide +kernel
      have hl : raw11124step1Labels = raw11124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11124step0 raw11124step0Labels permutation39 permutation3
    mixedMoment B raw11124step1 raw11124step1Labels = mixedMoment B raw11124step2 raw11124step2Labels := by
      have ha : raw11124step2 = raw11124step1 := by apply Matrix.ext; unfold raw11124step2 raw11124step1; decide +kernel
      have hl : raw11124step1Labels = labelEmbedding6 ∘ raw11124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11124step1 raw11124step1Labels raw11124step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical11125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11125 raw11125Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw11125 raw11125Labels = mixedMoment B raw11125step0 raw11125step0Labels := by
      have ha : raw11125step0 = (fun i j => raw11125 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11125step0 raw11125; decide +kernel
      have hl : raw11125step0Labels = raw11125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11125 raw11125Labels permutation201 permutation3
    mixedMoment B raw11125step0 raw11125step0Labels = mixedMoment B raw11125step1 raw11125step1Labels := by
      have ha : raw11125step1 = raw11125step0 := by apply Matrix.ext; unfold raw11125step1 raw11125step0; decide +kernel
      have hl : raw11125step0Labels = labelEmbedding6 ∘ raw11125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11125step0 raw11125step0Labels raw11125step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

theorem canonical11126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11126 raw11126Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw11126 raw11126Labels = mixedMoment B raw11126step0 raw11126step0Labels := by
      have hz : ∀ j, raw11126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11126step0 = (fun i j => raw11126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11126step0 raw11126; decide +kernel
      have hl : raw11126step0Labels = raw11126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11126 raw11126Labels permutation434 hz
    mixedMoment B raw11126step0 raw11126step0Labels = mixedMoment B raw11126step1 raw11126step1Labels := by
      have ha : raw11126step1 = (fun i j => raw11126step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11126step1 raw11126step0; decide +kernel
      have hl : raw11126step1Labels = raw11126step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11126step0 raw11126step0Labels permutation50 permutation5
    mixedMoment B raw11126step1 raw11126step1Labels = mixedMoment B raw11126step2 raw11126step2Labels := by
      have ha : raw11126step2 = -raw11126step1 := by apply Matrix.ext; change ∀ i j, raw11126step2 i j = -(raw11126step1 i j); unfold raw11126step2 raw11126step1; decide +kernel
      have hl : raw11126step2Labels = raw11126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11126step2 raw11126step2Labels = mixedMoment B raw11126step3 raw11126step3Labels := by
      have ha : raw11126step3 = raw11126step2 := by apply Matrix.ext; unfold raw11126step3 raw11126step2; decide +kernel
      have hl : raw11126step2Labels = labelEmbedding8 ∘ raw11126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11126step2 raw11126step2Labels raw11126step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical11128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11128 raw11128Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11128 raw11128Labels = mixedMoment B raw11128step0 raw11128step0Labels := by
      have hz : ∀ j, raw11128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11128step0 = (fun i j => raw11128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11128step0 raw11128; decide +kernel
      have hl : raw11128step0Labels = raw11128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11128 raw11128Labels permutation434 hz
    mixedMoment B raw11128step0 raw11128step0Labels = mixedMoment B raw11128step1 raw11128step1Labels := by
      have ha : raw11128step1 = (fun i j => raw11128step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11128step1 raw11128step0; decide +kernel
      have hl : raw11128step1Labels = raw11128step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11128step0 raw11128step0Labels permutation32 permutation3
    mixedMoment B raw11128step1 raw11128step1Labels = mixedMoment B raw11128step2 raw11128step2Labels := by
      have ha : raw11128step2 = raw11128step1 := by apply Matrix.ext; unfold raw11128step2 raw11128step1; decide +kernel
      have hl : raw11128step1Labels = labelEmbedding6 ∘ raw11128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11128step1 raw11128step1Labels raw11128step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

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

theorem singleton4200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4200 node4200Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node703 node703Labels + mixedMoment B node754 node754Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw864 singletonSmall4200
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4200) = raw864Labels := by decide +kernel
  rw [hl, canonical864 B hB] at h
  have hc0 : mixedMoment B raw864 (Fin.cases (0 : Fin 2) singletonSmall4200) =
      mixedMoment B node703 node703Labels := by
    have ha : raw864 = raw865 := by apply Matrix.ext; unfold raw864 raw865; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4200 = raw865Labels := by decide +kernel
    rw [ha, hj, canonical865 B hB]
  have hc1 : mixedMoment B raw864 (Fin.cases (1 : Fin 2) singletonSmall4200) =
      mixedMoment B node754 node754Labels := by
    have ha : raw864 = raw866 := by apply Matrix.ext; unfold raw864 raw866; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4200 = raw866Labels := by decide +kernel
    rw [ha, hj, canonical866 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4203 node4203Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node706 node706Labels + mixedMoment B node755 node755Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw873 singletonSmall4203
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4203) = raw873Labels := by decide +kernel
  rw [hl, canonical873 B hB] at h
  have hc0 : mixedMoment B raw873 (Fin.cases (0 : Fin 2) singletonSmall4203) =
      mixedMoment B node706 node706Labels := by
    have ha : raw873 = raw874 := by apply Matrix.ext; unfold raw873 raw874; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4203 = raw874Labels := by decide +kernel
    rw [ha, hj, canonical874 B hB]
  have hc1 : mixedMoment B raw873 (Fin.cases (1 : Fin 2) singletonSmall4203) =
      mixedMoment B node755 node755Labels := by
    have ha : raw873 = raw875 := by apply Matrix.ext; unfold raw873 raw875; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4203 = raw875Labels := by decide +kernel
    rw [ha, hj, canonical875 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4205 node4205Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node708 node708Labels + mixedMoment B node764 node764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw879 singletonSmall4205
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4205) = raw879Labels := by decide +kernel
  rw [hl, canonical879 B hB] at h
  have hc0 : mixedMoment B raw879 (Fin.cases (0 : Fin 2) singletonSmall4205) =
      mixedMoment B node708 node708Labels := by
    have ha : raw879 = raw880 := by apply Matrix.ext; unfold raw879 raw880; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4205 = raw880Labels := by decide +kernel
    rw [ha, hj, canonical880 B hB]
  have hc1 : mixedMoment B raw879 (Fin.cases (1 : Fin 2) singletonSmall4205) =
      mixedMoment B node764 node764Labels := by
    have ha : raw879 = raw881 := by apply Matrix.ext; unfold raw879 raw881; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4205 = raw881Labels := by decide +kernel
    rw [ha, hj, canonical881 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4223 node4223Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node724 node724Labels + mixedMoment B node758 node758Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw909 singletonSmall4223
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4223) = raw909Labels := by decide +kernel
  rw [hl, canonical909 B hB] at h
  have hc0 : mixedMoment B raw909 (Fin.cases (0 : Fin 2) singletonSmall4223) =
      mixedMoment B node724 node724Labels := by
    have ha : raw909 = raw910 := by apply Matrix.ext; unfold raw909 raw910; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4223 = raw910Labels := by decide +kernel
    rw [ha, hj, canonical910 B hB]
  have hc1 : mixedMoment B raw909 (Fin.cases (1 : Fin 2) singletonSmall4223) =
      mixedMoment B node758 node758Labels := by
    have ha : raw909 = raw911 := by apply Matrix.ext; unfold raw909 raw911; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4223 = raw911Labels := by decide +kernel
    rw [ha, hj, canonical911 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4255 node4255Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node789 node789Labels + mixedMoment B node823 node823Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw981 singletonSmall4255
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4255) = raw981Labels := by decide +kernel
  rw [hl, canonical981 B hB] at h
  have hc0 : mixedMoment B raw981 (Fin.cases (0 : Fin 2) singletonSmall4255) =
      mixedMoment B node789 node789Labels := by
    have ha : raw981 = raw982 := by apply Matrix.ext; unfold raw981 raw982; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4255 = raw982Labels := by decide +kernel
    rw [ha, hj, canonical982 B hB]
  have hc1 : mixedMoment B raw981 (Fin.cases (1 : Fin 2) singletonSmall4255) =
      mixedMoment B node823 node823Labels := by
    have ha : raw981 = raw983 := by apply Matrix.ext; unfold raw981 raw983; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4255 = raw983Labels := by decide +kernel
    rw [ha, hj, canonical983 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4634 node4634Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1763 node1763Labels + mixedMoment B node1842 node1842Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1482 singletonSmall4634
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4634) = raw1482Labels := by decide +kernel
  rw [hl, canonical1482 B hB] at h
  have hc0 : mixedMoment B raw1482 (Fin.cases (0 : Fin 2) singletonSmall4634) =
      mixedMoment B node1763 node1763Labels := by
    have ha : raw1482 = raw1483 := by apply Matrix.ext; unfold raw1482 raw1483; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4634 = raw1483Labels := by decide +kernel
    rw [ha, hj, canonical1483 B hB]
  have hc1 : mixedMoment B raw1482 (Fin.cases (1 : Fin 2) singletonSmall4634) =
      mixedMoment B node1842 node1842Labels := by
    have ha : raw1482 = raw1484 := by apply Matrix.ext; unfold raw1482 raw1484; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4634 = raw1484Labels := by decide +kernel
    rw [ha, hj, canonical1484 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4636 node4636Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1765 node1765Labels + mixedMoment B node1843 node1843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1488 singletonSmall4636
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4636) = raw1488Labels := by decide +kernel
  rw [hl, canonical1488 B hB] at h
  have hc0 : mixedMoment B raw1488 (Fin.cases (0 : Fin 2) singletonSmall4636) =
      mixedMoment B node1765 node1765Labels := by
    have ha : raw1488 = raw1489 := by apply Matrix.ext; unfold raw1488 raw1489; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4636 = raw1489Labels := by decide +kernel
    rw [ha, hj, canonical1489 B hB]
  have hc1 : mixedMoment B raw1488 (Fin.cases (1 : Fin 2) singletonSmall4636) =
      mixedMoment B node1843 node1843Labels := by
    have ha : raw1488 = raw1490 := by apply Matrix.ext; unfold raw1488 raw1490; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4636 = raw1490Labels := by decide +kernel
    rw [ha, hj, canonical1490 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4638 node4638Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1767 node1767Labels + mixedMoment B node1851 node1851Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1494 singletonSmall4638
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4638) = raw1494Labels := by decide +kernel
  rw [hl, canonical1494 B hB] at h
  have hc0 : mixedMoment B raw1494 (Fin.cases (0 : Fin 2) singletonSmall4638) =
      mixedMoment B node1767 node1767Labels := by
    have ha : raw1494 = raw1495 := by apply Matrix.ext; unfold raw1494 raw1495; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4638 = raw1495Labels := by decide +kernel
    rw [ha, hj, canonical1495 B hB]
  have hc1 : mixedMoment B raw1494 (Fin.cases (1 : Fin 2) singletonSmall4638) =
      mixedMoment B node1851 node1851Labels := by
    have ha : raw1494 = raw1496 := by apply Matrix.ext; unfold raw1494 raw1496; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4638 = raw1496Labels := by decide +kernel
    rw [ha, hj, canonical1496 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4653 node4653Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1781 node1781Labels + mixedMoment B node1846 node1846Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1521 singletonSmall4653
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4653) = raw1521Labels := by decide +kernel
  rw [hl, canonical1521 B hB] at h
  have hc0 : mixedMoment B raw1521 (Fin.cases (0 : Fin 2) singletonSmall4653) =
      mixedMoment B node1781 node1781Labels := by
    have ha : raw1521 = raw1522 := by apply Matrix.ext; unfold raw1521 raw1522; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4653 = raw1522Labels := by decide +kernel
    rw [ha, hj, canonical1522 B hB]
  have hc1 : mixedMoment B raw1521 (Fin.cases (1 : Fin 2) singletonSmall4653) =
      mixedMoment B node1846 node1846Labels := by
    have ha : raw1521 = raw1523 := by apply Matrix.ext; unfold raw1521 raw1523; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4653 = raw1523Labels := by decide +kernel
    rw [ha, hj, canonical1523 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4658 node4658Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1784 node1784Labels + mixedMoment B node1884 node1884Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1530 singletonSmall4658
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4658) = raw1530Labels := by decide +kernel
  rw [hl, canonical1530 B hB] at h
  have hc0 : mixedMoment B raw1530 (Fin.cases (0 : Fin 2) singletonSmall4658) =
      mixedMoment B node1784 node1784Labels := by
    have ha : raw1530 = raw1531 := by apply Matrix.ext; unfold raw1530 raw1531; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4658 = raw1531Labels := by decide +kernel
    rw [ha, hj, canonical1531 B hB]
  have hc1 : mixedMoment B raw1530 (Fin.cases (1 : Fin 2) singletonSmall4658) =
      mixedMoment B node1884 node1884Labels := by
    have ha : raw1530 = raw1532 := by apply Matrix.ext; unfold raw1530 raw1532; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4658 = raw1532Labels := by decide +kernel
    rw [ha, hj, canonical1532 B hB]
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

theorem singleton4678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4678 node4678Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1804 node1804Labels + mixedMoment B node2143 node2143Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1557 singletonSmall4678
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4678) = raw1557Labels := by decide +kernel
  rw [hl, canonical1557 B hB] at h
  have hc0 : mixedMoment B raw1557 (Fin.cases (0 : Fin 2) singletonSmall4678) =
      mixedMoment B node1804 node1804Labels := by
    have ha : raw1557 = raw1558 := by apply Matrix.ext; unfold raw1557 raw1558; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4678 = raw1558Labels := by decide +kernel
    rw [ha, hj, canonical1558 B hB]
  have hc1 : mixedMoment B raw1557 (Fin.cases (1 : Fin 2) singletonSmall4678) =
      mixedMoment B node2143 node2143Labels := by
    have ha : raw1557 = raw1559 := by apply Matrix.ext; unfold raw1557 raw1559; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4678 = raw1559Labels := by decide +kernel
    rw [ha, hj, canonical1559 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4707 node4707Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1861 node1861Labels + mixedMoment B node1889 node1889Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1593 singletonSmall4707
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4707) = raw1593Labels := by decide +kernel
  rw [hl, canonical1593 B hB] at h
  have hc0 : mixedMoment B raw1593 (Fin.cases (0 : Fin 2) singletonSmall4707) =
      mixedMoment B node1861 node1861Labels := by
    have ha : raw1593 = raw1594 := by apply Matrix.ext; unfold raw1593 raw1594; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4707 = raw1594Labels := by decide +kernel
    rw [ha, hj, canonical1594 B hB]
  have hc1 : mixedMoment B raw1593 (Fin.cases (1 : Fin 2) singletonSmall4707) =
      mixedMoment B node1889 node1889Labels := by
    have ha : raw1593 = raw1595 := by apply Matrix.ext; unfold raw1593 raw1595; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4707 = raw1595Labels := by decide +kernel
    rw [ha, hj, canonical1595 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4716 node4716Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1870 node1870Labels + mixedMoment B node1886 node1886Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1608 singletonSmall4716
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4716) = raw1608Labels := by decide +kernel
  rw [hl, canonical1608 B hB] at h
  have hc0 : mixedMoment B raw1608 (Fin.cases (0 : Fin 2) singletonSmall4716) =
      mixedMoment B node1870 node1870Labels := by
    have ha : raw1608 = raw1609 := by apply Matrix.ext; unfold raw1608 raw1609; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4716 = raw1609Labels := by decide +kernel
    rw [ha, hj, canonical1609 B hB]
  have hc1 : mixedMoment B raw1608 (Fin.cases (1 : Fin 2) singletonSmall4716) =
      mixedMoment B node1886 node1886Labels := by
    have ha : raw1608 = raw1610 := by apply Matrix.ext; unfold raw1608 raw1610; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4716 = raw1610Labels := by decide +kernel
    rw [ha, hj, canonical1610 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4731 node4731Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1900 node1900Labels + mixedMoment B node1921 node1921Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1647 singletonSmall4731
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4731) = raw1647Labels := by decide +kernel
  rw [hl, canonical1647 B hB] at h
  have hc0 : mixedMoment B raw1647 (Fin.cases (0 : Fin 2) singletonSmall4731) =
      mixedMoment B node1900 node1900Labels := by
    have ha : raw1647 = raw1648 := by apply Matrix.ext; unfold raw1647 raw1648; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4731 = raw1648Labels := by decide +kernel
    rw [ha, hj, canonical1648 B hB]
  have hc1 : mixedMoment B raw1647 (Fin.cases (1 : Fin 2) singletonSmall4731) =
      mixedMoment B node1921 node1921Labels := by
    have ha : raw1647 = raw1649 := by apply Matrix.ext; unfold raw1647 raw1649; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4731 = raw1649Labels := by decide +kernel
    rw [ha, hj, canonical1649 B hB]
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

theorem singleton4770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4770 node4770Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1970 node1970Labels + mixedMoment B node2186 node2186Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1707 singletonSmall4770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4770) = raw1707Labels := by decide +kernel
  rw [hl, canonical1707 B hB] at h
  have hc0 : mixedMoment B raw1707 (Fin.cases (0 : Fin 2) singletonSmall4770) =
      mixedMoment B node1970 node1970Labels := by
    have ha : raw1707 = raw1708 := by apply Matrix.ext; unfold raw1707 raw1708; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4770 = raw1708Labels := by decide +kernel
    rw [ha, hj, canonical1708 B hB]
  have hc1 : mixedMoment B raw1707 (Fin.cases (1 : Fin 2) singletonSmall4770) =
      mixedMoment B node2186 node2186Labels := by
    have ha : raw1707 = raw1709 := by apply Matrix.ext; unfold raw1707 raw1709; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4770 = raw1709Labels := by decide +kernel
    rw [ha, hj, canonical1709 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4800 node4800Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2018 node2018Labels + mixedMoment B node2018 node2018Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1728 singletonSmall4800
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4800) = raw1728Labels := by decide +kernel
  rw [hl, canonical1728 B hB] at h
  have hc0 : mixedMoment B raw1728 (Fin.cases (0 : Fin 2) singletonSmall4800) =
      mixedMoment B node2018 node2018Labels := by
    have ha : raw1728 = raw1729 := by apply Matrix.ext; unfold raw1728 raw1729; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4800 = raw1729Labels := by decide +kernel
    rw [ha, hj, canonical1729 B hB]
  have hc1 : mixedMoment B raw1728 (Fin.cases (1 : Fin 2) singletonSmall4800) =
      mixedMoment B node2018 node2018Labels := by
    have ha : raw1728 = raw1730 := by apply Matrix.ext; unfold raw1728 raw1730; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4800 = raw1730Labels := by decide +kernel
    rw [ha, hj, canonical1730 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4805 node4805Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2023 node2023Labels + mixedMoment B node2214 node2214Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1740 singletonSmall4805
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4805) = raw1740Labels := by decide +kernel
  rw [hl, canonical1740 B hB] at h
  have hc0 : mixedMoment B raw1740 (Fin.cases (0 : Fin 2) singletonSmall4805) =
      mixedMoment B node2023 node2023Labels := by
    have ha : raw1740 = raw1741 := by apply Matrix.ext; unfold raw1740 raw1741; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4805 = raw1741Labels := by decide +kernel
    rw [ha, hj, canonical1741 B hB]
  have hc1 : mixedMoment B raw1740 (Fin.cases (1 : Fin 2) singletonSmall4805) =
      mixedMoment B node2214 node2214Labels := by
    have ha : raw1740 = raw1742 := by apply Matrix.ext; unfold raw1740 raw1742; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4805 = raw1742Labels := by decide +kernel
    rw [ha, hj, canonical1742 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4807 node4807Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2025 node2025Labels + mixedMoment B node2224 node2224Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1743 singletonSmall4807
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4807) = raw1743Labels := by decide +kernel
  rw [hl, canonical1743 B hB] at h
  have hc0 : mixedMoment B raw1743 (Fin.cases (0 : Fin 2) singletonSmall4807) =
      mixedMoment B node2025 node2025Labels := by
    have ha : raw1743 = raw1744 := by apply Matrix.ext; unfold raw1743 raw1744; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4807 = raw1744Labels := by decide +kernel
    rw [ha, hj, canonical1744 B hB]
  have hc1 : mixedMoment B raw1743 (Fin.cases (1 : Fin 2) singletonSmall4807) =
      mixedMoment B node2224 node2224Labels := by
    have ha : raw1743 = raw1745 := by apply Matrix.ext; unfold raw1743 raw1745; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4807 = raw1745Labels := by decide +kernel
    rw [ha, hj, canonical1745 B hB]
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

theorem singleton4828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4828 node4828Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2048 node2048Labels + mixedMoment B node2082 node2082Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1758 singletonSmall4828
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4828) = raw1758Labels := by decide +kernel
  rw [hl, canonical1758 B hB] at h
  have hc0 : mixedMoment B raw1758 (Fin.cases (0 : Fin 2) singletonSmall4828) =
      mixedMoment B node2048 node2048Labels := by
    have ha : raw1758 = raw1759 := by apply Matrix.ext; unfold raw1758 raw1759; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4828 = raw1759Labels := by decide +kernel
    rw [ha, hj, canonical1759 B hB]
  have hc1 : mixedMoment B raw1758 (Fin.cases (1 : Fin 2) singletonSmall4828) =
      mixedMoment B node2082 node2082Labels := by
    have ha : raw1758 = raw1760 := by apply Matrix.ext; unfold raw1758 raw1760; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4828 = raw1760Labels := by decide +kernel
    rw [ha, hj, canonical1760 B hB]
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

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5355 node5355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3693 node3693Labels + mixedMoment B node3770 node3770Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2400 singletonSmall5355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5355) = raw2400Labels := by decide +kernel
  rw [hl, canonical2400 B hB] at h
  have hc0 : mixedMoment B raw2400 (Fin.cases (0 : Fin 2) singletonSmall5355) =
      mixedMoment B node3693 node3693Labels := by
    have ha : raw2400 = raw2401 := by apply Matrix.ext; unfold raw2400 raw2401; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5355 = raw2401Labels := by decide +kernel
    rw [ha, hj, canonical2401 B hB]
  have hc1 : mixedMoment B raw2400 (Fin.cases (1 : Fin 2) singletonSmall5355) =
      mixedMoment B node3770 node3770Labels := by
    have ha : raw2400 = raw2402 := by apply Matrix.ext; unfold raw2400 raw2402; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5355 = raw2402Labels := by decide +kernel
    rw [ha, hj, canonical2402 B hB]
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

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5432 node5432Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3850 node3850Labels + mixedMoment B node3850 node3850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2523 singletonSmall5432
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5432) = raw2523Labels := by decide +kernel
  rw [hl, canonical2523 B hB] at h
  have hc0 : mixedMoment B raw2523 (Fin.cases (0 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2524 := by apply Matrix.ext; unfold raw2523 raw2524; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5432 = raw2524Labels := by decide +kernel
    rw [ha, hj, canonical2524 B hB]
  have hc1 : mixedMoment B raw2523 (Fin.cases (1 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2525 := by apply Matrix.ext; unfold raw2523 raw2525; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5432 = raw2525Labels := by decide +kernel
    rw [ha, hj, canonical2525 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node703 node703Labels = Sparse.eval nodeValue703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 703) = mixedMoment B node703 node703Labels := rfl
  simpa [nodeValue703, Sparse.eval] using hc.symm

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

theorem sound708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node708 node708Labels = Sparse.eval nodeValue708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 708) = mixedMoment B node708 node708Labels := rfl
  simpa [nodeValue708, Sparse.eval] using hc.symm

theorem sound724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node724 node724Labels = Sparse.eval nodeValue724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 724) = mixedMoment B node724 node724Labels := rfl
  simpa [nodeValue724, Sparse.eval] using hc.symm

theorem sound754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node754 node754Labels = Sparse.eval nodeValue754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 754) = mixedMoment B node754 node754Labels := rfl
  simpa [nodeValue754, Sparse.eval] using hc.symm

theorem sound755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node755 node755Labels = Sparse.eval nodeValue755 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 755) = mixedMoment B node755 node755Labels := rfl
  simpa [nodeValue755, Sparse.eval] using hc.symm

theorem sound758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node758 node758Labels = Sparse.eval nodeValue758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 758) = mixedMoment B node758 node758Labels := rfl
  simpa [nodeValue758, Sparse.eval] using hc.symm

theorem sound764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node764 node764Labels = Sparse.eval nodeValue764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 764) = mixedMoment B node764 node764Labels := rfl
  simpa [nodeValue764, Sparse.eval] using hc.symm

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

theorem sound789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node789 node789Labels = Sparse.eval nodeValue789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 789) = mixedMoment B node789 node789Labels := rfl
  simpa [nodeValue789, Sparse.eval] using hc.symm

theorem sound823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node823 node823Labels = Sparse.eval nodeValue823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 823) = mixedMoment B node823 node823Labels := rfl
  simpa [nodeValue823, Sparse.eval] using hc.symm

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

theorem sound1763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1763 node1763Labels = Sparse.eval nodeValue1763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1763) = mixedMoment B node1763 node1763Labels := rfl
  simpa [nodeValue1763, Sparse.eval] using hc.symm

theorem sound1765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1765 node1765Labels = Sparse.eval nodeValue1765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1765) = mixedMoment B node1765 node1765Labels := rfl
  simpa [nodeValue1765, Sparse.eval] using hc.symm

theorem sound1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1767 node1767Labels = Sparse.eval nodeValue1767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1767) = mixedMoment B node1767 node1767Labels := rfl
  simpa [nodeValue1767, Sparse.eval] using hc.symm

theorem sound1781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1781 node1781Labels = Sparse.eval nodeValue1781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1781) = mixedMoment B node1781 node1781Labels := rfl
  simpa [nodeValue1781, Sparse.eval] using hc.symm

theorem sound1784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1784 node1784Labels = Sparse.eval nodeValue1784 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1784) = mixedMoment B node1784 node1784Labels := rfl
  simpa [nodeValue1784, Sparse.eval] using hc.symm

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

theorem sound1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1804 node1804Labels = Sparse.eval nodeValue1804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1804) = mixedMoment B node1804 node1804Labels := rfl
  simpa [nodeValue1804, Sparse.eval] using hc.symm

theorem sound1842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1842 node1842Labels = Sparse.eval nodeValue1842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1842) = mixedMoment B node1842 node1842Labels := rfl
  simpa [nodeValue1842, Sparse.eval] using hc.symm

theorem sound1843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1843 node1843Labels = Sparse.eval nodeValue1843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1843) = mixedMoment B node1843 node1843Labels := rfl
  simpa [nodeValue1843, Sparse.eval] using hc.symm

theorem sound1846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1846 node1846Labels = Sparse.eval nodeValue1846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1846) = mixedMoment B node1846 node1846Labels := rfl
  simpa [nodeValue1846, Sparse.eval] using hc.symm

theorem sound1851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1851 node1851Labels = Sparse.eval nodeValue1851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1851) = mixedMoment B node1851 node1851Labels := rfl
  simpa [nodeValue1851, Sparse.eval] using hc.symm

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

theorem sound1861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1861 node1861Labels = Sparse.eval nodeValue1861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1861) = mixedMoment B node1861 node1861Labels := rfl
  simpa [nodeValue1861, Sparse.eval] using hc.symm

theorem sound1870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1870 node1870Labels = Sparse.eval nodeValue1870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1870) = mixedMoment B node1870 node1870Labels := rfl
  simpa [nodeValue1870, Sparse.eval] using hc.symm

theorem sound1884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1884 node1884Labels = Sparse.eval nodeValue1884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1884) = mixedMoment B node1884 node1884Labels := rfl
  simpa [nodeValue1884, Sparse.eval] using hc.symm

theorem sound1886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1886 node1886Labels = Sparse.eval nodeValue1886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1886) = mixedMoment B node1886 node1886Labels := rfl
  simpa [nodeValue1886, Sparse.eval] using hc.symm

theorem sound1889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1889 node1889Labels = Sparse.eval nodeValue1889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1889) = mixedMoment B node1889 node1889Labels := rfl
  simpa [nodeValue1889, Sparse.eval] using hc.symm

theorem sound1900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1900 node1900Labels = Sparse.eval nodeValue1900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1900) = mixedMoment B node1900 node1900Labels := rfl
  simpa [nodeValue1900, Sparse.eval] using hc.symm

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

theorem sound1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1921 node1921Labels = Sparse.eval nodeValue1921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1921) = mixedMoment B node1921 node1921Labels := rfl
  simpa [nodeValue1921, Sparse.eval] using hc.symm

theorem sound1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1966 node1966Labels = Sparse.eval nodeValue1966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1966) = mixedMoment B node1966 node1966Labels := rfl
  simpa [nodeValue1966, Sparse.eval] using hc.symm

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

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

theorem sound2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2018 node2018Labels = Sparse.eval nodeValue2018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2018) = mixedMoment B node2018 node2018Labels := rfl
  simpa [nodeValue2018, Sparse.eval] using hc.symm

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

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

theorem sound2048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2048 node2048Labels = Sparse.eval nodeValue2048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2048) = mixedMoment B node2048 node2048Labels := rfl
  simpa [nodeValue2048, Sparse.eval] using hc.symm

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2082 node2082Labels = Sparse.eval nodeValue2082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2082) = mixedMoment B node2082 node2082Labels := rfl
  simpa [nodeValue2082, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

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

theorem sound2143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2143 node2143Labels = Sparse.eval nodeValue2143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2143) = mixedMoment B node2143 node2143Labels := rfl
  simpa [nodeValue2143, Sparse.eval] using hc.symm

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

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

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

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

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

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

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

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

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

theorem sound4200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4200 node4200Labels = Sparse.eval nodeValue4200 (mixedVector B) := by
  have h := singleton4200 B _hB
  rw [sound703 B _hB _hF, sound754 B _hB _hF] at h
  norm_num [nodeValue4200, nodeValue703, nodeValue754, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4203 node4203Labels = Sparse.eval nodeValue4203 (mixedVector B) := by
  have h := singleton4203 B _hB
  rw [sound706 B _hB _hF, sound755 B _hB _hF] at h
  norm_num [nodeValue4203, nodeValue706, nodeValue755, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4205 node4205Labels = Sparse.eval nodeValue4205 (mixedVector B) := by
  have h := singleton4205 B _hB
  rw [sound708 B _hB _hF, sound764 B _hB _hF] at h
  norm_num [nodeValue4205, nodeValue708, nodeValue764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4223 node4223Labels = Sparse.eval nodeValue4223 (mixedVector B) := by
  have h := singleton4223 B _hB
  rw [sound724 B _hB _hF, sound758 B _hB _hF] at h
  norm_num [nodeValue4223, nodeValue724, nodeValue758, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4255 node4255Labels = Sparse.eval nodeValue4255 (mixedVector B) := by
  have h := singleton4255 B _hB
  rw [sound789 B _hB _hF, sound823 B _hB _hF] at h
  norm_num [nodeValue4255, nodeValue789, nodeValue823, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4634 node4634Labels = Sparse.eval nodeValue4634 (mixedVector B) := by
  have h := singleton4634 B _hB
  rw [sound1763 B _hB _hF, sound1842 B _hB _hF] at h
  norm_num [nodeValue4634, nodeValue1763, nodeValue1842, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4636 node4636Labels = Sparse.eval nodeValue4636 (mixedVector B) := by
  have h := singleton4636 B _hB
  rw [sound1765 B _hB _hF, sound1843 B _hB _hF] at h
  norm_num [nodeValue4636, nodeValue1765, nodeValue1843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4638 node4638Labels = Sparse.eval nodeValue4638 (mixedVector B) := by
  have h := singleton4638 B _hB
  rw [sound1767 B _hB _hF, sound1851 B _hB _hF] at h
  norm_num [nodeValue4638, nodeValue1767, nodeValue1851, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4653 node4653Labels = Sparse.eval nodeValue4653 (mixedVector B) := by
  have h := singleton4653 B _hB
  rw [sound1781 B _hB _hF, sound1846 B _hB _hF] at h
  norm_num [nodeValue4653, nodeValue1781, nodeValue1846, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4658 node4658Labels = Sparse.eval nodeValue4658 (mixedVector B) := by
  have h := singleton4658 B _hB
  rw [sound1784 B _hB _hF, sound1884 B _hB _hF] at h
  norm_num [nodeValue4658, nodeValue1784, nodeValue1884, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4678 node4678Labels = Sparse.eval nodeValue4678 (mixedVector B) := by
  have h := singleton4678 B _hB
  rw [sound1804 B _hB _hF, sound2143 B _hB _hF] at h
  norm_num [nodeValue4678, nodeValue1804, nodeValue2143, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4707 node4707Labels = Sparse.eval nodeValue4707 (mixedVector B) := by
  have h := singleton4707 B _hB
  rw [sound1861 B _hB _hF, sound1889 B _hB _hF] at h
  norm_num [nodeValue4707, nodeValue1861, nodeValue1889, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4716 node4716Labels = Sparse.eval nodeValue4716 (mixedVector B) := by
  have h := singleton4716 B _hB
  rw [sound1870 B _hB _hF, sound1886 B _hB _hF] at h
  norm_num [nodeValue4716, nodeValue1870, nodeValue1886, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4731 node4731Labels = Sparse.eval nodeValue4731 (mixedVector B) := by
  have h := singleton4731 B _hB
  rw [sound1900 B _hB _hF, sound1921 B _hB _hF] at h
  norm_num [nodeValue4731, nodeValue1900, nodeValue1921, Sparse.eval] at h ⊢
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

theorem sound4766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4766 node4766Labels = Sparse.eval nodeValue4766 (mixedVector B) := by
  have h := singleton4766 B _hB
  rw [sound1966 B _hB _hF, sound2177 B _hB _hF] at h
  norm_num [nodeValue4766, nodeValue1966, nodeValue2177, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4770 node4770Labels = Sparse.eval nodeValue4770 (mixedVector B) := by
  have h := singleton4770 B _hB
  rw [sound1970 B _hB _hF, sound2186 B _hB _hF] at h
  norm_num [nodeValue4770, nodeValue1970, nodeValue2186, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4798 node4798Labels = Sparse.eval nodeValue4798 (mixedVector B) := by
  have h := singleton4798 B _hB
  rw [sound2016 B _hB _hF, sound2075 B _hB _hF] at h
  norm_num [nodeValue4798, nodeValue2016, nodeValue2075, Sparse.eval] at h ⊢
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

theorem sound4800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4800 node4800Labels = Sparse.eval nodeValue4800 (mixedVector B) := by
  have h := singleton4800 B _hB
  rw [sound2018 B _hB _hF] at h
  norm_num [nodeValue4800, nodeValue2018, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4828 node4828Labels = Sparse.eval nodeValue4828 (mixedVector B) := by
  have h := singleton4828 B _hB
  rw [sound2048 B _hB _hF, sound2082 B _hB _hF] at h
  norm_num [nodeValue4828, nodeValue2048, nodeValue2082, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
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

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5432 node5432Labels = Sparse.eval nodeValue5432 (mixedVector B) := by
  have h := singleton5432 B _hB
  rw [sound3850 B _hB _hF] at h
  norm_num [nodeValue5432, nodeValue3850, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources71
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2279 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 1) (sourceB2279 + difference 1 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 1) (sourceB2279 + difference 1 0) sourceC2279) = raw31380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31380; decide +kernel
    rw [ha]
    exact (canonical31380 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 2) (sourceB2279 + difference 2 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 2) (sourceB2279 + difference 2 0) sourceC2279) = raw31381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31381; decide +kernel
    rw [ha]
    exact (canonical31381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 3) (sourceB2279 + difference 3 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 3) (sourceB2279 + difference 3 0) sourceC2279) = raw31382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31382; decide +kernel
    rw [ha]
    exact (canonical31382 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 4) (sourceB2279 + difference 4 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 4) (sourceB2279 + difference 4 0) sourceC2279) = raw11102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11102; decide +kernel
    rw [ha]
    exact (canonical11102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 5) (sourceB2279 + difference 5 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 5) (sourceB2279 + difference 5 0) sourceC2279) = raw31383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31383; decide +kernel
    rw [ha]
    exact (canonical31383 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 0) (sourceB2279 + difference 0 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 0) (sourceB2279 + difference 0 1) sourceC2279) = raw11122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11122; decide +kernel
    rw [ha]
    exact (canonical11122 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 2) (sourceB2279 + difference 2 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 2) (sourceB2279 + difference 2 1) sourceC2279) = raw11124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11124; decide +kernel
    rw [ha]
    exact (canonical11124 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 3) (sourceB2279 + difference 3 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 3) (sourceB2279 + difference 3 1) sourceC2279) = raw11125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11125; decide +kernel
    rw [ha]
    exact (canonical11125 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 4) (sourceB2279 + difference 4 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 4) (sourceB2279 + difference 4 1) sourceC2279) = raw31384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31384; decide +kernel
    rw [ha]
    exact (canonical31384 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 5) (sourceB2279 + difference 5 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 5) (sourceB2279 + difference 5 1) sourceC2279) = raw11126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11126; decide +kernel
    rw [ha]
    exact (canonical11126 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 0) (sourceB2279 + difference 0 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4223) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 0) (sourceB2279 + difference 0 2) sourceC2279) = raw31385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31385; decide +kernel
    rw [ha]
    exact (canonical31385 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 1) (sourceB2279 + difference 1 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4653) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 1) (sourceB2279 + difference 1 2) sourceC2279) = raw31386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31386; decide +kernel
    rw [ha]
    exact (canonical31386 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 3) (sourceB2279 + difference 3 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4716) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 3) (sourceB2279 + difference 3 2) sourceC2279) = raw31387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31387; decide +kernel
    rw [ha]
    exact (canonical31387 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 4) (sourceB2279 + difference 4 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 4) (sourceB2279 + difference 4 2) sourceC2279) = raw11113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11113; decide +kernel
    rw [ha]
    exact (canonical11113 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 5) (sourceB2279 + difference 5 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 5) (sourceB2279 + difference 5 2) sourceC2279) = raw31388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31388; decide +kernel
    rw [ha]
    exact (canonical31388 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 0) (sourceB2279 + difference 0 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4200) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 0) (sourceB2279 + difference 0 3) sourceC2279) = raw31389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31389; decide +kernel
    rw [ha]
    exact (canonical31389 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 1) (sourceB2279 + difference 1 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 1) (sourceB2279 + difference 1 3) sourceC2279) = raw31390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31390; decide +kernel
    rw [ha]
    exact (canonical31390 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 2) (sourceB2279 + difference 2 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 2) (sourceB2279 + difference 2 3) sourceC2279) = raw31391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31391; decide +kernel
    rw [ha]
    exact (canonical31391 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 4) (sourceB2279 + difference 4 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 4) (sourceB2279 + difference 4 3) sourceC2279) = raw11118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11118; decide +kernel
    rw [ha]
    exact (canonical11118 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 5) (sourceB2279 + difference 5 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 5) (sourceB2279 + difference 5 3) sourceC2279) = raw31392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31392; decide +kernel
    rw [ha]
    exact (canonical31392 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 0) (sourceB2279 + difference 0 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4203) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 0) (sourceB2279 + difference 0 4) sourceC2279) = raw31393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31393; decide +kernel
    rw [ha]
    exact (canonical31393 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 1) (sourceB2279 + difference 1 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4636) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 1) (sourceB2279 + difference 1 4) sourceC2279) = raw31394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31394; decide +kernel
    rw [ha]
    exact (canonical31394 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 2) (sourceB2279 + difference 2 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 2) (sourceB2279 + difference 2 4) sourceC2279) = raw31395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31395; decide +kernel
    rw [ha]
    exact (canonical31395 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 3) (sourceB2279 + difference 3 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4658) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 3) (sourceB2279 + difference 3 4) sourceC2279) = raw31396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31396; decide +kernel
    rw [ha]
    exact (canonical31396 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 5) (sourceB2279 + difference 5 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 5) (sourceB2279 + difference 5 4) sourceC2279) = raw31397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31397; decide +kernel
    rw [ha]
    exact (canonical31397 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 0) (sourceB2279 + difference 0 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4205) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 0) (sourceB2279 + difference 0 5) sourceC2279) = raw31398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31398; decide +kernel
    rw [ha]
    exact (canonical31398 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 1) (sourceB2279 + difference 1 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4638) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 1) (sourceB2279 + difference 1 5) sourceC2279) = raw31399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31399; decide +kernel
    rw [ha]
    exact (canonical31399 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 2) (sourceB2279 + difference 2 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 2) (sourceB2279 + difference 2 5) sourceC2279) = raw31400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31400; decide +kernel
    rw [ha]
    exact (canonical31400 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 3) (sourceB2279 + difference 3 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4707) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 3) (sourceB2279 + difference 3 5) sourceC2279) = raw31401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31401; decide +kernel
    rw [ha]
    exact (canonical31401 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 4) (sourceB2279 + difference 4 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 4) (sourceB2279 + difference 4 5) sourceC2279) = raw11128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11128; decide +kernel
    rw [ha]
    exact (canonical11128 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2279 sourceB2279 sourceC2279
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2279, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1864 : Integer.Sparse.reindex keyMap MixedData.row1864 = numericRow1864 := by decide +kernel

theorem numericCheck1864 (x : Master → ℝ) : Integer.Sparse.eval numericRow1864 x =
    (51840 : ℝ) * reducedSource1864 x := by
  norm_num [numericRow1864, reducedSource1864, Integer.Sparse.eval, Sparse.eval, nodeValue4200, nodeValue4203, nodeValue4205, nodeValue4223, nodeValue4255, nodeValue4634, nodeValue4636, nodeValue4638, nodeValue4653, nodeValue4658, nodeValue4678, nodeValue4707, nodeValue4716, nodeValue4731, nodeValue4766, nodeValue4770, nodeValue4798, nodeValue4800, nodeValue4805, nodeValue4807, nodeValue4810, nodeValue4828, nodeValue4839, nodeValue4865, nodeValue4889, nodeValue5355, nodeValue5378, nodeValue5387, nodeValue5432, nodeValue5435]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1864 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1864 (mixedVector B) = 0 := by
  have h4200 : mixedVector B (Sum.inr 4200) = Sparse.eval nodeValue4200 (mixedVector B) := by
    change mixedMoment B node4200 node4200Labels = _
    exact sound4200 B hB hF
  have h4203 : mixedVector B (Sum.inr 4203) = Sparse.eval nodeValue4203 (mixedVector B) := by
    change mixedMoment B node4203 node4203Labels = _
    exact sound4203 B hB hF
  have h4205 : mixedVector B (Sum.inr 4205) = Sparse.eval nodeValue4205 (mixedVector B) := by
    change mixedMoment B node4205 node4205Labels = _
    exact sound4205 B hB hF
  have h4223 : mixedVector B (Sum.inr 4223) = Sparse.eval nodeValue4223 (mixedVector B) := by
    change mixedMoment B node4223 node4223Labels = _
    exact sound4223 B hB hF
  have h4255 : mixedVector B (Sum.inr 4255) = Sparse.eval nodeValue4255 (mixedVector B) := by
    change mixedMoment B node4255 node4255Labels = _
    exact sound4255 B hB hF
  have h4634 : mixedVector B (Sum.inr 4634) = Sparse.eval nodeValue4634 (mixedVector B) := by
    change mixedMoment B node4634 node4634Labels = _
    exact sound4634 B hB hF
  have h4636 : mixedVector B (Sum.inr 4636) = Sparse.eval nodeValue4636 (mixedVector B) := by
    change mixedMoment B node4636 node4636Labels = _
    exact sound4636 B hB hF
  have h4638 : mixedVector B (Sum.inr 4638) = Sparse.eval nodeValue4638 (mixedVector B) := by
    change mixedMoment B node4638 node4638Labels = _
    exact sound4638 B hB hF
  have h4653 : mixedVector B (Sum.inr 4653) = Sparse.eval nodeValue4653 (mixedVector B) := by
    change mixedMoment B node4653 node4653Labels = _
    exact sound4653 B hB hF
  have h4658 : mixedVector B (Sum.inr 4658) = Sparse.eval nodeValue4658 (mixedVector B) := by
    change mixedMoment B node4658 node4658Labels = _
    exact sound4658 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4707 : mixedVector B (Sum.inr 4707) = Sparse.eval nodeValue4707 (mixedVector B) := by
    change mixedMoment B node4707 node4707Labels = _
    exact sound4707 B hB hF
  have h4716 : mixedVector B (Sum.inr 4716) = Sparse.eval nodeValue4716 (mixedVector B) := by
    change mixedMoment B node4716 node4716Labels = _
    exact sound4716 B hB hF
  have h4731 : mixedVector B (Sum.inr 4731) = Sparse.eval nodeValue4731 (mixedVector B) := by
    change mixedMoment B node4731 node4731Labels = _
    exact sound4731 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4800 : mixedVector B (Sum.inr 4800) = Sparse.eval nodeValue4800 (mixedVector B) := by
    change mixedMoment B node4800 node4800Labels = _
    exact sound4800 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387_e B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  simpa only [sourceForm2279, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4200, h4203, h4205, h4223, h4255, h4634, h4636, h4638, h4653, h4658, h4678, h4707, h4716, h4731, h4766, h4770, h4798, h4800, h4805, h4807, h4810, h4828, h4839, h4865, h4889, h5355, h5378, h5387, h5432, h5435, reducedSource1864] using sourceEq2279 B hB

theorem rowSound1864_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1864 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1864, numericCheck1864, reducedZero1864 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e_oai
