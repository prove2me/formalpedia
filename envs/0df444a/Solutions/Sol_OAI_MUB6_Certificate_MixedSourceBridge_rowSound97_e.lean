-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:09:08.799081+00:00
-- url     : https://prove2.me/submissions/c8fa3739-8842-45c6-93e4-99846da03cbe

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171

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

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

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

theorem transition_reverse (b c : Basis) :
    transition c b = (transition b c).conjTranspose := by
  ext i j
  simp [transition, Matrix.conjTranspose_apply]

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

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem familyAverage_add (B : Fin 7 → Basis) (F G : CMatrix → ℝ) :
    familyAverage B (fun H => F H + G H) = familyAverage B F + familyAverage B G := by
  simp only [familyAverage, average_add]

theorem familyAverage_mul (B : Fin 7 → Basis) (c : ℝ) (F : CMatrix → ℝ) :
    familyAverage B (fun H => c * F H) = c * familyAverage B F := by
  simp only [familyAverage, average_mul]

theorem relativeMatrix_reverse (B : Fin 7 → Basis) (p : Fin 7 × Coord) :
    relativeMatrix B (reversePair p).1 (reversePair p).2 =
      (relativeMatrix B p.1 p.2).conjTranspose := by
  simp only [relativeMatrix, reversePair, Fin.succAbove_succAbove_predAbove]
  exact transition_reverse _ _

theorem familyAverage_transpose (B : Fin 7 → Basis) (F : CMatrix → ℝ)
    (hF : ∀ H, F (fun i j => conj (H i j)) = F H) :
    familyAverage B (fun H => F H.transpose) = familyAverage B F := by
  change (average (fun r : Fin 7 => average (fun s : Coord => F ((relativeMatrix B r s).transpose)))) =
    average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))
  rw [← average_prod (fun p : Fin 7 × Coord => F ((relativeMatrix B p.1 p.2).transpose)),
    ← average_prod (fun p : Fin 7 × Coord => F (relativeMatrix B p.1 p.2))]
  have h (p : Fin 7 × Coord) :
      F ((relativeMatrix B p.1 p.2).transpose) =
        F (relativeMatrix B (reversePair p).1 (reversePair p).2) := by
    rw [relativeMatrix_reverse]
    exact (hF ((relativeMatrix B p.1 p.2).transpose)).symm
  simp_rw [h]
  exact average_equiv reversePairEquiv (fun p => F (relativeMatrix B p.1 p.2))

theorem rowFourier_conjugate {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier (fun i j => conj (H i j)) ρ a = conj (rowFourier H ρ a) := by
  simp only [rowFourier, map_mul, map_sum, map_prod, map_zpow₀, map_inv₀, map_ofNat]

theorem unorientedRowProducts_conjugate {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    unorientedRowProducts (fun i j => conj (H i j)) A = unorientedRowProducts H A := by
  apply average_congr
  intro ρ
  simp only [rowFourier_conjugate, ← map_prod, Complex.conj_re]

theorem averagedRowProducts_split {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    averagedRowProducts H A =
      (1 / 2 : ℝ) * unorientedRowProducts H A +
        (1 / 2 : ℝ) * unorientedRowProducts H.transpose A := by
  have h (ρ : Fin p ↪ Coord) :
      ((∏ j, rowFourier H ρ (fun i => A i j)).re +
        (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (1 / 2 : ℝ) * (∏ j, rowFourier H ρ (fun i => A i j)).re +
        (1 / 2 : ℝ) * (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re := by ring
  simp only [averagedRowProducts, h, average_add, average_mul, unorientedRowProducts]

theorem familyAverage_averagedRowProducts {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    familyAverage B (fun H => averagedRowProducts H A) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  simp only [averagedRowProducts_split, familyAverage_add, familyAverage_mul]
  rw [familyAverage_transpose B (fun H => unorientedRowProducts H A)
    (fun H => unorientedRowProducts_conjugate H A)]
  ring

theorem mixedMoment_single_label {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) :
      average (fun τ : Fin 1 ↪ Coord =>
        (mixedIntegrand B A (fun _ => (0 : Fin 1)) r ρ τ).re) =
      average (fun s : Coord => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re) := by
    exact average_equiv singletonEmbeddingEquiv
      (fun s => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re)
  simp_rw [h]
  exact average_comm _

/-- Single-label mixed moments expand into the manuscript's transpose-averaged
pair moments with the exact falling-factorial weights. -/
theorem mixedMoment_single_label_partition {p n : ℕ} {P : Type*} [Fintype P]
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        familyPairMoment B (groupedColumns A (F.label s)) := by
  rw [mixedMoment_single_label, ← familyAverage_averagedRowProducts]
  unfold familyAverage
  simp_rw [averagedRowProducts_partition (relativeMatrix_isHadamard B hB _ _) A F cover,
    average_sum, average_mul]
  rfl

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

theorem canonical1407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1407 raw1407Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw1407 raw1407Labels = mixedMoment B raw1407step0 raw1407step0Labels := by
      have ha : raw1407step0 = (fun i j => raw1407 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1407step0 raw1407; decide +kernel
      have hl : raw1407step0Labels = raw1407Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1407 raw1407Labels permutation8 permutation4
    mixedMoment B raw1407step0 raw1407step0Labels = mixedMoment B raw1407step1 raw1407step1Labels := by
      have ha : raw1407step1 = raw1407step0 := by apply Matrix.ext; unfold raw1407step1 raw1407step0; decide +kernel
      have hl : raw1407step0Labels = labelEmbedding7 ∘ raw1407step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1407step0 raw1407step0Labels raw1407step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

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

theorem canonical1408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1408 raw1408Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw1408 raw1408Labels = mixedMoment B raw1408step0 raw1408step0Labels := by
      have ha : raw1408step0 = (fun i j => raw1408 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1408step0 raw1408; decide +kernel
      have hl : raw1408step0Labels = raw1408Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1408 raw1408Labels permutation8 permutation4
    _ = mixedMoment B node1190 node1190Labels := by rfl

theorem canonical1409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1409 raw1409Labels = mixedMoment B node1952 node1952Labels := by
  calc
    mixedMoment B raw1409 raw1409Labels = mixedMoment B raw1409step0 raw1409step0Labels := by
      have ha : raw1409step0 = (fun i j => raw1409 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1409step0 raw1409; decide +kernel
      have hl : raw1409step0Labels = raw1409Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1409 raw1409Labels permutation31 permutation6
    mixedMoment B raw1409step0 raw1409step0Labels = mixedMoment B raw1409step1 raw1409step1Labels := by
      have ha : raw1409step1 = raw1409step0 := by apply Matrix.ext; unfold raw1409step1 raw1409step0; decide +kernel
      have hl : raw1409step0Labels = labelEmbedding1 ∘ raw1409step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1409step0 raw1409step0Labels raw1409step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1952 node1952Labels := by rfl

theorem canonical1446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1446 raw1446Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw1446 raw1446Labels = mixedMoment B raw1446step0 raw1446step0Labels := by
      have ha : raw1446step0 = (fun i j => raw1446 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1446step0 raw1446; decide +kernel
      have hl : raw1446step0Labels = raw1446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1446 raw1446Labels permutation2 permutation4
    mixedMoment B raw1446step0 raw1446step0Labels = mixedMoment B raw1446step1 raw1446step1Labels := by
      have ha : raw1446step1 = raw1446step0 := by apply Matrix.ext; unfold raw1446step1 raw1446step0; decide +kernel
      have hl : raw1446step0Labels = labelEmbedding7 ∘ raw1446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1446step0 raw1446step0Labels raw1446step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical1447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1447 raw1447Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw1447 raw1447Labels = mixedMoment B raw1447step0 raw1447step0Labels := by
      have ha : raw1447step0 = (fun i j => raw1447 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1447step0 raw1447; decide +kernel
      have hl : raw1447step0Labels = raw1447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1447 raw1447Labels permutation2 permutation4
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical1448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1448 raw1448Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw1448 raw1448Labels = mixedMoment B raw1448step0 raw1448step0Labels := by
      have ha : raw1448step0 = (fun i j => raw1448 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1448step0 raw1448; decide +kernel
      have hl : raw1448step0Labels = raw1448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1448 raw1448Labels permutation7 permutation6
    mixedMoment B raw1448step0 raw1448step0Labels = mixedMoment B raw1448step1 raw1448step1Labels := by
      have ha : raw1448step1 = raw1448step0 := by apply Matrix.ext; unfold raw1448step1 raw1448step0; decide +kernel
      have hl : raw1448step0Labels = labelEmbedding1 ∘ raw1448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1448step0 raw1448step0Labels raw1448step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

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

theorem canonical1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1668 raw1668Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw1668 raw1668Labels = mixedMoment B raw1668step0 raw1668step0Labels := by
      have ha : raw1668step0 = (fun i j => raw1668 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1668step0 raw1668; decide +kernel
      have hl : raw1668step0Labels = raw1668Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1668 raw1668Labels permutation32 permutation4
    mixedMoment B raw1668step0 raw1668step0Labels = mixedMoment B raw1668step1 raw1668step1Labels := by
      have ha : raw1668step1 = raw1668step0 := by apply Matrix.ext; unfold raw1668step1 raw1668step0; decide +kernel
      have hl : raw1668step0Labels = labelEmbedding7 ∘ raw1668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1668step0 raw1668step0Labels raw1668step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical1669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1669 raw1669Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw1669 raw1669Labels = mixedMoment B raw1669step0 raw1669step0Labels := by
      have ha : raw1669step0 = (fun i j => raw1669 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1669step0 raw1669; decide +kernel
      have hl : raw1669step0Labels = raw1669Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1669 raw1669Labels permutation32 permutation4
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1670 raw1670Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw1670 raw1670Labels = mixedMoment B raw1670step0 raw1670step0Labels := by
      have ha : raw1670step0 = (fun i j => raw1670 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1670step0 raw1670; decide +kernel
      have hl : raw1670step0Labels = raw1670Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1670 raw1670Labels permutation35 permutation6
    mixedMoment B raw1670step0 raw1670step0Labels = mixedMoment B raw1670step1 raw1670step1Labels := by
      have ha : raw1670step1 = -raw1670step0 := by apply Matrix.ext; change ∀ i j, raw1670step1 i j = -(raw1670step0 i j); unfold raw1670step1 raw1670step0; decide +kernel
      have hl : raw1670step1Labels = raw1670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1670step1 raw1670step1Labels = mixedMoment B raw1670step2 raw1670step2Labels := by
      have ha : raw1670step2 = raw1670step1 := by apply Matrix.ext; unfold raw1670step2 raw1670step1; decide +kernel
      have hl : raw1670step1Labels = labelEmbedding1 ∘ raw1670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1670step1 raw1670step1Labels raw1670step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1948 node1948Labels := by rfl

theorem canonical1677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1677 raw1677Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw1677 raw1677Labels = mixedMoment B raw1677step0 raw1677step0Labels := by
      have ha : raw1677step0 = (fun i j => raw1677 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1677step0 raw1677; decide +kernel
      have hl : raw1677step0Labels = raw1677Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1677 raw1677Labels permutation8 permutation4
    mixedMoment B raw1677step0 raw1677step0Labels = mixedMoment B raw1677step1 raw1677step1Labels := by
      have ha : raw1677step1 = raw1677step0 := by apply Matrix.ext; unfold raw1677step1 raw1677step0; decide +kernel
      have hl : raw1677step0Labels = labelEmbedding7 ∘ raw1677step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1677step0 raw1677step0Labels raw1677step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

theorem canonical1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1678 raw1678Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw1678 raw1678Labels = mixedMoment B raw1678step0 raw1678step0Labels := by
      have ha : raw1678step0 = (fun i j => raw1678 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1678step0 raw1678; decide +kernel
      have hl : raw1678step0Labels = raw1678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1678 raw1678Labels permutation8 permutation4
    _ = mixedMoment B node1951 node1951Labels := by rfl

theorem canonical1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1679 raw1679Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw1679 raw1679Labels = mixedMoment B raw1679step0 raw1679step0Labels := by
      have ha : raw1679step0 = (fun i j => raw1679 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1679step0 raw1679; decide +kernel
      have hl : raw1679step0Labels = raw1679Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1679 raw1679Labels permutation9 permutation6
    mixedMoment B raw1679step0 raw1679step0Labels = mixedMoment B raw1679step1 raw1679step1Labels := by
      have ha : raw1679step1 = -raw1679step0 := by apply Matrix.ext; change ∀ i j, raw1679step1 i j = -(raw1679step0 i j); unfold raw1679step1 raw1679step0; decide +kernel
      have hl : raw1679step1Labels = raw1679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1679step1 raw1679step1Labels = mixedMoment B raw1679step2 raw1679step2Labels := by
      have ha : raw1679step2 = raw1679step1 := by apply Matrix.ext; unfold raw1679step2 raw1679step1; decide +kernel
      have hl : raw1679step1Labels = labelEmbedding1 ∘ raw1679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1679step1 raw1679step1Labels raw1679step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1951 node1951Labels := by rfl

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

theorem canonical1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1803 raw1803Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw1803 raw1803Labels = mixedMoment B raw1803step0 raw1803step0Labels := by
      have ha : raw1803step0 = (fun i j => raw1803 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1803step0 raw1803; decide +kernel
      have hl : raw1803step0Labels = raw1803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1803 raw1803Labels permutation8 permutation4
    mixedMoment B raw1803step0 raw1803step0Labels = mixedMoment B raw1803step1 raw1803step1Labels := by
      have ha : raw1803step1 = raw1803step0 := by apply Matrix.ext; unfold raw1803step1 raw1803step0; decide +kernel
      have hl : raw1803step0Labels = labelEmbedding7 ∘ raw1803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1803step0 raw1803step0Labels raw1803step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1804 raw1804Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw1804 raw1804Labels = mixedMoment B raw1804step0 raw1804step0Labels := by
      have ha : raw1804step0 = (fun i j => raw1804 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1804step0 raw1804; decide +kernel
      have hl : raw1804step0Labels = raw1804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1804 raw1804Labels permutation8 permutation4
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1805 raw1805Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw1805 raw1805Labels = mixedMoment B raw1805step0 raw1805step0Labels := by
      have ha : raw1805step0 = (fun i j => raw1805 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1805step0 raw1805; decide +kernel
      have hl : raw1805step0Labels = raw1805Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1805 raw1805Labels permutation8 permutation6
    mixedMoment B raw1805step0 raw1805step0Labels = mixedMoment B raw1805step1 raw1805step1Labels := by
      have ha : raw1805step1 = -raw1805step0 := by apply Matrix.ext; change ∀ i j, raw1805step1 i j = -(raw1805step0 i j); unfold raw1805step1 raw1805step0; decide +kernel
      have hl : raw1805step1Labels = raw1805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1805step1 raw1805step1Labels = mixedMoment B raw1805step2 raw1805step2Labels := by
      have ha : raw1805step2 = raw1805step1 := by apply Matrix.ext; unfold raw1805step2 raw1805step1; decide +kernel
      have hl : raw1805step1Labels = labelEmbedding1 ∘ raw1805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1805step1 raw1805step1Labels raw1805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical1827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1827 raw1827Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw1827 raw1827Labels = mixedMoment B raw1827step0 raw1827step0Labels := by
      have ha : raw1827step0 = (fun i j => raw1827 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1827step0 raw1827; decide +kernel
      have hl : raw1827step0Labels = raw1827Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1827 raw1827Labels permutation8 permutation4
    mixedMoment B raw1827step0 raw1827step0Labels = mixedMoment B raw1827step1 raw1827step1Labels := by
      have ha : raw1827step1 = raw1827step0 := by apply Matrix.ext; unfold raw1827step1 raw1827step0; decide +kernel
      have hl : raw1827step0Labels = labelEmbedding7 ∘ raw1827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1827step0 raw1827step0Labels raw1827step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical1828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1828 raw1828Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1828 raw1828Labels = mixedMoment B raw1828step0 raw1828step0Labels := by
      have ha : raw1828step0 = (fun i j => raw1828 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1828step0 raw1828; decide +kernel
      have hl : raw1828step0Labels = raw1828Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1828 raw1828Labels permutation8 permutation4
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical1829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1829 raw1829Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1829 raw1829Labels = mixedMoment B raw1829step0 raw1829step0Labels := by
      have ha : raw1829step0 = (fun i j => raw1829 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1829step0 raw1829; decide +kernel
      have hl : raw1829step0Labels = raw1829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1829 raw1829Labels permutation13 permutation6
    mixedMoment B raw1829step0 raw1829step0Labels = mixedMoment B raw1829step1 raw1829step1Labels := by
      have ha : raw1829step1 = -raw1829step0 := by apply Matrix.ext; change ∀ i j, raw1829step1 i j = -(raw1829step0 i j); unfold raw1829step1 raw1829step0; decide +kernel
      have hl : raw1829step1Labels = raw1829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1829step1 raw1829step1Labels = mixedMoment B raw1829step2 raw1829step2Labels := by
      have ha : raw1829step2 = raw1829step1 := by apply Matrix.ext; unfold raw1829step2 raw1829step1; decide +kernel
      have hl : raw1829step1Labels = labelEmbedding1 ∘ raw1829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1829step1 raw1829step1Labels raw1829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1830 raw1830Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw1830 raw1830Labels = mixedMoment B raw1830step0 raw1830step0Labels := by
      have ha : raw1830step0 = (fun i j => raw1830 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1830step0 raw1830; decide +kernel
      have hl : raw1830step0Labels = raw1830Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1830 raw1830Labels permutation2 permutation4
    mixedMoment B raw1830step0 raw1830step0Labels = mixedMoment B raw1830step1 raw1830step1Labels := by
      have ha : raw1830step1 = raw1830step0 := by apply Matrix.ext; unfold raw1830step1 raw1830step0; decide +kernel
      have hl : raw1830step0Labels = labelEmbedding7 ∘ raw1830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1830step0 raw1830step0Labels raw1830step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1831 raw1831Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw1831 raw1831Labels = mixedMoment B raw1831step0 raw1831step0Labels := by
      have ha : raw1831step0 = (fun i j => raw1831 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1831step0 raw1831; decide +kernel
      have hl : raw1831step0Labels = raw1831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1831 raw1831Labels permutation2 permutation4
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1832 raw1832Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw1832 raw1832Labels = mixedMoment B raw1832step0 raw1832step0Labels := by
      have ha : raw1832step0 = (fun i j => raw1832 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1832step0 raw1832; decide +kernel
      have hl : raw1832step0Labels = raw1832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1832 raw1832Labels permutation3 permutation6
    mixedMoment B raw1832step0 raw1832step0Labels = mixedMoment B raw1832step1 raw1832step1Labels := by
      have ha : raw1832step1 = -raw1832step0 := by apply Matrix.ext; change ∀ i j, raw1832step1 i j = -(raw1832step0 i j); unfold raw1832step1 raw1832step0; decide +kernel
      have hl : raw1832step1Labels = raw1832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1832step1 raw1832step1Labels = mixedMoment B raw1832step2 raw1832step2Labels := by
      have ha : raw1832step2 = raw1832step1 := by apply Matrix.ext; unfold raw1832step2 raw1832step1; decide +kernel
      have hl : raw1832step1Labels = labelEmbedding1 ∘ raw1832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1832step1 raw1832step1Labels raw1832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

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

theorem canonical2313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2313 raw2313Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2313 raw2313Labels = mixedMoment B raw2313step0 raw2313step0Labels := by
      have ha : raw2313step0 = (fun i j => raw2313 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2313step0 raw2313; decide +kernel
      have hl : raw2313step0Labels = raw2313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2313 raw2313Labels permutation8 permutation5
    mixedMoment B raw2313step0 raw2313step0Labels = mixedMoment B raw2313step1 raw2313step1Labels := by
      have ha : raw2313step1 = raw2313step0 := by apply Matrix.ext; unfold raw2313step1 raw2313step0; decide +kernel
      have hl : raw2313step0Labels = labelEmbedding8 ∘ raw2313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2313step0 raw2313step0Labels raw2313step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2314 raw2314Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw2314 raw2314Labels = mixedMoment B raw2314step0 raw2314step0Labels := by
      have ha : raw2314step0 = (fun i j => raw2314 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2314step0 raw2314; decide +kernel
      have hl : raw2314step0Labels = raw2314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2314 raw2314Labels permutation8 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical2315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2315 raw2315Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw2315 raw2315Labels = mixedMoment B raw2315step0 raw2315step0Labels := by
      have ha : raw2315step0 = (fun i j => raw2315 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2315step0 raw2315; decide +kernel
      have hl : raw2315step0Labels = raw2315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2315 raw2315Labels permutation11 permutation3
    mixedMoment B raw2315step0 raw2315step0Labels = mixedMoment B raw2315step1 raw2315step1Labels := by
      have ha : raw2315step1 = -raw2315step0 := by apply Matrix.ext; change ∀ i j, raw2315step1 i j = -(raw2315step0 i j); unfold raw2315step1 raw2315step0; decide +kernel
      have hl : raw2315step1Labels = raw2315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2315step1 raw2315step1Labels = mixedMoment B raw2315step2 raw2315step2Labels := by
      have ha : raw2315step2 = raw2315step1 := by apply Matrix.ext; unfold raw2315step2 raw2315step1; decide +kernel
      have hl : raw2315step1Labels = labelEmbedding1 ∘ raw2315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2315step1 raw2315step1Labels raw2315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical2325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2325 raw2325Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2325 raw2325Labels = mixedMoment B raw2325step0 raw2325step0Labels := by
      have ha : raw2325step0 = (fun i j => raw2325 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2325step0 raw2325; decide +kernel
      have hl : raw2325step0Labels = raw2325Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2325 raw2325Labels permutation2 permutation4
    mixedMoment B raw2325step0 raw2325step0Labels = mixedMoment B raw2325step1 raw2325step1Labels := by
      have ha : raw2325step1 = raw2325step0 := by apply Matrix.ext; unfold raw2325step1 raw2325step0; decide +kernel
      have hl : raw2325step0Labels = labelEmbedding7 ∘ raw2325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2325step0 raw2325step0Labels raw2325step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical2326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2326 raw2326Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw2326 raw2326Labels = mixedMoment B raw2326step0 raw2326step0Labels := by
      have ha : raw2326step0 = (fun i j => raw2326 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2326step0 raw2326; decide +kernel
      have hl : raw2326step0Labels = raw2326Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2326 raw2326Labels permutation2 permutation4
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2327 raw2327Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw2327 raw2327Labels = mixedMoment B raw2327step0 raw2327step0Labels := by
      have ha : raw2327step0 = (fun i j => raw2327 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2327step0 raw2327; decide +kernel
      have hl : raw2327step0Labels = raw2327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2327 raw2327Labels permutation3 permutation6
    mixedMoment B raw2327step0 raw2327step0Labels = mixedMoment B raw2327step1 raw2327step1Labels := by
      have ha : raw2327step1 = -raw2327step0 := by apply Matrix.ext; change ∀ i j, raw2327step1 i j = -(raw2327step0 i j); unfold raw2327step1 raw2327step0; decide +kernel
      have hl : raw2327step1Labels = raw2327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2327step1 raw2327step1Labels = mixedMoment B raw2327step2 raw2327step2Labels := by
      have ha : raw2327step2 = raw2327step1 := by apply Matrix.ext; unfold raw2327step2 raw2327step1; decide +kernel
      have hl : raw2327step1Labels = labelEmbedding1 ∘ raw2327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2327step1 raw2327step1Labels raw2327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3633 node3633Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw284 raw284Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw284 raw284Labels = mixedMoment B raw284step0 raw284step0Labels := by
      have ha : raw284step0 = (fun i j => raw284 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw284step0 raw284; decide +kernel
      have hl : raw284step0Labels = raw284Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw284 raw284Labels permutation2 permutation5
    mixedMoment B raw284step0 raw284step0Labels = mixedMoment B raw284step1 raw284step1Labels := by
      have ha : raw284step1 = raw284step0 := by apply Matrix.ext; unfold raw284step1 raw284step0; decide +kernel
      have hl : raw284step0Labels = labelEmbedding1 ∘ raw284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw284step0 raw284step0Labels raw284step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw285 raw285Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw285 raw285Labels = mixedMoment B raw285step0 raw285step0Labels := by
      have ha : raw285step0 = (fun i j => raw285 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw285step0 raw285; decide +kernel
      have hl : raw285step0Labels = raw285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw285 raw285Labels permutation2 permutation5
    _ = mixedMoment B node420 node420Labels := by rfl

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

theorem canonical2568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2568 raw2568Labels = mixedMoment B node5456 node5456Labels := by
  calc
    _ = mixedMoment B node5456 node5456Labels := by rfl

theorem canonical2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2569 raw2569Labels = mixedMoment B node3916 node3916Labels := by
  calc
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical2570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2570 raw2570Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw2570 raw2570Labels = mixedMoment B raw2570step0 raw2570step0Labels := by
      have ha : raw2570step0 = (fun i j => raw2570 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2570step0 raw2570; decide +kernel
      have hl : raw2570step0Labels = raw2570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2570 raw2570Labels permutation7 permutation3
    mixedMoment B raw2570step0 raw2570step0Labels = mixedMoment B raw2570step1 raw2570step1Labels := by
      have ha : raw2570step1 = -raw2570step0 := by apply Matrix.ext; change ∀ i j, raw2570step1 i j = -(raw2570step0 i j); unfold raw2570step1 raw2570step0; decide +kernel
      have hl : raw2570step1Labels = raw2570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2570step1 raw2570step1Labels = mixedMoment B raw2570step2 raw2570step2Labels := by
      have ha : raw2570step2 = raw2570step1 := by apply Matrix.ext; unfold raw2570step2 raw2570step1; decide +kernel
      have hl : raw2570step1Labels = labelEmbedding1 ∘ raw2570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2570step1 raw2570step1Labels raw2570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical2636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2636 raw2636Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2636 raw2636Labels = mixedMoment B raw2636step0 raw2636step0Labels := by
      have hz : ∀ j, raw2636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2636step0 = (fun i j => raw2636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2636step0 raw2636; decide +kernel
      have hl : raw2636step0Labels = raw2636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2636 raw2636Labels permutation434 hz
    mixedMoment B raw2636step0 raw2636step0Labels = mixedMoment B raw2636step1 raw2636step1Labels := by
      have hz : ∀ j, raw2636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2636step1 = (fun i j => raw2636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2636step1 raw2636step0; decide +kernel
      have hl : raw2636step1Labels = raw2636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2636step0 raw2636step0Labels permutation80 hz
    mixedMoment B raw2636step1 raw2636step1Labels = mixedMoment B raw2636step2 raw2636step2Labels := by
      have ha : raw2636step2 = (fun i j => raw2636step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2636step2 raw2636step1; decide +kernel
      have hl : raw2636step2Labels = raw2636step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2636step1 raw2636step1Labels permutation10 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2641 raw2641Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2641 raw2641Labels = mixedMoment B raw2641step0 raw2641step0Labels := by
      have hz : ∀ j, raw2641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2641step0 = (fun i j => raw2641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2641step0 raw2641; decide +kernel
      have hl : raw2641step0Labels = raw2641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2641 raw2641Labels permutation434 hz
    mixedMoment B raw2641step0 raw2641step0Labels = mixedMoment B raw2641step1 raw2641step1Labels := by
      have hz : ∀ j, raw2641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2641step1 = (fun i j => raw2641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2641step1 raw2641step0; decide +kernel
      have hl : raw2641step1Labels = raw2641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2641step0 raw2641step0Labels permutation56 hz
    mixedMoment B raw2641step1 raw2641step1Labels = mixedMoment B raw2641step2 raw2641step2Labels := by
      have ha : raw2641step2 = (fun i j => raw2641step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2641step2 raw2641step1; decide +kernel
      have hl : raw2641step2Labels = raw2641step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2641step1 raw2641step1Labels permutation10 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2646 raw2646Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2646 raw2646Labels = mixedMoment B raw2646step0 raw2646step0Labels := by
      have hz : ∀ j, raw2646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2646step0 = (fun i j => raw2646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2646step0 raw2646; decide +kernel
      have hl : raw2646step0Labels = raw2646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2646 raw2646Labels permutation346 hz
    mixedMoment B raw2646step0 raw2646step0Labels = mixedMoment B raw2646step1 raw2646step1Labels := by
      have hz : ∀ j, raw2646step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2646step1 = (fun i j => raw2646step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2646step1 raw2646step0; decide +kernel
      have hl : raw2646step1Labels = raw2646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2646step0 raw2646step0Labels permutation56 hz
    mixedMoment B raw2646step1 raw2646step1Labels = mixedMoment B raw2646step2 raw2646step2Labels := by
      have ha : raw2646step2 = (fun i j => raw2646step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2646step2 raw2646step1; decide +kernel
      have hl : raw2646step2Labels = raw2646step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2646step1 raw2646step1Labels permutation10 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2651 raw2651Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2651 raw2651Labels = mixedMoment B raw2651step0 raw2651step0Labels := by
      have hz : ∀ j, raw2651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2651step0 = (fun i j => raw2651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2651step0 raw2651; decide +kernel
      have hl : raw2651step0Labels = raw2651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2651 raw2651Labels permutation434 hz
    mixedMoment B raw2651step0 raw2651step0Labels = mixedMoment B raw2651step1 raw2651step1Labels := by
      have hz : ∀ j, raw2651step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2651step1 = (fun i j => raw2651step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2651step1 raw2651step0; decide +kernel
      have hl : raw2651step1Labels = raw2651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2651step0 raw2651step0Labels permutation80 hz
    mixedMoment B raw2651step1 raw2651step1Labels = mixedMoment B raw2651step2 raw2651step2Labels := by
      have hz : ∀ j, raw2651step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2651step2 = (fun i j => raw2651step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2651step2 raw2651step1; decide +kernel
      have hl : raw2651step2Labels = raw2651step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2651step1 raw2651step1Labels permutation14 hz
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2657 raw2657Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw2657 raw2657Labels = mixedMoment B raw2657step0 raw2657step0Labels := by
      have hz : ∀ j, raw2657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2657step0 = (fun i j => raw2657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2657step0 raw2657; decide +kernel
      have hl : raw2657step0Labels = raw2657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2657 raw2657Labels permutation434 hz
    mixedMoment B raw2657step0 raw2657step0Labels = mixedMoment B raw2657step1 raw2657step1Labels := by
      have hz : ∀ j, raw2657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2657step1 = (fun i j => raw2657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2657step1 raw2657step0; decide +kernel
      have hl : raw2657step1Labels = raw2657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2657step0 raw2657step0Labels permutation80 hz
    mixedMoment B raw2657step1 raw2657step1Labels = mixedMoment B raw2657step2 raw2657step2Labels := by
      have ha : raw2657step2 = (fun i j => raw2657step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2657step2 raw2657step1; decide +kernel
      have hl : raw2657step2Labels = raw2657step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2657step1 raw2657step1Labels permutation31 permutation3
    mixedMoment B raw2657step2 raw2657step2Labels = mixedMoment B raw2657step3 raw2657step3Labels := by
      have ha : raw2657step3 = -raw2657step2 := by apply Matrix.ext; change ∀ i j, raw2657step3 i j = -(raw2657step2 i j); unfold raw2657step3 raw2657step2; decide +kernel
      have hl : raw2657step3Labels = raw2657step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2657step3 raw2657step3Labels = mixedMoment B raw2657step4 raw2657step4Labels := by
      have ha : raw2657step4 = raw2657step3 := by apply Matrix.ext; unfold raw2657step4 raw2657step3; decide +kernel
      have hl : raw2657step3Labels = labelEmbedding6 ∘ raw2657step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2657step3 raw2657step3Labels raw2657step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2658 raw2658Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw2658 raw2658Labels = mixedMoment B raw2658step0 raw2658step0Labels := by
      have hz : ∀ j, raw2658 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2658step0 = (fun i j => raw2658 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2658step0 raw2658; decide +kernel
      have hl : raw2658step0Labels = raw2658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2658 raw2658Labels permutation434 hz
    mixedMoment B raw2658step0 raw2658step0Labels = mixedMoment B raw2658step1 raw2658step1Labels := by
      have hz : ∀ j, raw2658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2658step1 = (fun i j => raw2658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2658step1 raw2658step0; decide +kernel
      have hl : raw2658step1Labels = raw2658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2658step0 raw2658step0Labels permutation56 hz
    mixedMoment B raw2658step1 raw2658step1Labels = mixedMoment B raw2658step2 raw2658step2Labels := by
      have ha : raw2658step2 = (fun i j => raw2658step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2658step2 raw2658step1; decide +kernel
      have hl : raw2658step2Labels = raw2658step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2658step1 raw2658step1Labels permutation31 permutation3
    mixedMoment B raw2658step2 raw2658step2Labels = mixedMoment B raw2658step3 raw2658step3Labels := by
      have ha : raw2658step3 = -raw2658step2 := by apply Matrix.ext; change ∀ i j, raw2658step3 i j = -(raw2658step2 i j); unfold raw2658step3 raw2658step2; decide +kernel
      have hl : raw2658step3Labels = raw2658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2658step3 raw2658step3Labels = mixedMoment B raw2658step4 raw2658step4Labels := by
      have ha : raw2658step4 = raw2658step3 := by apply Matrix.ext; unfold raw2658step4 raw2658step3; decide +kernel
      have hl : raw2658step3Labels = labelEmbedding6 ∘ raw2658step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2658step3 raw2658step3Labels raw2658step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical2659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2659 raw2659Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw2659 raw2659Labels = mixedMoment B raw2659step0 raw2659step0Labels := by
      have hz : ∀ j, raw2659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2659step0 = (fun i j => raw2659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2659step0 raw2659; decide +kernel
      have hl : raw2659step0Labels = raw2659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2659 raw2659Labels permutation346 hz
    mixedMoment B raw2659step0 raw2659step0Labels = mixedMoment B raw2659step1 raw2659step1Labels := by
      have hz : ∀ j, raw2659step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2659step1 = (fun i j => raw2659step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2659step1 raw2659step0; decide +kernel
      have hl : raw2659step1Labels = raw2659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2659step0 raw2659step0Labels permutation56 hz
    mixedMoment B raw2659step1 raw2659step1Labels = mixedMoment B raw2659step2 raw2659step2Labels := by
      have ha : raw2659step2 = (fun i j => raw2659step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2659step2 raw2659step1; decide +kernel
      have hl : raw2659step2Labels = raw2659step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2659step1 raw2659step1Labels permutation31 permutation3
    mixedMoment B raw2659step2 raw2659step2Labels = mixedMoment B raw2659step3 raw2659step3Labels := by
      have ha : raw2659step3 = -raw2659step2 := by apply Matrix.ext; change ∀ i j, raw2659step3 i j = -(raw2659step2 i j); unfold raw2659step3 raw2659step2; decide +kernel
      have hl : raw2659step3Labels = raw2659step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2659step3 raw2659step3Labels = mixedMoment B raw2659step4 raw2659step4Labels := by
      have ha : raw2659step4 = raw2659step3 := by apply Matrix.ext; unfold raw2659step4 raw2659step3; decide +kernel
      have hl : raw2659step3Labels = labelEmbedding6 ∘ raw2659step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2659step3 raw2659step3Labels raw2659step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical2660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2660 raw2660Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw2660 raw2660Labels = mixedMoment B raw2660step0 raw2660step0Labels := by
      have hz : ∀ j, raw2660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2660step0 = (fun i j => raw2660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2660step0 raw2660; decide +kernel
      have hl : raw2660step0Labels = raw2660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2660 raw2660Labels permutation434 hz
    mixedMoment B raw2660step0 raw2660step0Labels = mixedMoment B raw2660step1 raw2660step1Labels := by
      have hz : ∀ j, raw2660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2660step1 = (fun i j => raw2660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2660step1 raw2660step0; decide +kernel
      have hl : raw2660step1Labels = raw2660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2660step0 raw2660step0Labels permutation80 hz
    mixedMoment B raw2660step1 raw2660step1Labels = mixedMoment B raw2660step2 raw2660step2Labels := by
      have hz : ∀ j, raw2660step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2660step2 = (fun i j => raw2660step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2660step2 raw2660step1; decide +kernel
      have hl : raw2660step2Labels = raw2660step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2660step1 raw2660step1Labels permutation14 hz
    mixedMoment B raw2660step2 raw2660step2Labels = mixedMoment B raw2660step3 raw2660step3Labels := by
      have ha : raw2660step3 = (fun i j => raw2660step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2660step3 raw2660step2; decide +kernel
      have hl : raw2660step3Labels = raw2660step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2660step2 raw2660step2Labels permutation6 permutation5
    mixedMoment B raw2660step3 raw2660step3Labels = mixedMoment B raw2660step4 raw2660step4Labels := by
      have ha : raw2660step4 = raw2660step3 := by apply Matrix.ext; unfold raw2660step4 raw2660step3; decide +kernel
      have hl : raw2660step3Labels = labelEmbedding8 ∘ raw2660step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2660step3 raw2660step3Labels raw2660step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4379 raw4379Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw4379 raw4379Labels = mixedMoment B raw4379step0 raw4379step0Labels := by
      have hz : ∀ j, raw4379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4379step0 = (fun i j => raw4379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4379step0 raw4379; decide +kernel
      have hl : raw4379step0Labels = raw4379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4379 raw4379Labels permutation434 hz
    mixedMoment B raw4379step0 raw4379step0Labels = mixedMoment B raw4379step1 raw4379step1Labels := by
      have hz : ∀ j, raw4379step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4379step1 = (fun i j => raw4379step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4379step1 raw4379step0; decide +kernel
      have hl : raw4379step1Labels = raw4379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4379step0 raw4379step0Labels permutation80 hz
    mixedMoment B raw4379step1 raw4379step1Labels = mixedMoment B raw4379step2 raw4379step2Labels := by
      have hz : ∀ j, raw4379step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4379step2 = (fun i j => raw4379step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4379step2 raw4379step1; decide +kernel
      have hl : raw4379step2Labels = raw4379step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4379step1 raw4379step1Labels permutation14 hz
    _ = mixedMoment B node5456 node5456Labels := by rfl

theorem canonical4380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4380 raw4380Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw4380 raw4380Labels = mixedMoment B raw4380step0 raw4380step0Labels := by
      have hz : ∀ j, raw4380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4380step0 = (fun i j => raw4380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4380step0 raw4380; decide +kernel
      have hl : raw4380step0Labels = raw4380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4380 raw4380Labels permutation434 hz
    mixedMoment B raw4380step0 raw4380step0Labels = mixedMoment B raw4380step1 raw4380step1Labels := by
      have hz : ∀ j, raw4380step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4380step1 = (fun i j => raw4380step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4380step1 raw4380step0; decide +kernel
      have hl : raw4380step1Labels = raw4380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4380step0 raw4380step0Labels permutation80 hz
    mixedMoment B raw4380step1 raw4380step1Labels = mixedMoment B raw4380step2 raw4380step2Labels := by
      have ha : raw4380step2 = (fun i j => raw4380step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4380step2 raw4380step1; decide +kernel
      have hl : raw4380step2Labels = raw4380step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4380step1 raw4380step1Labels permutation10 permutation3
    mixedMoment B raw4380step2 raw4380step2Labels = mixedMoment B raw4380step3 raw4380step3Labels := by
      have ha : raw4380step3 = raw4380step2 := by apply Matrix.ext; unfold raw4380step3 raw4380step2; decide +kernel
      have hl : raw4380step2Labels = labelEmbedding6 ∘ raw4380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4380step2 raw4380step2Labels raw4380step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

theorem canonical4381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4381 raw4381Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4381 raw4381Labels = mixedMoment B raw4381step0 raw4381step0Labels := by
      have hz : ∀ j, raw4381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4381step0 = (fun i j => raw4381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4381step0 raw4381; decide +kernel
      have hl : raw4381step0Labels = raw4381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4381 raw4381Labels permutation434 hz
    mixedMoment B raw4381step0 raw4381step0Labels = mixedMoment B raw4381step1 raw4381step1Labels := by
      have ha : raw4381step1 = (fun i j => raw4381step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4381step1 raw4381step0; decide +kernel
      have hl : raw4381step1Labels = raw4381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4381step0 raw4381step0Labels permutation139 permutation3
    mixedMoment B raw4381step1 raw4381step1Labels = mixedMoment B raw4381step2 raw4381step2Labels := by
      have ha : raw4381step2 = -raw4381step1 := by apply Matrix.ext; change ∀ i j, raw4381step2 i j = -(raw4381step1 i j); unfold raw4381step2 raw4381step1; decide +kernel
      have hl : raw4381step2Labels = raw4381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4381step2 raw4381step2Labels = mixedMoment B raw4381step3 raw4381step3Labels := by
      have ha : raw4381step3 = raw4381step2 := by apply Matrix.ext; unfold raw4381step3 raw4381step2; decide +kernel
      have hl : raw4381step2Labels = labelEmbedding6 ∘ raw4381step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4381step2 raw4381step2Labels raw4381step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical4382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4382 raw4382Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4382 raw4382Labels = mixedMoment B raw4382step0 raw4382step0Labels := by
      have hz : ∀ j, raw4382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4382step0 = (fun i j => raw4382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4382step0 raw4382; decide +kernel
      have hl : raw4382step0Labels = raw4382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4382 raw4382Labels permutation346 hz
    mixedMoment B raw4382step0 raw4382step0Labels = mixedMoment B raw4382step1 raw4382step1Labels := by
      have ha : raw4382step1 = (fun i j => raw4382step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4382step1 raw4382step0; decide +kernel
      have hl : raw4382step1Labels = raw4382step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4382step0 raw4382step0Labels permutation139 permutation3
    mixedMoment B raw4382step1 raw4382step1Labels = mixedMoment B raw4382step2 raw4382step2Labels := by
      have ha : raw4382step2 = -raw4382step1 := by apply Matrix.ext; change ∀ i j, raw4382step2 i j = -(raw4382step1 i j); unfold raw4382step2 raw4382step1; decide +kernel
      have hl : raw4382step2Labels = raw4382step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4382step2 raw4382step2Labels = mixedMoment B raw4382step3 raw4382step3Labels := by
      have ha : raw4382step3 = raw4382step2 := by apply Matrix.ext; unfold raw4382step3 raw4382step2; decide +kernel
      have hl : raw4382step2Labels = labelEmbedding6 ∘ raw4382step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4382step2 raw4382step2Labels raw4382step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical4383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4383 raw4383Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw4383 raw4383Labels = mixedMoment B raw4383step0 raw4383step0Labels := by
      have hz : ∀ j, raw4383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4383step0 = (fun i j => raw4383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4383step0 raw4383; decide +kernel
      have hl : raw4383step0Labels = raw4383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4383 raw4383Labels permutation434 hz
    mixedMoment B raw4383step0 raw4383step0Labels = mixedMoment B raw4383step1 raw4383step1Labels := by
      have hz : ∀ j, raw4383step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4383step1 = (fun i j => raw4383step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4383step1 raw4383step0; decide +kernel
      have hl : raw4383step1Labels = raw4383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4383step0 raw4383step0Labels permutation80 hz
    mixedMoment B raw4383step1 raw4383step1Labels = mixedMoment B raw4383step2 raw4383step2Labels := by
      have ha : raw4383step2 = (fun i j => raw4383step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4383step2 raw4383step1; decide +kernel
      have hl : raw4383step2Labels = raw4383step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4383step1 raw4383step1Labels permutation29 permutation3
    mixedMoment B raw4383step2 raw4383step2Labels = mixedMoment B raw4383step3 raw4383step3Labels := by
      have ha : raw4383step3 = -raw4383step2 := by apply Matrix.ext; change ∀ i j, raw4383step3 i j = -(raw4383step2 i j); unfold raw4383step3 raw4383step2; decide +kernel
      have hl : raw4383step3Labels = raw4383step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4383step3 raw4383step3Labels = mixedMoment B raw4383step4 raw4383step4Labels := by
      have ha : raw4383step4 = raw4383step3 := by apply Matrix.ext; unfold raw4383step4 raw4383step3; decide +kernel
      have hl : raw4383step3Labels = labelEmbedding6 ∘ raw4383step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4383step3 raw4383step3Labels raw4383step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

theorem canonical4384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4384 raw4384Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw4384 raw4384Labels = mixedMoment B raw4384step0 raw4384step0Labels := by
      have hz : ∀ j, raw4384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4384step0 = (fun i j => raw4384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4384step0 raw4384; decide +kernel
      have hl : raw4384step0Labels = raw4384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4384 raw4384Labels permutation434 hz
    mixedMoment B raw4384step0 raw4384step0Labels = mixedMoment B raw4384step1 raw4384step1Labels := by
      have hz : ∀ j, raw4384step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4384step1 = (fun i j => raw4384step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4384step1 raw4384step0; decide +kernel
      have hl : raw4384step1Labels = raw4384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4384step0 raw4384step0Labels permutation56 hz
    mixedMoment B raw4384step1 raw4384step1Labels = mixedMoment B raw4384step2 raw4384step2Labels := by
      have ha : raw4384step2 = (fun i j => raw4384step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4384step2 raw4384step1; decide +kernel
      have hl : raw4384step2Labels = raw4384step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4384step1 raw4384step1Labels permutation10 permutation3
    mixedMoment B raw4384step2 raw4384step2Labels = mixedMoment B raw4384step3 raw4384step3Labels := by
      have ha : raw4384step3 = raw4384step2 := by apply Matrix.ext; unfold raw4384step3 raw4384step2; decide +kernel
      have hl : raw4384step2Labels = labelEmbedding6 ∘ raw4384step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4384step2 raw4384step2Labels raw4384step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

theorem canonical4385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4385 raw4385Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4385 raw4385Labels = mixedMoment B raw4385step0 raw4385step0Labels := by
      have hz : ∀ j, raw4385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4385step0 = (fun i j => raw4385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4385step0 raw4385; decide +kernel
      have hl : raw4385step0Labels = raw4385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4385 raw4385Labels permutation434 hz
    mixedMoment B raw4385step0 raw4385step0Labels = mixedMoment B raw4385step1 raw4385step1Labels := by
      have ha : raw4385step1 = (fun i j => raw4385step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4385step1 raw4385step0; decide +kernel
      have hl : raw4385step1Labels = raw4385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4385step0 raw4385step0Labels permutation145 permutation3
    mixedMoment B raw4385step1 raw4385step1Labels = mixedMoment B raw4385step2 raw4385step2Labels := by
      have ha : raw4385step2 = -raw4385step1 := by apply Matrix.ext; change ∀ i j, raw4385step2 i j = -(raw4385step1 i j); unfold raw4385step2 raw4385step1; decide +kernel
      have hl : raw4385step2Labels = raw4385step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4385step2 raw4385step2Labels = mixedMoment B raw4385step3 raw4385step3Labels := by
      have ha : raw4385step3 = raw4385step2 := by apply Matrix.ext; unfold raw4385step3 raw4385step2; decide +kernel
      have hl : raw4385step2Labels = labelEmbedding6 ∘ raw4385step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4385step2 raw4385step2Labels raw4385step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical4386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4386 raw4386Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4386 raw4386Labels = mixedMoment B raw4386step0 raw4386step0Labels := by
      have hz : ∀ j, raw4386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4386step0 = (fun i j => raw4386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4386step0 raw4386; decide +kernel
      have hl : raw4386step0Labels = raw4386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4386 raw4386Labels permutation265 hz
    mixedMoment B raw4386step0 raw4386step0Labels = mixedMoment B raw4386step1 raw4386step1Labels := by
      have ha : raw4386step1 = (fun i j => raw4386step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4386step1 raw4386step0; decide +kernel
      have hl : raw4386step1Labels = raw4386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4386step0 raw4386step0Labels permutation139 permutation3
    mixedMoment B raw4386step1 raw4386step1Labels = mixedMoment B raw4386step2 raw4386step2Labels := by
      have ha : raw4386step2 = -raw4386step1 := by apply Matrix.ext; change ∀ i j, raw4386step2 i j = -(raw4386step1 i j); unfold raw4386step2 raw4386step1; decide +kernel
      have hl : raw4386step2Labels = raw4386step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4386step2 raw4386step2Labels = mixedMoment B raw4386step3 raw4386step3Labels := by
      have ha : raw4386step3 = raw4386step2 := by apply Matrix.ext; unfold raw4386step3 raw4386step2; decide +kernel
      have hl : raw4386step2Labels = labelEmbedding6 ∘ raw4386step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4386step2 raw4386step2Labels raw4386step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical4387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4387 raw4387Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw4387 raw4387Labels = mixedMoment B raw4387step0 raw4387step0Labels := by
      have hz : ∀ j, raw4387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4387step0 = (fun i j => raw4387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4387step0 raw4387; decide +kernel
      have hl : raw4387step0Labels = raw4387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4387 raw4387Labels permutation434 hz
    mixedMoment B raw4387step0 raw4387step0Labels = mixedMoment B raw4387step1 raw4387step1Labels := by
      have hz : ∀ j, raw4387step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4387step1 = (fun i j => raw4387step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4387step1 raw4387step0; decide +kernel
      have hl : raw4387step1Labels = raw4387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4387step0 raw4387step0Labels permutation56 hz
    mixedMoment B raw4387step1 raw4387step1Labels = mixedMoment B raw4387step2 raw4387step2Labels := by
      have ha : raw4387step2 = (fun i j => raw4387step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4387step2 raw4387step1; decide +kernel
      have hl : raw4387step2Labels = raw4387step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4387step1 raw4387step1Labels permutation29 permutation3
    mixedMoment B raw4387step2 raw4387step2Labels = mixedMoment B raw4387step3 raw4387step3Labels := by
      have ha : raw4387step3 = -raw4387step2 := by apply Matrix.ext; change ∀ i j, raw4387step3 i j = -(raw4387step2 i j); unfold raw4387step3 raw4387step2; decide +kernel
      have hl : raw4387step3Labels = raw4387step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4387step3 raw4387step3Labels = mixedMoment B raw4387step4 raw4387step4Labels := by
      have ha : raw4387step4 = raw4387step3 := by apply Matrix.ext; unfold raw4387step4 raw4387step3; decide +kernel
      have hl : raw4387step3Labels = labelEmbedding6 ∘ raw4387step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4387step3 raw4387step3Labels raw4387step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

theorem canonical4388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4388 raw4388Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw4388 raw4388Labels = mixedMoment B raw4388step0 raw4388step0Labels := by
      have hz : ∀ j, raw4388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4388step0 = (fun i j => raw4388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4388step0 raw4388; decide +kernel
      have hl : raw4388step0Labels = raw4388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4388 raw4388Labels permutation346 hz
    mixedMoment B raw4388step0 raw4388step0Labels = mixedMoment B raw4388step1 raw4388step1Labels := by
      have hz : ∀ j, raw4388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4388step1 = (fun i j => raw4388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4388step1 raw4388step0; decide +kernel
      have hl : raw4388step1Labels = raw4388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4388step0 raw4388step0Labels permutation56 hz
    mixedMoment B raw4388step1 raw4388step1Labels = mixedMoment B raw4388step2 raw4388step2Labels := by
      have ha : raw4388step2 = (fun i j => raw4388step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4388step2 raw4388step1; decide +kernel
      have hl : raw4388step2Labels = raw4388step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4388step1 raw4388step1Labels permutation10 permutation3
    mixedMoment B raw4388step2 raw4388step2Labels = mixedMoment B raw4388step3 raw4388step3Labels := by
      have ha : raw4388step3 = raw4388step2 := by apply Matrix.ext; unfold raw4388step3 raw4388step2; decide +kernel
      have hl : raw4388step2Labels = labelEmbedding6 ∘ raw4388step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4388step2 raw4388step2Labels raw4388step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

theorem canonical4389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4389 raw4389Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4389 raw4389Labels = mixedMoment B raw4389step0 raw4389step0Labels := by
      have hz : ∀ j, raw4389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4389step0 = (fun i j => raw4389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4389step0 raw4389; decide +kernel
      have hl : raw4389step0Labels = raw4389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4389 raw4389Labels permutation346 hz
    mixedMoment B raw4389step0 raw4389step0Labels = mixedMoment B raw4389step1 raw4389step1Labels := by
      have ha : raw4389step1 = (fun i j => raw4389step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4389step1 raw4389step0; decide +kernel
      have hl : raw4389step1Labels = raw4389step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4389step0 raw4389step0Labels permutation145 permutation3
    mixedMoment B raw4389step1 raw4389step1Labels = mixedMoment B raw4389step2 raw4389step2Labels := by
      have ha : raw4389step2 = -raw4389step1 := by apply Matrix.ext; change ∀ i j, raw4389step2 i j = -(raw4389step1 i j); unfold raw4389step2 raw4389step1; decide +kernel
      have hl : raw4389step2Labels = raw4389step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4389step2 raw4389step2Labels = mixedMoment B raw4389step3 raw4389step3Labels := by
      have ha : raw4389step3 = raw4389step2 := by apply Matrix.ext; unfold raw4389step3 raw4389step2; decide +kernel
      have hl : raw4389step2Labels = labelEmbedding6 ∘ raw4389step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4389step2 raw4389step2Labels raw4389step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical4390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4390 raw4390Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw4390 raw4390Labels = mixedMoment B raw4390step0 raw4390step0Labels := by
      have hz : ∀ j, raw4390 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4390step0 = (fun i j => raw4390 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4390step0 raw4390; decide +kernel
      have hl : raw4390step0Labels = raw4390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4390 raw4390Labels permutation265 hz
    mixedMoment B raw4390step0 raw4390step0Labels = mixedMoment B raw4390step1 raw4390step1Labels := by
      have ha : raw4390step1 = (fun i j => raw4390step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4390step1 raw4390step0; decide +kernel
      have hl : raw4390step1Labels = raw4390step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4390step0 raw4390step0Labels permutation145 permutation3
    mixedMoment B raw4390step1 raw4390step1Labels = mixedMoment B raw4390step2 raw4390step2Labels := by
      have ha : raw4390step2 = -raw4390step1 := by apply Matrix.ext; change ∀ i j, raw4390step2 i j = -(raw4390step1 i j); unfold raw4390step2 raw4390step1; decide +kernel
      have hl : raw4390step2Labels = raw4390step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4390step2 raw4390step2Labels = mixedMoment B raw4390step3 raw4390step3Labels := by
      have ha : raw4390step3 = raw4390step2 := by apply Matrix.ext; unfold raw4390step3 raw4390step2; decide +kernel
      have hl : raw4390step2Labels = labelEmbedding6 ∘ raw4390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4390step2 raw4390step2Labels raw4390step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

theorem canonical4391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4391 raw4391Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw4391 raw4391Labels = mixedMoment B raw4391step0 raw4391step0Labels := by
      have hz : ∀ j, raw4391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4391step0 = (fun i j => raw4391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4391step0 raw4391; decide +kernel
      have hl : raw4391step0Labels = raw4391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4391 raw4391Labels permutation346 hz
    mixedMoment B raw4391step0 raw4391step0Labels = mixedMoment B raw4391step1 raw4391step1Labels := by
      have hz : ∀ j, raw4391step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4391step1 = (fun i j => raw4391step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4391step1 raw4391step0; decide +kernel
      have hl : raw4391step1Labels = raw4391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4391step0 raw4391step0Labels permutation56 hz
    mixedMoment B raw4391step1 raw4391step1Labels = mixedMoment B raw4391step2 raw4391step2Labels := by
      have ha : raw4391step2 = (fun i j => raw4391step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4391step2 raw4391step1; decide +kernel
      have hl : raw4391step2Labels = raw4391step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4391step1 raw4391step1Labels permutation29 permutation3
    mixedMoment B raw4391step2 raw4391step2Labels = mixedMoment B raw4391step3 raw4391step3Labels := by
      have ha : raw4391step3 = -raw4391step2 := by apply Matrix.ext; change ∀ i j, raw4391step3 i j = -(raw4391step2 i j); unfold raw4391step3 raw4391step2; decide +kernel
      have hl : raw4391step3Labels = raw4391step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4391step3 raw4391step3Labels = mixedMoment B raw4391step4 raw4391step4Labels := by
      have ha : raw4391step4 = raw4391step3 := by apply Matrix.ext; unfold raw4391step4 raw4391step3; decide +kernel
      have hl : raw4391step3Labels = labelEmbedding6 ∘ raw4391step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4391step3 raw4391step3Labels raw4391step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

theorem canonical4392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4392 raw4392Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw4392 raw4392Labels = mixedMoment B raw4392step0 raw4392step0Labels := by
      have hz : ∀ j, raw4392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4392step0 = (fun i j => raw4392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4392step0 raw4392; decide +kernel
      have hl : raw4392step0Labels = raw4392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4392 raw4392Labels permutation434 hz
    mixedMoment B raw4392step0 raw4392step0Labels = mixedMoment B raw4392step1 raw4392step1Labels := by
      have hz : ∀ j, raw4392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4392step1 = (fun i j => raw4392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4392step1 raw4392step0; decide +kernel
      have hl : raw4392step1Labels = raw4392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4392step0 raw4392step0Labels permutation80 hz
    mixedMoment B raw4392step1 raw4392step1Labels = mixedMoment B raw4392step2 raw4392step2Labels := by
      have hz : ∀ j, raw4392step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4392step2 = (fun i j => raw4392step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4392step2 raw4392step1; decide +kernel
      have hl : raw4392step2Labels = raw4392step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4392step1 raw4392step1Labels permutation14 hz
    mixedMoment B raw4392step2 raw4392step2Labels = mixedMoment B raw4392step3 raw4392step3Labels := by
      have ha : raw4392step3 = (fun i j => raw4392step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4392step3 raw4392step2; decide +kernel
      have hl : raw4392step3Labels = raw4392step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4392step2 raw4392step2Labels permutation2 permutation3
    mixedMoment B raw4392step3 raw4392step3Labels = mixedMoment B raw4392step4 raw4392step4Labels := by
      have ha : raw4392step4 = raw4392step3 := by apply Matrix.ext; unfold raw4392step4 raw4392step3; decide +kernel
      have hl : raw4392step3Labels = labelEmbedding6 ∘ raw4392step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4392step3 raw4392step3Labels raw4392step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical4393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4393 raw4393Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw4393 raw4393Labels = mixedMoment B raw4393step0 raw4393step0Labels := by
      have hz : ∀ j, raw4393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4393step0 = (fun i j => raw4393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4393step0 raw4393; decide +kernel
      have hl : raw4393step0Labels = raw4393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4393 raw4393Labels permutation434 hz
    mixedMoment B raw4393step0 raw4393step0Labels = mixedMoment B raw4393step1 raw4393step1Labels := by
      have hz : ∀ j, raw4393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4393step1 = (fun i j => raw4393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4393step1 raw4393step0; decide +kernel
      have hl : raw4393step1Labels = raw4393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4393step0 raw4393step0Labels permutation80 hz
    mixedMoment B raw4393step1 raw4393step1Labels = mixedMoment B raw4393step2 raw4393step2Labels := by
      have ha : raw4393step2 = (fun i j => raw4393step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4393step2 raw4393step1; decide +kernel
      have hl : raw4393step2Labels = raw4393step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4393step1 raw4393step1Labels permutation31 permutation3
    mixedMoment B raw4393step2 raw4393step2Labels = mixedMoment B raw4393step3 raw4393step3Labels := by
      have ha : raw4393step3 = -raw4393step2 := by apply Matrix.ext; change ∀ i j, raw4393step3 i j = -(raw4393step2 i j); unfold raw4393step3 raw4393step2; decide +kernel
      have hl : raw4393step3Labels = raw4393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4393step3 raw4393step3Labels = mixedMoment B raw4393step4 raw4393step4Labels := by
      have ha : raw4393step4 = raw4393step3 := by apply Matrix.ext; unfold raw4393step4 raw4393step3; decide +kernel
      have hl : raw4393step3Labels = labelEmbedding6 ∘ raw4393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4393step3 raw4393step3Labels raw4393step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical4394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4394 raw4394Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw4394 raw4394Labels = mixedMoment B raw4394step0 raw4394step0Labels := by
      have hz : ∀ j, raw4394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4394step0 = (fun i j => raw4394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4394step0 raw4394; decide +kernel
      have hl : raw4394step0Labels = raw4394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4394 raw4394Labels permutation434 hz
    mixedMoment B raw4394step0 raw4394step0Labels = mixedMoment B raw4394step1 raw4394step1Labels := by
      have hz : ∀ j, raw4394step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4394step1 = (fun i j => raw4394step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4394step1 raw4394step0; decide +kernel
      have hl : raw4394step1Labels = raw4394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4394step0 raw4394step0Labels permutation56 hz
    mixedMoment B raw4394step1 raw4394step1Labels = mixedMoment B raw4394step2 raw4394step2Labels := by
      have ha : raw4394step2 = (fun i j => raw4394step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4394step2 raw4394step1; decide +kernel
      have hl : raw4394step2Labels = raw4394step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4394step1 raw4394step1Labels permutation31 permutation3
    mixedMoment B raw4394step2 raw4394step2Labels = mixedMoment B raw4394step3 raw4394step3Labels := by
      have ha : raw4394step3 = -raw4394step2 := by apply Matrix.ext; change ∀ i j, raw4394step3 i j = -(raw4394step2 i j); unfold raw4394step3 raw4394step2; decide +kernel
      have hl : raw4394step3Labels = raw4394step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4394step3 raw4394step3Labels = mixedMoment B raw4394step4 raw4394step4Labels := by
      have ha : raw4394step4 = raw4394step3 := by apply Matrix.ext; unfold raw4394step4 raw4394step3; decide +kernel
      have hl : raw4394step3Labels = labelEmbedding6 ∘ raw4394step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4394step3 raw4394step3Labels raw4394step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical4395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4395 raw4395Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw4395 raw4395Labels = mixedMoment B raw4395step0 raw4395step0Labels := by
      have hz : ∀ j, raw4395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4395step0 = (fun i j => raw4395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4395step0 raw4395; decide +kernel
      have hl : raw4395step0Labels = raw4395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4395 raw4395Labels permutation346 hz
    mixedMoment B raw4395step0 raw4395step0Labels = mixedMoment B raw4395step1 raw4395step1Labels := by
      have hz : ∀ j, raw4395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4395step1 = (fun i j => raw4395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4395step1 raw4395step0; decide +kernel
      have hl : raw4395step1Labels = raw4395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4395step0 raw4395step0Labels permutation56 hz
    mixedMoment B raw4395step1 raw4395step1Labels = mixedMoment B raw4395step2 raw4395step2Labels := by
      have ha : raw4395step2 = (fun i j => raw4395step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4395step2 raw4395step1; decide +kernel
      have hl : raw4395step2Labels = raw4395step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4395step1 raw4395step1Labels permutation31 permutation3
    mixedMoment B raw4395step2 raw4395step2Labels = mixedMoment B raw4395step3 raw4395step3Labels := by
      have ha : raw4395step3 = -raw4395step2 := by apply Matrix.ext; change ∀ i j, raw4395step3 i j = -(raw4395step2 i j); unfold raw4395step3 raw4395step2; decide +kernel
      have hl : raw4395step3Labels = raw4395step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4395step3 raw4395step3Labels = mixedMoment B raw4395step4 raw4395step4Labels := by
      have ha : raw4395step4 = raw4395step3 := by apply Matrix.ext; unfold raw4395step4 raw4395step3; decide +kernel
      have hl : raw4395step3Labels = labelEmbedding6 ∘ raw4395step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4395step3 raw4395step3Labels raw4395step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical4396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4396 raw4396Labels = mixedMoment B node4280 node4280Labels := by
  calc
    mixedMoment B raw4396 raw4396Labels = mixedMoment B raw4396step0 raw4396step0Labels := by
      have hz : ∀ j, raw4396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4396step0 = (fun i j => raw4396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4396step0 raw4396; decide +kernel
      have hl : raw4396step0Labels = raw4396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4396 raw4396Labels permutation434 hz
    mixedMoment B raw4396step0 raw4396step0Labels = mixedMoment B raw4396step1 raw4396step1Labels := by
      have hz : ∀ j, raw4396step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4396step1 = (fun i j => raw4396step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4396step1 raw4396step0; decide +kernel
      have hl : raw4396step1Labels = raw4396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4396step0 raw4396step0Labels permutation80 hz
    mixedMoment B raw4396step1 raw4396step1Labels = mixedMoment B raw4396step2 raw4396step2Labels := by
      have hz : ∀ j, raw4396step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4396step2 = (fun i j => raw4396step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4396step2 raw4396step1; decide +kernel
      have hl : raw4396step2Labels = raw4396step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4396step1 raw4396step1Labels permutation14 hz
    mixedMoment B raw4396step2 raw4396step2Labels = mixedMoment B raw4396step3 raw4396step3Labels := by
      have ha : raw4396step3 = (fun i j => raw4396step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4396step3 raw4396step2; decide +kernel
      have hl : raw4396step3Labels = raw4396step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4396step2 raw4396step2Labels permutation7 permutation3
    mixedMoment B raw4396step3 raw4396step3Labels = mixedMoment B raw4396step4 raw4396step4Labels := by
      have ha : raw4396step4 = -raw4396step3 := by apply Matrix.ext; change ∀ i j, raw4396step4 i j = -(raw4396step3 i j); unfold raw4396step4 raw4396step3; decide +kernel
      have hl : raw4396step4Labels = raw4396step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4396step4 raw4396step4Labels = mixedMoment B raw4396step5 raw4396step5Labels := by
      have ha : raw4396step5 = raw4396step4 := by apply Matrix.ext; unfold raw4396step5 raw4396step4; decide +kernel
      have hl : raw4396step4Labels = labelEmbedding6 ∘ raw4396step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4396step4 raw4396step4Labels raw4396step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4280 node4280Labels := by rfl

theorem canonical4397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4397 raw4397Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw4397 raw4397Labels = mixedMoment B raw4397step0 raw4397step0Labels := by
      have hz : ∀ j, raw4397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4397step0 = (fun i j => raw4397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4397step0 raw4397; decide +kernel
      have hl : raw4397step0Labels = raw4397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4397 raw4397Labels permutation434 hz
    mixedMoment B raw4397step0 raw4397step0Labels = mixedMoment B raw4397step1 raw4397step1Labels := by
      have hz : ∀ j, raw4397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4397step1 = (fun i j => raw4397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4397step1 raw4397step0; decide +kernel
      have hl : raw4397step1Labels = raw4397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4397step0 raw4397step0Labels permutation80 hz
    mixedMoment B raw4397step1 raw4397step1Labels = mixedMoment B raw4397step2 raw4397step2Labels := by
      have ha : raw4397step2 = (fun i j => raw4397step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4397step2 raw4397step1; decide +kernel
      have hl : raw4397step2Labels = raw4397step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4397step1 raw4397step1Labels permutation31 permutation3
    mixedMoment B raw4397step2 raw4397step2Labels = mixedMoment B raw4397step3 raw4397step3Labels := by
      have ha : raw4397step3 = -raw4397step2 := by apply Matrix.ext; change ∀ i j, raw4397step3 i j = -(raw4397step2 i j); unfold raw4397step3 raw4397step2; decide +kernel
      have hl : raw4397step3Labels = raw4397step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4397step3 raw4397step3Labels = mixedMoment B raw4397step4 raw4397step4Labels := by
      have ha : raw4397step4 = raw4397step3 := by apply Matrix.ext; unfold raw4397step4 raw4397step3; decide +kernel
      have hl : raw4397step3Labels = labelEmbedding6 ∘ raw4397step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4397step3 raw4397step3Labels raw4397step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

theorem canonical4398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4398 raw4398Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw4398 raw4398Labels = mixedMoment B raw4398step0 raw4398step0Labels := by
      have hz : ∀ j, raw4398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4398step0 = (fun i j => raw4398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4398step0 raw4398; decide +kernel
      have hl : raw4398step0Labels = raw4398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4398 raw4398Labels permutation434 hz
    mixedMoment B raw4398step0 raw4398step0Labels = mixedMoment B raw4398step1 raw4398step1Labels := by
      have hz : ∀ j, raw4398step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4398step1 = (fun i j => raw4398step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4398step1 raw4398step0; decide +kernel
      have hl : raw4398step1Labels = raw4398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4398step0 raw4398step0Labels permutation56 hz
    mixedMoment B raw4398step1 raw4398step1Labels = mixedMoment B raw4398step2 raw4398step2Labels := by
      have ha : raw4398step2 = (fun i j => raw4398step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4398step2 raw4398step1; decide +kernel
      have hl : raw4398step2Labels = raw4398step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4398step1 raw4398step1Labels permutation31 permutation3
    mixedMoment B raw4398step2 raw4398step2Labels = mixedMoment B raw4398step3 raw4398step3Labels := by
      have ha : raw4398step3 = -raw4398step2 := by apply Matrix.ext; change ∀ i j, raw4398step3 i j = -(raw4398step2 i j); unfold raw4398step3 raw4398step2; decide +kernel
      have hl : raw4398step3Labels = raw4398step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4398step3 raw4398step3Labels = mixedMoment B raw4398step4 raw4398step4Labels := by
      have ha : raw4398step4 = raw4398step3 := by apply Matrix.ext; unfold raw4398step4 raw4398step3; decide +kernel
      have hl : raw4398step3Labels = labelEmbedding6 ∘ raw4398step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4398step3 raw4398step3Labels raw4398step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

theorem canonical4399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4399 raw4399Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw4399 raw4399Labels = mixedMoment B raw4399step0 raw4399step0Labels := by
      have hz : ∀ j, raw4399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4399step0 = (fun i j => raw4399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4399step0 raw4399; decide +kernel
      have hl : raw4399step0Labels = raw4399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4399 raw4399Labels permutation346 hz
    mixedMoment B raw4399step0 raw4399step0Labels = mixedMoment B raw4399step1 raw4399step1Labels := by
      have hz : ∀ j, raw4399step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4399step1 = (fun i j => raw4399step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4399step1 raw4399step0; decide +kernel
      have hl : raw4399step1Labels = raw4399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4399step0 raw4399step0Labels permutation56 hz
    mixedMoment B raw4399step1 raw4399step1Labels = mixedMoment B raw4399step2 raw4399step2Labels := by
      have ha : raw4399step2 = (fun i j => raw4399step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4399step2 raw4399step1; decide +kernel
      have hl : raw4399step2Labels = raw4399step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4399step1 raw4399step1Labels permutation31 permutation3
    mixedMoment B raw4399step2 raw4399step2Labels = mixedMoment B raw4399step3 raw4399step3Labels := by
      have ha : raw4399step3 = -raw4399step2 := by apply Matrix.ext; change ∀ i j, raw4399step3 i j = -(raw4399step2 i j); unfold raw4399step3 raw4399step2; decide +kernel
      have hl : raw4399step3Labels = raw4399step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4399step3 raw4399step3Labels = mixedMoment B raw4399step4 raw4399step4Labels := by
      have ha : raw4399step4 = raw4399step3 := by apply Matrix.ext; unfold raw4399step4 raw4399step3; decide +kernel
      have hl : raw4399step3Labels = labelEmbedding6 ∘ raw4399step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4399step3 raw4399step3Labels raw4399step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

theorem canonical4400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4400 raw4400Labels = mixedMoment B node4285 node4285Labels := by
  calc
    mixedMoment B raw4400 raw4400Labels = mixedMoment B raw4400step0 raw4400step0Labels := by
      have hz : ∀ j, raw4400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4400step0 = (fun i j => raw4400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4400step0 raw4400; decide +kernel
      have hl : raw4400step0Labels = raw4400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4400 raw4400Labels permutation434 hz
    mixedMoment B raw4400step0 raw4400step0Labels = mixedMoment B raw4400step1 raw4400step1Labels := by
      have hz : ∀ j, raw4400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4400step1 = (fun i j => raw4400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4400step1 raw4400step0; decide +kernel
      have hl : raw4400step1Labels = raw4400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4400step0 raw4400step0Labels permutation80 hz
    mixedMoment B raw4400step1 raw4400step1Labels = mixedMoment B raw4400step2 raw4400step2Labels := by
      have hz : ∀ j, raw4400step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4400step2 = (fun i j => raw4400step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4400step2 raw4400step1; decide +kernel
      have hl : raw4400step2Labels = raw4400step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4400step1 raw4400step1Labels permutation14 hz
    mixedMoment B raw4400step2 raw4400step2Labels = mixedMoment B raw4400step3 raw4400step3Labels := by
      have ha : raw4400step3 = (fun i j => raw4400step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4400step3 raw4400step2; decide +kernel
      have hl : raw4400step3Labels = raw4400step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4400step2 raw4400step2Labels permutation7 permutation3
    mixedMoment B raw4400step3 raw4400step3Labels = mixedMoment B raw4400step4 raw4400step4Labels := by
      have ha : raw4400step4 = -raw4400step3 := by apply Matrix.ext; change ∀ i j, raw4400step4 i j = -(raw4400step3 i j); unfold raw4400step4 raw4400step3; decide +kernel
      have hl : raw4400step4Labels = raw4400step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4400step4 raw4400step4Labels = mixedMoment B raw4400step5 raw4400step5Labels := by
      have ha : raw4400step5 = raw4400step4 := by apply Matrix.ext; unfold raw4400step5 raw4400step4; decide +kernel
      have hl : raw4400step4Labels = labelEmbedding6 ∘ raw4400step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4400step4 raw4400step4Labels raw4400step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4285 node4285Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw554 raw554Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw554 raw554Labels = mixedMoment B raw554step0 raw554step0Labels := by
      have ha : raw554step0 = (fun i j => raw554 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw554step0 raw554; decide +kernel
      have hl : raw554step0Labels = raw554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw554 raw554Labels permutation2 permutation5
    mixedMoment B raw554step0 raw554step0Labels = mixedMoment B raw554step1 raw554step1Labels := by
      have ha : raw554step1 = raw554step0 := by apply Matrix.ext; unfold raw554step1 raw554step0; decide +kernel
      have hl : raw554step0Labels = labelEmbedding1 ∘ raw554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw554step0 raw554step0Labels raw554step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw555 raw555Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw555 raw555Labels = mixedMoment B raw555step0 raw555step0Labels := by
      have ha : raw555step0 = (fun i j => raw555 (permutation5 i) (permutation2 j)) := by apply Matrix.ext; unfold raw555step0 raw555; decide +kernel
      have hl : raw555step0Labels = raw555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw555 raw555Labels permutation5 permutation2
    _ = mixedMoment B node507 node507Labels := by rfl

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

theorem canonical1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1005 raw1005Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw1005 raw1005Labels = mixedMoment B raw1005step0 raw1005step0Labels := by
      have ha : raw1005step0 = (fun i j => raw1005 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1005step0 raw1005; decide +kernel
      have hl : raw1005step0Labels = raw1005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1005 raw1005Labels permutation8 permutation4
    mixedMoment B raw1005step0 raw1005step0Labels = mixedMoment B raw1005step1 raw1005step1Labels := by
      have ha : raw1005step1 = raw1005step0 := by apply Matrix.ext; unfold raw1005step1 raw1005step0; decide +kernel
      have hl : raw1005step0Labels = labelEmbedding7 ∘ raw1005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1005step0 raw1005step0Labels raw1005step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

theorem canonical1006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1006 raw1006Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw1006 raw1006Labels = mixedMoment B raw1006step0 raw1006step0Labels := by
      have ha : raw1006step0 = (fun i j => raw1006 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1006step0 raw1006; decide +kernel
      have hl : raw1006step0Labels = raw1006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1006 raw1006Labels permutation8 permutation4
    _ = mixedMoment B node828 node828Labels := by rfl

theorem canonical1007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1007 raw1007Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw1007 raw1007Labels = mixedMoment B raw1007step0 raw1007step0Labels := by
      have ha : raw1007step0 = (fun i j => raw1007 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1007step0 raw1007; decide +kernel
      have hl : raw1007step0Labels = raw1007Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1007 raw1007Labels permutation11 permutation6
    mixedMoment B raw1007step0 raw1007step0Labels = mixedMoment B raw1007step1 raw1007step1Labels := by
      have ha : raw1007step1 = -raw1007step0 := by apply Matrix.ext; change ∀ i j, raw1007step1 i j = -(raw1007step0 i j); unfold raw1007step1 raw1007step0; decide +kernel
      have hl : raw1007step1Labels = raw1007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1007step1 raw1007step1Labels = mixedMoment B raw1007step2 raw1007step2Labels := by
      have ha : raw1007step2 = raw1007step1 := by apply Matrix.ext; unfold raw1007step2 raw1007step1; decide +kernel
      have hl : raw1007step1Labels = labelEmbedding1 ∘ raw1007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1007step1 raw1007step1Labels raw1007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node857 node857Labels := by rfl

theorem canonical1014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1014 raw1014Labels = mixedMoment B node4280 node4280Labels := by
  calc
    mixedMoment B raw1014 raw1014Labels = mixedMoment B raw1014step0 raw1014step0Labels := by
      have ha : raw1014step0 = (fun i j => raw1014 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1014step0 raw1014; decide +kernel
      have hl : raw1014step0Labels = raw1014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1014 raw1014Labels permutation2 permutation4
    mixedMoment B raw1014step0 raw1014step0Labels = mixedMoment B raw1014step1 raw1014step1Labels := by
      have ha : raw1014step1 = raw1014step0 := by apply Matrix.ext; unfold raw1014step1 raw1014step0; decide +kernel
      have hl : raw1014step0Labels = labelEmbedding7 ∘ raw1014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1014step0 raw1014step0Labels raw1014step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4280 node4280Labels := by rfl

theorem canonical1015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1015 raw1015Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw1015 raw1015Labels = mixedMoment B raw1015step0 raw1015step0Labels := by
      have ha : raw1015step0 = (fun i j => raw1015 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1015step0 raw1015; decide +kernel
      have hl : raw1015step0Labels = raw1015Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1015 raw1015Labels permutation2 permutation4
    _ = mixedMoment B node832 node832Labels := by rfl

theorem canonical1016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1016 raw1016Labels = mixedMoment B node862 node862Labels := by
  calc
    mixedMoment B raw1016 raw1016Labels = mixedMoment B raw1016step0 raw1016step0Labels := by
      have ha : raw1016step0 = (fun i j => raw1016 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1016step0 raw1016; decide +kernel
      have hl : raw1016step0Labels = raw1016Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1016 raw1016Labels permutation2 permutation6
    mixedMoment B raw1016step0 raw1016step0Labels = mixedMoment B raw1016step1 raw1016step1Labels := by
      have ha : raw1016step1 = -raw1016step0 := by apply Matrix.ext; change ∀ i j, raw1016step1 i j = -(raw1016step0 i j); unfold raw1016step1 raw1016step0; decide +kernel
      have hl : raw1016step1Labels = raw1016step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1016step1 raw1016step1Labels = mixedMoment B raw1016step2 raw1016step2Labels := by
      have ha : raw1016step2 = raw1016step1 := by apply Matrix.ext; unfold raw1016step2 raw1016step1; decide +kernel
      have hl : raw1016step1Labels = labelEmbedding1 ∘ raw1016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1016step1 raw1016step1Labels raw1016step2Labels labelEmbedding1 hl
    _ = mixedMoment B node862 node862Labels := by rfl

theorem canonical1017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1017 raw1017Labels = mixedMoment B node4285 node4285Labels := by
  calc
    mixedMoment B raw1017 raw1017Labels = mixedMoment B raw1017step0 raw1017step0Labels := by
      have ha : raw1017step0 = (fun i j => raw1017 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1017step0 raw1017; decide +kernel
      have hl : raw1017step0Labels = raw1017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1017 raw1017Labels permutation2 permutation4
    mixedMoment B raw1017step0 raw1017step0Labels = mixedMoment B raw1017step1 raw1017step1Labels := by
      have ha : raw1017step1 = raw1017step0 := by apply Matrix.ext; unfold raw1017step1 raw1017step0; decide +kernel
      have hl : raw1017step0Labels = labelEmbedding7 ∘ raw1017step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1017step0 raw1017step0Labels raw1017step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4285 node4285Labels := by rfl

theorem canonical1018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1018 raw1018Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw1018 raw1018Labels = mixedMoment B raw1018step0 raw1018step0Labels := by
      have ha : raw1018step0 = (fun i j => raw1018 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1018step0 raw1018; decide +kernel
      have hl : raw1018step0Labels = raw1018Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1018 raw1018Labels permutation2 permutation4
    _ = mixedMoment B node860 node860Labels := by rfl

theorem canonical1019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1019 raw1019Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw1019 raw1019Labels = mixedMoment B raw1019step0 raw1019step0Labels := by
      have ha : raw1019step0 = (fun i j => raw1019 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1019step0 raw1019; decide +kernel
      have hl : raw1019step0Labels = raw1019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1019 raw1019Labels permutation3 permutation6
    mixedMoment B raw1019step0 raw1019step0Labels = mixedMoment B raw1019step1 raw1019step1Labels := by
      have ha : raw1019step1 = -raw1019step0 := by apply Matrix.ext; change ∀ i j, raw1019step1 i j = -(raw1019step0 i j); unfold raw1019step1 raw1019step0; decide +kernel
      have hl : raw1019step1Labels = raw1019step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1019step1 raw1019step1Labels = mixedMoment B raw1019step2 raw1019step2Labels := by
      have ha : raw1019step2 = raw1019step1 := by apply Matrix.ext; unfold raw1019step2 raw1019step1; decide +kernel
      have hl : raw1019step1Labels = labelEmbedding1 ∘ raw1019step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1019step1 raw1019step1Labels raw1019step2Labels labelEmbedding1 hl
    _ = mixedMoment B node860 node860Labels := by rfl

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

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_GroupedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit grouping formulas for the two- and three-column equality
patterns. These discharge the dependent finite-label calculations once,
so concrete certificate rows need only ordinary integer arithmetic. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family3_0 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1 + A i 2) := by
  change groupedColumns A (fun _ : Fin 3 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family3_1 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 1) =
      (fun i => ![A i 0 + A i 1, A i 2]) := by
  change groupedColumns A (![0, 0, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_2 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 2) =
      (fun i => ![A i 0 + A i 2, A i 1]) := by
  change groupedColumns A (![0, 1, 0] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_3 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 3) =
      (fun i => ![A i 0, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_4 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 4) = A := by
  change groupedColumns A (fun j : Fin 3 => j) = _
  ext i b
  simp [groupedColumns, Finset.sum_filter]

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleRules
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

/-- The five equality patterns for three sampled column indices. -/
theorem single_label_three {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 3) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family3 EqualityPatterns.covers3
  rw [sum_fin_five] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3,
    EqualityPatterns.blocks3, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Nat.descFactorial] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

theorem canonical5214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5214 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5214 = injectiveMoment H raw5214step0 := by
      have hz : ∀ j, raw5214 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5214step0 = (fun i j => raw5214 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5214 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7683 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7683 = injectiveMoment H raw7683step0 := by
      have heq : raw7683step0 = (fun i j => raw7683 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7683 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8985 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8985 = injectiveMoment H raw8985step0 := by
      have hz : ∀ j, raw8985 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8985step0 = (fun i j => raw8985 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8985 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw813 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw813 = injectiveMoment H raw813step0 := by
      have heq : raw813step0 = -raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw813).symm
    injectiveMoment H raw813step0 = injectiveMoment H raw813step1 := by
      have heq : raw813step1 = (fun i j => raw813step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw813step0 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node507 node507Labels = Sparse.eval singlePairValue507 (familyPairVector B) := by
  have hp := single_label_three B hB node507
  have hl : node507Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node507 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node507 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node507 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 3) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node507 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value41 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 4) = PairSemantics.raw4141 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node507 PairSemantics.raw4141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4141 hH).trans (PairSemantics.sound41 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue507, PairSemantics.value0, PairSemantics.value4, PairSemantics.value41, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node420 node420Labels = Sparse.eval singlePairValue420 (familyPairVector B) := by
  have hp := single_label_three B hB node420
  have hl : node420Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node420 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node420 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node420 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node420 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value36 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 4) = PairSemantics.raw813 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node420 PairSemantics.raw813; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical813 hH).trans (PairSemantics.sound36 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue420, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value11, PairSemantics.value36, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2788 node2788Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw284 singletonSmall2788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2788) = raw284Labels := by decide +kernel
  rw [hl, canonical284 B hB] at h
  have hc0 : mixedMoment B raw284 (Fin.cases (0 : Fin 1) singletonSmall2788) =
      mixedMoment B node420 node420Labels := by
    have ha : raw284 = raw285 := by apply Matrix.ext; unfold raw284 raw285; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2788 = raw285Labels := by decide +kernel
    rw [ha, hj, canonical285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3916 node3916Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node507 node507Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw554 singletonSmall3916
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3916) = raw554Labels := by decide +kernel
  rw [hl, canonical554 B hB] at h
  have hc0 : mixedMoment B raw554 (Fin.cases (0 : Fin 1) singletonSmall3916) =
      mixedMoment B node507 node507Labels := by
    have ha : raw554 = raw555 := by apply Matrix.ext; unfold raw554 raw555; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3916 = raw555Labels := by decide +kernel
    rw [ha, hj, canonical555 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4276 node4276Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node828 node828Labels + mixedMoment B node857 node857Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1005 singletonSmall4276
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4276) = raw1005Labels := by decide +kernel
  rw [hl, canonical1005 B hB] at h
  have hc0 : mixedMoment B raw1005 (Fin.cases (0 : Fin 2) singletonSmall4276) =
      mixedMoment B node828 node828Labels := by
    have ha : raw1005 = raw1006 := by apply Matrix.ext; unfold raw1005 raw1006; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4276 = raw1006Labels := by decide +kernel
    rw [ha, hj, canonical1006 B hB]
  have hc1 : mixedMoment B raw1005 (Fin.cases (1 : Fin 2) singletonSmall4276) =
      mixedMoment B node857 node857Labels := by
    have ha : raw1005 = raw1007 := by apply Matrix.ext; unfold raw1005 raw1007; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4276 = raw1007Labels := by decide +kernel
    rw [ha, hj, canonical1007 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4280 node4280Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node832 node832Labels + mixedMoment B node862 node862Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1014 singletonSmall4280
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4280) = raw1014Labels := by decide +kernel
  rw [hl, canonical1014 B hB] at h
  have hc0 : mixedMoment B raw1014 (Fin.cases (0 : Fin 2) singletonSmall4280) =
      mixedMoment B node832 node832Labels := by
    have ha : raw1014 = raw1015 := by apply Matrix.ext; unfold raw1014 raw1015; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4280 = raw1015Labels := by decide +kernel
    rw [ha, hj, canonical1015 B hB]
  have hc1 : mixedMoment B raw1014 (Fin.cases (1 : Fin 2) singletonSmall4280) =
      mixedMoment B node862 node862Labels := by
    have ha : raw1014 = raw1016 := by apply Matrix.ext; unfold raw1014 raw1016; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4280 = raw1016Labels := by decide +kernel
    rw [ha, hj, canonical1016 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4285 node4285Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node860 node860Labels + mixedMoment B node860 node860Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1017 singletonSmall4285
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4285) = raw1017Labels := by decide +kernel
  rw [hl, canonical1017 B hB] at h
  have hc0 : mixedMoment B raw1017 (Fin.cases (0 : Fin 2) singletonSmall4285) =
      mixedMoment B node860 node860Labels := by
    have ha : raw1017 = raw1018 := by apply Matrix.ext; unfold raw1017 raw1018; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4285 = raw1018Labels := by decide +kernel
    rw [ha, hj, canonical1018 B hB]
  have hc1 : mixedMoment B raw1017 (Fin.cases (1 : Fin 2) singletonSmall4285) =
      mixedMoment B node860 node860Labels := by
    have ha : raw1017 = raw1019 := by apply Matrix.ext; unfold raw1017 raw1019; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4285 = raw1019Labels := by decide +kernel
    rw [ha, hj, canonical1019 B hB]
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

theorem singleton4572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4572 node4572Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1190 node1190Labels + mixedMoment B node1952 node1952Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1407 singletonSmall4572
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4572) = raw1407Labels := by decide +kernel
  rw [hl, canonical1407 B hB] at h
  have hc0 : mixedMoment B raw1407 (Fin.cases (0 : Fin 2) singletonSmall4572) =
      mixedMoment B node1190 node1190Labels := by
    have ha : raw1407 = raw1408 := by apply Matrix.ext; unfold raw1407 raw1408; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4572 = raw1408Labels := by decide +kernel
    rw [ha, hj, canonical1408 B hB]
  have hc1 : mixedMoment B raw1407 (Fin.cases (1 : Fin 2) singletonSmall4572) =
      mixedMoment B node1952 node1952Labels := by
    have ha : raw1407 = raw1409 := by apply Matrix.ext; unfold raw1407 raw1409; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4572 = raw1409Labels := by decide +kernel
    rw [ha, hj, canonical1409 B hB]
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

theorem singleton4621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4621 node4621Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1297 node1297Labels + mixedMoment B node2289 node2289Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1446 singletonSmall4621
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4621) = raw1446Labels := by decide +kernel
  rw [hl, canonical1446 B hB] at h
  have hc0 : mixedMoment B raw1446 (Fin.cases (0 : Fin 2) singletonSmall4621) =
      mixedMoment B node1297 node1297Labels := by
    have ha : raw1446 = raw1447 := by apply Matrix.ext; unfold raw1446 raw1447; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4621 = raw1447Labels := by decide +kernel
    rw [ha, hj, canonical1447 B hB]
  have hc1 : mixedMoment B raw1446 (Fin.cases (1 : Fin 2) singletonSmall4621) =
      mixedMoment B node2289 node2289Labels := by
    have ha : raw1446 = raw1448 := by apply Matrix.ext; unfold raw1446 raw1448; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4621 = raw1448Labels := by decide +kernel
    rw [ha, hj, canonical1448 B hB]
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

theorem singleton4747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4747 node4747Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1926 node1926Labels + mixedMoment B node1948 node1948Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1668 singletonSmall4747
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4747) = raw1668Labels := by decide +kernel
  rw [hl, canonical1668 B hB] at h
  have hc0 : mixedMoment B raw1668 (Fin.cases (0 : Fin 2) singletonSmall4747) =
      mixedMoment B node1926 node1926Labels := by
    have ha : raw1668 = raw1669 := by apply Matrix.ext; unfold raw1668 raw1669; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4747 = raw1669Labels := by decide +kernel
    rw [ha, hj, canonical1669 B hB]
  have hc1 : mixedMoment B raw1668 (Fin.cases (1 : Fin 2) singletonSmall4747) =
      mixedMoment B node1948 node1948Labels := by
    have ha : raw1668 = raw1670 := by apply Matrix.ext; unfold raw1668 raw1670; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4747 = raw1670Labels := by decide +kernel
    rw [ha, hj, canonical1670 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4754 node4754Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1951 node1951Labels + mixedMoment B node1951 node1951Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1677 singletonSmall4754
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4754) = raw1677Labels := by decide +kernel
  rw [hl, canonical1677 B hB] at h
  have hc0 : mixedMoment B raw1677 (Fin.cases (0 : Fin 2) singletonSmall4754) =
      mixedMoment B node1951 node1951Labels := by
    have ha : raw1677 = raw1678 := by apply Matrix.ext; unfold raw1677 raw1678; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4754 = raw1678Labels := by decide +kernel
    rw [ha, hj, canonical1678 B hB]
  have hc1 : mixedMoment B raw1677 (Fin.cases (1 : Fin 2) singletonSmall4754) =
      mixedMoment B node1951 node1951Labels := by
    have ha : raw1677 = raw1679 := by apply Matrix.ext; unfold raw1677 raw1679; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4754 = raw1679Labels := by decide +kernel
    rw [ha, hj, canonical1679 B hB]
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

theorem singleton4871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4871 node4871Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2112 node2112Labels + mixedMoment B node2287 node2287Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1803 singletonSmall4871
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4871) = raw1803Labels := by decide +kernel
  rw [hl, canonical1803 B hB] at h
  have hc0 : mixedMoment B raw1803 (Fin.cases (0 : Fin 2) singletonSmall4871) =
      mixedMoment B node2112 node2112Labels := by
    have ha : raw1803 = raw1804 := by apply Matrix.ext; unfold raw1803 raw1804; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4871 = raw1804Labels := by decide +kernel
    rw [ha, hj, canonical1804 B hB]
  have hc1 : mixedMoment B raw1803 (Fin.cases (1 : Fin 2) singletonSmall4871) =
      mixedMoment B node2287 node2287Labels := by
    have ha : raw1803 = raw1805 := by apply Matrix.ext; unfold raw1803 raw1805; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4871 = raw1805Labels := by decide +kernel
    rw [ha, hj, canonical1805 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4898 node4898Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2279 node2279Labels + mixedMoment B node2279 node2279Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1827 singletonSmall4898
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4898) = raw1827Labels := by decide +kernel
  rw [hl, canonical1827 B hB] at h
  have hc0 : mixedMoment B raw1827 (Fin.cases (0 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1828 := by apply Matrix.ext; unfold raw1827 raw1828; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4898 = raw1828Labels := by decide +kernel
    rw [ha, hj, canonical1828 B hB]
  have hc1 : mixedMoment B raw1827 (Fin.cases (1 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1829 := by apply Matrix.ext; unfold raw1827 raw1829; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4898 = raw1829Labels := by decide +kernel
    rw [ha, hj, canonical1829 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4899 node4899Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2281 node2281Labels + mixedMoment B node2294 node2294Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1830 singletonSmall4899
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4899) = raw1830Labels := by decide +kernel
  rw [hl, canonical1830 B hB] at h
  have hc0 : mixedMoment B raw1830 (Fin.cases (0 : Fin 2) singletonSmall4899) =
      mixedMoment B node2281 node2281Labels := by
    have ha : raw1830 = raw1831 := by apply Matrix.ext; unfold raw1830 raw1831; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4899 = raw1831Labels := by decide +kernel
    rw [ha, hj, canonical1831 B hB]
  have hc1 : mixedMoment B raw1830 (Fin.cases (1 : Fin 2) singletonSmall4899) =
      mixedMoment B node2294 node2294Labels := by
    have ha : raw1830 = raw1832 := by apply Matrix.ext; unfold raw1830 raw1832; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4899 = raw1832Labels := by decide +kernel
    rw [ha, hj, canonical1832 B hB]
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

theorem singleton5302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5302 node5302Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3054 node3054Labels + mixedMoment B node3626 node3626Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2313 singletonSmall5302
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5302) = raw2313Labels := by decide +kernel
  rw [hl, canonical2313 B hB] at h
  have hc0 : mixedMoment B raw2313 (Fin.cases (0 : Fin 2) singletonSmall5302) =
      mixedMoment B node3054 node3054Labels := by
    have ha : raw2313 = raw2314 := by apply Matrix.ext; unfold raw2313 raw2314; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5302 = raw2314Labels := by decide +kernel
    rw [ha, hj, canonical2314 B hB]
  have hc1 : mixedMoment B raw2313 (Fin.cases (1 : Fin 2) singletonSmall5302) =
      mixedMoment B node3626 node3626Labels := by
    have ha : raw2313 = raw2315 := by apply Matrix.ext; unfold raw2313 raw2315; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5302 = raw2315Labels := by decide +kernel
    rw [ha, hj, canonical2315 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5310 node5310Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2788 node2788Labels + mixedMoment B node3633 node3633Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2325 singletonSmall5310
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5310) = raw2325Labels := by decide +kernel
  rw [hl, canonical2325 B hB] at h
  have hc0 : mixedMoment B raw2325 (Fin.cases (0 : Fin 2) singletonSmall5310) =
      mixedMoment B node2788 node2788Labels := by
    have ha : raw2325 = raw2326 := by apply Matrix.ext; unfold raw2325 raw2326; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5310 = raw2326Labels := by decide +kernel
    rw [ha, hj, canonical2326 B hB]
  have hc1 : mixedMoment B raw2325 (Fin.cases (1 : Fin 2) singletonSmall5310) =
      mixedMoment B node3633 node3633Labels := by
    have ha : raw2325 = raw2327 := by apply Matrix.ext; unfold raw2325 raw2327; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5310 = raw2327Labels := by decide +kernel
    rw [ha, hj, canonical2327 B hB]
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

theorem singleton5456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5456 node5456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3916 node3916Labels + mixedMoment B node3916 node3916Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2568 singletonSmall5456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5456) = raw2568Labels := by decide +kernel
  rw [hl, canonical2568 B hB] at h
  have hc0 : mixedMoment B raw2568 (Fin.cases (0 : Fin 2) singletonSmall5456) =
      mixedMoment B node3916 node3916Labels := by
    have ha : raw2568 = raw2569 := by apply Matrix.ext; unfold raw2568 raw2569; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5456 = raw2569Labels := by decide +kernel
    rw [ha, hj, canonical2569 B hB]
  have hc1 : mixedMoment B raw2568 (Fin.cases (1 : Fin 2) singletonSmall5456) =
      mixedMoment B node3916 node3916Labels := by
    have ha : raw2568 = raw2570 := by apply Matrix.ext; unfold raw2568 raw2570; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5456 = raw2570Labels := by decide +kernel
    rw [ha, hj, canonical2570 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node420 node420Labels = Sparse.eval nodeValue420 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue420 (familyPairVector B) := singlePair420 B _hB
    _ = _ := by norm_num [singlePairValue420, nodeValue420, Sparse.eval, mixedVector] <;> ring

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2281 node2281Labels = Sparse.eval nodeValue2281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2281) = mixedMoment B node2281 node2281Labels := rfl
  simpa [nodeValue2281, Sparse.eval] using hc.symm

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

theorem sound2788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2788 node2788Labels = Sparse.eval nodeValue2788 (mixedVector B) := by
  have h := singleton2788 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue2788, nodeValue420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3633 node3633Labels = Sparse.eval nodeValue3633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3633) = mixedMoment B node3633 node3633Labels := rfl
  simpa [nodeValue3633, Sparse.eval] using hc.symm

theorem sound4898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4898 node4898Labels = Sparse.eval nodeValue4898 (mixedVector B) := by
  have h := singleton4898 B _hB
  rw [sound2279 B _hB _hF] at h
  norm_num [nodeValue4898, nodeValue2279, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4899 node4899Labels = Sparse.eval nodeValue4899 (mixedVector B) := by
  have h := singleton4899 B _hB
  rw [sound2281 B _hB _hF, sound2294 B _hB _hF] at h
  norm_num [nodeValue4899, nodeValue2281, nodeValue2294, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5302 node5302Labels = Sparse.eval nodeValue5302 (mixedVector B) := by
  have h := singleton5302 B _hB
  rw [sound3054 B _hB _hF, sound3626 B _hB _hF] at h
  norm_num [nodeValue5302, nodeValue3054, nodeValue3626, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5310 node5310Labels = Sparse.eval nodeValue5310 (mixedVector B) := by
  have h := singleton5310 B _hB
  rw [sound2788 B _hB _hF, sound3633 B _hB _hF] at h
  norm_num [nodeValue5310, nodeValue2788, nodeValue3633, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node828 node828Labels = Sparse.eval nodeValue828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 828) = mixedMoment B node828 node828Labels := rfl
  simpa [nodeValue828, Sparse.eval] using hc.symm

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

theorem sound832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node832 node832Labels = Sparse.eval nodeValue832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 832) = mixedMoment B node832 node832Labels := rfl
  simpa [nodeValue832, Sparse.eval] using hc.symm

theorem sound857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node857 node857Labels = Sparse.eval nodeValue857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 857) = mixedMoment B node857 node857Labels := rfl
  simpa [nodeValue857, Sparse.eval] using hc.symm

theorem sound860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node860 node860Labels = Sparse.eval nodeValue860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 860) = mixedMoment B node860 node860Labels := rfl
  simpa [nodeValue860, Sparse.eval] using hc.symm

theorem sound862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node862 node862Labels = Sparse.eval nodeValue862 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 862) = mixedMoment B node862 node862Labels := rfl
  simpa [nodeValue862, Sparse.eval] using hc.symm

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

theorem sound1190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1190 node1190Labels = Sparse.eval nodeValue1190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1190) = mixedMoment B node1190 node1190Labels := rfl
  simpa [nodeValue1190, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

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

theorem sound1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1926 node1926Labels = Sparse.eval nodeValue1926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1926) = mixedMoment B node1926 node1926Labels := rfl
  simpa [nodeValue1926, Sparse.eval] using hc.symm

theorem sound1948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1948 node1948Labels = Sparse.eval nodeValue1948 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1948) = mixedMoment B node1948 node1948Labels := rfl
  simpa [nodeValue1948, Sparse.eval] using hc.symm

theorem sound1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1951 node1951Labels = Sparse.eval nodeValue1951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1951) = mixedMoment B node1951 node1951Labels := rfl
  simpa [nodeValue1951, Sparse.eval] using hc.symm

theorem sound1952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1952 node1952Labels = Sparse.eval nodeValue1952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1952) = mixedMoment B node1952 node1952Labels := rfl
  simpa [nodeValue1952, Sparse.eval] using hc.symm

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

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

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

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node507 node507Labels = Sparse.eval nodeValue507 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue507 (familyPairVector B) := singlePair507 B _hB
    _ = _ := by norm_num [singlePairValue507, nodeValue507, Sparse.eval, mixedVector] <;> ring

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

theorem sound3916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3916 node3916Labels = Sparse.eval nodeValue3916 (mixedVector B) := by
  have h := singleton3916 B _hB
  rw [sound507 B _hB _hF] at h
  norm_num [nodeValue3916, nodeValue507, Sparse.eval] at h ⊢
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

theorem sound4276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4276 node4276Labels = Sparse.eval nodeValue4276 (mixedVector B) := by
  have h := singleton4276 B _hB
  rw [sound828 B _hB _hF, sound857 B _hB _hF] at h
  norm_num [nodeValue4276, nodeValue828, nodeValue857, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4280 node4280Labels = Sparse.eval nodeValue4280 (mixedVector B) := by
  have h := singleton4280 B _hB
  rw [sound832 B _hB _hF, sound862 B _hB _hF] at h
  norm_num [nodeValue4280, nodeValue832, nodeValue862, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4285 node4285Labels = Sparse.eval nodeValue4285 (mixedVector B) := by
  have h := singleton4285 B _hB
  rw [sound860 B _hB _hF] at h
  norm_num [nodeValue4285, nodeValue860, Sparse.eval] at h ⊢
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

theorem sound4572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4572 node4572Labels = Sparse.eval nodeValue4572 (mixedVector B) := by
  have h := singleton4572 B _hB
  rw [sound1190 B _hB _hF, sound1952 B _hB _hF] at h
  norm_num [nodeValue4572, nodeValue1190, nodeValue1952, Sparse.eval] at h ⊢
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

theorem sound4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4621 node4621Labels = Sparse.eval nodeValue4621 (mixedVector B) := by
  have h := singleton4621 B _hB
  rw [sound1297 B _hB _hF, sound2289 B _hB _hF] at h
  norm_num [nodeValue4621, nodeValue1297, nodeValue2289, Sparse.eval] at h ⊢
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

theorem sound4747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4747 node4747Labels = Sparse.eval nodeValue4747 (mixedVector B) := by
  have h := singleton4747 B _hB
  rw [sound1926 B _hB _hF, sound1948 B _hB _hF] at h
  norm_num [nodeValue4747, nodeValue1926, nodeValue1948, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4754 node4754Labels = Sparse.eval nodeValue4754 (mixedVector B) := by
  have h := singleton4754 B _hB
  rw [sound1951 B _hB _hF] at h
  norm_num [nodeValue4754, nodeValue1951, Sparse.eval] at h ⊢
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

theorem sound4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4871 node4871Labels = Sparse.eval nodeValue4871 (mixedVector B) := by
  have h := singleton4871 B _hB
  rw [sound2112 B _hB _hF, sound2287 B _hB _hF] at h
  norm_num [nodeValue4871, nodeValue2112, nodeValue2287, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5456 node5456Labels = Sparse.eval nodeValue5456 (mixedVector B) := by
  have h := singleton5456 B _hB
  rw [sound3916 B _hB _hF] at h
  norm_num [nodeValue5456, nodeValue3916, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources3
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm117 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA117 + difference 0 1) (sourceB117 + difference 1 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA117 + difference 0 1) (sourceB117 + difference 1 0) sourceC117) = raw2657 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2657; decide +kernel
    rw [ha]
    exact (canonical2657 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA117 + difference 0 2) (sourceB117 + difference 2 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA117 + difference 0 2) (sourceB117 + difference 2 0) sourceC117) = raw2658 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2658; decide +kernel
    rw [ha]
    exact (canonical2658 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA117 + difference 0 3) (sourceB117 + difference 3 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA117 + difference 0 3) (sourceB117 + difference 3 0) sourceC117) = raw2659 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2659; decide +kernel
    rw [ha]
    exact (canonical2659 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA117 + difference 0 4) (sourceB117 + difference 4 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA117 + difference 0 4) (sourceB117 + difference 4 0) sourceC117) = raw2660 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2660; decide +kernel
    rw [ha]
    exact (canonical2660 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA117 + difference 0 5) (sourceB117 + difference 5 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA117 + difference 0 5) (sourceB117 + difference 5 0) sourceC117) = raw4379 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4379; decide +kernel
    rw [ha]
    exact (canonical4379 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA117 + difference 1 0) (sourceB117 + difference 0 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA117 + difference 1 0) (sourceB117 + difference 0 1) sourceC117) = raw4380 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4380; decide +kernel
    rw [ha]
    exact (canonical4380 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA117 + difference 1 2) (sourceB117 + difference 2 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 1 2) (sourceB117 + difference 2 1) sourceC117) = raw4381 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4381; decide +kernel
    rw [ha]
    exact (canonical4381 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA117 + difference 1 3) (sourceB117 + difference 3 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 1 3) (sourceB117 + difference 3 1) sourceC117) = raw4382 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4382; decide +kernel
    rw [ha]
    exact (canonical4382 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA117 + difference 1 4) (sourceB117 + difference 4 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA117 + difference 1 4) (sourceB117 + difference 4 1) sourceC117) = raw4383 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4383; decide +kernel
    rw [ha]
    exact (canonical4383 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA117 + difference 1 5) (sourceB117 + difference 5 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA117 + difference 1 5) (sourceB117 + difference 5 1) sourceC117) = raw2636 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2636; decide +kernel
    rw [ha]
    exact (canonical2636 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA117 + difference 2 0) (sourceB117 + difference 0 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA117 + difference 2 0) (sourceB117 + difference 0 2) sourceC117) = raw4384 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4384; decide +kernel
    rw [ha]
    exact (canonical4384 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA117 + difference 2 1) (sourceB117 + difference 1 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 2 1) (sourceB117 + difference 1 2) sourceC117) = raw4385 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4385; decide +kernel
    rw [ha]
    exact (canonical4385 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA117 + difference 2 3) (sourceB117 + difference 3 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 2 3) (sourceB117 + difference 3 2) sourceC117) = raw4386 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4386; decide +kernel
    rw [ha]
    exact (canonical4386 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA117 + difference 2 4) (sourceB117 + difference 4 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA117 + difference 2 4) (sourceB117 + difference 4 2) sourceC117) = raw4387 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4387; decide +kernel
    rw [ha]
    exact (canonical4387 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA117 + difference 2 5) (sourceB117 + difference 5 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA117 + difference 2 5) (sourceB117 + difference 5 2) sourceC117) = raw2641 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2641; decide +kernel
    rw [ha]
    exact (canonical2641 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA117 + difference 3 0) (sourceB117 + difference 0 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA117 + difference 3 0) (sourceB117 + difference 0 3) sourceC117) = raw4388 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4388; decide +kernel
    rw [ha]
    exact (canonical4388 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA117 + difference 3 1) (sourceB117 + difference 1 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 3 1) (sourceB117 + difference 1 3) sourceC117) = raw4389 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4389; decide +kernel
    rw [ha]
    exact (canonical4389 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA117 + difference 3 2) (sourceB117 + difference 2 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 3 2) (sourceB117 + difference 2 3) sourceC117) = raw4390 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4390; decide +kernel
    rw [ha]
    exact (canonical4390 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA117 + difference 3 4) (sourceB117 + difference 4 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA117 + difference 3 4) (sourceB117 + difference 4 3) sourceC117) = raw4391 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4391; decide +kernel
    rw [ha]
    exact (canonical4391 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA117 + difference 3 5) (sourceB117 + difference 5 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA117 + difference 3 5) (sourceB117 + difference 5 3) sourceC117) = raw2646 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2646; decide +kernel
    rw [ha]
    exact (canonical2646 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA117 + difference 4 0) (sourceB117 + difference 0 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA117 + difference 4 0) (sourceB117 + difference 0 4) sourceC117) = raw4392 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4392; decide +kernel
    rw [ha]
    exact (canonical4392 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA117 + difference 4 1) (sourceB117 + difference 1 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA117 + difference 4 1) (sourceB117 + difference 1 4) sourceC117) = raw4393 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4393; decide +kernel
    rw [ha]
    exact (canonical4393 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA117 + difference 4 2) (sourceB117 + difference 2 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA117 + difference 4 2) (sourceB117 + difference 2 4) sourceC117) = raw4394 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4394; decide +kernel
    rw [ha]
    exact (canonical4394 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA117 + difference 4 3) (sourceB117 + difference 3 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA117 + difference 4 3) (sourceB117 + difference 3 4) sourceC117) = raw4395 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4395; decide +kernel
    rw [ha]
    exact (canonical4395 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA117 + difference 4 5) (sourceB117 + difference 5 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA117 + difference 4 5) (sourceB117 + difference 5 4) sourceC117) = raw2651 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2651; decide +kernel
    rw [ha]
    exact (canonical2651 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA117 + difference 5 0) (sourceB117 + difference 0 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4280) := by
    have ha : (tripleCharges (sourceA117 + difference 5 0) (sourceB117 + difference 0 5) sourceC117) = raw4396 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4396; decide +kernel
    rw [ha]
    exact (canonical4396 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA117 + difference 5 1) (sourceB117 + difference 1 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA117 + difference 5 1) (sourceB117 + difference 1 5) sourceC117) = raw4397 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4397; decide +kernel
    rw [ha]
    exact (canonical4397 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA117 + difference 5 2) (sourceB117 + difference 2 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA117 + difference 5 2) (sourceB117 + difference 2 5) sourceC117) = raw4398 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4398; decide +kernel
    rw [ha]
    exact (canonical4398 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA117 + difference 5 3) (sourceB117 + difference 3 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA117 + difference 5 3) (sourceB117 + difference 3 5) sourceC117) = raw4399 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4399; decide +kernel
    rw [ha]
    exact (canonical4399 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA117 + difference 5 4) (sourceB117 + difference 4 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4285) := by
    have ha : (tripleCharges (sourceA117 + difference 5 4) (sourceB117 + difference 4 5) sourceC117) = raw4400 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4400; decide +kernel
    rw [ha]
    exact (canonical4400 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA117 sourceB117 sourceC117
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm117, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck97 : Integer.Sparse.reindex keyMap MixedData.row97 = numericRow97 := by decide +kernel

theorem numericCheck97 (x : Master → ℝ) : Integer.Sparse.eval numericRow97 x =
    (2880 : ℝ) * reducedSource97 x := by
  norm_num [numericRow97, reducedSource97, Integer.Sparse.eval, Sparse.eval, nodeValue4276, nodeValue4280, nodeValue4285, nodeValue4572, nodeValue4621, nodeValue4747, nodeValue4754, nodeValue4871, nodeValue4898, nodeValue4899, nodeValue5302, nodeValue5310, nodeValue5456]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero97 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource97 (mixedVector B) = 0 := by
  have h4276 : mixedVector B (Sum.inr 4276) = Sparse.eval nodeValue4276 (mixedVector B) := by
    change mixedMoment B node4276 node4276Labels = _
    exact sound4276 B hB hF
  have h4280 : mixedVector B (Sum.inr 4280) = Sparse.eval nodeValue4280 (mixedVector B) := by
    change mixedMoment B node4280 node4280Labels = _
    exact sound4280 B hB hF
  have h4285 : mixedVector B (Sum.inr 4285) = Sparse.eval nodeValue4285 (mixedVector B) := by
    change mixedMoment B node4285 node4285Labels = _
    exact sound4285 B hB hF
  have h4572 : mixedVector B (Sum.inr 4572) = Sparse.eval nodeValue4572 (mixedVector B) := by
    change mixedMoment B node4572 node4572Labels = _
    exact sound4572 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4747 : mixedVector B (Sum.inr 4747) = Sparse.eval nodeValue4747 (mixedVector B) := by
    change mixedMoment B node4747 node4747Labels = _
    exact sound4747 B hB hF
  have h4754 : mixedVector B (Sum.inr 4754) = Sparse.eval nodeValue4754 (mixedVector B) := by
    change mixedMoment B node4754 node4754Labels = _
    exact sound4754 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  have h5456 : mixedVector B (Sum.inr 5456) = Sparse.eval nodeValue5456 (mixedVector B) := by
    change mixedMoment B node5456 node5456Labels = _
    exact sound5456 B hB hF
  simpa only [sourceForm117, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4276, h4280, h4285, h4572, h4621, h4747, h4754, h4871, h4898, h4899, h5302, h5310, h5456, reducedSource97] using sourceEq117 B hB

theorem rowSound97_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row97 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck97, numericCheck97, reducedZero97 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e_oai
