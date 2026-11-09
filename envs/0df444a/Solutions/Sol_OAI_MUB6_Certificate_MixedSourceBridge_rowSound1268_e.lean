-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:25:17.564235+00:00
-- url     : https://prove2.me/submissions/73e1929d-79a8-4a68-b77f-d005034d8f25

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical90 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw90 raw90Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw90 raw90Labels = mixedMoment B raw90step0 raw90step0Labels := by
      have ha : raw90step0 = (fun i j => raw90 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw90step0 raw90; decide +kernel
      have hl : raw90step0Labels = raw90Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw90 raw90Labels permutation2 permutation5
    mixedMoment B raw90step0 raw90step0Labels = mixedMoment B raw90step1 raw90step1Labels := by
      have ha : raw90step1 = raw90step0 := by apply Matrix.ext; unfold raw90step1 raw90step0; decide +kernel
      have hl : raw90step0Labels = labelEmbedding1 ∘ raw90step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw90step0 raw90step0Labels raw90step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1311 node1311Labels := by rfl

theorem canonical91 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw91 raw91Labels = mixedMoment B node160 node160Labels := by
  calc
    mixedMoment B raw91 raw91Labels = mixedMoment B raw91step0 raw91step0Labels := by
      have ha : raw91step0 = (fun i j => raw91 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw91step0 raw91; decide +kernel
      have hl : raw91step0Labels = raw91Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw91 raw91Labels permutation3 permutation4
    _ = mixedMoment B node160 node160Labels := by rfl

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

theorem canonical1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1437 raw1437Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw1437 raw1437Labels = mixedMoment B raw1437step0 raw1437step0Labels := by
      have ha : raw1437step0 = (fun i j => raw1437 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1437step0 raw1437; decide +kernel
      have hl : raw1437step0Labels = raw1437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1437 raw1437Labels permutation8 permutation4
    mixedMoment B raw1437step0 raw1437step0Labels = mixedMoment B raw1437step1 raw1437step1Labels := by
      have ha : raw1437step1 = raw1437step0 := by apply Matrix.ext; unfold raw1437step1 raw1437step0; decide +kernel
      have hl : raw1437step0Labels = labelEmbedding7 ∘ raw1437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1437step0 raw1437step0Labels raw1437step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1438 raw1438Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw1438 raw1438Labels = mixedMoment B raw1438step0 raw1438step0Labels := by
      have ha : raw1438step0 = (fun i j => raw1438 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1438step0 raw1438; decide +kernel
      have hl : raw1438step0Labels = raw1438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1438 raw1438Labels permutation8 permutation4
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical1439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1439 raw1439Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw1439 raw1439Labels = mixedMoment B raw1439step0 raw1439step0Labels := by
      have ha : raw1439step0 = (fun i j => raw1439 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1439step0 raw1439; decide +kernel
      have hl : raw1439step0Labels = raw1439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1439 raw1439Labels permutation8 permutation6
    mixedMoment B raw1439step0 raw1439step0Labels = mixedMoment B raw1439step1 raw1439step1Labels := by
      have ha : raw1439step1 = -raw1439step0 := by apply Matrix.ext; change ∀ i j, raw1439step1 i j = -(raw1439step0 i j); unfold raw1439step1 raw1439step0; decide +kernel
      have hl : raw1439step1Labels = raw1439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1439step1 raw1439step1Labels = mixedMoment B raw1439step2 raw1439step2Labels := by
      have ha : raw1439step2 = raw1439step1 := by apply Matrix.ext; unfold raw1439step2 raw1439step1; decide +kernel
      have hl : raw1439step1Labels = labelEmbedding1 ∘ raw1439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1439step1 raw1439step1Labels raw1439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical1461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1461 raw1461Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw1461 raw1461Labels = mixedMoment B raw1461step0 raw1461step0Labels := by
      have ha : raw1461step0 = (fun i j => raw1461 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1461step0 raw1461; decide +kernel
      have hl : raw1461step0Labels = raw1461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1461 raw1461Labels permutation2 permutation4
    mixedMoment B raw1461step0 raw1461step0Labels = mixedMoment B raw1461step1 raw1461step1Labels := by
      have ha : raw1461step1 = raw1461step0 := by apply Matrix.ext; unfold raw1461step1 raw1461step0; decide +kernel
      have hl : raw1461step0Labels = labelEmbedding7 ∘ raw1461step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1461step0 raw1461step0Labels raw1461step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4627 node4627Labels := by rfl

theorem canonical1462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1462 raw1462Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw1462 raw1462Labels = mixedMoment B raw1462step0 raw1462step0Labels := by
      have ha : raw1462step0 = (fun i j => raw1462 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1462step0 raw1462; decide +kernel
      have hl : raw1462step0Labels = raw1462Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1462 raw1462Labels permutation2 permutation4
    _ = mixedMoment B node1311 node1311Labels := by rfl

theorem canonical1463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1463 raw1463Labels = mixedMoment B node3311 node3311Labels := by
  calc
    mixedMoment B raw1463 raw1463Labels = mixedMoment B raw1463step0 raw1463step0Labels := by
      have ha : raw1463step0 = (fun i j => raw1463 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1463step0 raw1463; decide +kernel
      have hl : raw1463step0Labels = raw1463Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1463 raw1463Labels permutation3 permutation3
    mixedMoment B raw1463step0 raw1463step0Labels = mixedMoment B raw1463step1 raw1463step1Labels := by
      have ha : raw1463step1 = -raw1463step0 := by apply Matrix.ext; change ∀ i j, raw1463step1 i j = -(raw1463step0 i j); unfold raw1463step1 raw1463step0; decide +kernel
      have hl : raw1463step1Labels = raw1463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1463step1 raw1463step1Labels = mixedMoment B raw1463step2 raw1463step2Labels := by
      have ha : raw1463step2 = raw1463step1 := by apply Matrix.ext; unfold raw1463step2 raw1463step1; decide +kernel
      have hl : raw1463step1Labels = labelEmbedding1 ∘ raw1463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1463step1 raw1463step1Labels raw1463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3311 node3311Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22510 raw22510Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22510 raw22510Labels = mixedMoment B raw22510step0 raw22510step0Labels := by
      have hz : ∀ j, raw22510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22510step0 = (fun i j => raw22510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22510step0 raw22510; decide +kernel
      have hl : raw22510step0Labels = raw22510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510 raw22510Labels permutation434 hz
    mixedMoment B raw22510step0 raw22510step0Labels = mixedMoment B raw22510step1 raw22510step1Labels := by
      have hz : ∀ j, raw22510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22510step1 = (fun i j => raw22510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22510step1 raw22510step0; decide +kernel
      have hl : raw22510step1Labels = raw22510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510step0 raw22510step0Labels permutation80 hz
    mixedMoment B raw22510step1 raw22510step1Labels = mixedMoment B raw22510step2 raw22510step2Labels := by
      have hz : ∀ j, raw22510step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22510step2 = (fun i j => raw22510step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22510step2 raw22510step1; decide +kernel
      have hl : raw22510step2Labels = raw22510step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510step1 raw22510step1Labels permutation14 hz
    mixedMoment B raw22510step2 raw22510step2Labels = mixedMoment B raw22510step3 raw22510step3Labels := by
      have ha : raw22510step3 = (fun i j => raw22510step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22510step3 raw22510step2; decide +kernel
      have hl : raw22510step3Labels = raw22510step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22510step2 raw22510step2Labels permutation3 permutation7
    mixedMoment B raw22510step3 raw22510step3Labels = mixedMoment B raw22510step4 raw22510step4Labels := by
      have ha : raw22510step4 = raw22510step3 := by apply Matrix.ext; unfold raw22510step4 raw22510step3; decide +kernel
      have hl : raw22510step3Labels = labelEmbedding10 ∘ raw22510step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22510step3 raw22510step3Labels raw22510step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical22515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22515 raw22515Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22515 raw22515Labels = mixedMoment B raw22515step0 raw22515step0Labels := by
      have hz : ∀ j, raw22515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22515step0 = (fun i j => raw22515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22515step0 raw22515; decide +kernel
      have hl : raw22515step0Labels = raw22515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22515 raw22515Labels permutation434 hz
    mixedMoment B raw22515step0 raw22515step0Labels = mixedMoment B raw22515step1 raw22515step1Labels := by
      have hz : ∀ j, raw22515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22515step1 = (fun i j => raw22515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22515step1 raw22515step0; decide +kernel
      have hl : raw22515step1Labels = raw22515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22515step0 raw22515step0Labels permutation80 hz
    mixedMoment B raw22515step1 raw22515step1Labels = mixedMoment B raw22515step2 raw22515step2Labels := by
      have ha : raw22515step2 = (fun i j => raw22515step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22515step2 raw22515step1; decide +kernel
      have hl : raw22515step2Labels = raw22515step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22515step1 raw22515step1Labels permutation9 permutation7
    mixedMoment B raw22515step2 raw22515step2Labels = mixedMoment B raw22515step3 raw22515step3Labels := by
      have ha : raw22515step3 = raw22515step2 := by apply Matrix.ext; unfold raw22515step3 raw22515step2; decide +kernel
      have hl : raw22515step2Labels = labelEmbedding10 ∘ raw22515step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22515step2 raw22515step2Labels raw22515step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22520 raw22520Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22520 raw22520Labels = mixedMoment B raw22520step0 raw22520step0Labels := by
      have hz : ∀ j, raw22520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22520step0 = (fun i j => raw22520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22520step0 raw22520; decide +kernel
      have hl : raw22520step0Labels = raw22520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22520 raw22520Labels permutation434 hz
    mixedMoment B raw22520step0 raw22520step0Labels = mixedMoment B raw22520step1 raw22520step1Labels := by
      have hz : ∀ j, raw22520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22520step1 = (fun i j => raw22520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22520step1 raw22520step0; decide +kernel
      have hl : raw22520step1Labels = raw22520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22520step0 raw22520step0Labels permutation56 hz
    mixedMoment B raw22520step1 raw22520step1Labels = mixedMoment B raw22520step2 raw22520step2Labels := by
      have ha : raw22520step2 = (fun i j => raw22520step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22520step2 raw22520step1; decide +kernel
      have hl : raw22520step2Labels = raw22520step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22520step1 raw22520step1Labels permutation9 permutation7
    mixedMoment B raw22520step2 raw22520step2Labels = mixedMoment B raw22520step3 raw22520step3Labels := by
      have ha : raw22520step3 = raw22520step2 := by apply Matrix.ext; unfold raw22520step3 raw22520step2; decide +kernel
      have hl : raw22520step2Labels = labelEmbedding10 ∘ raw22520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22520step2 raw22520step2Labels raw22520step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22525 raw22525Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22525 raw22525Labels = mixedMoment B raw22525step0 raw22525step0Labels := by
      have hz : ∀ j, raw22525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22525step0 = (fun i j => raw22525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22525step0 raw22525; decide +kernel
      have hl : raw22525step0Labels = raw22525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22525 raw22525Labels permutation346 hz
    mixedMoment B raw22525step0 raw22525step0Labels = mixedMoment B raw22525step1 raw22525step1Labels := by
      have hz : ∀ j, raw22525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22525step1 = (fun i j => raw22525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22525step1 raw22525step0; decide +kernel
      have hl : raw22525step1Labels = raw22525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22525step0 raw22525step0Labels permutation56 hz
    mixedMoment B raw22525step1 raw22525step1Labels = mixedMoment B raw22525step2 raw22525step2Labels := by
      have ha : raw22525step2 = (fun i j => raw22525step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22525step2 raw22525step1; decide +kernel
      have hl : raw22525step2Labels = raw22525step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22525step1 raw22525step1Labels permutation9 permutation7
    mixedMoment B raw22525step2 raw22525step2Labels = mixedMoment B raw22525step3 raw22525step3Labels := by
      have ha : raw22525step3 = raw22525step2 := by apply Matrix.ext; unfold raw22525step3 raw22525step2; decide +kernel
      have hl : raw22525step2Labels = labelEmbedding10 ∘ raw22525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22525step2 raw22525step2Labels raw22525step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22526 raw22526Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22526 raw22526Labels = mixedMoment B raw22526step0 raw22526step0Labels := by
      have hz : ∀ j, raw22526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22526step0 = (fun i j => raw22526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22526step0 raw22526; decide +kernel
      have hl : raw22526step0Labels = raw22526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526 raw22526Labels permutation434 hz
    mixedMoment B raw22526step0 raw22526step0Labels = mixedMoment B raw22526step1 raw22526step1Labels := by
      have hz : ∀ j, raw22526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22526step1 = (fun i j => raw22526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22526step1 raw22526step0; decide +kernel
      have hl : raw22526step1Labels = raw22526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526step0 raw22526step0Labels permutation80 hz
    mixedMoment B raw22526step1 raw22526step1Labels = mixedMoment B raw22526step2 raw22526step2Labels := by
      have hz : ∀ j, raw22526step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22526step2 = (fun i j => raw22526step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22526step2 raw22526step1; decide +kernel
      have hl : raw22526step2Labels = raw22526step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526step1 raw22526step1Labels permutation14 hz
    mixedMoment B raw22526step2 raw22526step2Labels = mixedMoment B raw22526step3 raw22526step3Labels := by
      have ha : raw22526step3 = (fun i j => raw22526step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22526step3 raw22526step2; decide +kernel
      have hl : raw22526step3Labels = raw22526step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22526step2 raw22526step2Labels permutation2 permutation6
    mixedMoment B raw22526step3 raw22526step3Labels = mixedMoment B raw22526step4 raw22526step4Labels := by
      have ha : raw22526step4 = raw22526step3 := by apply Matrix.ext; unfold raw22526step4 raw22526step3; decide +kernel
      have hl : raw22526step3Labels = labelEmbedding9 ∘ raw22526step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22526step3 raw22526step3Labels raw22526step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical22527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22527 raw22527Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22527 raw22527Labels = mixedMoment B raw22527step0 raw22527step0Labels := by
      have hz : ∀ j, raw22527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22527step0 = (fun i j => raw22527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22527step0 raw22527; decide +kernel
      have hl : raw22527step0Labels = raw22527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22527 raw22527Labels permutation434 hz
    mixedMoment B raw22527step0 raw22527step0Labels = mixedMoment B raw22527step1 raw22527step1Labels := by
      have hz : ∀ j, raw22527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22527step1 = (fun i j => raw22527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22527step1 raw22527step0; decide +kernel
      have hl : raw22527step1Labels = raw22527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22527step0 raw22527step0Labels permutation80 hz
    mixedMoment B raw22527step1 raw22527step1Labels = mixedMoment B raw22527step2 raw22527step2Labels := by
      have ha : raw22527step2 = (fun i j => raw22527step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22527step2 raw22527step1; decide +kernel
      have hl : raw22527step2Labels = raw22527step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22527step1 raw22527step1Labels permutation8 permutation6
    mixedMoment B raw22527step2 raw22527step2Labels = mixedMoment B raw22527step3 raw22527step3Labels := by
      have ha : raw22527step3 = raw22527step2 := by apply Matrix.ext; unfold raw22527step3 raw22527step2; decide +kernel
      have hl : raw22527step2Labels = labelEmbedding9 ∘ raw22527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22527step2 raw22527step2Labels raw22527step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22528 raw22528Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22528 raw22528Labels = mixedMoment B raw22528step0 raw22528step0Labels := by
      have hz : ∀ j, raw22528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22528step0 = (fun i j => raw22528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22528step0 raw22528; decide +kernel
      have hl : raw22528step0Labels = raw22528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22528 raw22528Labels permutation434 hz
    mixedMoment B raw22528step0 raw22528step0Labels = mixedMoment B raw22528step1 raw22528step1Labels := by
      have hz : ∀ j, raw22528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22528step1 = (fun i j => raw22528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22528step1 raw22528step0; decide +kernel
      have hl : raw22528step1Labels = raw22528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22528step0 raw22528step0Labels permutation56 hz
    mixedMoment B raw22528step1 raw22528step1Labels = mixedMoment B raw22528step2 raw22528step2Labels := by
      have ha : raw22528step2 = (fun i j => raw22528step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22528step2 raw22528step1; decide +kernel
      have hl : raw22528step2Labels = raw22528step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22528step1 raw22528step1Labels permutation8 permutation6
    mixedMoment B raw22528step2 raw22528step2Labels = mixedMoment B raw22528step3 raw22528step3Labels := by
      have ha : raw22528step3 = raw22528step2 := by apply Matrix.ext; unfold raw22528step3 raw22528step2; decide +kernel
      have hl : raw22528step2Labels = labelEmbedding9 ∘ raw22528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22528step2 raw22528step2Labels raw22528step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22529 raw22529Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22529 raw22529Labels = mixedMoment B raw22529step0 raw22529step0Labels := by
      have hz : ∀ j, raw22529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22529step0 = (fun i j => raw22529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22529step0 raw22529; decide +kernel
      have hl : raw22529step0Labels = raw22529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22529 raw22529Labels permutation346 hz
    mixedMoment B raw22529step0 raw22529step0Labels = mixedMoment B raw22529step1 raw22529step1Labels := by
      have hz : ∀ j, raw22529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22529step1 = (fun i j => raw22529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22529step1 raw22529step0; decide +kernel
      have hl : raw22529step1Labels = raw22529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22529step0 raw22529step0Labels permutation56 hz
    mixedMoment B raw22529step1 raw22529step1Labels = mixedMoment B raw22529step2 raw22529step2Labels := by
      have ha : raw22529step2 = (fun i j => raw22529step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22529step2 raw22529step1; decide +kernel
      have hl : raw22529step2Labels = raw22529step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22529step1 raw22529step1Labels permutation8 permutation6
    mixedMoment B raw22529step2 raw22529step2Labels = mixedMoment B raw22529step3 raw22529step3Labels := by
      have ha : raw22529step3 = raw22529step2 := by apply Matrix.ext; unfold raw22529step3 raw22529step2; decide +kernel
      have hl : raw22529step2Labels = labelEmbedding9 ∘ raw22529step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22529step2 raw22529step2Labels raw22529step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22607 raw22607Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22607 raw22607Labels = mixedMoment B raw22607step0 raw22607step0Labels := by
      have hz : ∀ j, raw22607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22607step0 = (fun i j => raw22607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22607step0 raw22607; decide +kernel
      have hl : raw22607step0Labels = raw22607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22607 raw22607Labels permutation434 hz
    mixedMoment B raw22607step0 raw22607step0Labels = mixedMoment B raw22607step1 raw22607step1Labels := by
      have hz : ∀ j, raw22607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22607step1 = (fun i j => raw22607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22607step1 raw22607step0; decide +kernel
      have hl : raw22607step1Labels = raw22607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22607step0 raw22607step0Labels permutation80 hz
    mixedMoment B raw22607step1 raw22607step1Labels = mixedMoment B raw22607step2 raw22607step2Labels := by
      have ha : raw22607step2 = (fun i j => raw22607step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22607step2 raw22607step1; decide +kernel
      have hl : raw22607step2Labels = raw22607step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22607step1 raw22607step1Labels permutation8 permutation7
    mixedMoment B raw22607step2 raw22607step2Labels = mixedMoment B raw22607step3 raw22607step3Labels := by
      have ha : raw22607step3 = raw22607step2 := by apply Matrix.ext; unfold raw22607step3 raw22607step2; decide +kernel
      have hl : raw22607step2Labels = labelEmbedding10 ∘ raw22607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22607step2 raw22607step2Labels raw22607step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical22608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22608 raw22608Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22608 raw22608Labels = mixedMoment B raw22608step0 raw22608step0Labels := by
      have hz : ∀ j, raw22608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22608step0 = (fun i j => raw22608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22608step0 raw22608; decide +kernel
      have hl : raw22608step0Labels = raw22608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22608 raw22608Labels permutation434 hz
    mixedMoment B raw22608step0 raw22608step0Labels = mixedMoment B raw22608step1 raw22608step1Labels := by
      have hz : ∀ j, raw22608step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22608step1 = (fun i j => raw22608step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22608step1 raw22608step0; decide +kernel
      have hl : raw22608step1Labels = raw22608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22608step0 raw22608step0Labels permutation56 hz
    mixedMoment B raw22608step1 raw22608step1Labels = mixedMoment B raw22608step2 raw22608step2Labels := by
      have ha : raw22608step2 = (fun i j => raw22608step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22608step2 raw22608step1; decide +kernel
      have hl : raw22608step2Labels = raw22608step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22608step1 raw22608step1Labels permutation8 permutation7
    mixedMoment B raw22608step2 raw22608step2Labels = mixedMoment B raw22608step3 raw22608step3Labels := by
      have ha : raw22608step3 = raw22608step2 := by apply Matrix.ext; unfold raw22608step3 raw22608step2; decide +kernel
      have hl : raw22608step2Labels = labelEmbedding10 ∘ raw22608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22608step2 raw22608step2Labels raw22608step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical22609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22609 raw22609Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22609 raw22609Labels = mixedMoment B raw22609step0 raw22609step0Labels := by
      have hz : ∀ j, raw22609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22609step0 = (fun i j => raw22609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22609step0 raw22609; decide +kernel
      have hl : raw22609step0Labels = raw22609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22609 raw22609Labels permutation346 hz
    mixedMoment B raw22609step0 raw22609step0Labels = mixedMoment B raw22609step1 raw22609step1Labels := by
      have hz : ∀ j, raw22609step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22609step1 = (fun i j => raw22609step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22609step1 raw22609step0; decide +kernel
      have hl : raw22609step1Labels = raw22609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22609step0 raw22609step0Labels permutation56 hz
    mixedMoment B raw22609step1 raw22609step1Labels = mixedMoment B raw22609step2 raw22609step2Labels := by
      have ha : raw22609step2 = (fun i j => raw22609step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22609step2 raw22609step1; decide +kernel
      have hl : raw22609step2Labels = raw22609step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22609step1 raw22609step1Labels permutation8 permutation7
    mixedMoment B raw22609step2 raw22609step2Labels = mixedMoment B raw22609step3 raw22609step3Labels := by
      have ha : raw22609step3 = raw22609step2 := by apply Matrix.ext; unfold raw22609step3 raw22609step2; decide +kernel
      have hl : raw22609step2Labels = labelEmbedding10 ∘ raw22609step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22609step2 raw22609step2Labels raw22609step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical22610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22610 raw22610Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22610 raw22610Labels = mixedMoment B raw22610step0 raw22610step0Labels := by
      have hz : ∀ j, raw22610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22610step0 = (fun i j => raw22610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22610step0 raw22610; decide +kernel
      have hl : raw22610step0Labels = raw22610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22610 raw22610Labels permutation434 hz
    mixedMoment B raw22610step0 raw22610step0Labels = mixedMoment B raw22610step1 raw22610step1Labels := by
      have hz : ∀ j, raw22610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22610step1 = (fun i j => raw22610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22610step1 raw22610step0; decide +kernel
      have hl : raw22610step1Labels = raw22610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22610step0 raw22610step0Labels permutation80 hz
    mixedMoment B raw22610step1 raw22610step1Labels = mixedMoment B raw22610step2 raw22610step2Labels := by
      have hz : ∀ j, raw22610step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22610step2 = (fun i j => raw22610step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22610step2 raw22610step1; decide +kernel
      have hl : raw22610step2Labels = raw22610step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22610step1 raw22610step1Labels permutation14 hz
    mixedMoment B raw22610step2 raw22610step2Labels = mixedMoment B raw22610step3 raw22610step3Labels := by
      have ha : raw22610step3 = (fun i j => raw22610step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22610step3 raw22610step2; decide +kernel
      have hl : raw22610step3Labels = raw22610step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22610step2 raw22610step2Labels permutation2 permutation7
    mixedMoment B raw22610step3 raw22610step3Labels = mixedMoment B raw22610step4 raw22610step4Labels := by
      have ha : raw22610step4 = raw22610step3 := by apply Matrix.ext; unfold raw22610step4 raw22610step3; decide +kernel
      have hl : raw22610step3Labels = labelEmbedding10 ∘ raw22610step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22610step3 raw22610step3Labels raw22610step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical22611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22611 raw22611Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22611 raw22611Labels = mixedMoment B raw22611step0 raw22611step0Labels := by
      have hz : ∀ j, raw22611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22611step0 = (fun i j => raw22611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22611step0 raw22611; decide +kernel
      have hl : raw22611step0Labels = raw22611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22611 raw22611Labels permutation434 hz
    mixedMoment B raw22611step0 raw22611step0Labels = mixedMoment B raw22611step1 raw22611step1Labels := by
      have hz : ∀ j, raw22611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22611step1 = (fun i j => raw22611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22611step1 raw22611step0; decide +kernel
      have hl : raw22611step1Labels = raw22611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22611step0 raw22611step0Labels permutation80 hz
    mixedMoment B raw22611step1 raw22611step1Labels = mixedMoment B raw22611step2 raw22611step2Labels := by
      have ha : raw22611step2 = (fun i j => raw22611step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22611step2 raw22611step1; decide +kernel
      have hl : raw22611step2Labels = raw22611step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22611step1 raw22611step1Labels permutation8 permutation6
    mixedMoment B raw22611step2 raw22611step2Labels = mixedMoment B raw22611step3 raw22611step3Labels := by
      have ha : raw22611step3 = raw22611step2 := by apply Matrix.ext; unfold raw22611step3 raw22611step2; decide +kernel
      have hl : raw22611step2Labels = labelEmbedding9 ∘ raw22611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22611step2 raw22611step2Labels raw22611step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical22612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22612 raw22612Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22612 raw22612Labels = mixedMoment B raw22612step0 raw22612step0Labels := by
      have hz : ∀ j, raw22612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22612step0 = (fun i j => raw22612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22612step0 raw22612; decide +kernel
      have hl : raw22612step0Labels = raw22612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22612 raw22612Labels permutation434 hz
    mixedMoment B raw22612step0 raw22612step0Labels = mixedMoment B raw22612step1 raw22612step1Labels := by
      have ha : raw22612step1 = (fun i j => raw22612step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22612step1 raw22612step0; decide +kernel
      have hl : raw22612step1Labels = raw22612step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22612step0 raw22612step0Labels permutation38 permutation6
    mixedMoment B raw22612step1 raw22612step1Labels = mixedMoment B raw22612step2 raw22612step2Labels := by
      have ha : raw22612step2 = raw22612step1 := by apply Matrix.ext; unfold raw22612step2 raw22612step1; decide +kernel
      have hl : raw22612step1Labels = labelEmbedding9 ∘ raw22612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22612step1 raw22612step1Labels raw22612step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical22613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22613 raw22613Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22613 raw22613Labels = mixedMoment B raw22613step0 raw22613step0Labels := by
      have hz : ∀ j, raw22613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22613step0 = (fun i j => raw22613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22613step0 raw22613; decide +kernel
      have hl : raw22613step0Labels = raw22613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22613 raw22613Labels permutation346 hz
    mixedMoment B raw22613step0 raw22613step0Labels = mixedMoment B raw22613step1 raw22613step1Labels := by
      have ha : raw22613step1 = (fun i j => raw22613step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22613step1 raw22613step0; decide +kernel
      have hl : raw22613step1Labels = raw22613step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22613step0 raw22613step0Labels permutation38 permutation6
    mixedMoment B raw22613step1 raw22613step1Labels = mixedMoment B raw22613step2 raw22613step2Labels := by
      have ha : raw22613step2 = raw22613step1 := by apply Matrix.ext; unfold raw22613step2 raw22613step1; decide +kernel
      have hl : raw22613step1Labels = labelEmbedding9 ∘ raw22613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22613step1 raw22613step1Labels raw22613step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical22614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22614 raw22614Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22614 raw22614Labels = mixedMoment B raw22614step0 raw22614step0Labels := by
      have hz : ∀ j, raw22614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22614step0 = (fun i j => raw22614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22614step0 raw22614; decide +kernel
      have hl : raw22614step0Labels = raw22614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22614 raw22614Labels permutation434 hz
    mixedMoment B raw22614step0 raw22614step0Labels = mixedMoment B raw22614step1 raw22614step1Labels := by
      have hz : ∀ j, raw22614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22614step1 = (fun i j => raw22614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22614step1 raw22614step0; decide +kernel
      have hl : raw22614step1Labels = raw22614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22614step0 raw22614step0Labels permutation80 hz
    mixedMoment B raw22614step1 raw22614step1Labels = mixedMoment B raw22614step2 raw22614step2Labels := by
      have ha : raw22614step2 = (fun i j => raw22614step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22614step2 raw22614step1; decide +kernel
      have hl : raw22614step2Labels = raw22614step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22614step1 raw22614step1Labels permutation8 permutation7
    mixedMoment B raw22614step2 raw22614step2Labels = mixedMoment B raw22614step3 raw22614step3Labels := by
      have ha : raw22614step3 = raw22614step2 := by apply Matrix.ext; unfold raw22614step3 raw22614step2; decide +kernel
      have hl : raw22614step2Labels = labelEmbedding10 ∘ raw22614step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22614step2 raw22614step2Labels raw22614step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22615 raw22615Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22615 raw22615Labels = mixedMoment B raw22615step0 raw22615step0Labels := by
      have hz : ∀ j, raw22615 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22615step0 = (fun i j => raw22615 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22615step0 raw22615; decide +kernel
      have hl : raw22615step0Labels = raw22615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22615 raw22615Labels permutation434 hz
    mixedMoment B raw22615step0 raw22615step0Labels = mixedMoment B raw22615step1 raw22615step1Labels := by
      have hz : ∀ j, raw22615step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22615step1 = (fun i j => raw22615step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22615step1 raw22615step0; decide +kernel
      have hl : raw22615step1Labels = raw22615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22615step0 raw22615step0Labels permutation56 hz
    mixedMoment B raw22615step1 raw22615step1Labels = mixedMoment B raw22615step2 raw22615step2Labels := by
      have ha : raw22615step2 = (fun i j => raw22615step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22615step2 raw22615step1; decide +kernel
      have hl : raw22615step2Labels = raw22615step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22615step1 raw22615step1Labels permutation8 permutation6
    mixedMoment B raw22615step2 raw22615step2Labels = mixedMoment B raw22615step3 raw22615step3Labels := by
      have ha : raw22615step3 = raw22615step2 := by apply Matrix.ext; unfold raw22615step3 raw22615step2; decide +kernel
      have hl : raw22615step2Labels = labelEmbedding9 ∘ raw22615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22615step2 raw22615step2Labels raw22615step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical22616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22616 raw22616Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22616 raw22616Labels = mixedMoment B raw22616step0 raw22616step0Labels := by
      have hz : ∀ j, raw22616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22616step0 = (fun i j => raw22616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22616step0 raw22616; decide +kernel
      have hl : raw22616step0Labels = raw22616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22616 raw22616Labels permutation434 hz
    mixedMoment B raw22616step0 raw22616step0Labels = mixedMoment B raw22616step1 raw22616step1Labels := by
      have ha : raw22616step1 = (fun i j => raw22616step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22616step1 raw22616step0; decide +kernel
      have hl : raw22616step1Labels = raw22616step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22616step0 raw22616step0Labels permutation32 permutation6
    mixedMoment B raw22616step1 raw22616step1Labels = mixedMoment B raw22616step2 raw22616step2Labels := by
      have ha : raw22616step2 = raw22616step1 := by apply Matrix.ext; unfold raw22616step2 raw22616step1; decide +kernel
      have hl : raw22616step1Labels = labelEmbedding9 ∘ raw22616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22616step1 raw22616step1Labels raw22616step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical22617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22617 raw22617Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22617 raw22617Labels = mixedMoment B raw22617step0 raw22617step0Labels := by
      have hz : ∀ j, raw22617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22617step0 = (fun i j => raw22617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22617step0 raw22617; decide +kernel
      have hl : raw22617step0Labels = raw22617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22617 raw22617Labels permutation265 hz
    mixedMoment B raw22617step0 raw22617step0Labels = mixedMoment B raw22617step1 raw22617step1Labels := by
      have ha : raw22617step1 = (fun i j => raw22617step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22617step1 raw22617step0; decide +kernel
      have hl : raw22617step1Labels = raw22617step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22617step0 raw22617step0Labels permutation38 permutation6
    mixedMoment B raw22617step1 raw22617step1Labels = mixedMoment B raw22617step2 raw22617step2Labels := by
      have ha : raw22617step2 = raw22617step1 := by apply Matrix.ext; unfold raw22617step2 raw22617step1; decide +kernel
      have hl : raw22617step1Labels = labelEmbedding9 ∘ raw22617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22617step1 raw22617step1Labels raw22617step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical22618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22618 raw22618Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22618 raw22618Labels = mixedMoment B raw22618step0 raw22618step0Labels := by
      have hz : ∀ j, raw22618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22618step0 = (fun i j => raw22618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22618step0 raw22618; decide +kernel
      have hl : raw22618step0Labels = raw22618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22618 raw22618Labels permutation434 hz
    mixedMoment B raw22618step0 raw22618step0Labels = mixedMoment B raw22618step1 raw22618step1Labels := by
      have hz : ∀ j, raw22618step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22618step1 = (fun i j => raw22618step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22618step1 raw22618step0; decide +kernel
      have hl : raw22618step1Labels = raw22618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22618step0 raw22618step0Labels permutation56 hz
    mixedMoment B raw22618step1 raw22618step1Labels = mixedMoment B raw22618step2 raw22618step2Labels := by
      have ha : raw22618step2 = (fun i j => raw22618step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22618step2 raw22618step1; decide +kernel
      have hl : raw22618step2Labels = raw22618step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22618step1 raw22618step1Labels permutation8 permutation7
    mixedMoment B raw22618step2 raw22618step2Labels = mixedMoment B raw22618step3 raw22618step3Labels := by
      have ha : raw22618step3 = raw22618step2 := by apply Matrix.ext; unfold raw22618step3 raw22618step2; decide +kernel
      have hl : raw22618step2Labels = labelEmbedding10 ∘ raw22618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22618step2 raw22618step2Labels raw22618step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22619 raw22619Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22619 raw22619Labels = mixedMoment B raw22619step0 raw22619step0Labels := by
      have hz : ∀ j, raw22619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22619step0 = (fun i j => raw22619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22619step0 raw22619; decide +kernel
      have hl : raw22619step0Labels = raw22619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22619 raw22619Labels permutation346 hz
    mixedMoment B raw22619step0 raw22619step0Labels = mixedMoment B raw22619step1 raw22619step1Labels := by
      have hz : ∀ j, raw22619step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22619step1 = (fun i j => raw22619step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22619step1 raw22619step0; decide +kernel
      have hl : raw22619step1Labels = raw22619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22619step0 raw22619step0Labels permutation56 hz
    mixedMoment B raw22619step1 raw22619step1Labels = mixedMoment B raw22619step2 raw22619step2Labels := by
      have ha : raw22619step2 = (fun i j => raw22619step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22619step2 raw22619step1; decide +kernel
      have hl : raw22619step2Labels = raw22619step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22619step1 raw22619step1Labels permutation8 permutation6
    mixedMoment B raw22619step2 raw22619step2Labels = mixedMoment B raw22619step3 raw22619step3Labels := by
      have ha : raw22619step3 = raw22619step2 := by apply Matrix.ext; unfold raw22619step3 raw22619step2; decide +kernel
      have hl : raw22619step2Labels = labelEmbedding9 ∘ raw22619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22619step2 raw22619step2Labels raw22619step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical22620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22620 raw22620Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22620 raw22620Labels = mixedMoment B raw22620step0 raw22620step0Labels := by
      have hz : ∀ j, raw22620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22620step0 = (fun i j => raw22620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22620step0 raw22620; decide +kernel
      have hl : raw22620step0Labels = raw22620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22620 raw22620Labels permutation346 hz
    mixedMoment B raw22620step0 raw22620step0Labels = mixedMoment B raw22620step1 raw22620step1Labels := by
      have ha : raw22620step1 = (fun i j => raw22620step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22620step1 raw22620step0; decide +kernel
      have hl : raw22620step1Labels = raw22620step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22620step0 raw22620step0Labels permutation32 permutation6
    mixedMoment B raw22620step1 raw22620step1Labels = mixedMoment B raw22620step2 raw22620step2Labels := by
      have ha : raw22620step2 = raw22620step1 := by apply Matrix.ext; unfold raw22620step2 raw22620step1; decide +kernel
      have hl : raw22620step1Labels = labelEmbedding9 ∘ raw22620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22620step1 raw22620step1Labels raw22620step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical22621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22621 raw22621Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22621 raw22621Labels = mixedMoment B raw22621step0 raw22621step0Labels := by
      have hz : ∀ j, raw22621 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22621step0 = (fun i j => raw22621 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22621step0 raw22621; decide +kernel
      have hl : raw22621step0Labels = raw22621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22621 raw22621Labels permutation265 hz
    mixedMoment B raw22621step0 raw22621step0Labels = mixedMoment B raw22621step1 raw22621step1Labels := by
      have ha : raw22621step1 = (fun i j => raw22621step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22621step1 raw22621step0; decide +kernel
      have hl : raw22621step1Labels = raw22621step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22621step0 raw22621step0Labels permutation32 permutation6
    mixedMoment B raw22621step1 raw22621step1Labels = mixedMoment B raw22621step2 raw22621step2Labels := by
      have ha : raw22621step2 = raw22621step1 := by apply Matrix.ext; unfold raw22621step2 raw22621step1; decide +kernel
      have hl : raw22621step1Labels = labelEmbedding9 ∘ raw22621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22621step1 raw22621step1Labels raw22621step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

theorem canonical22622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22622 raw22622Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22622 raw22622Labels = mixedMoment B raw22622step0 raw22622step0Labels := by
      have hz : ∀ j, raw22622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22622step0 = (fun i j => raw22622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22622step0 raw22622; decide +kernel
      have hl : raw22622step0Labels = raw22622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22622 raw22622Labels permutation346 hz
    mixedMoment B raw22622step0 raw22622step0Labels = mixedMoment B raw22622step1 raw22622step1Labels := by
      have hz : ∀ j, raw22622step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22622step1 = (fun i j => raw22622step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22622step1 raw22622step0; decide +kernel
      have hl : raw22622step1Labels = raw22622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22622step0 raw22622step0Labels permutation56 hz
    mixedMoment B raw22622step1 raw22622step1Labels = mixedMoment B raw22622step2 raw22622step2Labels := by
      have ha : raw22622step2 = (fun i j => raw22622step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22622step2 raw22622step1; decide +kernel
      have hl : raw22622step2Labels = raw22622step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22622step1 raw22622step1Labels permutation8 permutation7
    mixedMoment B raw22622step2 raw22622step2Labels = mixedMoment B raw22622step3 raw22622step3Labels := by
      have ha : raw22622step3 = raw22622step2 := by apply Matrix.ext; unfold raw22622step3 raw22622step2; decide +kernel
      have hl : raw22622step2Labels = labelEmbedding10 ∘ raw22622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22622step2 raw22622step2Labels raw22622step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22623 raw22623Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22623 raw22623Labels = mixedMoment B raw22623step0 raw22623step0Labels := by
      have hz : ∀ j, raw22623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22623step0 = (fun i j => raw22623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22623step0 raw22623; decide +kernel
      have hl : raw22623step0Labels = raw22623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623 raw22623Labels permutation434 hz
    mixedMoment B raw22623step0 raw22623step0Labels = mixedMoment B raw22623step1 raw22623step1Labels := by
      have hz : ∀ j, raw22623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22623step1 = (fun i j => raw22623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22623step1 raw22623step0; decide +kernel
      have hl : raw22623step1Labels = raw22623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623step0 raw22623step0Labels permutation80 hz
    mixedMoment B raw22623step1 raw22623step1Labels = mixedMoment B raw22623step2 raw22623step2Labels := by
      have hz : ∀ j, raw22623step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22623step2 = (fun i j => raw22623step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22623step2 raw22623step1; decide +kernel
      have hl : raw22623step2Labels = raw22623step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623step1 raw22623step1Labels permutation14 hz
    mixedMoment B raw22623step2 raw22623step2Labels = mixedMoment B raw22623step3 raw22623step3Labels := by
      have ha : raw22623step3 = (fun i j => raw22623step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22623step3 raw22623step2; decide +kernel
      have hl : raw22623step3Labels = raw22623step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22623step2 raw22623step2Labels permutation3 permutation6
    mixedMoment B raw22623step3 raw22623step3Labels = mixedMoment B raw22623step4 raw22623step4Labels := by
      have ha : raw22623step4 = raw22623step3 := by apply Matrix.ext; unfold raw22623step4 raw22623step3; decide +kernel
      have hl : raw22623step3Labels = labelEmbedding9 ∘ raw22623step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22623step3 raw22623step3Labels raw22623step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical22624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22624 raw22624Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22624 raw22624Labels = mixedMoment B raw22624step0 raw22624step0Labels := by
      have hz : ∀ j, raw22624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22624step0 = (fun i j => raw22624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22624step0 raw22624; decide +kernel
      have hl : raw22624step0Labels = raw22624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22624 raw22624Labels permutation434 hz
    mixedMoment B raw22624step0 raw22624step0Labels = mixedMoment B raw22624step1 raw22624step1Labels := by
      have hz : ∀ j, raw22624step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22624step1 = (fun i j => raw22624step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22624step1 raw22624step0; decide +kernel
      have hl : raw22624step1Labels = raw22624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22624step0 raw22624step0Labels permutation80 hz
    mixedMoment B raw22624step1 raw22624step1Labels = mixedMoment B raw22624step2 raw22624step2Labels := by
      have ha : raw22624step2 = (fun i j => raw22624step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22624step2 raw22624step1; decide +kernel
      have hl : raw22624step2Labels = raw22624step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22624step1 raw22624step1Labels permutation9 permutation6
    mixedMoment B raw22624step2 raw22624step2Labels = mixedMoment B raw22624step3 raw22624step3Labels := by
      have ha : raw22624step3 = raw22624step2 := by apply Matrix.ext; unfold raw22624step3 raw22624step2; decide +kernel
      have hl : raw22624step2Labels = labelEmbedding9 ∘ raw22624step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22624step2 raw22624step2Labels raw22624step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22625 raw22625Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22625 raw22625Labels = mixedMoment B raw22625step0 raw22625step0Labels := by
      have hz : ∀ j, raw22625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22625step0 = (fun i j => raw22625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22625step0 raw22625; decide +kernel
      have hl : raw22625step0Labels = raw22625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22625 raw22625Labels permutation434 hz
    mixedMoment B raw22625step0 raw22625step0Labels = mixedMoment B raw22625step1 raw22625step1Labels := by
      have hz : ∀ j, raw22625step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22625step1 = (fun i j => raw22625step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22625step1 raw22625step0; decide +kernel
      have hl : raw22625step1Labels = raw22625step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22625step0 raw22625step0Labels permutation56 hz
    mixedMoment B raw22625step1 raw22625step1Labels = mixedMoment B raw22625step2 raw22625step2Labels := by
      have ha : raw22625step2 = (fun i j => raw22625step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22625step2 raw22625step1; decide +kernel
      have hl : raw22625step2Labels = raw22625step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22625step1 raw22625step1Labels permutation9 permutation6
    mixedMoment B raw22625step2 raw22625step2Labels = mixedMoment B raw22625step3 raw22625step3Labels := by
      have ha : raw22625step3 = raw22625step2 := by apply Matrix.ext; unfold raw22625step3 raw22625step2; decide +kernel
      have hl : raw22625step2Labels = labelEmbedding9 ∘ raw22625step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22625step2 raw22625step2Labels raw22625step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22626 raw22626Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22626 raw22626Labels = mixedMoment B raw22626step0 raw22626step0Labels := by
      have hz : ∀ j, raw22626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22626step0 = (fun i j => raw22626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22626step0 raw22626; decide +kernel
      have hl : raw22626step0Labels = raw22626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22626 raw22626Labels permutation346 hz
    mixedMoment B raw22626step0 raw22626step0Labels = mixedMoment B raw22626step1 raw22626step1Labels := by
      have hz : ∀ j, raw22626step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22626step1 = (fun i j => raw22626step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22626step1 raw22626step0; decide +kernel
      have hl : raw22626step1Labels = raw22626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22626step0 raw22626step0Labels permutation56 hz
    mixedMoment B raw22626step1 raw22626step1Labels = mixedMoment B raw22626step2 raw22626step2Labels := by
      have ha : raw22626step2 = (fun i j => raw22626step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22626step2 raw22626step1; decide +kernel
      have hl : raw22626step2Labels = raw22626step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22626step1 raw22626step1Labels permutation9 permutation6
    mixedMoment B raw22626step2 raw22626step2Labels = mixedMoment B raw22626step3 raw22626step3Labels := by
      have ha : raw22626step3 = raw22626step2 := by apply Matrix.ext; unfold raw22626step3 raw22626step2; decide +kernel
      have hl : raw22626step2Labels = labelEmbedding9 ∘ raw22626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22626step2 raw22626step2Labels raw22626step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical22627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22627 raw22627Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw22627 raw22627Labels = mixedMoment B raw22627step0 raw22627step0Labels := by
      have hz : ∀ j, raw22627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22627step0 = (fun i j => raw22627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22627step0 raw22627; decide +kernel
      have hl : raw22627step0Labels = raw22627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22627 raw22627Labels permutation434 hz
    mixedMoment B raw22627step0 raw22627step0Labels = mixedMoment B raw22627step1 raw22627step1Labels := by
      have hz : ∀ j, raw22627step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22627step1 = (fun i j => raw22627step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22627step1 raw22627step0; decide +kernel
      have hl : raw22627step1Labels = raw22627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22627step0 raw22627step0Labels permutation80 hz
    mixedMoment B raw22627step1 raw22627step1Labels = mixedMoment B raw22627step2 raw22627step2Labels := by
      have hz : ∀ j, raw22627step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22627step2 = (fun i j => raw22627step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22627step2 raw22627step1; decide +kernel
      have hl : raw22627step2Labels = raw22627step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22627step1 raw22627step1Labels permutation14 hz
    mixedMoment B raw22627step2 raw22627step2Labels = mixedMoment B raw22627step3 raw22627step3Labels := by
      have ha : raw22627step3 = (fun i j => raw22627step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22627step3 raw22627step2; decide +kernel
      have hl : raw22627step3Labels = raw22627step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22627step2 raw22627step2Labels permutation3 permutation6
    mixedMoment B raw22627step3 raw22627step3Labels = mixedMoment B raw22627step4 raw22627step4Labels := by
      have ha : raw22627step4 = raw22627step3 := by apply Matrix.ext; unfold raw22627step4 raw22627step3; decide +kernel
      have hl : raw22627step3Labels = labelEmbedding9 ∘ raw22627step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22627step3 raw22627step3Labels raw22627step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4627 node4627Labels := by rfl

theorem canonical22628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22628 raw22628Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw22628 raw22628Labels = mixedMoment B raw22628step0 raw22628step0Labels := by
      have hz : ∀ j, raw22628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22628step0 = (fun i j => raw22628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22628step0 raw22628; decide +kernel
      have hl : raw22628step0Labels = raw22628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22628 raw22628Labels permutation434 hz
    mixedMoment B raw22628step0 raw22628step0Labels = mixedMoment B raw22628step1 raw22628step1Labels := by
      have hz : ∀ j, raw22628step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22628step1 = (fun i j => raw22628step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22628step1 raw22628step0; decide +kernel
      have hl : raw22628step1Labels = raw22628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22628step0 raw22628step0Labels permutation80 hz
    mixedMoment B raw22628step1 raw22628step1Labels = mixedMoment B raw22628step2 raw22628step2Labels := by
      have hz : ∀ j, raw22628step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22628step2 = (fun i j => raw22628step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22628step2 raw22628step1; decide +kernel
      have hl : raw22628step2Labels = raw22628step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22628step1 raw22628step1Labels permutation14 hz
    mixedMoment B raw22628step2 raw22628step2Labels = mixedMoment B raw22628step3 raw22628step3Labels := by
      have ha : raw22628step3 = (fun i j => raw22628step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22628step3 raw22628step2; decide +kernel
      have hl : raw22628step3Labels = raw22628step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22628step2 raw22628step2Labels permutation2 permutation6
    mixedMoment B raw22628step3 raw22628step3Labels = mixedMoment B raw22628step4 raw22628step4Labels := by
      have ha : raw22628step4 = raw22628step3 := by apply Matrix.ext; unfold raw22628step4 raw22628step3; decide +kernel
      have hl : raw22628step3Labels = labelEmbedding9 ∘ raw22628step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22628step3 raw22628step3Labels raw22628step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4627 node4627Labels := by rfl

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

theorem canonical1275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1275 raw1275Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw1275 raw1275Labels = mixedMoment B raw1275step0 raw1275step0Labels := by
      have ha : raw1275step0 = (fun i j => raw1275 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1275step0 raw1275; decide +kernel
      have hl : raw1275step0Labels = raw1275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1275 raw1275Labels permutation8 permutation4
    mixedMoment B raw1275step0 raw1275step0Labels = mixedMoment B raw1275step1 raw1275step1Labels := by
      have ha : raw1275step1 = raw1275step0 := by apply Matrix.ext; unfold raw1275step1 raw1275step0; decide +kernel
      have hl : raw1275step0Labels = labelEmbedding7 ∘ raw1275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1275step0 raw1275step0Labels raw1275step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1276 raw1276Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw1276 raw1276Labels = mixedMoment B raw1276step0 raw1276step0Labels := by
      have ha : raw1276step0 = (fun i j => raw1276 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1276step0 raw1276; decide +kernel
      have hl : raw1276step0Labels = raw1276Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1276 raw1276Labels permutation8 permutation4
    _ = mixedMoment B node1050 node1050Labels := by rfl

theorem canonical1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1277 raw1277Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw1277 raw1277Labels = mixedMoment B raw1277step0 raw1277step0Labels := by
      have ha : raw1277step0 = (fun i j => raw1277 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1277step0 raw1277; decide +kernel
      have hl : raw1277step0Labels = raw1277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1277 raw1277Labels permutation8 permutation6
    mixedMoment B raw1277step0 raw1277step0Labels = mixedMoment B raw1277step1 raw1277step1Labels := by
      have ha : raw1277step1 = -raw1277step0 := by apply Matrix.ext; change ∀ i j, raw1277step1 i j = -(raw1277step0 i j); unfold raw1277step1 raw1277step0; decide +kernel
      have hl : raw1277step1Labels = raw1277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1277step1 raw1277step1Labels = mixedMoment B raw1277step2 raw1277step2Labels := by
      have ha : raw1277step2 = raw1277step1 := by apply Matrix.ext; unfold raw1277step2 raw1277step1; decide +kernel
      have hl : raw1277step1Labels = labelEmbedding1 ∘ raw1277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1277step1 raw1277step1Labels raw1277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw178 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw178 = injectiveMoment H raw178step0 := by
      have heq : raw178step0 = -raw178 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw178).symm
    injectiveMoment H raw178step0 = injectiveMoment H raw178step1 := by
      have heq : raw178step1 = (fun i j => raw178step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw178step0 permutation4 permutation6
    _ = injectiveMoment H node31 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
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

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node160 node160Labels = Sparse.eval singlePairValue160 (familyPairVector B) := by
  have hp := single_label_three B hB node160
  have hl : node160Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node160 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 1) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node160 PairSemantics.raw5183
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 2) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node160 PairSemantics.raw5214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node160 PairSemantics.raw214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node160 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value31 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node160 (EqualityPatterns.family3.label 4) = PairSemantics.raw178 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node160 PairSemantics.raw178
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical178 hH).trans (PairSemantics.sound31 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue160, PairSemantics.value0, PairSemantics.value4, PairSemantics.value9, PairSemantics.value31, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1311 node1311Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node160 node160Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw90 singletonSmall1311
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1311) = raw90Labels := by decide +kernel
  rw [hl, canonical90 B hB] at h
  have hc0 : mixedMoment B raw90 (Fin.cases (0 : Fin 1) singletonSmall1311) =
      mixedMoment B node160 node160Labels := by
    have ha : raw90 = raw91 := by apply Matrix.ext; unfold raw90 raw91; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1311 = raw91Labels := by decide +kernel
    rw [ha, hj, canonical91 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4467 node4467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1050 node1050Labels + mixedMoment B node1751 node1751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1275 singletonSmall4467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4467) = raw1275Labels := by decide +kernel
  rw [hl, canonical1275 B hB] at h
  have hc0 : mixedMoment B raw1275 (Fin.cases (0 : Fin 2) singletonSmall4467) =
      mixedMoment B node1050 node1050Labels := by
    have ha : raw1275 = raw1276 := by apply Matrix.ext; unfold raw1275 raw1276; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4467 = raw1276Labels := by decide +kernel
    rw [ha, hj, canonical1276 B hB]
  have hc1 : mixedMoment B raw1275 (Fin.cases (1 : Fin 2) singletonSmall4467) =
      mixedMoment B node1751 node1751Labels := by
    have ha : raw1275 = raw1277 := by apply Matrix.ext; unfold raw1275 raw1277; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4467 = raw1277Labels := by decide +kernel
    rw [ha, hj, canonical1277 B hB]
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

theorem singleton4612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4612 node4612Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1246 node1246Labels + mixedMoment B node3301 node3301Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1437 singletonSmall4612
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4612) = raw1437Labels := by decide +kernel
  rw [hl, canonical1437 B hB] at h
  have hc0 : mixedMoment B raw1437 (Fin.cases (0 : Fin 2) singletonSmall4612) =
      mixedMoment B node1246 node1246Labels := by
    have ha : raw1437 = raw1438 := by apply Matrix.ext; unfold raw1437 raw1438; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4612 = raw1438Labels := by decide +kernel
    rw [ha, hj, canonical1438 B hB]
  have hc1 : mixedMoment B raw1437 (Fin.cases (1 : Fin 2) singletonSmall4612) =
      mixedMoment B node3301 node3301Labels := by
    have ha : raw1437 = raw1439 := by apply Matrix.ext; unfold raw1437 raw1439; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4612 = raw1439Labels := by decide +kernel
    rw [ha, hj, canonical1439 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4627 node4627Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1311 node1311Labels + mixedMoment B node3311 node3311Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1461 singletonSmall4627
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4627) = raw1461Labels := by decide +kernel
  rw [hl, canonical1461 B hB] at h
  have hc0 : mixedMoment B raw1461 (Fin.cases (0 : Fin 2) singletonSmall4627) =
      mixedMoment B node1311 node1311Labels := by
    have ha : raw1461 = raw1462 := by apply Matrix.ext; unfold raw1461 raw1462; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4627 = raw1462Labels := by decide +kernel
    rw [ha, hj, canonical1462 B hB]
  have hc1 : mixedMoment B raw1461 (Fin.cases (1 : Fin 2) singletonSmall4627) =
      mixedMoment B node3311 node3311Labels := by
    have ha : raw1461 = raw1463 := by apply Matrix.ext; unfold raw1461 raw1463; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4627 = raw1463Labels := by decide +kernel
    rw [ha, hj, canonical1463 B hB]
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

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node160 node160Labels = Sparse.eval nodeValue160 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue160 (familyPairVector B) := singlePair160 B _hB
    _ = _ := by
      norm_num [singlePairValue160, nodeValue160, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

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

theorem sound1311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1311 node1311Labels = Sparse.eval nodeValue1311 (mixedVector B) := by
  have h := singleton1311 B _hB
  rw [sound160 B _hB _hF] at h
  norm_num [nodeValue1311, nodeValue160, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

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

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3311 node3311Labels = Sparse.eval nodeValue3311 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3311) = mixedMoment B node3311 node3311Labels := rfl
  simpa [nodeValue3311, Sparse.eval] using hc.symm

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

theorem sound4467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4467 node4467Labels = Sparse.eval nodeValue4467 (mixedVector B) := by
  have h := singleton4467 B _hB
  rw [sound1050 B _hB _hF, sound1751 B _hB _hF] at h
  norm_num [nodeValue4467, nodeValue1050, nodeValue1751, Sparse.eval] at h ⊢
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

theorem sound4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = Sparse.eval nodeValue4511 (mixedVector B) := by
  simpa only [nodeValue4511, Sparse.eval_nil] using zero4511 B _hB _hF

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

theorem sound4593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4593 node4593Labels = Sparse.eval nodeValue4593 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4593) = mixedMoment B node4593 node4593Labels := rfl
  simpa [nodeValue4593, Sparse.eval] using hc.symm

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

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4627 node4627Labels = Sparse.eval nodeValue4627 (mixedVector B) := by
  have h := singleton4627 B _hB
  rw [sound1311 B _hB _hF, sound3311 B _hB _hF] at h
  norm_num [nodeValue4627, nodeValue1311, nodeValue3311, Sparse.eval] at h ⊢
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

theorem sourceEq1480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1480 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 1) (sourceB1480 + difference 1 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 1) (sourceB1480 + difference 1 0) sourceC1480) = raw22607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22607; decide +kernel
    rw [ha]
    exact (canonical22607 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 2) (sourceB1480 + difference 2 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 2) (sourceB1480 + difference 2 0) sourceC1480) = raw22608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22608; decide +kernel
    rw [ha]
    exact (canonical22608 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 3) (sourceB1480 + difference 3 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 3) (sourceB1480 + difference 3 0) sourceC1480) = raw22609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22609; decide +kernel
    rw [ha]
    exact (canonical22609 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 4) (sourceB1480 + difference 4 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 4) (sourceB1480 + difference 4 0) sourceC1480) = raw22510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22510; decide +kernel
    rw [ha]
    exact (canonical22510 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1480 + difference 0 5) (sourceB1480 + difference 5 0) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1480 + difference 0 5) (sourceB1480 + difference 5 0) sourceC1480) = raw22610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22610; decide +kernel
    rw [ha]
    exact (canonical22610 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 0) (sourceB1480 + difference 0 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 0) (sourceB1480 + difference 0 1) sourceC1480) = raw22611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22611; decide +kernel
    rw [ha]
    exact (canonical22611 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 2) (sourceB1480 + difference 2 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 2) (sourceB1480 + difference 2 1) sourceC1480) = raw22612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22612; decide +kernel
    rw [ha]
    exact (canonical22612 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 3) (sourceB1480 + difference 3 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 3) (sourceB1480 + difference 3 1) sourceC1480) = raw22613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22613; decide +kernel
    rw [ha]
    exact (canonical22613 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 4) (sourceB1480 + difference 4 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 4) (sourceB1480 + difference 4 1) sourceC1480) = raw22515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22515; decide +kernel
    rw [ha]
    exact (canonical22515 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1480 + difference 1 5) (sourceB1480 + difference 5 1) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 1 5) (sourceB1480 + difference 5 1) sourceC1480) = raw22614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22614; decide +kernel
    rw [ha]
    exact (canonical22614 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 0) (sourceB1480 + difference 0 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 0) (sourceB1480 + difference 0 2) sourceC1480) = raw22615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22615; decide +kernel
    rw [ha]
    exact (canonical22615 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 1) (sourceB1480 + difference 1 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 1) (sourceB1480 + difference 1 2) sourceC1480) = raw22616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22616; decide +kernel
    rw [ha]
    exact (canonical22616 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 3) (sourceB1480 + difference 3 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 3) (sourceB1480 + difference 3 2) sourceC1480) = raw22617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22617; decide +kernel
    rw [ha]
    exact (canonical22617 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 4) (sourceB1480 + difference 4 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 4) (sourceB1480 + difference 4 2) sourceC1480) = raw22520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22520; decide +kernel
    rw [ha]
    exact (canonical22520 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1480 + difference 2 5) (sourceB1480 + difference 5 2) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 2 5) (sourceB1480 + difference 5 2) sourceC1480) = raw22618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22618; decide +kernel
    rw [ha]
    exact (canonical22618 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 0) (sourceB1480 + difference 0 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 0) (sourceB1480 + difference 0 3) sourceC1480) = raw22619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22619; decide +kernel
    rw [ha]
    exact (canonical22619 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 1) (sourceB1480 + difference 1 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 1) (sourceB1480 + difference 1 3) sourceC1480) = raw22620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22620; decide +kernel
    rw [ha]
    exact (canonical22620 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 2) (sourceB1480 + difference 2 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 2) (sourceB1480 + difference 2 3) sourceC1480) = raw22621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22621; decide +kernel
    rw [ha]
    exact (canonical22621 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 4) (sourceB1480 + difference 4 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 4) (sourceB1480 + difference 4 3) sourceC1480) = raw22525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22525; decide +kernel
    rw [ha]
    exact (canonical22525 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1480 + difference 3 5) (sourceB1480 + difference 5 3) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 3 5) (sourceB1480 + difference 5 3) sourceC1480) = raw22622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22622; decide +kernel
    rw [ha]
    exact (canonical22622 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 0) (sourceB1480 + difference 0 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 0) (sourceB1480 + difference 0 4) sourceC1480) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 1) (sourceB1480 + difference 1 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 1) (sourceB1480 + difference 1 4) sourceC1480) = raw22624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22624; decide +kernel
    rw [ha]
    exact (canonical22624 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 2) (sourceB1480 + difference 2 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 2) (sourceB1480 + difference 2 4) sourceC1480) = raw22625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22625; decide +kernel
    rw [ha]
    exact (canonical22625 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 3) (sourceB1480 + difference 3 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 3) (sourceB1480 + difference 3 4) sourceC1480) = raw22626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22626; decide +kernel
    rw [ha]
    exact (canonical22626 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1480 + difference 4 5) (sourceB1480 + difference 5 4) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1480 + difference 4 5) (sourceB1480 + difference 5 4) sourceC1480) = raw22627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22627; decide +kernel
    rw [ha]
    exact (canonical22627 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 0) (sourceB1480 + difference 0 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 0) (sourceB1480 + difference 0 5) sourceC1480) = raw22526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22526; decide +kernel
    rw [ha]
    exact (canonical22526 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 1) (sourceB1480 + difference 1 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 1) (sourceB1480 + difference 1 5) sourceC1480) = raw22527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22527; decide +kernel
    rw [ha]
    exact (canonical22527 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 2) (sourceB1480 + difference 2 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 2) (sourceB1480 + difference 2 5) sourceC1480) = raw22528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22528; decide +kernel
    rw [ha]
    exact (canonical22528 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 3) (sourceB1480 + difference 3 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 3) (sourceB1480 + difference 3 5) sourceC1480) = raw22529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22529; decide +kernel
    rw [ha]
    exact (canonical22529 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1480 + difference 5 4) (sourceB1480 + difference 4 5) sourceC1480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1480 + difference 5 4) (sourceB1480 + difference 4 5) sourceC1480) = raw22628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1480 sourceB1480 sourceC1480 difference raw22628; decide +kernel
    rw [ha]
    exact (canonical22628 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1480 sourceB1480 sourceC1480
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1480, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1268 : Integer.Sparse.reindex keyMap MixedData.row1268 = numericRow1268 := by decide +kernel

theorem numericCheck1268 (x : Master → ℝ) : Integer.Sparse.eval numericRow1268 x =
    (360 : ℝ) * reducedSource1268 x := by
  norm_num [numericRow1268, reducedSource1268, Integer.Sparse.eval, Sparse.eval, nodeValue4467, nodeValue4511, nodeValue4593, nodeValue4612, nodeValue4627] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1268 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1268 (mixedVector B) = 0 := by
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4593 : mixedVector B (Sum.inr 4593) = Sparse.eval nodeValue4593 (mixedVector B) := by
    change mixedMoment B node4593 node4593Labels = _
    exact sound4593 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4627 : mixedVector B (Sum.inr 4627) = Sparse.eval nodeValue4627 (mixedVector B) := by
    change mixedMoment B node4627 node4627Labels = _
    exact sound4627 B hB hF
  simpa only [sourceForm1480, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4467, h4511, h4593, h4612, h4627, reducedSource1268] using sourceEq1480 B hB

theorem rowSound1268_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1268 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1268, numericCheck1268, reducedZero1268 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e_oai
