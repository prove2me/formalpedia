-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:34:58.7462+00:00
-- url     : https://prove2.me/submissions/0a4a2eba-d002-42ef-91e6-f2bbda4e2c98

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
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

theorem canonical62 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw62 raw62Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw62 raw62Labels = mixedMoment B raw62step0 raw62step0Labels := by
      have ha : raw62step0 = (fun i j => raw62 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw62step0 raw62; decide +kernel
      have hl : raw62step0Labels = raw62Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw62 raw62Labels permutation8 permutation5
    mixedMoment B raw62step0 raw62step0Labels = mixedMoment B raw62step1 raw62step1Labels := by
      have ha : raw62step1 = raw62step0 := by apply Matrix.ext; unfold raw62step1 raw62step0; decide +kernel
      have hl : raw62step0Labels = labelEmbedding1 ∘ raw62step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw62step0 raw62step0Labels raw62step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1274 node1274Labels := by rfl

theorem canonical63 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw63 raw63Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw63 raw63Labels = mixedMoment B raw63step0 raw63step0Labels := by
      have ha : raw63step0 = (fun i j => raw63 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw63step0 raw63; decide +kernel
      have hl : raw63step0Labels = raw63Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw63 raw63Labels permutation9 permutation4
    _ = mixedMoment B node149 node149Labels := by rfl

theorem canonical92 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw92 raw92Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw92 raw92Labels = mixedMoment B raw92step0 raw92step0Labels := by
      have ha : raw92step0 = (fun i j => raw92 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw92step0 raw92; decide +kernel
      have hl : raw92step0Labels = raw92Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw92 raw92Labels permutation2 permutation5
    mixedMoment B raw92step0 raw92step0Labels = mixedMoment B raw92step1 raw92step1Labels := by
      have ha : raw92step1 = raw92step0 := by apply Matrix.ext; unfold raw92step1 raw92step0; decide +kernel
      have hl : raw92step0Labels = labelEmbedding1 ∘ raw92step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw92step0 raw92step0Labels raw92step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1312 node1312Labels := by rfl

theorem canonical93 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw93 raw93Labels = mixedMoment B node161 node161Labels := by
  calc
    mixedMoment B raw93 raw93Labels = mixedMoment B raw93step0 raw93step0Labels := by
      have ha : raw93step0 = (fun i j => raw93 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw93step0 raw93; decide +kernel
      have hl : raw93step0Labels = raw93Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw93 raw93Labels permutation2 permutation4
    _ = mixedMoment B node161 node161Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw140 raw140Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw140 raw140Labels = mixedMoment B raw140step0 raw140step0Labels := by
      have ha : raw140step0 = (fun i j => raw140 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw140step0 raw140; decide +kernel
      have hl : raw140step0Labels = raw140Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw140 raw140Labels permutation8 permutation5
    mixedMoment B raw140step0 raw140step0Labels = mixedMoment B raw140step1 raw140step1Labels := by
      have ha : raw140step1 = raw140step0 := by apply Matrix.ext; unfold raw140step1 raw140step0; decide +kernel
      have hl : raw140step0Labels = labelEmbedding1 ∘ raw140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw140step0 raw140step0Labels raw140step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

theorem canonical141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw141 raw141Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw141 raw141Labels = mixedMoment B raw141step0 raw141step0Labels := by
      have ha : raw141step0 = (fun i j => raw141 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw141step0 raw141; decide +kernel
      have hl : raw141step0Labels = raw141Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw141 raw141Labels permutation9 permutation4
    _ = mixedMoment B node98 node98Labels := by rfl

theorem canonical168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw168 raw168Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw168 raw168Labels = mixedMoment B raw168step0 raw168step0Labels := by
      have ha : raw168step0 = (fun i j => raw168 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw168step0 raw168; decide +kernel
      have hl : raw168step0Labels = raw168Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw168 raw168Labels permutation2 permutation5
    mixedMoment B raw168step0 raw168step0Labels = mixedMoment B raw168step1 raw168step1Labels := by
      have ha : raw168step1 = raw168step0 := by apply Matrix.ext; unfold raw168step1 raw168step0; decide +kernel
      have hl : raw168step0Labels = labelEmbedding1 ∘ raw168step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw168step0 raw168step0Labels raw168step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1454 node1454Labels := by rfl

theorem canonical169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw169 raw169Labels = mixedMoment B node113 node113Labels := by
  calc
    mixedMoment B raw169 raw169Labels = mixedMoment B raw169step0 raw169step0Labels := by
      have ha : raw169step0 = (fun i j => raw169 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw169step0 raw169; decide +kernel
      have hl : raw169step0Labels = raw169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw169 raw169Labels permutation3 permutation4
    _ = mixedMoment B node113 node113Labels := by rfl

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

theorem canonical22536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22536 raw22536Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw22536 raw22536Labels = mixedMoment B raw22536step0 raw22536step0Labels := by
      have hz : ∀ j, raw22536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22536step0 = (fun i j => raw22536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22536step0 raw22536; decide +kernel
      have hl : raw22536step0Labels = raw22536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22536 raw22536Labels permutation434 hz
    mixedMoment B raw22536step0 raw22536step0Labels = mixedMoment B raw22536step1 raw22536step1Labels := by
      have hz : ∀ j, raw22536step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22536step1 = (fun i j => raw22536step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22536step1 raw22536step0; decide +kernel
      have hl : raw22536step1Labels = raw22536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22536step0 raw22536step0Labels permutation80 hz
    mixedMoment B raw22536step1 raw22536step1Labels = mixedMoment B raw22536step2 raw22536step2Labels := by
      have ha : raw22536step2 = (fun i j => raw22536step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22536step2 raw22536step1; decide +kernel
      have hl : raw22536step2Labels = raw22536step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22536step1 raw22536step1Labels permutation8 permutation6
    _ = mixedMoment B node1419 node1419Labels := by rfl

theorem canonical22537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22537 raw22537Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw22537 raw22537Labels = mixedMoment B raw22537step0 raw22537step0Labels := by
      have hz : ∀ j, raw22537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22537step0 = (fun i j => raw22537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22537step0 raw22537; decide +kernel
      have hl : raw22537step0Labels = raw22537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22537 raw22537Labels permutation434 hz
    mixedMoment B raw22537step0 raw22537step0Labels = mixedMoment B raw22537step1 raw22537step1Labels := by
      have hz : ∀ j, raw22537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22537step1 = (fun i j => raw22537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22537step1 raw22537step0; decide +kernel
      have hl : raw22537step1Labels = raw22537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22537step0 raw22537step0Labels permutation56 hz
    mixedMoment B raw22537step1 raw22537step1Labels = mixedMoment B raw22537step2 raw22537step2Labels := by
      have ha : raw22537step2 = (fun i j => raw22537step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22537step2 raw22537step1; decide +kernel
      have hl : raw22537step2Labels = raw22537step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22537step1 raw22537step1Labels permutation8 permutation6
    _ = mixedMoment B node1419 node1419Labels := by rfl

theorem canonical22538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22538 raw22538Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw22538 raw22538Labels = mixedMoment B raw22538step0 raw22538step0Labels := by
      have hz : ∀ j, raw22538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22538step0 = (fun i j => raw22538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22538step0 raw22538; decide +kernel
      have hl : raw22538step0Labels = raw22538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22538 raw22538Labels permutation346 hz
    mixedMoment B raw22538step0 raw22538step0Labels = mixedMoment B raw22538step1 raw22538step1Labels := by
      have hz : ∀ j, raw22538step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22538step1 = (fun i j => raw22538step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22538step1 raw22538step0; decide +kernel
      have hl : raw22538step1Labels = raw22538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22538step0 raw22538step0Labels permutation56 hz
    mixedMoment B raw22538step1 raw22538step1Labels = mixedMoment B raw22538step2 raw22538step2Labels := by
      have ha : raw22538step2 = (fun i j => raw22538step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22538step2 raw22538step1; decide +kernel
      have hl : raw22538step2Labels = raw22538step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22538step1 raw22538step1Labels permutation8 permutation6
    _ = mixedMoment B node1419 node1419Labels := by rfl

theorem canonical22539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22539 raw22539Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw22539 raw22539Labels = mixedMoment B raw22539step0 raw22539step0Labels := by
      have hz : ∀ j, raw22539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22539step0 = (fun i j => raw22539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22539step0 raw22539; decide +kernel
      have hl : raw22539step0Labels = raw22539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22539 raw22539Labels permutation434 hz
    mixedMoment B raw22539step0 raw22539step0Labels = mixedMoment B raw22539step1 raw22539step1Labels := by
      have hz : ∀ j, raw22539step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22539step1 = (fun i j => raw22539step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22539step1 raw22539step0; decide +kernel
      have hl : raw22539step1Labels = raw22539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22539step0 raw22539step0Labels permutation80 hz
    mixedMoment B raw22539step1 raw22539step1Labels = mixedMoment B raw22539step2 raw22539step2Labels := by
      have hz : ∀ j, raw22539step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22539step2 = (fun i j => raw22539step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22539step2 raw22539step1; decide +kernel
      have hl : raw22539step2Labels = raw22539step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22539step1 raw22539step1Labels permutation14 hz
    mixedMoment B raw22539step2 raw22539step2Labels = mixedMoment B raw22539step3 raw22539step3Labels := by
      have ha : raw22539step3 = (fun i j => raw22539step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22539step3 raw22539step2; decide +kernel
      have hl : raw22539step3Labels = raw22539step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22539step2 raw22539step2Labels permutation2 permutation6
    _ = mixedMoment B node1454 node1454Labels := by rfl

theorem canonical22540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22540 raw22540Labels = mixedMoment B node1455 node1455Labels := by
  calc
    mixedMoment B raw22540 raw22540Labels = mixedMoment B raw22540step0 raw22540step0Labels := by
      have hz : ∀ j, raw22540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22540step0 = (fun i j => raw22540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22540step0 raw22540; decide +kernel
      have hl : raw22540step0Labels = raw22540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22540 raw22540Labels permutation434 hz
    mixedMoment B raw22540step0 raw22540step0Labels = mixedMoment B raw22540step1 raw22540step1Labels := by
      have hz : ∀ j, raw22540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22540step1 = (fun i j => raw22540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22540step1 raw22540step0; decide +kernel
      have hl : raw22540step1Labels = raw22540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22540step0 raw22540step0Labels permutation80 hz
    mixedMoment B raw22540step1 raw22540step1Labels = mixedMoment B raw22540step2 raw22540step2Labels := by
      have hz : ∀ j, raw22540step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22540step2 = (fun i j => raw22540step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22540step2 raw22540step1; decide +kernel
      have hl : raw22540step2Labels = raw22540step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22540step1 raw22540step1Labels permutation14 hz
    mixedMoment B raw22540step2 raw22540step2Labels = mixedMoment B raw22540step3 raw22540step3Labels := by
      have ha : raw22540step3 = (fun i j => raw22540step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22540step3 raw22540step2; decide +kernel
      have hl : raw22540step3Labels = raw22540step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22540step2 raw22540step2Labels permutation2 permutation6
    _ = mixedMoment B node1455 node1455Labels := by rfl

theorem canonical22541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22541 raw22541Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw22541 raw22541Labels = mixedMoment B raw22541step0 raw22541step0Labels := by
      have hz : ∀ j, raw22541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22541step0 = (fun i j => raw22541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22541step0 raw22541; decide +kernel
      have hl : raw22541step0Labels = raw22541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22541 raw22541Labels permutation434 hz
    mixedMoment B raw22541step0 raw22541step0Labels = mixedMoment B raw22541step1 raw22541step1Labels := by
      have hz : ∀ j, raw22541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22541step1 = (fun i j => raw22541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22541step1 raw22541step0; decide +kernel
      have hl : raw22541step1Labels = raw22541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22541step0 raw22541step0Labels permutation80 hz
    mixedMoment B raw22541step1 raw22541step1Labels = mixedMoment B raw22541step2 raw22541step2Labels := by
      have ha : raw22541step2 = (fun i j => raw22541step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22541step2 raw22541step1; decide +kernel
      have hl : raw22541step2Labels = raw22541step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22541step1 raw22541step1Labels permutation8 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical22542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22542 raw22542Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22542 raw22542Labels = mixedMoment B raw22542step0 raw22542step0Labels := by
      have hz : ∀ j, raw22542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22542step0 = (fun i j => raw22542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22542step0 raw22542; decide +kernel
      have hl : raw22542step0Labels = raw22542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22542 raw22542Labels permutation434 hz
    mixedMoment B raw22542step0 raw22542step0Labels = mixedMoment B raw22542step1 raw22542step1Labels := by
      have ha : raw22542step1 = (fun i j => raw22542step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22542step1 raw22542step0; decide +kernel
      have hl : raw22542step1Labels = raw22542step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22542step0 raw22542step0Labels permutation38 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical22543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22543 raw22543Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22543 raw22543Labels = mixedMoment B raw22543step0 raw22543step0Labels := by
      have hz : ∀ j, raw22543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22543step0 = (fun i j => raw22543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22543step0 raw22543; decide +kernel
      have hl : raw22543step0Labels = raw22543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22543 raw22543Labels permutation346 hz
    mixedMoment B raw22543step0 raw22543step0Labels = mixedMoment B raw22543step1 raw22543step1Labels := by
      have ha : raw22543step1 = (fun i j => raw22543step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22543step1 raw22543step0; decide +kernel
      have hl : raw22543step1Labels = raw22543step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22543step0 raw22543step0Labels permutation38 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical22544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22544 raw22544Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22544 raw22544Labels = mixedMoment B raw22544step0 raw22544step0Labels := by
      have hz : ∀ j, raw22544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22544step0 = (fun i j => raw22544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22544step0 raw22544; decide +kernel
      have hl : raw22544step0Labels = raw22544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22544 raw22544Labels permutation434 hz
    mixedMoment B raw22544step0 raw22544step0Labels = mixedMoment B raw22544step1 raw22544step1Labels := by
      have hz : ∀ j, raw22544step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22544step1 = (fun i j => raw22544step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22544step1 raw22544step0; decide +kernel
      have hl : raw22544step1Labels = raw22544step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22544step0 raw22544step0Labels permutation80 hz
    mixedMoment B raw22544step1 raw22544step1Labels = mixedMoment B raw22544step2 raw22544step2Labels := by
      have ha : raw22544step2 = (fun i j => raw22544step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22544step2 raw22544step1; decide +kernel
      have hl : raw22544step2Labels = raw22544step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22544step1 raw22544step1Labels permutation8 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical22545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22545 raw22545Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22545 raw22545Labels = mixedMoment B raw22545step0 raw22545step0Labels := by
      have hz : ∀ j, raw22545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22545step0 = (fun i j => raw22545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22545step0 raw22545; decide +kernel
      have hl : raw22545step0Labels = raw22545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22545 raw22545Labels permutation434 hz
    mixedMoment B raw22545step0 raw22545step0Labels = mixedMoment B raw22545step1 raw22545step1Labels := by
      have hz : ∀ j, raw22545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22545step1 = (fun i j => raw22545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22545step1 raw22545step0; decide +kernel
      have hl : raw22545step1Labels = raw22545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22545step0 raw22545step0Labels permutation80 hz
    mixedMoment B raw22545step1 raw22545step1Labels = mixedMoment B raw22545step2 raw22545step2Labels := by
      have ha : raw22545step2 = (fun i j => raw22545step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22545step2 raw22545step1; decide +kernel
      have hl : raw22545step2Labels = raw22545step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22545step1 raw22545step1Labels permutation8 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

theorem canonical22546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22546 raw22546Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw22546 raw22546Labels = mixedMoment B raw22546step0 raw22546step0Labels := by
      have hz : ∀ j, raw22546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22546step0 = (fun i j => raw22546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22546step0 raw22546; decide +kernel
      have hl : raw22546step0Labels = raw22546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22546 raw22546Labels permutation434 hz
    mixedMoment B raw22546step0 raw22546step0Labels = mixedMoment B raw22546step1 raw22546step1Labels := by
      have hz : ∀ j, raw22546step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22546step1 = (fun i j => raw22546step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22546step1 raw22546step0; decide +kernel
      have hl : raw22546step1Labels = raw22546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22546step0 raw22546step0Labels permutation56 hz
    mixedMoment B raw22546step1 raw22546step1Labels = mixedMoment B raw22546step2 raw22546step2Labels := by
      have ha : raw22546step2 = (fun i j => raw22546step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22546step2 raw22546step1; decide +kernel
      have hl : raw22546step2Labels = raw22546step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22546step1 raw22546step1Labels permutation8 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical22547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22547 raw22547Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22547 raw22547Labels = mixedMoment B raw22547step0 raw22547step0Labels := by
      have hz : ∀ j, raw22547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22547step0 = (fun i j => raw22547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22547step0 raw22547; decide +kernel
      have hl : raw22547step0Labels = raw22547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22547 raw22547Labels permutation434 hz
    mixedMoment B raw22547step0 raw22547step0Labels = mixedMoment B raw22547step1 raw22547step1Labels := by
      have ha : raw22547step1 = (fun i j => raw22547step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22547step1 raw22547step0; decide +kernel
      have hl : raw22547step1Labels = raw22547step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22547step0 raw22547step0Labels permutation32 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical22548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22548 raw22548Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22548 raw22548Labels = mixedMoment B raw22548step0 raw22548step0Labels := by
      have hz : ∀ j, raw22548 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22548step0 = (fun i j => raw22548 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22548step0 raw22548; decide +kernel
      have hl : raw22548step0Labels = raw22548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22548 raw22548Labels permutation265 hz
    mixedMoment B raw22548step0 raw22548step0Labels = mixedMoment B raw22548step1 raw22548step1Labels := by
      have ha : raw22548step1 = (fun i j => raw22548step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22548step1 raw22548step0; decide +kernel
      have hl : raw22548step1Labels = raw22548step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22548step0 raw22548step0Labels permutation38 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical22549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22549 raw22549Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22549 raw22549Labels = mixedMoment B raw22549step0 raw22549step0Labels := by
      have hz : ∀ j, raw22549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22549step0 = (fun i j => raw22549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22549step0 raw22549; decide +kernel
      have hl : raw22549step0Labels = raw22549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22549 raw22549Labels permutation434 hz
    mixedMoment B raw22549step0 raw22549step0Labels = mixedMoment B raw22549step1 raw22549step1Labels := by
      have hz : ∀ j, raw22549step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22549step1 = (fun i j => raw22549step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22549step1 raw22549step0; decide +kernel
      have hl : raw22549step1Labels = raw22549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22549step0 raw22549step0Labels permutation56 hz
    mixedMoment B raw22549step1 raw22549step1Labels = mixedMoment B raw22549step2 raw22549step2Labels := by
      have ha : raw22549step2 = (fun i j => raw22549step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22549step2 raw22549step1; decide +kernel
      have hl : raw22549step2Labels = raw22549step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22549step1 raw22549step1Labels permutation8 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical22550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22550 raw22550Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22550 raw22550Labels = mixedMoment B raw22550step0 raw22550step0Labels := by
      have hz : ∀ j, raw22550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22550step0 = (fun i j => raw22550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22550step0 raw22550; decide +kernel
      have hl : raw22550step0Labels = raw22550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22550 raw22550Labels permutation434 hz
    mixedMoment B raw22550step0 raw22550step0Labels = mixedMoment B raw22550step1 raw22550step1Labels := by
      have hz : ∀ j, raw22550step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22550step1 = (fun i j => raw22550step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22550step1 raw22550step0; decide +kernel
      have hl : raw22550step1Labels = raw22550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22550step0 raw22550step0Labels permutation56 hz
    mixedMoment B raw22550step1 raw22550step1Labels = mixedMoment B raw22550step2 raw22550step2Labels := by
      have ha : raw22550step2 = (fun i j => raw22550step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22550step2 raw22550step1; decide +kernel
      have hl : raw22550step2Labels = raw22550step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22550step1 raw22550step1Labels permutation8 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

theorem canonical22551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22551 raw22551Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw22551 raw22551Labels = mixedMoment B raw22551step0 raw22551step0Labels := by
      have hz : ∀ j, raw22551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22551step0 = (fun i j => raw22551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22551step0 raw22551; decide +kernel
      have hl : raw22551step0Labels = raw22551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22551 raw22551Labels permutation346 hz
    mixedMoment B raw22551step0 raw22551step0Labels = mixedMoment B raw22551step1 raw22551step1Labels := by
      have hz : ∀ j, raw22551step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22551step1 = (fun i j => raw22551step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22551step1 raw22551step0; decide +kernel
      have hl : raw22551step1Labels = raw22551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22551step0 raw22551step0Labels permutation56 hz
    mixedMoment B raw22551step1 raw22551step1Labels = mixedMoment B raw22551step2 raw22551step2Labels := by
      have ha : raw22551step2 = (fun i j => raw22551step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22551step2 raw22551step1; decide +kernel
      have hl : raw22551step2Labels = raw22551step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22551step1 raw22551step1Labels permutation8 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical22552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22552 raw22552Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22552 raw22552Labels = mixedMoment B raw22552step0 raw22552step0Labels := by
      have hz : ∀ j, raw22552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22552step0 = (fun i j => raw22552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22552step0 raw22552; decide +kernel
      have hl : raw22552step0Labels = raw22552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22552 raw22552Labels permutation346 hz
    mixedMoment B raw22552step0 raw22552step0Labels = mixedMoment B raw22552step1 raw22552step1Labels := by
      have ha : raw22552step1 = (fun i j => raw22552step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22552step1 raw22552step0; decide +kernel
      have hl : raw22552step1Labels = raw22552step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22552step0 raw22552step0Labels permutation32 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical22553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22553 raw22553Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22553 raw22553Labels = mixedMoment B raw22553step0 raw22553step0Labels := by
      have hz : ∀ j, raw22553 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22553step0 = (fun i j => raw22553 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22553step0 raw22553; decide +kernel
      have hl : raw22553step0Labels = raw22553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22553 raw22553Labels permutation265 hz
    mixedMoment B raw22553step0 raw22553step0Labels = mixedMoment B raw22553step1 raw22553step1Labels := by
      have ha : raw22553step1 = (fun i j => raw22553step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22553step1 raw22553step0; decide +kernel
      have hl : raw22553step1Labels = raw22553step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22553step0 raw22553step0Labels permutation32 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical22554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22554 raw22554Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22554 raw22554Labels = mixedMoment B raw22554step0 raw22554step0Labels := by
      have hz : ∀ j, raw22554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22554step0 = (fun i j => raw22554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22554step0 raw22554; decide +kernel
      have hl : raw22554step0Labels = raw22554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22554 raw22554Labels permutation346 hz
    mixedMoment B raw22554step0 raw22554step0Labels = mixedMoment B raw22554step1 raw22554step1Labels := by
      have hz : ∀ j, raw22554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22554step1 = (fun i j => raw22554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22554step1 raw22554step0; decide +kernel
      have hl : raw22554step1Labels = raw22554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22554step0 raw22554step0Labels permutation56 hz
    mixedMoment B raw22554step1 raw22554step1Labels = mixedMoment B raw22554step2 raw22554step2Labels := by
      have ha : raw22554step2 = (fun i j => raw22554step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22554step2 raw22554step1; decide +kernel
      have hl : raw22554step2Labels = raw22554step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22554step1 raw22554step1Labels permutation8 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical22555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22555 raw22555Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22555 raw22555Labels = mixedMoment B raw22555step0 raw22555step0Labels := by
      have hz : ∀ j, raw22555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22555step0 = (fun i j => raw22555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22555step0 raw22555; decide +kernel
      have hl : raw22555step0Labels = raw22555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22555 raw22555Labels permutation346 hz
    mixedMoment B raw22555step0 raw22555step0Labels = mixedMoment B raw22555step1 raw22555step1Labels := by
      have hz : ∀ j, raw22555step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22555step1 = (fun i j => raw22555step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22555step1 raw22555step0; decide +kernel
      have hl : raw22555step1Labels = raw22555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22555step0 raw22555step0Labels permutation56 hz
    mixedMoment B raw22555step1 raw22555step1Labels = mixedMoment B raw22555step2 raw22555step2Labels := by
      have ha : raw22555step2 = (fun i j => raw22555step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22555step2 raw22555step1; decide +kernel
      have hl : raw22555step2Labels = raw22555step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22555step1 raw22555step1Labels permutation8 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

theorem canonical22556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22556 raw22556Labels = mixedMoment B node1095 node1095Labels := by
  calc
    mixedMoment B raw22556 raw22556Labels = mixedMoment B raw22556step0 raw22556step0Labels := by
      have hz : ∀ j, raw22556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22556step0 = (fun i j => raw22556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22556step0 raw22556; decide +kernel
      have hl : raw22556step0Labels = raw22556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22556 raw22556Labels permutation434 hz
    mixedMoment B raw22556step0 raw22556step0Labels = mixedMoment B raw22556step1 raw22556step1Labels := by
      have hz : ∀ j, raw22556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22556step1 = (fun i j => raw22556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22556step1 raw22556step0; decide +kernel
      have hl : raw22556step1Labels = raw22556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22556step0 raw22556step0Labels permutation80 hz
    mixedMoment B raw22556step1 raw22556step1Labels = mixedMoment B raw22556step2 raw22556step2Labels := by
      have hz : ∀ j, raw22556step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22556step2 = (fun i j => raw22556step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22556step2 raw22556step1; decide +kernel
      have hl : raw22556step2Labels = raw22556step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22556step1 raw22556step1Labels permutation14 hz
    mixedMoment B raw22556step2 raw22556step2Labels = mixedMoment B raw22556step3 raw22556step3Labels := by
      have ha : raw22556step3 = (fun i j => raw22556step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22556step3 raw22556step2; decide +kernel
      have hl : raw22556step3Labels = raw22556step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22556step2 raw22556step2Labels permutation2 permutation6
    _ = mixedMoment B node1095 node1095Labels := by rfl

theorem canonical22557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22557 raw22557Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22557 raw22557Labels = mixedMoment B raw22557step0 raw22557step0Labels := by
      have hz : ∀ j, raw22557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22557step0 = (fun i j => raw22557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22557step0 raw22557; decide +kernel
      have hl : raw22557step0Labels = raw22557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22557 raw22557Labels permutation434 hz
    mixedMoment B raw22557step0 raw22557step0Labels = mixedMoment B raw22557step1 raw22557step1Labels := by
      have hz : ∀ j, raw22557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22557step1 = (fun i j => raw22557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22557step1 raw22557step0; decide +kernel
      have hl : raw22557step1Labels = raw22557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22557step0 raw22557step0Labels permutation80 hz
    mixedMoment B raw22557step1 raw22557step1Labels = mixedMoment B raw22557step2 raw22557step2Labels := by
      have ha : raw22557step2 = (fun i j => raw22557step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22557step2 raw22557step1; decide +kernel
      have hl : raw22557step2Labels = raw22557step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22557step1 raw22557step1Labels permutation8 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical22558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22558 raw22558Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22558 raw22558Labels = mixedMoment B raw22558step0 raw22558step0Labels := by
      have hz : ∀ j, raw22558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22558step0 = (fun i j => raw22558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22558step0 raw22558; decide +kernel
      have hl : raw22558step0Labels = raw22558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22558 raw22558Labels permutation434 hz
    mixedMoment B raw22558step0 raw22558step0Labels = mixedMoment B raw22558step1 raw22558step1Labels := by
      have hz : ∀ j, raw22558step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22558step1 = (fun i j => raw22558step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22558step1 raw22558step0; decide +kernel
      have hl : raw22558step1Labels = raw22558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22558step0 raw22558step0Labels permutation56 hz
    mixedMoment B raw22558step1 raw22558step1Labels = mixedMoment B raw22558step2 raw22558step2Labels := by
      have ha : raw22558step2 = (fun i j => raw22558step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22558step2 raw22558step1; decide +kernel
      have hl : raw22558step2Labels = raw22558step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22558step1 raw22558step1Labels permutation8 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical22559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22559 raw22559Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22559 raw22559Labels = mixedMoment B raw22559step0 raw22559step0Labels := by
      have hz : ∀ j, raw22559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22559step0 = (fun i j => raw22559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22559step0 raw22559; decide +kernel
      have hl : raw22559step0Labels = raw22559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22559 raw22559Labels permutation346 hz
    mixedMoment B raw22559step0 raw22559step0Labels = mixedMoment B raw22559step1 raw22559step1Labels := by
      have hz : ∀ j, raw22559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22559step1 = (fun i j => raw22559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22559step1 raw22559step0; decide +kernel
      have hl : raw22559step1Labels = raw22559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22559step0 raw22559step0Labels permutation56 hz
    mixedMoment B raw22559step1 raw22559step1Labels = mixedMoment B raw22559step2 raw22559step2Labels := by
      have ha : raw22559step2 = (fun i j => raw22559step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22559step2 raw22559step1; decide +kernel
      have hl : raw22559step2Labels = raw22559step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22559step1 raw22559step1Labels permutation8 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical22560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22560 raw22560Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw22560 raw22560Labels = mixedMoment B raw22560step0 raw22560step0Labels := by
      have hz : ∀ j, raw22560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22560step0 = (fun i j => raw22560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22560step0 raw22560; decide +kernel
      have hl : raw22560step0Labels = raw22560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22560 raw22560Labels permutation434 hz
    mixedMoment B raw22560step0 raw22560step0Labels = mixedMoment B raw22560step1 raw22560step1Labels := by
      have hz : ∀ j, raw22560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22560step1 = (fun i j => raw22560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22560step1 raw22560step0; decide +kernel
      have hl : raw22560step1Labels = raw22560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22560step0 raw22560step0Labels permutation80 hz
    mixedMoment B raw22560step1 raw22560step1Labels = mixedMoment B raw22560step2 raw22560step2Labels := by
      have hz : ∀ j, raw22560step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22560step2 = (fun i j => raw22560step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22560step2 raw22560step1; decide +kernel
      have hl : raw22560step2Labels = raw22560step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22560step1 raw22560step1Labels permutation14 hz
    mixedMoment B raw22560step2 raw22560step2Labels = mixedMoment B raw22560step3 raw22560step3Labels := by
      have ha : raw22560step3 = (fun i j => raw22560step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22560step3 raw22560step2; decide +kernel
      have hl : raw22560step3Labels = raw22560step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22560step2 raw22560step2Labels permutation2 permutation6
    _ = mixedMoment B node1312 node1312Labels := by rfl

theorem canonical22561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22561 raw22561Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw22561 raw22561Labels = mixedMoment B raw22561step0 raw22561step0Labels := by
      have hz : ∀ j, raw22561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22561step0 = (fun i j => raw22561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22561step0 raw22561; decide +kernel
      have hl : raw22561step0Labels = raw22561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22561 raw22561Labels permutation434 hz
    mixedMoment B raw22561step0 raw22561step0Labels = mixedMoment B raw22561step1 raw22561step1Labels := by
      have hz : ∀ j, raw22561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22561step1 = (fun i j => raw22561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22561step1 raw22561step0; decide +kernel
      have hl : raw22561step1Labels = raw22561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22561step0 raw22561step0Labels permutation80 hz
    mixedMoment B raw22561step1 raw22561step1Labels = mixedMoment B raw22561step2 raw22561step2Labels := by
      have hz : ∀ j, raw22561step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22561step2 = (fun i j => raw22561step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22561step2 raw22561step1; decide +kernel
      have hl : raw22561step2Labels = raw22561step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22561step1 raw22561step1Labels permutation14 hz
    mixedMoment B raw22561step2 raw22561step2Labels = mixedMoment B raw22561step3 raw22561step3Labels := by
      have ha : raw22561step3 = (fun i j => raw22561step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22561step3 raw22561step2; decide +kernel
      have hl : raw22561step3Labels = raw22561step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22561step2 raw22561step2Labels permutation2 permutation6
    _ = mixedMoment B node1094 node1094Labels := by rfl

theorem canonical22562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22562 raw22562Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22562 raw22562Labels = mixedMoment B raw22562step0 raw22562step0Labels := by
      have hz : ∀ j, raw22562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22562step0 = (fun i j => raw22562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22562step0 raw22562; decide +kernel
      have hl : raw22562step0Labels = raw22562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22562 raw22562Labels permutation434 hz
    mixedMoment B raw22562step0 raw22562step0Labels = mixedMoment B raw22562step1 raw22562step1Labels := by
      have hz : ∀ j, raw22562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22562step1 = (fun i j => raw22562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22562step1 raw22562step0; decide +kernel
      have hl : raw22562step1Labels = raw22562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22562step0 raw22562step0Labels permutation80 hz
    mixedMoment B raw22562step1 raw22562step1Labels = mixedMoment B raw22562step2 raw22562step2Labels := by
      have ha : raw22562step2 = (fun i j => raw22562step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22562step2 raw22562step1; decide +kernel
      have hl : raw22562step2Labels = raw22562step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22562step1 raw22562step1Labels permutation8 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

theorem canonical22563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22563 raw22563Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22563 raw22563Labels = mixedMoment B raw22563step0 raw22563step0Labels := by
      have hz : ∀ j, raw22563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22563step0 = (fun i j => raw22563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22563step0 raw22563; decide +kernel
      have hl : raw22563step0Labels = raw22563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22563 raw22563Labels permutation434 hz
    mixedMoment B raw22563step0 raw22563step0Labels = mixedMoment B raw22563step1 raw22563step1Labels := by
      have hz : ∀ j, raw22563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22563step1 = (fun i j => raw22563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22563step1 raw22563step0; decide +kernel
      have hl : raw22563step1Labels = raw22563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22563step0 raw22563step0Labels permutation56 hz
    mixedMoment B raw22563step1 raw22563step1Labels = mixedMoment B raw22563step2 raw22563step2Labels := by
      have ha : raw22563step2 = (fun i j => raw22563step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22563step2 raw22563step1; decide +kernel
      have hl : raw22563step2Labels = raw22563step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22563step1 raw22563step1Labels permutation8 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

theorem canonical22564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22564 raw22564Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22564 raw22564Labels = mixedMoment B raw22564step0 raw22564step0Labels := by
      have hz : ∀ j, raw22564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22564step0 = (fun i j => raw22564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22564step0 raw22564; decide +kernel
      have hl : raw22564step0Labels = raw22564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22564 raw22564Labels permutation346 hz
    mixedMoment B raw22564step0 raw22564step0Labels = mixedMoment B raw22564step1 raw22564step1Labels := by
      have hz : ∀ j, raw22564step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22564step1 = (fun i j => raw22564step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22564step1 raw22564step0; decide +kernel
      have hl : raw22564step1Labels = raw22564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22564step0 raw22564step0Labels permutation56 hz
    mixedMoment B raw22564step1 raw22564step1Labels = mixedMoment B raw22564step2 raw22564step2Labels := by
      have ha : raw22564step2 = (fun i j => raw22564step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22564step2 raw22564step1; decide +kernel
      have hl : raw22564step2Labels = raw22564step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22564step1 raw22564step1Labels permutation8 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

theorem canonical22565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22565 raw22565Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw22565 raw22565Labels = mixedMoment B raw22565step0 raw22565step0Labels := by
      have hz : ∀ j, raw22565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22565step0 = (fun i j => raw22565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22565step0 raw22565; decide +kernel
      have hl : raw22565step0Labels = raw22565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22565 raw22565Labels permutation434 hz
    mixedMoment B raw22565step0 raw22565step0Labels = mixedMoment B raw22565step1 raw22565step1Labels := by
      have hz : ∀ j, raw22565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22565step1 = (fun i j => raw22565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22565step1 raw22565step0; decide +kernel
      have hl : raw22565step1Labels = raw22565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22565step0 raw22565step0Labels permutation80 hz
    mixedMoment B raw22565step1 raw22565step1Labels = mixedMoment B raw22565step2 raw22565step2Labels := by
      have hz : ∀ j, raw22565step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22565step2 = (fun i j => raw22565step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22565step2 raw22565step1; decide +kernel
      have hl : raw22565step2Labels = raw22565step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22565step1 raw22565step1Labels permutation14 hz
    mixedMoment B raw22565step2 raw22565step2Labels = mixedMoment B raw22565step3 raw22565step3Labels := by
      have ha : raw22565step3 = (fun i j => raw22565step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22565step3 raw22565step2; decide +kernel
      have hl : raw22565step3Labels = raw22565step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22565step2 raw22565step2Labels permutation2 permutation6
    _ = mixedMoment B node1310 node1310Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7685 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7685 = injectiveMoment H raw7685step0 := by
      have hz : ∀ j, raw7685 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7685step0 = (fun i j => raw7685 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7685 permutation27 hz
    injectiveMoment H raw7685step0 = injectiveMoment H raw7685step1 := by
      have heq : raw7685step1 = (fun i j => raw7685step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7685step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
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

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

theorem canonical909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw909 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw909 = injectiveMoment H raw909step0 := by
      have hz : ∀ j, raw909 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw909step0 = (fun i j => raw909 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw909 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw116 = injectiveMoment H node201 := by
  calc
    injectiveMoment H raw116 = injectiveMoment H raw116step0 := by
      have heq : raw116step0 = (fun i j => raw116 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw116 permutation26 permutation6
    _ = injectiveMoment H node201 := by rfl

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

theorem canonical199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw199 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw199 = injectiveMoment H raw199step0 := by
      have hz : ∀ j, raw199 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw199step0 = (fun i j => raw199 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw199 permutation15 hz
    _ = injectiveMoment H node9 := by rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

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

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5204 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5204 = injectiveMoment H raw5204step0 := by
      have hz : ∀ j, raw5204 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5204step0 = (fun i j => raw5204 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5204 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5547 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5547 = injectiveMoment H node52 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical167 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw167 = injectiveMoment H node153 := by
  calc
    injectiveMoment H raw167 = injectiveMoment H raw167step0 := by
      have heq : raw167step0 = -raw167 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw167).symm
    injectiveMoment H raw167step0 = injectiveMoment H raw167step1 := by
      have heq : raw167step1 = (fun i j => raw167step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw167step0 permutation13 permutation6
    _ = injectiveMoment H node153 := by rfl

theorem canonical179 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw179 = injectiveMoment H node35 := by
  calc
    injectiveMoment H raw179 = injectiveMoment H raw179step0 := by
      have heq : raw179step0 = -raw179 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw179).symm
    injectiveMoment H raw179step0 = injectiveMoment H raw179step1 := by
      have heq : raw179step1 = (fun i j => raw179step0 (permutation3 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw179step0 permutation3 permutation6
    _ = injectiveMoment H node35 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

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

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4048 = injectiveMoment H node31 := by
  calc
    injectiveMoment H raw4048 = injectiveMoment H raw4048step0 := by
      have heq : raw4048step0 = -raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4048).symm
    injectiveMoment H raw4048step0 = injectiveMoment H raw4048step1 := by
      have heq : raw4048step1 = (fun i j => raw4048step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4048step0 permutation8 permutation3
    _ = injectiveMoment H node31 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical4157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4157 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4157 = injectiveMoment H raw4157step0 := by
      have heq : raw4157step0 = raw4157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4157).symm
    injectiveMoment H raw4157step0 = injectiveMoment H raw4157step1 := by
      have heq : raw4157step1 = -raw4157step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4157step0).symm
    injectiveMoment H raw4157step1 = injectiveMoment H raw4157step2 := by
      have heq : raw4157step2 = (fun i j => raw4157step1 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4157step1 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6789 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6789 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw6789 = injectiveMoment H raw6789step0 := by
      have heq : raw6789step0 = -raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6789).symm
    injectiveMoment H raw6789step0 = injectiveMoment H raw6789step1 := by
      have heq : raw6789step1 = (fun i j => raw6789step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6789step0 permutation8 permutation3
    _ = injectiveMoment H node52 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound153 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node153 = Sparse.eval value153 (momentVector H) := by
  have heq : pivotMatrix153 = (fun u v => node153 (pivotPermutation153 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node153 = injectiveMoment H pivotMatrix153 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix153 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix153 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix153 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (0 : Fin 3) = raw5547 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5547 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix153 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix153 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix153 (2 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node153 + (injectiveMoment H (mergeFirst pivotMatrix153 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix153 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix153 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value153, value31, value35, value52, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound201 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node201 = Sparse.eval value201 (momentVector H) := by
  have heq : pivotMatrix201 = (fun u v => node201 (pivotPermutation201 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node201 = injectiveMoment H pivotMatrix201 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix201 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix201 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (0 : Fin 3) = raw6789 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6789 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (1 : Fin 3) = raw4157 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4157 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix201 (2 : Fin 3) = raw4048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4048 hH).trans (sound31 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node201 + (injectiveMoment H (mergeFirst pivotMatrix201 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix201 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value201, value31, value32, value52, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7749 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7749 = injectiveMoment H raw7749step0 := by
      have heq : raw7749step0 = (fun i j => raw7749 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7749 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair98 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node98 node98Labels = Sparse.eval singlePairValue98 (familyPairVector B) := by
  have hp := single_label_three B hB node98
  have hl : node98Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node98 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node98 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node98 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node98 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node98 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value201 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node98 (EqualityPatterns.family3.label 4) = PairSemantics.raw116 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node98 PairSemantics.raw116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical116 hH).trans (PairSemantics.sound201 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue98, PairSemantics.value0, PairSemantics.value9, PairSemantics.value10, PairSemantics.value11, PairSemantics.value201, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical131 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw131 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw131 = injectiveMoment H raw131step0 := by
      have heq : raw131step0 = raw131.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw131).symm
    injectiveMoment H raw131step0 = injectiveMoment H raw131step1 := by
      have heq : raw131step1 = -raw131step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw131step0).symm
    injectiveMoment H raw131step1 = injectiveMoment H raw131step2 := by
      have heq : raw131step2 = (fun i j => raw131step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw131step1 permutation4 permutation6
    _ = injectiveMoment H node32 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node113 node113Labels = Sparse.eval singlePairValue113 (familyPairVector B) := by
  have hp := single_label_three B hB node113
  have hl : node113Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node113 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 1) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node113 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm2 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 2) = PairSemantics.raw7749 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node113 PairSemantics.raw7749; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7749 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node113 PairSemantics.raw214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node113 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value32 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node113 (EqualityPatterns.family3.label 4) = PairSemantics.raw131 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node113 PairSemantics.raw131; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical131 hH).trans (PairSemantics.sound32 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue113, PairSemantics.value0, PairSemantics.value3, PairSemantics.value9, PairSemantics.value11, PairSemantics.value32, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node149 node149Labels = Sparse.eval singlePairValue149 (familyPairVector B) := by
  have hp := single_label_three B hB node149
  have hl : node149Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node149 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 1) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node149 PairSemantics.raw5141
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm2 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node149 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node149 PairSemantics.raw199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node149 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value153 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node149 (EqualityPatterns.family3.label 4) = PairSemantics.raw167 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node149 PairSemantics.raw167
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical167 hH).trans (PairSemantics.sound153 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue149, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value46, PairSemantics.value153, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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

theorem singlePair161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node161 node161Labels = Sparse.eval singlePairValue161 (familyPairVector B) := by
  have hp := single_label_three B hB node161
  have hl : node161Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node161 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node161 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node161 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 3) = PairSemantics.raw214 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node161 PairSemantics.raw214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical214 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node161 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value35 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node161 (EqualityPatterns.family3.label 4) = PairSemantics.raw179 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node161 PairSemantics.raw179
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical179 hH).trans (PairSemantics.sound35 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue161, PairSemantics.value0, PairSemantics.value9, PairSemantics.value11, PairSemantics.value35, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1274 node1274Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node149 node149Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw62 singletonSmall1274
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1274) = raw62Labels := by decide +kernel
  rw [hl, canonical62 B hB] at h
  have hc0 : mixedMoment B raw62 (Fin.cases (0 : Fin 1) singletonSmall1274) =
      mixedMoment B node149 node149Labels := by
    have ha : raw62 = raw63 := by apply Matrix.ext; unfold raw62 raw63; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1274 = raw63Labels := by decide +kernel
    rw [ha, hj, canonical63 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1312 node1312Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node161 node161Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw92 singletonSmall1312
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1312) = raw92Labels := by decide +kernel
  rw [hl, canonical92 B hB] at h
  have hc0 : mixedMoment B raw92 (Fin.cases (0 : Fin 1) singletonSmall1312) =
      mixedMoment B node161 node161Labels := by
    have ha : raw92 = raw93 := by apply Matrix.ext; unfold raw92 raw93; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1312 = raw93Labels := by decide +kernel
    rw [ha, hj, canonical93 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1419 node1419Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node98 node98Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw140 singletonSmall1419
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1419) = raw140Labels := by decide +kernel
  rw [hl, canonical140 B hB] at h
  have hc0 : mixedMoment B raw140 (Fin.cases (0 : Fin 1) singletonSmall1419) =
      mixedMoment B node98 node98Labels := by
    have ha : raw140 = raw141 := by apply Matrix.ext; unfold raw140 raw141; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1419 = raw141Labels := by decide +kernel
    rw [ha, hj, canonical141 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1454 node1454Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node113 node113Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw168 singletonSmall1454
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1454) = raw168Labels := by decide +kernel
  rw [hl, canonical168 B hB] at h
  have hc0 : mixedMoment B raw168 (Fin.cases (0 : Fin 1) singletonSmall1454) =
      mixedMoment B node113 node113Labels := by
    have ha : raw168 = raw169 := by apply Matrix.ext; unfold raw168 raw169; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1454 = raw169Labels := by decide +kernel
    rw [ha, hj, canonical169 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound98 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node98 node98Labels = Sparse.eval nodeValue98 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue98 (familyPairVector B) := singlePair98 B _hB
    _ = _ := by norm_num [singlePairValue98, nodeValue98, Sparse.eval, mixedVector] <;> ring

theorem sound113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node113 node113Labels = Sparse.eval nodeValue113 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue113 (familyPairVector B) := singlePair113 B _hB
    _ = _ := by norm_num [singlePairValue113, nodeValue113, Sparse.eval, mixedVector] <;> ring

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

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1095 node1095Labels = 0 := by
  exact mixedMoment_order_one B hB node1095 node1095Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1094 node1094Labels = Sparse.eval nodeValue1094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1094) = mixedMoment B node1094 node1094Labels := rfl
  simpa [nodeValue1094, Sparse.eval] using hc.symm

theorem sound1095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1095 node1095Labels = Sparse.eval nodeValue1095 (mixedVector B) := by
  simpa only [nodeValue1095, Sparse.eval_nil] using zero1095 B _hB _hF

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

theorem sound149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node149 node149Labels = Sparse.eval nodeValue149 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue149 (familyPairVector B) := singlePair149 B _hB
    _ = _ := by
      norm_num [singlePairValue149, nodeValue149, Sparse.eval, mixedVector]
      ring

theorem sound161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node161 node161Labels = Sparse.eval nodeValue161 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue161 (familyPairVector B) := singlePair161 B _hB
    _ = _ := by
      norm_num [singlePairValue161, nodeValue161, Sparse.eval, mixedVector]
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

theorem sound1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1219 node1219Labels = Sparse.eval nodeValue1219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1219) = mixedMoment B node1219 node1219Labels := rfl
  simpa [nodeValue1219, Sparse.eval] using hc.symm

theorem sound1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1245 node1245Labels = Sparse.eval nodeValue1245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1245) = mixedMoment B node1245 node1245Labels := rfl
  simpa [nodeValue1245, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

theorem sound1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1273 node1273Labels = Sparse.eval nodeValue1273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1273) = mixedMoment B node1273 node1273Labels := rfl
  simpa [nodeValue1273, Sparse.eval] using hc.symm

theorem sound1274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1274 node1274Labels = Sparse.eval nodeValue1274 (mixedVector B) := by
  have h := singleton1274 B _hB
  rw [sound149 B _hB _hF] at h
  norm_num [nodeValue1274, nodeValue149, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1310 node1310Labels = Sparse.eval nodeValue1310 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1310) = mixedMoment B node1310 node1310Labels := rfl
  simpa [nodeValue1310, Sparse.eval] using hc.symm

theorem sound1312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1312 node1312Labels = Sparse.eval nodeValue1312 (mixedVector B) := by
  have h := singleton1312 B _hB
  rw [sound161 B _hB _hF] at h
  norm_num [nodeValue1312, nodeValue161, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1455 node1455Labels = 0 := by
  exact mixedMoment_order_one B hB node1455 node1455Labels 2
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1419 node1419Labels = Sparse.eval nodeValue1419 (mixedVector B) := by
  have h := singleton1419 B _hB
  rw [sound98 B _hB _hF] at h
  norm_num [nodeValue1419, nodeValue98, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1454 node1454Labels = Sparse.eval nodeValue1454 (mixedVector B) := by
  have h := singleton1454 B _hB
  rw [sound113 B _hB _hF] at h
  norm_num [nodeValue1454, nodeValue113, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1455 node1455Labels = Sparse.eval nodeValue1455 (mixedVector B) := by
  simpa only [nodeValue1455, Sparse.eval_nil] using zero1455 B _hB _hF

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

theorem sourceEq1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1476 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 1) (sourceB1476 + difference 1 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 1) (sourceB1476 + difference 1 0) sourceC1476) = raw22536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22536; decide +kernel
    rw [ha]
    exact (canonical22536 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 2) (sourceB1476 + difference 2 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 2) (sourceB1476 + difference 2 0) sourceC1476) = raw22537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22537; decide +kernel
    rw [ha]
    exact (canonical22537 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 3) (sourceB1476 + difference 3 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 3) (sourceB1476 + difference 3 0) sourceC1476) = raw22538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22538; decide +kernel
    rw [ha]
    exact (canonical22538 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 4) (sourceB1476 + difference 4 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1454) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 4) (sourceB1476 + difference 4 0) sourceC1476) = raw22539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22539; decide +kernel
    rw [ha]
    exact (canonical22539 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1476 + difference 0 5) (sourceB1476 + difference 5 0) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1476 + difference 0 5) (sourceB1476 + difference 5 0) sourceC1476) = raw22540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22540; decide +kernel
    rw [ha]
    exact (canonical22540 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 0) (sourceB1476 + difference 0 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 0) (sourceB1476 + difference 0 1) sourceC1476) = raw22541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22541; decide +kernel
    rw [ha]
    exact (canonical22541 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 2) (sourceB1476 + difference 2 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 2) (sourceB1476 + difference 2 1) sourceC1476) = raw22542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22542; decide +kernel
    rw [ha]
    exact (canonical22542 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 3) (sourceB1476 + difference 3 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 3) (sourceB1476 + difference 3 1) sourceC1476) = raw22543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22543; decide +kernel
    rw [ha]
    exact (canonical22543 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 4) (sourceB1476 + difference 4 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 4) (sourceB1476 + difference 4 1) sourceC1476) = raw22544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22544; decide +kernel
    rw [ha]
    exact (canonical22544 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1476 + difference 1 5) (sourceB1476 + difference 5 1) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1476 + difference 1 5) (sourceB1476 + difference 5 1) sourceC1476) = raw22545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22545; decide +kernel
    rw [ha]
    exact (canonical22545 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 0) (sourceB1476 + difference 0 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 0) (sourceB1476 + difference 0 2) sourceC1476) = raw22546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22546; decide +kernel
    rw [ha]
    exact (canonical22546 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 1) (sourceB1476 + difference 1 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 1) (sourceB1476 + difference 1 2) sourceC1476) = raw22547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22547; decide +kernel
    rw [ha]
    exact (canonical22547 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 3) (sourceB1476 + difference 3 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 3) (sourceB1476 + difference 3 2) sourceC1476) = raw22548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22548; decide +kernel
    rw [ha]
    exact (canonical22548 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 4) (sourceB1476 + difference 4 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 4) (sourceB1476 + difference 4 2) sourceC1476) = raw22549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22549; decide +kernel
    rw [ha]
    exact (canonical22549 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1476 + difference 2 5) (sourceB1476 + difference 5 2) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1476 + difference 2 5) (sourceB1476 + difference 5 2) sourceC1476) = raw22550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22550; decide +kernel
    rw [ha]
    exact (canonical22550 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 0) (sourceB1476 + difference 0 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 0) (sourceB1476 + difference 0 3) sourceC1476) = raw22551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22551; decide +kernel
    rw [ha]
    exact (canonical22551 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 1) (sourceB1476 + difference 1 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 1) (sourceB1476 + difference 1 3) sourceC1476) = raw22552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22552; decide +kernel
    rw [ha]
    exact (canonical22552 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 2) (sourceB1476 + difference 2 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 2) (sourceB1476 + difference 2 3) sourceC1476) = raw22553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22553; decide +kernel
    rw [ha]
    exact (canonical22553 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 4) (sourceB1476 + difference 4 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 4) (sourceB1476 + difference 4 3) sourceC1476) = raw22554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22554; decide +kernel
    rw [ha]
    exact (canonical22554 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1476 + difference 3 5) (sourceB1476 + difference 5 3) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1476 + difference 3 5) (sourceB1476 + difference 5 3) sourceC1476) = raw22555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22555; decide +kernel
    rw [ha]
    exact (canonical22555 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 0) (sourceB1476 + difference 0 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 0) (sourceB1476 + difference 0 4) sourceC1476) = raw22556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22556; decide +kernel
    rw [ha]
    exact (canonical22556 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 1) (sourceB1476 + difference 1 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 1) (sourceB1476 + difference 1 4) sourceC1476) = raw22557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22557; decide +kernel
    rw [ha]
    exact (canonical22557 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 2) (sourceB1476 + difference 2 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 2) (sourceB1476 + difference 2 4) sourceC1476) = raw22558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22558; decide +kernel
    rw [ha]
    exact (canonical22558 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 3) (sourceB1476 + difference 3 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 3) (sourceB1476 + difference 3 4) sourceC1476) = raw22559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22559; decide +kernel
    rw [ha]
    exact (canonical22559 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1476 + difference 4 5) (sourceB1476 + difference 5 4) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA1476 + difference 4 5) (sourceB1476 + difference 5 4) sourceC1476) = raw22560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22560; decide +kernel
    rw [ha]
    exact (canonical22560 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 0) (sourceB1476 + difference 0 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 0) (sourceB1476 + difference 0 5) sourceC1476) = raw22561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22561; decide +kernel
    rw [ha]
    exact (canonical22561 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 1) (sourceB1476 + difference 1 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 1) (sourceB1476 + difference 1 5) sourceC1476) = raw22562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22562; decide +kernel
    rw [ha]
    exact (canonical22562 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 2) (sourceB1476 + difference 2 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 2) (sourceB1476 + difference 2 5) sourceC1476) = raw22563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22563; decide +kernel
    rw [ha]
    exact (canonical22563 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 3) (sourceB1476 + difference 3 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 3) (sourceB1476 + difference 3 5) sourceC1476) = raw22564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22564; decide +kernel
    rw [ha]
    exact (canonical22564 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1476 + difference 5 4) (sourceB1476 + difference 4 5) sourceC1476) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA1476 + difference 5 4) (sourceB1476 + difference 4 5) sourceC1476) = raw22565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1476 sourceB1476 sourceC1476 difference raw22565; decide +kernel
    rw [ha]
    exact (canonical22565 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1476 sourceB1476 sourceC1476
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1476, Integer.Sparse.eval]
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

theorem reindexCheck1264 : Integer.Sparse.reindex keyMap MixedData.row1264 = numericRow1264 := by decide +kernel

theorem numericCheck1264 (x : Master → ℝ) : Integer.Sparse.eval numericRow1264 x =
    (18 : ℝ) * reducedSource1264 x := by
  norm_num [numericRow1264, reducedSource1264, Integer.Sparse.eval, Sparse.eval, nodeValue1049, nodeValue1094, nodeValue1095, nodeValue1219, nodeValue1245, nodeValue1246, nodeValue1273, nodeValue1274, nodeValue1310, nodeValue1312, nodeValue1419, nodeValue1454, nodeValue1455] <;> ring

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

theorem reducedZero1264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1264 (mixedVector B) = 0 := by
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h1095 : mixedVector B (Sum.inr 1095) = Sparse.eval nodeValue1095 (mixedVector B) := by
    change mixedMoment B node1095 node1095Labels = _
    exact sound1095 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1274 : mixedVector B (Sum.inr 1274) = Sparse.eval nodeValue1274 (mixedVector B) := by
    change mixedMoment B node1274 node1274Labels = _
    exact sound1274 B hB hF
  have h1310 : mixedVector B (Sum.inr 1310) = Sparse.eval nodeValue1310 (mixedVector B) := by
    change mixedMoment B node1310 node1310Labels = _
    exact sound1310 B hB hF
  have h1312 : mixedVector B (Sum.inr 1312) = Sparse.eval nodeValue1312 (mixedVector B) := by
    change mixedMoment B node1312 node1312Labels = _
    exact sound1312 B hB hF
  have h1419 : mixedVector B (Sum.inr 1419) = Sparse.eval nodeValue1419 (mixedVector B) := by
    change mixedMoment B node1419 node1419Labels = _
    exact sound1419 B hB hF
  have h1454 : mixedVector B (Sum.inr 1454) = Sparse.eval nodeValue1454 (mixedVector B) := by
    change mixedMoment B node1454 node1454Labels = _
    exact sound1454 B hB hF
  have h1455 : mixedVector B (Sum.inr 1455) = Sparse.eval nodeValue1455 (mixedVector B) := by
    change mixedMoment B node1455 node1455Labels = _
    exact sound1455 B hB hF
  simpa only [sourceForm1476, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1049, h1094, h1095, h1219, h1245, h1246, h1273, h1274, h1310, h1312, h1419, h1454, h1455, reducedSource1264] using sourceEq1476 B hB

theorem rowSound1264_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1264 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1264, numericCheck1264, reducedZero1264 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e_oai
