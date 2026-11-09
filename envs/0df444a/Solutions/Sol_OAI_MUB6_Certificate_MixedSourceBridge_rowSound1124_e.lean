-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T19:55:04.847779+00:00
-- url     : https://prove2.me/submissions/7c4e4ad3-df8d-40e8-b52b-d76b248c33cc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1170_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2941_e

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

theorem canonical38 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38 raw38Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw38 raw38Labels = mixedMoment B raw38step0 raw38step0Labels := by
      have ha : raw38step0 = (fun i j => raw38 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38step0 raw38; decide +kernel
      have hl : raw38step0Labels = raw38Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38 raw38Labels permutation8 permutation5
    mixedMoment B raw38step0 raw38step0Labels = mixedMoment B raw38step1 raw38step1Labels := by
      have ha : raw38step1 = raw38step0 := by apply Matrix.ext; unfold raw38step1 raw38step0; decide +kernel
      have hl : raw38step0Labels = labelEmbedding1 ∘ raw38step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38step0 raw38step0Labels raw38step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1173 node1173Labels := by rfl

theorem canonical39 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39 raw39Labels = mixedMoment B node70 node70Labels := by
  calc
    mixedMoment B raw39 raw39Labels = mixedMoment B raw39step0 raw39step0Labels := by
      have ha : raw39step0 = (fun i j => raw39 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39step0 raw39; decide +kernel
      have hl : raw39step0Labels = raw39Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39 raw39Labels permutation31 permutation4
    mixedMoment B raw39step0 raw39step0Labels = mixedMoment B raw39step1 raw39step1Labels := by
      have ha : raw39step1 = -raw39step0 := by apply Matrix.ext; change ∀ i j, raw39step1 i j = -(raw39step0 i j); unfold raw39step1 raw39step0; decide +kernel
      have hl : raw39step1Labels = raw39step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node70 node70Labels := by rfl

theorem canonical44 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw44 raw44Labels = mixedMoment B node1177 node1177Labels := by
  calc
    mixedMoment B raw44 raw44Labels = mixedMoment B raw44step0 raw44step0Labels := by
      have ha : raw44step0 = (fun i j => raw44 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw44step0 raw44; decide +kernel
      have hl : raw44step0Labels = raw44Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw44 raw44Labels permutation8 permutation5
    mixedMoment B raw44step0 raw44step0Labels = mixedMoment B raw44step1 raw44step1Labels := by
      have ha : raw44step1 = raw44step0 := by apply Matrix.ext; unfold raw44step1 raw44step0; decide +kernel
      have hl : raw44step0Labels = labelEmbedding1 ∘ raw44step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw44step0 raw44step0Labels raw44step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1177 node1177Labels := by rfl

theorem canonical45 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw45 raw45Labels = mixedMoment B node131 node131Labels := by
  calc
    mixedMoment B raw45 raw45Labels = mixedMoment B raw45step0 raw45step0Labels := by
      have ha : raw45step0 = (fun i j => raw45 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw45step0 raw45; decide +kernel
      have hl : raw45step0Labels = raw45Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw45 raw45Labels permutation8 permutation4
    _ = mixedMoment B node131 node131Labels := by rfl

theorem canonical60 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw60 raw60Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw60 raw60Labels = mixedMoment B raw60step0 raw60step0Labels := by
      have ha : raw60step0 = (fun i j => raw60 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw60step0 raw60; decide +kernel
      have hl : raw60step0Labels = raw60Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw60 raw60Labels permutation8 permutation5
    mixedMoment B raw60step0 raw60step0Labels = mixedMoment B raw60step1 raw60step1Labels := by
      have ha : raw60step1 = raw60step0 := by apply Matrix.ext; unfold raw60step1 raw60step0; decide +kernel
      have hl : raw60step0Labels = labelEmbedding1 ∘ raw60step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw60step0 raw60step0Labels raw60step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical61 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw61 raw61Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw61 raw61Labels = mixedMoment B raw61step0 raw61step0Labels := by
      have ha : raw61step0 = (fun i j => raw61 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw61step0 raw61; decide +kernel
      have hl : raw61step0Labels = raw61Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw61 raw61Labels permutation8 permutation4
    _ = mixedMoment B node143 node143Labels := by rfl

theorem canonical64 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw64 raw64Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw64 raw64Labels = mixedMoment B raw64step0 raw64step0Labels := by
      have ha : raw64step0 = (fun i j => raw64 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw64step0 raw64; decide +kernel
      have hl : raw64step0Labels = raw64Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw64 raw64Labels permutation2 permutation5
    mixedMoment B raw64step0 raw64step0Labels = mixedMoment B raw64step1 raw64step1Labels := by
      have ha : raw64step1 = raw64step0 := by apply Matrix.ext; unfold raw64step1 raw64step0; decide +kernel
      have hl : raw64step0Labels = labelEmbedding1 ∘ raw64step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw64step0 raw64step0Labels raw64step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1275 node1275Labels := by rfl

theorem canonical65 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw65 raw65Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw65 raw65Labels = mixedMoment B raw65step0 raw65step0Labels := by
      have ha : raw65step0 = (fun i j => raw65 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw65step0 raw65; decide +kernel
      have hl : raw65step0Labels = raw65Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw65 raw65Labels permutation7 permutation4
    mixedMoment B raw65step0 raw65step0Labels = mixedMoment B raw65step1 raw65step1Labels := by
      have ha : raw65step1 = -raw65step0 := by apply Matrix.ext; change ∀ i j, raw65step1 i j = -(raw65step0 i j); unfold raw65step1 raw65step0; decide +kernel
      have hl : raw65step1Labels = raw65step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node100 node100Labels := by rfl

theorem canonical88 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw88 raw88Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw88 raw88Labels = mixedMoment B raw88step0 raw88step0Labels := by
      have ha : raw88step0 = (fun i j => raw88 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw88step0 raw88; decide +kernel
      have hl : raw88step0Labels = raw88Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw88 raw88Labels permutation2 permutation5
    mixedMoment B raw88step0 raw88step0Labels = mixedMoment B raw88step1 raw88step1Labels := by
      have ha : raw88step1 = raw88step0 := by apply Matrix.ext; unfold raw88step1 raw88step0; decide +kernel
      have hl : raw88step0Labels = labelEmbedding1 ∘ raw88step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw88step0 raw88step0Labels raw88step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1308 node1308Labels := by rfl

theorem canonical89 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw89 raw89Labels = mixedMoment B node154 node154Labels := by
  calc
    mixedMoment B raw89 raw89Labels = mixedMoment B raw89step0 raw89step0Labels := by
      have ha : raw89step0 = (fun i j => raw89 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw89step0 raw89; decide +kernel
      have hl : raw89step0Labels = raw89Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw89 raw89Labels permutation2 permutation4
    _ = mixedMoment B node154 node154Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20866 raw20866Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw20866 raw20866Labels = mixedMoment B raw20866step0 raw20866step0Labels := by
      have hz : ∀ j, raw20866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20866step0 = (fun i j => raw20866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20866step0 raw20866; decide +kernel
      have hl : raw20866step0Labels = raw20866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20866 raw20866Labels permutation346 hz
    mixedMoment B raw20866step0 raw20866step0Labels = mixedMoment B raw20866step1 raw20866step1Labels := by
      have hz : ∀ j, raw20866step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20866step1 = (fun i j => raw20866step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20866step1 raw20866step0; decide +kernel
      have hl : raw20866step1Labels = raw20866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20866step0 raw20866step0Labels permutation56 hz
    mixedMoment B raw20866step1 raw20866step1Labels = mixedMoment B raw20866step2 raw20866step2Labels := by
      have ha : raw20866step2 = (fun i j => raw20866step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20866step2 raw20866step1; decide +kernel
      have hl : raw20866step2Labels = raw20866step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20866step1 raw20866step1Labels permutation8 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

theorem canonical20867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20867 raw20867Labels = mixedMoment B node585 node585Labels := by
  calc
    mixedMoment B raw20867 raw20867Labels = mixedMoment B raw20867step0 raw20867step0Labels := by
      have hz : ∀ j, raw20867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20867step0 = (fun i j => raw20867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20867step0 raw20867; decide +kernel
      have hl : raw20867step0Labels = raw20867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20867 raw20867Labels permutation346 hz
    mixedMoment B raw20867step0 raw20867step0Labels = mixedMoment B raw20867step1 raw20867step1Labels := by
      have ha : raw20867step1 = (fun i j => raw20867step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20867step1 raw20867step0; decide +kernel
      have hl : raw20867step1Labels = raw20867step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20867step0 raw20867step0Labels permutation38 permutation3
    _ = mixedMoment B node585 node585Labels := by rfl

theorem canonical20868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20868 raw20868Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw20868 raw20868Labels = mixedMoment B raw20868step0 raw20868step0Labels := by
      have ha : raw20868step0 = (fun i j => raw20868 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20868step0 raw20868; decide +kernel
      have hl : raw20868step0Labels = raw20868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20868 raw20868Labels permutation182 permutation3
    _ = mixedMoment B node1116 node1116Labels := by rfl

theorem canonical20869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20869 raw20869Labels = mixedMoment B node1170 node1170Labels := by
  calc
    mixedMoment B raw20869 raw20869Labels = mixedMoment B raw20869step0 raw20869step0Labels := by
      have hz : ∀ j, raw20869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20869step0 = (fun i j => raw20869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20869step0 raw20869; decide +kernel
      have hl : raw20869step0Labels = raw20869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20869 raw20869Labels permutation346 hz
    mixedMoment B raw20869step0 raw20869step0Labels = mixedMoment B raw20869step1 raw20869step1Labels := by
      have ha : raw20869step1 = (fun i j => raw20869step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20869step1 raw20869step0; decide +kernel
      have hl : raw20869step1Labels = raw20869step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20869step0 raw20869step0Labels permutation38 permutation3
    _ = mixedMoment B node1170 node1170Labels := by rfl

theorem canonical20870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20870 raw20870Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20870 raw20870Labels = mixedMoment B raw20870step0 raw20870step0Labels := by
      have hz : ∀ j, raw20870 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20870step0 = (fun i j => raw20870 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20870step0 raw20870; decide +kernel
      have hl : raw20870step0Labels = raw20870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20870 raw20870Labels permutation520 hz
    mixedMoment B raw20870step0 raw20870step0Labels = mixedMoment B raw20870step1 raw20870step1Labels := by
      have hz : ∀ j, raw20870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20870step1 = (fun i j => raw20870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20870step1 raw20870step0; decide +kernel
      have hl : raw20870step1Labels = raw20870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20870step0 raw20870step0Labels permutation80 hz
    mixedMoment B raw20870step1 raw20870step1Labels = mixedMoment B raw20870step2 raw20870step2Labels := by
      have ha : raw20870step2 = (fun i j => raw20870step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20870step2 raw20870step1; decide +kernel
      have hl : raw20870step2Labels = raw20870step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20870step1 raw20870step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical20871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20871 raw20871Labels = mixedMoment B node585 node585Labels := by
  calc
    mixedMoment B raw20871 raw20871Labels = mixedMoment B raw20871step0 raw20871step0Labels := by
      have hz : ∀ j, raw20871 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20871step0 = (fun i j => raw20871 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20871step0 raw20871; decide +kernel
      have hl : raw20871step0Labels = raw20871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20871 raw20871Labels permutation265 hz
    mixedMoment B raw20871step0 raw20871step0Labels = mixedMoment B raw20871step1 raw20871step1Labels := by
      have ha : raw20871step1 = (fun i j => raw20871step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20871step1 raw20871step0; decide +kernel
      have hl : raw20871step1Labels = raw20871step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20871step0 raw20871step0Labels permutation38 permutation3
    _ = mixedMoment B node585 node585Labels := by rfl

theorem canonical20872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20872 raw20872Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw20872 raw20872Labels = mixedMoment B raw20872step0 raw20872step0Labels := by
      have ha : raw20872step0 = (fun i j => raw20872 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20872step0 raw20872; decide +kernel
      have hl : raw20872step0Labels = raw20872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20872 raw20872Labels permutation158 permutation3
    _ = mixedMoment B node1116 node1116Labels := by rfl

theorem canonical20873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20873 raw20873Labels = mixedMoment B node1170 node1170Labels := by
  calc
    mixedMoment B raw20873 raw20873Labels = mixedMoment B raw20873step0 raw20873step0Labels := by
      have hz : ∀ j, raw20873 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20873step0 = (fun i j => raw20873 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20873step0 raw20873; decide +kernel
      have hl : raw20873step0Labels = raw20873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20873 raw20873Labels permutation265 hz
    mixedMoment B raw20873step0 raw20873step0Labels = mixedMoment B raw20873step1 raw20873step1Labels := by
      have ha : raw20873step1 = (fun i j => raw20873step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20873step1 raw20873step0; decide +kernel
      have hl : raw20873step1Labels = raw20873step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20873step0 raw20873step0Labels permutation38 permutation3
    _ = mixedMoment B node1170 node1170Labels := by rfl

theorem canonical20874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20874 raw20874Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20874 raw20874Labels = mixedMoment B raw20874step0 raw20874step0Labels := by
      have hz : ∀ j, raw20874 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20874step0 = (fun i j => raw20874 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20874step0 raw20874; decide +kernel
      have hl : raw20874step0Labels = raw20874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20874 raw20874Labels permutation520 hz
    mixedMoment B raw20874step0 raw20874step0Labels = mixedMoment B raw20874step1 raw20874step1Labels := by
      have hz : ∀ j, raw20874step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20874step1 = (fun i j => raw20874step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20874step1 raw20874step0; decide +kernel
      have hl : raw20874step1Labels = raw20874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20874step0 raw20874step0Labels permutation56 hz
    mixedMoment B raw20874step1 raw20874step1Labels = mixedMoment B raw20874step2 raw20874step2Labels := by
      have ha : raw20874step2 = (fun i j => raw20874step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20874step2 raw20874step1; decide +kernel
      have hl : raw20874step2Labels = raw20874step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20874step1 raw20874step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

theorem canonical20875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20875 raw20875Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw20875 raw20875Labels = mixedMoment B raw20875step0 raw20875step0Labels := by
      have hz : ∀ j, raw20875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20875step0 = (fun i j => raw20875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20875step0 raw20875; decide +kernel
      have hl : raw20875step0Labels = raw20875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20875 raw20875Labels permutation346 hz
    mixedMoment B raw20875step0 raw20875step0Labels = mixedMoment B raw20875step1 raw20875step1Labels := by
      have hz : ∀ j, raw20875step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20875step1 = (fun i j => raw20875step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20875step1 raw20875step0; decide +kernel
      have hl : raw20875step1Labels = raw20875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20875step0 raw20875step0Labels permutation56 hz
    mixedMoment B raw20875step1 raw20875step1Labels = mixedMoment B raw20875step2 raw20875step2Labels := by
      have ha : raw20875step2 = (fun i j => raw20875step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20875step2 raw20875step1; decide +kernel
      have hl : raw20875step2Labels = raw20875step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20875step1 raw20875step1Labels permutation10 permutation3
    _ = mixedMoment B node612 node612Labels := by rfl

theorem canonical20876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20876 raw20876Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20876 raw20876Labels = mixedMoment B raw20876step0 raw20876step0Labels := by
      have hz : ∀ j, raw20876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20876step0 = (fun i j => raw20876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20876step0 raw20876; decide +kernel
      have hl : raw20876step0Labels = raw20876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20876 raw20876Labels permutation346 hz
    mixedMoment B raw20876step0 raw20876step0Labels = mixedMoment B raw20876step1 raw20876step1Labels := by
      have ha : raw20876step1 = (fun i j => raw20876step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20876step1 raw20876step0; decide +kernel
      have hl : raw20876step1Labels = raw20876step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20876step0 raw20876step0Labels permutation34 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

theorem canonical20877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20877 raw20877Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20877 raw20877Labels = mixedMoment B raw20877step0 raw20877step0Labels := by
      have hz : ∀ j, raw20877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20877step0 = (fun i j => raw20877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20877step0 raw20877; decide +kernel
      have hl : raw20877step0Labels = raw20877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20877 raw20877Labels permutation265 hz
    mixedMoment B raw20877step0 raw20877step0Labels = mixedMoment B raw20877step1 raw20877step1Labels := by
      have ha : raw20877step1 = (fun i j => raw20877step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20877step1 raw20877step0; decide +kernel
      have hl : raw20877step1Labels = raw20877step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20877step0 raw20877step0Labels permutation34 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

theorem canonical20878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20878 raw20878Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw20878 raw20878Labels = mixedMoment B raw20878step0 raw20878step0Labels := by
      have hz : ∀ j, raw20878 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20878step0 = (fun i j => raw20878 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20878step0 raw20878; decide +kernel
      have hl : raw20878step0Labels = raw20878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20878 raw20878Labels permutation520 hz
    mixedMoment B raw20878step0 raw20878step0Labels = mixedMoment B raw20878step1 raw20878step1Labels := by
      have hz : ∀ j, raw20878step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20878step1 = (fun i j => raw20878step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20878step1 raw20878step0; decide +kernel
      have hl : raw20878step1Labels = raw20878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20878step0 raw20878step0Labels permutation80 hz
    mixedMoment B raw20878step1 raw20878step1Labels = mixedMoment B raw20878step2 raw20878step2Labels := by
      have hz : ∀ j, raw20878step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20878step2 = (fun i j => raw20878step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20878step2 raw20878step1; decide +kernel
      have hl : raw20878step2Labels = raw20878step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20878step1 raw20878step1Labels permutation14 hz
    mixedMoment B raw20878step2 raw20878step2Labels = mixedMoment B raw20878step3 raw20878step3Labels := by
      have ha : raw20878step3 = (fun i j => raw20878step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20878step3 raw20878step2; decide +kernel
      have hl : raw20878step3Labels = raw20878step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20878step2 raw20878step2Labels permutation2 permutation3
    _ = mixedMoment B node1308 node1308Labels := by rfl

theorem canonical20879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20879 raw20879Labels = mixedMoment B node590 node590Labels := by
  calc
    mixedMoment B raw20879 raw20879Labels = mixedMoment B raw20879step0 raw20879step0Labels := by
      have hz : ∀ j, raw20879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20879step0 = (fun i j => raw20879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20879step0 raw20879; decide +kernel
      have hl : raw20879step0Labels = raw20879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20879 raw20879Labels permutation346 hz
    mixedMoment B raw20879step0 raw20879step0Labels = mixedMoment B raw20879step1 raw20879step1Labels := by
      have hz : ∀ j, raw20879step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20879step1 = (fun i j => raw20879step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20879step1 raw20879step0; decide +kernel
      have hl : raw20879step1Labels = raw20879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20879step0 raw20879step0Labels permutation56 hz
    mixedMoment B raw20879step1 raw20879step1Labels = mixedMoment B raw20879step2 raw20879step2Labels := by
      have ha : raw20879step2 = (fun i j => raw20879step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20879step2 raw20879step1; decide +kernel
      have hl : raw20879step2Labels = raw20879step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20879step1 raw20879step1Labels permutation8 permutation3
    _ = mixedMoment B node590 node590Labels := by rfl

theorem canonical20880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20880 raw20880Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw20880 raw20880Labels = mixedMoment B raw20880step0 raw20880step0Labels := by
      have hz : ∀ j, raw20880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20880step0 = (fun i j => raw20880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20880step0 raw20880; decide +kernel
      have hl : raw20880step0Labels = raw20880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20880 raw20880Labels permutation346 hz
    mixedMoment B raw20880step0 raw20880step0Labels = mixedMoment B raw20880step1 raw20880step1Labels := by
      have ha : raw20880step1 = (fun i j => raw20880step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20880step1 raw20880step0; decide +kernel
      have hl : raw20880step1Labels = raw20880step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20880step0 raw20880step0Labels permutation32 permutation3
    _ = mixedMoment B node1121 node1121Labels := by rfl

theorem canonical20881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20881 raw20881Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw20881 raw20881Labels = mixedMoment B raw20881step0 raw20881step0Labels := by
      have hz : ∀ j, raw20881 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20881step0 = (fun i j => raw20881 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20881step0 raw20881; decide +kernel
      have hl : raw20881step0Labels = raw20881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20881 raw20881Labels permutation265 hz
    mixedMoment B raw20881step0 raw20881step0Labels = mixedMoment B raw20881step1 raw20881step1Labels := by
      have ha : raw20881step1 = (fun i j => raw20881step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20881step1 raw20881step0; decide +kernel
      have hl : raw20881step1Labels = raw20881step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20881step0 raw20881step0Labels permutation32 permutation3
    _ = mixedMoment B node1121 node1121Labels := by rfl

theorem canonical20882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20882 raw20882Labels = mixedMoment B node1177 node1177Labels := by
  calc
    mixedMoment B raw20882 raw20882Labels = mixedMoment B raw20882step0 raw20882step0Labels := by
      have hz : ∀ j, raw20882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20882step0 = (fun i j => raw20882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20882step0 raw20882; decide +kernel
      have hl : raw20882step0Labels = raw20882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20882 raw20882Labels permutation346 hz
    mixedMoment B raw20882step0 raw20882step0Labels = mixedMoment B raw20882step1 raw20882step1Labels := by
      have hz : ∀ j, raw20882step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20882step1 = (fun i j => raw20882step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20882step1 raw20882step0; decide +kernel
      have hl : raw20882step1Labels = raw20882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20882step0 raw20882step0Labels permutation56 hz
    mixedMoment B raw20882step1 raw20882step1Labels = mixedMoment B raw20882step2 raw20882step2Labels := by
      have ha : raw20882step2 = (fun i j => raw20882step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20882step2 raw20882step1; decide +kernel
      have hl : raw20882step2Labels = raw20882step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20882step1 raw20882step1Labels permutation8 permutation3
    _ = mixedMoment B node1177 node1177Labels := by rfl

theorem canonical20883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20883 raw20883Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw20883 raw20883Labels = mixedMoment B raw20883step0 raw20883step0Labels := by
      have hz : ∀ j, raw20883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20883step0 = (fun i j => raw20883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20883step0 raw20883; decide +kernel
      have hl : raw20883step0Labels = raw20883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20883 raw20883Labels permutation346 hz
    mixedMoment B raw20883step0 raw20883step0Labels = mixedMoment B raw20883step1 raw20883step1Labels := by
      have hz : ∀ j, raw20883step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20883step1 = (fun i j => raw20883step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20883step1 raw20883step0; decide +kernel
      have hl : raw20883step1Labels = raw20883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20883step0 raw20883step0Labels permutation56 hz
    mixedMoment B raw20883step1 raw20883step1Labels = mixedMoment B raw20883step2 raw20883step2Labels := by
      have ha : raw20883step2 = (fun i j => raw20883step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20883step2 raw20883step1; decide +kernel
      have hl : raw20883step2Labels = raw20883step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20883step1 raw20883step1Labels permutation8 permutation3
    _ = mixedMoment B node587 node587Labels := by rfl

theorem canonical20884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20884 raw20884Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw20884 raw20884Labels = mixedMoment B raw20884step0 raw20884step0Labels := by
      have hz : ∀ j, raw20884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20884step0 = (fun i j => raw20884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20884step0 raw20884; decide +kernel
      have hl : raw20884step0Labels = raw20884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20884 raw20884Labels permutation346 hz
    mixedMoment B raw20884step0 raw20884step0Labels = mixedMoment B raw20884step1 raw20884step1Labels := by
      have ha : raw20884step1 = (fun i j => raw20884step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20884step1 raw20884step0; decide +kernel
      have hl : raw20884step1Labels = raw20884step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20884step0 raw20884step0Labels permutation32 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical20885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20885 raw20885Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw20885 raw20885Labels = mixedMoment B raw20885step0 raw20885step0Labels := by
      have hz : ∀ j, raw20885 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20885step0 = (fun i j => raw20885 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20885step0 raw20885; decide +kernel
      have hl : raw20885step0Labels = raw20885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20885 raw20885Labels permutation265 hz
    mixedMoment B raw20885step0 raw20885step0Labels = mixedMoment B raw20885step1 raw20885step1Labels := by
      have ha : raw20885step1 = (fun i j => raw20885step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20885step1 raw20885step0; decide +kernel
      have hl : raw20885step1Labels = raw20885step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20885step0 raw20885step0Labels permutation32 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical20886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20886 raw20886Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw20886 raw20886Labels = mixedMoment B raw20886step0 raw20886step0Labels := by
      have hz : ∀ j, raw20886 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20886step0 = (fun i j => raw20886 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20886step0 raw20886; decide +kernel
      have hl : raw20886step0Labels = raw20886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20886 raw20886Labels permutation346 hz
    mixedMoment B raw20886step0 raw20886step0Labels = mixedMoment B raw20886step1 raw20886step1Labels := by
      have hz : ∀ j, raw20886step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20886step1 = (fun i j => raw20886step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20886step1 raw20886step0; decide +kernel
      have hl : raw20886step1Labels = raw20886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20886step0 raw20886step0Labels permutation56 hz
    mixedMoment B raw20886step1 raw20886step1Labels = mixedMoment B raw20886step2 raw20886step2Labels := by
      have ha : raw20886step2 = (fun i j => raw20886step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20886step2 raw20886step1; decide +kernel
      have hl : raw20886step2Labels = raw20886step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20886step1 raw20886step1Labels permutation8 permutation3
    _ = mixedMoment B node1173 node1173Labels := by rfl

theorem canonical20887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20887 raw20887Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw20887 raw20887Labels = mixedMoment B raw20887step0 raw20887step0Labels := by
      have hz : ∀ j, raw20887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20887step0 = (fun i j => raw20887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20887step0 raw20887; decide +kernel
      have hl : raw20887step0Labels = raw20887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20887 raw20887Labels permutation520 hz
    mixedMoment B raw20887step0 raw20887step0Labels = mixedMoment B raw20887step1 raw20887step1Labels := by
      have hz : ∀ j, raw20887step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20887step1 = (fun i j => raw20887step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20887step1 raw20887step0; decide +kernel
      have hl : raw20887step1Labels = raw20887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20887step0 raw20887step0Labels permutation80 hz
    mixedMoment B raw20887step1 raw20887step1Labels = mixedMoment B raw20887step2 raw20887step2Labels := by
      have hz : ∀ j, raw20887step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20887step2 = (fun i j => raw20887step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20887step2 raw20887step1; decide +kernel
      have hl : raw20887step2Labels = raw20887step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20887step1 raw20887step1Labels permutation14 hz
    mixedMoment B raw20887step2 raw20887step2Labels = mixedMoment B raw20887step3 raw20887step3Labels := by
      have ha : raw20887step3 = (fun i j => raw20887step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20887step3 raw20887step2; decide +kernel
      have hl : raw20887step3Labels = raw20887step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20887step2 raw20887step2Labels permutation2 permutation3
    _ = mixedMoment B node1275 node1275Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw394 raw394Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw394 raw394Labels = mixedMoment B raw394step0 raw394step0Labels := by
      have ha : raw394step0 = (fun i j => raw394 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw394step0 raw394; decide +kernel
      have hl : raw394step0Labels = raw394Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw394 raw394Labels permutation8 permutation5
    mixedMoment B raw394step0 raw394step0Labels = mixedMoment B raw394step1 raw394step1Labels := by
      have ha : raw394step1 = raw394step0 := by apply Matrix.ext; unfold raw394step1 raw394step0; decide +kernel
      have hl : raw394step0Labels = labelEmbedding1 ∘ raw394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw394step0 raw394step0Labels raw394step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3113 node3113Labels := by rfl

theorem canonical395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw395 raw395Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw395 raw395Labels = mixedMoment B raw395step0 raw395step0Labels := by
      have ha : raw395step0 = (fun i j => raw395 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw395step0 raw395; decide +kernel
      have hl : raw395step0Labels = raw395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw395 raw395Labels permutation8 permutation4
    _ = mixedMoment B node388 node388Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10617 raw10617Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw10617 raw10617Labels = mixedMoment B raw10617step0 raw10617step0Labels := by
      have hz : ∀ j, raw10617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10617step0 = (fun i j => raw10617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10617step0 raw10617; decide +kernel
      have hl : raw10617step0Labels = raw10617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10617 raw10617Labels permutation346 hz
    mixedMoment B raw10617step0 raw10617step0Labels = mixedMoment B raw10617step1 raw10617step1Labels := by
      have ha : raw10617step1 = (fun i j => raw10617step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10617step1 raw10617step0; decide +kernel
      have hl : raw10617step1Labels = raw10617step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10617step0 raw10617step0Labels permutation38 permutation3
    _ = mixedMoment B node1270 node1270Labels := by rfl

theorem canonical10622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10622 raw10622Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw10622 raw10622Labels = mixedMoment B raw10622step0 raw10622step0Labels := by
      have hz : ∀ j, raw10622 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10622step0 = (fun i j => raw10622 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10622step0 raw10622; decide +kernel
      have hl : raw10622step0Labels = raw10622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10622 raw10622Labels permutation265 hz
    mixedMoment B raw10622step0 raw10622step0Labels = mixedMoment B raw10622step1 raw10622step1Labels := by
      have ha : raw10622step1 = (fun i j => raw10622step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10622step1 raw10622step0; decide +kernel
      have hl : raw10622step1Labels = raw10622step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10622step0 raw10622step0Labels permutation38 permutation3
    _ = mixedMoment B node1270 node1270Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10627 raw10627Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw10627 raw10627Labels = mixedMoment B raw10627step0 raw10627step0Labels := by
      have hz : ∀ j, raw10627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10627step0 = (fun i j => raw10627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10627step0 raw10627; decide +kernel
      have hl : raw10627step0Labels = raw10627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10627 raw10627Labels permutation346 hz
    mixedMoment B raw10627step0 raw10627step0Labels = mixedMoment B raw10627step1 raw10627step1Labels := by
      have hz : ∀ j, raw10627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10627step1 = (fun i j => raw10627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10627step1 raw10627step0; decide +kernel
      have hl : raw10627step1Labels = raw10627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10627step0 raw10627step0Labels permutation56 hz
    mixedMoment B raw10627step1 raw10627step1Labels = mixedMoment B raw10627step2 raw10627step2Labels := by
      have ha : raw10627step2 = (fun i j => raw10627step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10627step2 raw10627step1; decide +kernel
      have hl : raw10627step2Labels = raw10627step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10627step1 raw10627step1Labels permutation10 permutation3
    _ = mixedMoment B node1306 node1306Labels := by rfl

theorem canonical10632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10632 raw10632Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw10632 raw10632Labels = mixedMoment B raw10632step0 raw10632step0Labels := by
      have hz : ∀ j, raw10632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10632step0 = (fun i j => raw10632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10632step0 raw10632; decide +kernel
      have hl : raw10632step0Labels = raw10632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10632 raw10632Labels permutation346 hz
    mixedMoment B raw10632step0 raw10632step0Labels = mixedMoment B raw10632step1 raw10632step1Labels := by
      have hz : ∀ j, raw10632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10632step1 = (fun i j => raw10632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10632step1 raw10632step0; decide +kernel
      have hl : raw10632step1Labels = raw10632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10632step0 raw10632step0Labels permutation56 hz
    mixedMoment B raw10632step1 raw10632step1Labels = mixedMoment B raw10632step2 raw10632step2Labels := by
      have ha : raw10632step2 = (fun i j => raw10632step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10632step2 raw10632step1; decide +kernel
      have hl : raw10632step2Labels = raw10632step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10632step1 raw10632step1Labels permutation9 permutation3
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical10638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10638 raw10638Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw10638 raw10638Labels = mixedMoment B raw10638step0 raw10638step0Labels := by
      have hz : ∀ j, raw10638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10638step0 = (fun i j => raw10638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10638step0 raw10638; decide +kernel
      have hl : raw10638step0Labels = raw10638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10638 raw10638Labels permutation346 hz
    mixedMoment B raw10638step0 raw10638step0Labels = mixedMoment B raw10638step1 raw10638step1Labels := by
      have ha : raw10638step1 = (fun i j => raw10638step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10638step1 raw10638step0; decide +kernel
      have hl : raw10638step1Labels = raw10638step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10638step0 raw10638step0Labels permutation32 permutation3
    _ = mixedMoment B node2941 node2941Labels := by rfl

theorem canonical10639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10639 raw10639Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw10639 raw10639Labels = mixedMoment B raw10639step0 raw10639step0Labels := by
      have hz : ∀ j, raw10639 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10639step0 = (fun i j => raw10639 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10639step0 raw10639; decide +kernel
      have hl : raw10639step0Labels = raw10639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10639 raw10639Labels permutation265 hz
    mixedMoment B raw10639step0 raw10639step0Labels = mixedMoment B raw10639step1 raw10639step1Labels := by
      have ha : raw10639step1 = (fun i j => raw10639step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10639step1 raw10639step0; decide +kernel
      have hl : raw10639step1Labels = raw10639step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10639step0 raw10639step0Labels permutation32 permutation3
    _ = mixedMoment B node2941 node2941Labels := by rfl

theorem canonical10640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10640 raw10640Labels = mixedMoment B node3004 node3004Labels := by
  calc
    mixedMoment B raw10640 raw10640Labels = mixedMoment B raw10640step0 raw10640step0Labels := by
      have hz : ∀ j, raw10640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10640step0 = (fun i j => raw10640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10640step0 raw10640; decide +kernel
      have hl : raw10640step0Labels = raw10640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10640 raw10640Labels permutation346 hz
    mixedMoment B raw10640step0 raw10640step0Labels = mixedMoment B raw10640step1 raw10640step1Labels := by
      have hz : ∀ j, raw10640step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10640step1 = (fun i j => raw10640step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10640step1 raw10640step0; decide +kernel
      have hl : raw10640step1Labels = raw10640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10640step0 raw10640step0Labels permutation56 hz
    mixedMoment B raw10640step1 raw10640step1Labels = mixedMoment B raw10640step2 raw10640step2Labels := by
      have ha : raw10640step2 = (fun i j => raw10640step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10640step2 raw10640step1; decide +kernel
      have hl : raw10640step2Labels = raw10640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10640step1 raw10640step1Labels permutation8 permutation3
    _ = mixedMoment B node3004 node3004Labels := by rfl

theorem canonical10641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10641 raw10641Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw10641 raw10641Labels = mixedMoment B raw10641step0 raw10641step0Labels := by
      have hz : ∀ j, raw10641 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10641step0 = (fun i j => raw10641 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10641step0 raw10641; decide +kernel
      have hl : raw10641step0Labels = raw10641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10641 raw10641Labels permutation520 hz
    mixedMoment B raw10641step0 raw10641step0Labels = mixedMoment B raw10641step1 raw10641step1Labels := by
      have hz : ∀ j, raw10641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10641step1 = (fun i j => raw10641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10641step1 raw10641step0; decide +kernel
      have hl : raw10641step1Labels = raw10641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10641step0 raw10641step0Labels permutation80 hz
    mixedMoment B raw10641step1 raw10641step1Labels = mixedMoment B raw10641step2 raw10641step2Labels := by
      have hz : ∀ j, raw10641step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10641step2 = (fun i j => raw10641step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10641step2 raw10641step1; decide +kernel
      have hl : raw10641step2Labels = raw10641step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10641step1 raw10641step1Labels permutation14 hz
    mixedMoment B raw10641step2 raw10641step2Labels = mixedMoment B raw10641step3 raw10641step3Labels := by
      have ha : raw10641step3 = (fun i j => raw10641step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10641step3 raw10641step2; decide +kernel
      have hl : raw10641step3Labels = raw10641step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10641step2 raw10641step2Labels permutation2 permutation3
    _ = mixedMoment B node3114 node3114Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5132 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5132 = injectiveMoment H raw5132step0 := by
      have hz : ∀ j, raw5132 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5132step0 = (fun i j => raw5132 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5132 permutation21 hz
    injectiveMoment H raw5132step0 = injectiveMoment H raw5132step1 := by
      have heq : raw5132step1 = (fun i j => raw5132step0 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5132step0 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical5151 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5151 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5151 = injectiveMoment H raw5151step0 := by
      have heq : raw5151step0 = (fun i j => raw5151 (permutation8 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5151 permutation8 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical748 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw748 = injectiveMoment H node263 := by
  calc
    injectiveMoment H raw748 = injectiveMoment H raw748step0 := by
      have heq : raw748step0 = -raw748 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw748).symm
    injectiveMoment H raw748step0 = injectiveMoment H raw748step1 := by
      have heq : raw748step1 = (fun i j => raw748step0 (permutation28 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw748step0 permutation28 permutation5
    _ = injectiveMoment H node263 := by rfl

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

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

theorem canonical7738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7738 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7738 = injectiveMoment H raw7738step0 := by
      have heq : raw7738step0 = (fun i j => raw7738 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7738 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

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

theorem canonical7996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7996 = injectiveMoment H node58 := by
  calc
    injectiveMoment H raw7996 = injectiveMoment H raw7996step0 := by
      have heq : raw7996step0 = (fun i j => raw7996 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7996 permutation5 permutation4
    _ = injectiveMoment H node58 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw35 = injectiveMoment H node7 := by
  calc
    injectiveMoment H raw35 = injectiveMoment H raw35step0 := by
      have heq : raw35step0 = raw35.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw35).symm
    injectiveMoment H raw35step0 = injectiveMoment H raw35step1 := by
      have heq : raw35step1 = (fun i j => raw35step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw35step0 permutation4 permutation1
    _ = injectiveMoment H node7 := by rfl

theorem canonical48 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw48 = injectiveMoment H node6 := by
  rfl

theorem canonical51 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw51 = injectiveMoment H node7 := by
  rfl

theorem canonical53 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw53 = injectiveMoment H node1 := by
  rfl

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

theorem canonical5185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5185 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5185 = injectiveMoment H raw5185step0 := by
      have hz : ∀ j, raw5185 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5185step0 = (fun i j => raw5185 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185 permutation27 hz
    injectiveMoment H raw5185step0 = injectiveMoment H raw5185step1 := by
      have hz : ∀ j, raw5185step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5185step1 = (fun i j => raw5185step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5459 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw5459 = injectiveMoment H raw5459step0 := by
      have heq : raw5459step0 = raw5459.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5459).symm
    injectiveMoment H raw5459step0 = injectiveMoment H raw5459step1 := by
      have heq : raw5459step1 = (fun i j => raw5459step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5459step0 permutation5 permutation2
    _ = injectiveMoment H node9 := by rfl

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

theorem canonical5550 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5550 = injectiveMoment H node53 := by
  rfl

theorem canonical5556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5556 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5556 = injectiveMoment H raw5556step0 := by
      have heq : raw5556step0 = raw5556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5556).symm
    injectiveMoment H raw5556step0 = injectiveMoment H raw5556step1 := by
      have heq : raw5556step1 = (fun i j => raw5556step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5556step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8005 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8005 = injectiveMoment H raw8005step0 := by
      have hz : ∀ i, raw8005 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8005step0 = (fun i j => raw8005 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8005 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw928 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw928 = injectiveMoment H raw928step0 := by
      have heq : raw928step0 = raw928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw928).symm
    injectiveMoment H raw928step0 = injectiveMoment H raw928step1 := by
      have heq : raw928step1 = (fun i j => raw928step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw928step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

theorem canonical958 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw958 = injectiveMoment H node28 := by
  rfl

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

theorem canonical161 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw161 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw161 = injectiveMoment H raw161step0 := by
      have heq : raw161step0 = -raw161 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw161).symm
    injectiveMoment H raw161step0 = injectiveMoment H raw161step1 := by
      have heq : raw161step1 = (fun i j => raw161step0 (permutation13 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw161step0 permutation13 permutation6
    _ = injectiveMoment H node155 := by rfl

theorem canonical172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw172 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw172 = injectiveMoment H raw172step0 := by
      have heq : raw172step0 = -raw172 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw172).symm
    injectiveMoment H raw172step0 = injectiveMoment H raw172step1 := by
      have heq : raw172step1 = (fun i j => raw172step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw172step0 permutation4 permutation6
    _ = injectiveMoment H node32 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

theorem canonical182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw182 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw182 = injectiveMoment H raw182step0 := by
      have heq : raw182step0 = raw182.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw182).symm
    injectiveMoment H raw182step0 = injectiveMoment H raw182step1 := by
      have heq : raw182step1 = (fun i j => raw182step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw182step0 permutation4 permutation1
    _ = injectiveMoment H node8 := by rfl

theorem canonical190 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw190 = injectiveMoment H node14 := by
  rfl

theorem canonical191 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw191 = injectiveMoment H node15 := by
  rfl

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

theorem canonical198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw198 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw198 = injectiveMoment H raw198step0 := by
      have hz : ∀ j, raw198 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw198step0 = (fun i j => raw198 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw198 permutation15 hz
    _ = injectiveMoment H node8 := by rfl

theorem canonical200 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw200 = injectiveMoment H node2 := by
  calc
    injectiveMoment H raw200 = injectiveMoment H raw200step0 := by
      have hz : ∀ j, raw200 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw200step0 = (fun i j => raw200 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw200 permutation5 hz
    _ = injectiveMoment H node2 := by rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
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

theorem sound1 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node1 = Sparse.eval value1 (momentVector H) := by
  have hc : momentVector H 58 = injectiveMoment H node1 := rfl
  simp [value1, Sparse.eval, hc]

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound6 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node6 = Sparse.eval value6 (momentVector H) := by
  have heq : pivotMatrix6 = (fun u v => node6 (pivotPermutation6 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node6 = injectiveMoment H pivotMatrix6 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix6 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix6 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix6 (0 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix6 (0 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix6 (1 : Fin 2)) =
      Sparse.eval value1 (momentVector H) := by
    have heq : mergeFirst pivotMatrix6 (1 : Fin 2) = raw53 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical53 hH).trans (sound1 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node6 + (injectiveMoment H (mergeFirst pivotMatrix6 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix6 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value6, value1, value2, Sparse.eval] at hc ⊢
  linarith

theorem sound7 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node7 = Sparse.eval value7 (momentVector H) := by
  have hc : momentVector H 9 = injectiveMoment H node7 := rfl
  simp [value7, Sparse.eval, hc]

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
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

theorem sound14 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node14 = Sparse.eval value14 (momentVector H) := by
  have heq : pivotMatrix14 = (fun u v => node14 (pivotPermutation14 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node14 = injectiveMoment H pivotMatrix14 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix14 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix14 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix14 (0 : Fin 3)) =
      Sparse.eval value6 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (0 : Fin 3) = raw48 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical48 hH).trans (sound6 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix14 (1 : Fin 3)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (1 : Fin 3) = raw200 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical200 hH).trans (sound2 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix14 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix14 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node14 + (injectiveMoment H (mergeFirst pivotMatrix14 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix14 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix14 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value14, value2, value6, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound15 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node15 = Sparse.eval value15 (momentVector H) := by
  have heq : pivotMatrix15 = (fun u v => node15 (pivotPermutation15 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node15 = injectiveMoment H pivotMatrix15 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix15 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix15 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix15 (0 : Fin 3)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (0 : Fin 3) = raw51 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical51 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix15 (1 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (1 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix15 (2 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix15 (2 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node15 + (injectiveMoment H (mergeFirst pivotMatrix15 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix15 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix15 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value15, value7, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound28 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node28 = Sparse.eval value28 (momentVector H) := by
  have hc : momentVector H 70 = injectiveMoment H node28 := rfl
  simp [value28, Sparse.eval, hc]

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound43 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node43 = Sparse.eval value43 (momentVector H) := by
  have hc : momentVector H 26 = injectiveMoment H node43 := rfl
  simp [value43, Sparse.eval, hc]

theorem sound49 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node49 = Sparse.eval value49 (momentVector H) := by
  have heq : pivotMatrix49 = (fun u v => node49.transpose (pivotPermutation49 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node49 = injectiveMoment H pivotMatrix49 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix49 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix49 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix49 (0 : Fin 2)) =
      Sparse.eval value7 (momentVector H) := by
    have heq : mergeFirst pivotMatrix49 (0 : Fin 2) = raw35 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical35 hH).trans (sound7 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix49 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix49 (1 : Fin 2) = raw182 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical182 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node49 + (injectiveMoment H (mergeFirst pivotMatrix49 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix49 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value49, value7, value8, Sparse.eval] at hc ⊢
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

theorem sound53 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node53 = Sparse.eval value53 (momentVector H) := by
  have heq : pivotMatrix53 = (fun u v => node53 (pivotPermutation53 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node53 = injectiveMoment H pivotMatrix53 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix53 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix53 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node53 + (injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value53, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound58 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node58 = Sparse.eval value58 (momentVector H) := by
  have heq : pivotMatrix58 = (fun u v => node58 (pivotPermutation58 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node58 = injectiveMoment H pivotMatrix58 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix58 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix58 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix58 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node58 + (injectiveMoment H (mergeFirst pivotMatrix58 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix58 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value58, value10, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound59 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node59 = Sparse.eval value59 (momentVector H) := by
  have heq : pivotMatrix59 = (fun u v => node59.transpose (pivotPermutation59 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node59 = injectiveMoment H pivotMatrix59 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix59 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix59 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (0 : Fin 2) = raw928 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical928 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (1 : Fin 2) = raw5459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5459 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node59 + (injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value59, value8, value9, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw962 = injectiveMoment H node49 := by
  calc
    injectiveMoment H raw962 = injectiveMoment H raw962step0 := by
      have heq : raw962step0 = raw962.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw962).symm
    injectiveMoment H raw962step0 = injectiveMoment H raw962step1 := by
      have heq : raw962step1 = (fun i j => raw962step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw962step0 permutation8 permutation6
    _ = injectiveMoment H node49 := by rfl

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

theorem canonical1439 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1439 = injectiveMoment H node32 := by
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

theorem canonical1446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1446 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1446 = injectiveMoment H raw1446step0 := by
      have heq : raw1446step0 = raw1446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1446).symm
    injectiveMoment H raw1446step0 = injectiveMoment H raw1446step1 := by
      have heq : raw1446step1 = (fun i j => raw1446step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1446step0 permutation6 permutation5
    _ = injectiveMoment H node59 := by rfl

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1450 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1450 = injectiveMoment H raw1450step0 := by
      have heq : raw1450step0 = raw1450.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1450).symm
    injectiveMoment H raw1450step0 = injectiveMoment H raw1450step1 := by
      have heq : raw1450step1 = (fun i j => raw1450step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1450step0 permutation8 permutation8
    _ = injectiveMoment H node52 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5902 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5902 = injectiveMoment H node43 := by
  calc
    injectiveMoment H raw5902 = injectiveMoment H raw5902step0 := by
      have heq : raw5902step0 = -raw5902 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5902).symm
    injectiveMoment H raw5902step0 = injectiveMoment H raw5902step1 := by
      have heq : raw5902step1 = (fun i j => raw5902step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5902step0 permutation8 permutation3
    _ = injectiveMoment H node43 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical88 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw88 = injectiveMoment H node143 := by
  calc
    injectiveMoment H raw88 = injectiveMoment H raw88step0 := by
      have heq : raw88step0 = (fun i j => raw88 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw88 permutation32 permutation6
    _ = injectiveMoment H node143 := by rfl

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

theorem sound141 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node141 = Sparse.eval value141 (momentVector H) := by
  have heq : pivotMatrix141 = (fun u v => node141 (pivotPermutation141 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node141 = injectiveMoment H pivotMatrix141 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix141 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix141 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix141 (0 : Fin 3)) =
      Sparse.eval value28 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (0 : Fin 3) = raw958 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical958 hH).trans (sound28 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix141 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix141 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix141 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node141 + (injectiveMoment H (mergeFirst pivotMatrix141 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix141 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix141 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value141, value28, value31, value32, Sparse.eval] at hc ⊢
  linarith

theorem sound143 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node143 = Sparse.eval value143 (momentVector H) := by
  have heq : pivotMatrix143 = (fun u v => node143 (pivotPermutation143 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node143 = injectiveMoment H pivotMatrix143 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix143 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix143 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix143 (0 : Fin 3)) =
      Sparse.eval value49 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (0 : Fin 3) = raw962 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical962 hH).trans (sound49 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix143 (1 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (1 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix143 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix143 (2 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node143 + (injectiveMoment H (mergeFirst pivotMatrix143 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix143 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix143 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value143, value49, value52, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound155 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node155 = Sparse.eval value155 (momentVector H) := by
  have heq : pivotMatrix155 = (fun u v => node155 (pivotPermutation155 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node155 = injectiveMoment H pivotMatrix155 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix155 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix155 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (0 : Fin 3) = raw5550 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5550 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (1 : Fin 3) = raw1450 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1450 hH).trans (sound52 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix155 (2 : Fin 3) = raw1439 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1439 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node155 + (injectiveMoment H (mergeFirst pivotMatrix155 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix155 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value155, value32, value52, value53, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound263 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node263 = Sparse.eval value263 (momentVector H) := by
  have heq : pivotMatrix263 = (fun u v => node263 (pivotPermutation263 u) v) := by apply Matrix.ext; unfold pivotMatrix263 node263 pivotPermutation263; decide +kernel
  have hmoment : injectiveMoment H node263 = injectiveMoment H pivotMatrix263 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix263 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix263 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix263 (0 : Fin 3)) =
      Sparse.eval value58 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (0 : Fin 3) = raw7996 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw7996; decide +kernel
    rw [heq]
    exact (canonical7996 hH).trans (sound58 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix263 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (1 : Fin 3) = raw5979 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw5979; decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix263 (2 : Fin 3)) =
      Sparse.eval value43 (momentVector H) := by
    have heq : mergeFirst pivotMatrix263 (2 : Fin 3) = raw5902 := by apply Matrix.ext; unfold mergeFirst pivotMatrix263 raw5902; decide +kernel
    rw [heq]
    exact (canonical5902 hH).trans (sound43 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node263 + (injectiveMoment H (mergeFirst pivotMatrix263 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix263 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix263 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value263, value43, value57, value58, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node388 node388Labels = Sparse.eval singlePairValue388 (familyPairVector B) := by
  have hp := single_label_three B hB node388
  have hl : node388Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node388 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node388 PairSemantics.raw5132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node388 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node388 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node388 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value263 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node388 (EqualityPatterns.family3.label 4) = PairSemantics.raw748 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node388 PairSemantics.raw748; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical748 hH).trans (PairSemantics.sound263 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue388, PairSemantics.value0, PairSemantics.value10, PairSemantics.value65, PairSemantics.value263, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair70 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node70 node70Labels = Sparse.eval singlePairValue70 (familyPairVector B) := by
  have hp := single_label_three B hB node70
  have hl : node70Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node70 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 1) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node70 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node70 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value14 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 3) = PairSemantics.raw190 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node70 PairSemantics.raw190; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical190 hH).trans (PairSemantics.sound14 hH)
  have hm4 : familyPairMoment B (groupedColumns node70 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value143 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node70 (EqualityPatterns.family3.label 4) = PairSemantics.raw88 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node70 PairSemantics.raw88; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical88 hH).trans (PairSemantics.sound143 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue70, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value14, PairSemantics.value143, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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

theorem canonical118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw118 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw118 = injectiveMoment H raw118step0 := by
      have heq : raw118step0 = raw118.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw118).symm
    injectiveMoment H raw118step0 = injectiveMoment H raw118step1 := by
      have heq : raw118step1 = (fun i j => raw118step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw118step0 permutation7 permutation6
    _ = injectiveMoment H node59 := by rfl

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

theorem singlePair100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node100 node100Labels = Sparse.eval singlePairValue100 (familyPairVector B) := by
  have hp := single_label_three B hB node100
  have hl : node100Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node100 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 1) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node100 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node100 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value2 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 3) = PairSemantics.raw200 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node100 PairSemantics.raw200; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical200 hH).trans (PairSemantics.sound2 hH)
  have hm4 : familyPairMoment B (groupedColumns node100 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value59 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node100 (EqualityPatterns.family3.label 4) = PairSemantics.raw118 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node100 PairSemantics.raw118; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical118 hH).trans (PairSemantics.sound59 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue100, PairSemantics.value0, PairSemantics.value2, PairSemantics.value10, PairSemantics.value11, PairSemantics.value59, Sparse.eval] at hp ⊢
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

theorem canonical149 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw149 = injectiveMoment H node141 := by
  calc
    injectiveMoment H raw149 = injectiveMoment H raw149step0 := by
      have heq : raw149step0 = -raw149 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw149).symm
    injectiveMoment H raw149step0 = injectiveMoment H raw149step1 := by
      have heq : raw149step1 = (fun i j => raw149step0 (permutation10 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw149step0 permutation10 permutation6
    _ = injectiveMoment H node141 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node131 node131Labels = Sparse.eval singlePairValue131 (familyPairVector B) := by
  have hp := single_label_three B hB node131
  have hl : node131Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node131 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node131 PairSemantics.raw5132; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 2) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node131 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value15 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 3) = PairSemantics.raw191 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node131 PairSemantics.raw191; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical191 hH).trans (PairSemantics.sound15 hH)
  have hm4 : familyPairMoment B (groupedColumns node131 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value141 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node131 (EqualityPatterns.family3.label 4) = PairSemantics.raw149 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node131 PairSemantics.raw149; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical149 hH).trans (PairSemantics.sound141 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue131, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value15, PairSemantics.value141, Sparse.eval] at hp ⊢
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

theorem singlePair143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node143 node143Labels = Sparse.eval singlePairValue143 (familyPairVector B) := by
  have hp := single_label_three B hB node143
  have hl : node143Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node143 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 1) = PairSemantics.raw5132 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node143 PairSemantics.raw5132
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5132 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node143 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node143 PairSemantics.raw198
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node143 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value155 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node143 (EqualityPatterns.family3.label 4) = PairSemantics.raw161 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node143 PairSemantics.raw161
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical161 hH).trans (PairSemantics.sound155 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue143, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value11, PairSemantics.value155, Sparse.eval] at hp ⊢
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

theorem singlePair154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node154 node154Labels = Sparse.eval singlePairValue154 (familyPairVector B) := by
  have hp := single_label_three B hB node154
  have hl : node154Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node154 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 1) = PairSemantics.raw5151 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node154 PairSemantics.raw5151
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5151 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 2) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node154 PairSemantics.raw5214
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node154 PairSemantics.raw211
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node154 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value32 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node154 (EqualityPatterns.family3.label 4) = PairSemantics.raw172 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node154 PairSemantics.raw172
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical172 hH).trans (PairSemantics.sound32 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue154, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value10, PairSemantics.value32, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1173 node1173Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node70 node70Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw38 singletonSmall1173
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1173) = raw38Labels := by decide +kernel
  rw [hl, canonical38 B hB] at h
  have hc0 : mixedMoment B raw38 (Fin.cases (0 : Fin 1) singletonSmall1173) =
      mixedMoment B node70 node70Labels := by
    have ha : raw38 = raw39 := by apply Matrix.ext; unfold raw38 raw39; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1173 = raw39Labels := by decide +kernel
    rw [ha, hj, canonical39 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1177 node1177Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node131 node131Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw44 singletonSmall1177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1177) = raw44Labels := by decide +kernel
  rw [hl, canonical44 B hB] at h
  have hc0 : mixedMoment B raw44 (Fin.cases (0 : Fin 1) singletonSmall1177) =
      mixedMoment B node131 node131Labels := by
    have ha : raw44 = raw45 := by apply Matrix.ext; unfold raw44 raw45; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1177 = raw45Labels := by decide +kernel
    rw [ha, hj, canonical45 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1271 node1271Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node143 node143Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw60 singletonSmall1271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1271) = raw60Labels := by decide +kernel
  rw [hl, canonical60 B hB] at h
  have hc0 : mixedMoment B raw60 (Fin.cases (0 : Fin 1) singletonSmall1271) =
      mixedMoment B node143 node143Labels := by
    have ha : raw60 = raw61 := by apply Matrix.ext; unfold raw60 raw61; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1271 = raw61Labels := by decide +kernel
    rw [ha, hj, canonical61 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1275 node1275Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node100 node100Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw64 singletonSmall1275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1275) = raw64Labels := by decide +kernel
  rw [hl, canonical64 B hB] at h
  have hc0 : mixedMoment B raw64 (Fin.cases (0 : Fin 1) singletonSmall1275) =
      mixedMoment B node100 node100Labels := by
    have ha : raw64 = raw65 := by apply Matrix.ext; unfold raw64 raw65; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1275 = raw65Labels := by decide +kernel
    rw [ha, hj, canonical65 B hB]
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

theorem singleton1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1308 node1308Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node154 node154Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw88 singletonSmall1308
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1308) = raw88Labels := by decide +kernel
  rw [hl, canonical88 B hB] at h
  have hc0 : mixedMoment B raw88 (Fin.cases (0 : Fin 1) singletonSmall1308) =
      mixedMoment B node154 node154Labels := by
    have ha : raw88 = raw89 := by apply Matrix.ext; unfold raw88 raw89; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1308 = raw89Labels := by decide +kernel
    rw [ha, hj, canonical89 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3113 node3113Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node388 node388Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw394 singletonSmall3113
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3113) = raw394Labels := by decide +kernel
  rw [hl, canonical394 B hB] at h
  have hc0 : mixedMoment B raw394 (Fin.cases (0 : Fin 1) singletonSmall3113) =
      mixedMoment B node388 node388Labels := by
    have ha : raw394 = raw395 := by apply Matrix.ext; unfold raw394 raw395; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3113 = raw395Labels := by decide +kernel
    rw [ha, hj, canonical395 B hB]
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

theorem sound70 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node70 node70Labels = Sparse.eval nodeValue70 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue70 (familyPairVector B) := singlePair70 B _hB
    _ = _ := by norm_num [singlePairValue70, nodeValue70, Sparse.eval, mixedVector] <;> ring

theorem sound100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node100 node100Labels = Sparse.eval nodeValue100 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue100 (familyPairVector B) := singlePair100 B _hB
    _ = _ := by norm_num [singlePairValue100, nodeValue100, Sparse.eval, mixedVector] <;> ring

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

theorem sound1116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1116 node1116Labels = Sparse.eval nodeValue1116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1116) = mixedMoment B node1116 node1116Labels := rfl
  simpa [nodeValue1116, Sparse.eval] using hc.symm

theorem sound1118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1118 node1118Labels = Sparse.eval nodeValue1118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1118) = mixedMoment B node1118 node1118Labels := rfl
  simpa [nodeValue1118, Sparse.eval] using hc.symm

theorem sound1121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1121 node1121Labels = Sparse.eval nodeValue1121 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1121) = mixedMoment B node1121 node1121Labels := rfl
  simpa [nodeValue1121, Sparse.eval] using hc.symm

theorem sound1137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1137 node1137Labels = Sparse.eval nodeValue1137 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1137) = mixedMoment B node1137 node1137Labels := rfl
  simpa [nodeValue1137, Sparse.eval] using hc.symm

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

theorem sound131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node131 node131Labels = Sparse.eval nodeValue131 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue131 (familyPairVector B) := singlePair131 B _hB
    _ = _ := by
      norm_num [singlePairValue131, nodeValue131, Sparse.eval, mixedVector]
      ring

theorem sound143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node143 node143Labels = Sparse.eval nodeValue143 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue143 (familyPairVector B) := singlePair143 B _hB
    _ = _ := by
      norm_num [singlePairValue143, nodeValue143, Sparse.eval, mixedVector]
      ring

theorem sound154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node154 node154Labels = Sparse.eval nodeValue154 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue154 (familyPairVector B) := singlePair154 B _hB
    _ = _ := by
      norm_num [singlePairValue154, nodeValue154, Sparse.eval, mixedVector]
      ring

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

theorem sound1173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1173 node1173Labels = Sparse.eval nodeValue1173 (mixedVector B) := by
  have h := singleton1173 B _hB
  rw [sound70 B _hB _hF] at h
  norm_num [nodeValue1173, nodeValue70, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1177 node1177Labels = Sparse.eval nodeValue1177 (mixedVector B) := by
  have h := singleton1177 B _hB
  rw [sound131 B _hB _hF] at h
  norm_num [nodeValue1177, nodeValue131, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1270 node1270Labels = Sparse.eval nodeValue1270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1270) = mixedMoment B node1270 node1270Labels := rfl
  simpa [nodeValue1270, Sparse.eval] using hc.symm

theorem sound1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1271 node1271Labels = Sparse.eval nodeValue1271 (mixedVector B) := by
  have h := singleton1271 B _hB
  rw [sound143 B _hB _hF] at h
  norm_num [nodeValue1271, nodeValue143, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1273 node1273Labels = Sparse.eval nodeValue1273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1273) = mixedMoment B node1273 node1273Labels := rfl
  simpa [nodeValue1273, Sparse.eval] using hc.symm

theorem sound1275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1275 node1275Labels = Sparse.eval nodeValue1275 (mixedVector B) := by
  have h := singleton1275 B _hB
  rw [sound100 B _hB _hF] at h
  norm_num [nodeValue1275, nodeValue100, Sparse.eval] at h ⊢
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

theorem sound1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1306 node1306Labels = Sparse.eval nodeValue1306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1306) = mixedMoment B node1306 node1306Labels := rfl
  simpa [nodeValue1306, Sparse.eval] using hc.symm

theorem sound1308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1308 node1308Labels = Sparse.eval nodeValue1308 (mixedVector B) := by
  have h := singleton1308 B _hB
  rw [sound154 B _hB _hF] at h
  norm_num [nodeValue1308, nodeValue154, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3004 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3004 node3004Labels = 0 := by
  exact mixedMoment_order_one B hB node3004 node3004Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound3004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3004 node3004Labels = Sparse.eval nodeValue3004 (mixedVector B) := by
  simpa only [nodeValue3004, Sparse.eval_nil] using zero3004 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node388 node388Labels = Sparse.eval nodeValue388 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue388 (familyPairVector B) := singlePair388 B _hB
    _ = _ := by
      norm_num [singlePairValue388, nodeValue388, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3114 node3114Labels = 0 := by
  exact mixedMoment_order_one B hB node3114 node3114Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound3113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3113 node3113Labels = Sparse.eval nodeValue3113 (mixedVector B) := by
  have h := singleton3113 B _hB
  rw [sound388 B _hB _hF] at h
  norm_num [nodeValue3113, nodeValue388, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3114 node3114Labels = Sparse.eval nodeValue3114 (mixedVector B) := by
  simpa only [nodeValue3114, Sparse.eval_nil] using zero3114 B _hB _hF

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

theorem sound585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node585 node585Labels = Sparse.eval nodeValue585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 585) = mixedMoment B node585 node585Labels := rfl
  simpa [nodeValue585, Sparse.eval] using hc.symm

theorem sound587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node587 node587Labels = Sparse.eval nodeValue587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 587) = mixedMoment B node587 node587Labels := rfl
  simpa [nodeValue587, Sparse.eval] using hc.symm

theorem sound590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node590 node590Labels = Sparse.eval nodeValue590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 590) = mixedMoment B node590 node590Labels := rfl
  simpa [nodeValue590, Sparse.eval] using hc.symm

theorem sound612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node612 node612Labels = Sparse.eval nodeValue612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 612) = mixedMoment B node612 node612Labels := rfl
  simpa [nodeValue612, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources40
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1297 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 1) (sourceB1297 + difference 1 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 1) (sourceB1297 + difference 1 0) sourceC1297) = raw10638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10638; decide +kernel
    rw [ha]
    exact (canonical10638 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 2) (sourceB1297 + difference 2 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 2) (sourceB1297 + difference 2 0) sourceC1297) = raw10639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10639; decide +kernel
    rw [ha]
    exact (canonical10639 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 3) (sourceB1297 + difference 3 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3004) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 3) (sourceB1297 + difference 3 0) sourceC1297) = raw10640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10640; decide +kernel
    rw [ha]
    exact (canonical10640 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 4) (sourceB1297 + difference 4 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 4) (sourceB1297 + difference 4 0) sourceC1297) = raw10641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10641; decide +kernel
    rw [ha]
    exact (canonical10641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1297 + difference 0 5) (sourceB1297 + difference 5 0) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA1297 + difference 0 5) (sourceB1297 + difference 5 0) sourceC1297) = raw20866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20866; decide +kernel
    rw [ha]
    exact (canonical20866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 0) (sourceB1297 + difference 0 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 585) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 0) (sourceB1297 + difference 0 1) sourceC1297) = raw20867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20867; decide +kernel
    rw [ha]
    exact (canonical20867 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 2) (sourceB1297 + difference 2 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 2) (sourceB1297 + difference 2 1) sourceC1297) = raw20868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20868; decide +kernel
    rw [ha]
    exact (canonical20868 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 3) (sourceB1297 + difference 3 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1170) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 3) (sourceB1297 + difference 3 1) sourceC1297) = raw20869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20869; decide +kernel
    rw [ha]
    exact (canonical20869 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 4) (sourceB1297 + difference 4 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 4) (sourceB1297 + difference 4 1) sourceC1297) = raw20870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20870; decide +kernel
    rw [ha]
    exact (canonical20870 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1297 + difference 1 5) (sourceB1297 + difference 5 1) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1297 + difference 1 5) (sourceB1297 + difference 5 1) sourceC1297) = raw10617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10617; decide +kernel
    rw [ha]
    exact (canonical10617 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 0) (sourceB1297 + difference 0 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 585) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 0) (sourceB1297 + difference 0 2) sourceC1297) = raw20871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20871; decide +kernel
    rw [ha]
    exact (canonical20871 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 1) (sourceB1297 + difference 1 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 1) (sourceB1297 + difference 1 2) sourceC1297) = raw20872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20872; decide +kernel
    rw [ha]
    exact (canonical20872 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 3) (sourceB1297 + difference 3 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1170) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 3) (sourceB1297 + difference 3 2) sourceC1297) = raw20873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20873; decide +kernel
    rw [ha]
    exact (canonical20873 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 4) (sourceB1297 + difference 4 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 4) (sourceB1297 + difference 4 2) sourceC1297) = raw20874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20874; decide +kernel
    rw [ha]
    exact (canonical20874 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1297 + difference 2 5) (sourceB1297 + difference 5 2) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1297 + difference 2 5) (sourceB1297 + difference 5 2) sourceC1297) = raw10622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10622; decide +kernel
    rw [ha]
    exact (canonical10622 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 0) (sourceB1297 + difference 0 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 612) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 0) (sourceB1297 + difference 0 3) sourceC1297) = raw20875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20875; decide +kernel
    rw [ha]
    exact (canonical20875 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 1) (sourceB1297 + difference 1 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 1) (sourceB1297 + difference 1 3) sourceC1297) = raw20876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20876; decide +kernel
    rw [ha]
    exact (canonical20876 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 2) (sourceB1297 + difference 2 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 2) (sourceB1297 + difference 2 3) sourceC1297) = raw20877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20877; decide +kernel
    rw [ha]
    exact (canonical20877 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 4) (sourceB1297 + difference 4 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 4) (sourceB1297 + difference 4 3) sourceC1297) = raw20878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20878; decide +kernel
    rw [ha]
    exact (canonical20878 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1297 + difference 3 5) (sourceB1297 + difference 5 3) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1297 + difference 3 5) (sourceB1297 + difference 5 3) sourceC1297) = raw10627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10627; decide +kernel
    rw [ha]
    exact (canonical10627 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 0) (sourceB1297 + difference 0 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 590) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 0) (sourceB1297 + difference 0 4) sourceC1297) = raw20879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20879; decide +kernel
    rw [ha]
    exact (canonical20879 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 1) (sourceB1297 + difference 1 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 1) (sourceB1297 + difference 1 4) sourceC1297) = raw20880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20880; decide +kernel
    rw [ha]
    exact (canonical20880 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 2) (sourceB1297 + difference 2 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 2) (sourceB1297 + difference 2 4) sourceC1297) = raw20881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20881; decide +kernel
    rw [ha]
    exact (canonical20881 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 3) (sourceB1297 + difference 3 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1177) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 3) (sourceB1297 + difference 3 4) sourceC1297) = raw20882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20882; decide +kernel
    rw [ha]
    exact (canonical20882 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1297 + difference 4 5) (sourceB1297 + difference 5 4) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1297 + difference 4 5) (sourceB1297 + difference 5 4) sourceC1297) = raw10632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw10632; decide +kernel
    rw [ha]
    exact (canonical10632 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 0) (sourceB1297 + difference 0 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 0) (sourceB1297 + difference 0 5) sourceC1297) = raw20883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20883; decide +kernel
    rw [ha]
    exact (canonical20883 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 1) (sourceB1297 + difference 1 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 1) (sourceB1297 + difference 1 5) sourceC1297) = raw20884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20884; decide +kernel
    rw [ha]
    exact (canonical20884 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 2) (sourceB1297 + difference 2 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 2) (sourceB1297 + difference 2 5) sourceC1297) = raw20885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20885; decide +kernel
    rw [ha]
    exact (canonical20885 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 3) (sourceB1297 + difference 3 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1173) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 3) (sourceB1297 + difference 3 5) sourceC1297) = raw20886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20886; decide +kernel
    rw [ha]
    exact (canonical20886 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1297 + difference 5 4) (sourceB1297 + difference 4 5) sourceC1297) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1297 + difference 5 4) (sourceB1297 + difference 4 5) sourceC1297) = raw20887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1297 sourceB1297 sourceC1297 difference raw20887; decide +kernel
    rw [ha]
    exact (canonical20887 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1297 sourceB1297 sourceC1297
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1297, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1124 : Integer.Sparse.reindex keyMap MixedData.row1124 = numericRow1124 := by decide +kernel

theorem numericCheck1124 (x : Master → ℝ) : Integer.Sparse.eval numericRow1124 x =
    (1440 : ℝ) * reducedSource1124 x := by
  norm_num [numericRow1124, reducedSource1124, Integer.Sparse.eval, Sparse.eval, nodeValue585, nodeValue587, nodeValue590, nodeValue612, nodeValue1116, nodeValue1118, nodeValue1121, nodeValue1137, nodeValue1170, nodeValue1173, nodeValue1177, nodeValue1270, nodeValue1271, nodeValue1273, nodeValue1275, nodeValue1306, nodeValue1308, nodeValue2941, nodeValue3004, nodeValue3113, nodeValue3114]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1124 (mixedVector B) = 0 := by
  have h585 : mixedVector B (Sum.inr 585) = Sparse.eval nodeValue585 (mixedVector B) := by
    change mixedMoment B node585 node585Labels = _
    exact sound585 B hB hF
  have h587 : mixedVector B (Sum.inr 587) = Sparse.eval nodeValue587 (mixedVector B) := by
    change mixedMoment B node587 node587Labels = _
    exact sound587 B hB hF
  have h590 : mixedVector B (Sum.inr 590) = Sparse.eval nodeValue590 (mixedVector B) := by
    change mixedMoment B node590 node590Labels = _
    exact sound590 B hB hF
  have h612 : mixedVector B (Sum.inr 612) = Sparse.eval nodeValue612 (mixedVector B) := by
    change mixedMoment B node612 node612Labels = _
    exact sound612 B hB hF
  have h1116 : mixedVector B (Sum.inr 1116) = Sparse.eval nodeValue1116 (mixedVector B) := by
    change mixedMoment B node1116 node1116Labels = _
    exact sound1116 B hB hF
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1121 : mixedVector B (Sum.inr 1121) = Sparse.eval nodeValue1121 (mixedVector B) := by
    change mixedMoment B node1121 node1121Labels = _
    exact sound1121 B hB hF
  have h1137 : mixedVector B (Sum.inr 1137) = Sparse.eval nodeValue1137 (mixedVector B) := by
    change mixedMoment B node1137 node1137Labels = _
    exact sound1137 B hB hF
  have h1170 : mixedVector B (Sum.inr 1170) = Sparse.eval nodeValue1170 (mixedVector B) := by
    change mixedMoment B node1170 node1170Labels = _
    exact sound1170_e B hB hF
  have h1173 : mixedVector B (Sum.inr 1173) = Sparse.eval nodeValue1173 (mixedVector B) := by
    change mixedMoment B node1173 node1173Labels = _
    exact sound1173 B hB hF
  have h1177 : mixedVector B (Sum.inr 1177) = Sparse.eval nodeValue1177 (mixedVector B) := by
    change mixedMoment B node1177 node1177Labels = _
    exact sound1177 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h1271 : mixedVector B (Sum.inr 1271) = Sparse.eval nodeValue1271 (mixedVector B) := by
    change mixedMoment B node1271 node1271Labels = _
    exact sound1271 B hB hF
  have h1273 : mixedVector B (Sum.inr 1273) = Sparse.eval nodeValue1273 (mixedVector B) := by
    change mixedMoment B node1273 node1273Labels = _
    exact sound1273 B hB hF
  have h1275 : mixedVector B (Sum.inr 1275) = Sparse.eval nodeValue1275 (mixedVector B) := by
    change mixedMoment B node1275 node1275Labels = _
    exact sound1275 B hB hF
  have h1306 : mixedVector B (Sum.inr 1306) = Sparse.eval nodeValue1306 (mixedVector B) := by
    change mixedMoment B node1306 node1306Labels = _
    exact sound1306 B hB hF
  have h1308 : mixedVector B (Sum.inr 1308) = Sparse.eval nodeValue1308 (mixedVector B) := by
    change mixedMoment B node1308 node1308Labels = _
    exact sound1308 B hB hF
  have h2941 : mixedVector B (Sum.inr 2941) = Sparse.eval nodeValue2941 (mixedVector B) := by
    change mixedMoment B node2941 node2941Labels = _
    exact sound2941_e B hB hF
  have h3004 : mixedVector B (Sum.inr 3004) = Sparse.eval nodeValue3004 (mixedVector B) := by
    change mixedMoment B node3004 node3004Labels = _
    exact sound3004 B hB hF
  have h3113 : mixedVector B (Sum.inr 3113) = Sparse.eval nodeValue3113 (mixedVector B) := by
    change mixedMoment B node3113 node3113Labels = _
    exact sound3113 B hB hF
  have h3114 : mixedVector B (Sum.inr 3114) = Sparse.eval nodeValue3114 (mixedVector B) := by
    change mixedMoment B node3114 node3114Labels = _
    exact sound3114 B hB hF
  simpa only [sourceForm1297, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h585, h587, h590, h612, h1116, h1118, h1121, h1137, h1170, h1173, h1177, h1270, h1271, h1273, h1275, h1306, h1308, h2941, h3004, h3113, h3114, reducedSource1124] using sourceEq1297 B hB

theorem rowSound1124_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1124 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1124, numericCheck1124, reducedZero1124 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e_oai
