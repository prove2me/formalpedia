-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:38:46.677291+00:00
-- url     : https://prove2.me/submissions/a4810e1c-6280-45bb-afe7-3b7db5ec82b0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw248 raw248Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw248 raw248Labels = mixedMoment B raw248step0 raw248step0Labels := by
      have ha : raw248step0 = (fun i j => raw248 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw248step0 raw248; decide +kernel
      have hl : raw248step0Labels = raw248Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw248 raw248Labels permutation8 permutation5
    mixedMoment B raw248step0 raw248step0Labels = mixedMoment B raw248step1 raw248step1Labels := by
      have ha : raw248step1 = raw248step0 := by apply Matrix.ext; unfold raw248step1 raw248step0; decide +kernel
      have hl : raw248step0Labels = labelEmbedding1 ∘ raw248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw248step0 raw248step0Labels raw248step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2605 node2605Labels := by rfl

theorem canonical249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw249 raw249Labels = mixedMoment B node344 node344Labels := by
  calc
    mixedMoment B raw249 raw249Labels = mixedMoment B raw249step0 raw249step0Labels := by
      have ha : raw249step0 = (fun i j => raw249 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw249step0 raw249; decide +kernel
      have hl : raw249step0Labels = raw249Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw249 raw249Labels permutation8 permutation5
    _ = mixedMoment B node344 node344Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1299 raw1299Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw1299 raw1299Labels = mixedMoment B raw1299step0 raw1299step0Labels := by
      have ha : raw1299step0 = (fun i j => raw1299 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1299step0 raw1299; decide +kernel
      have hl : raw1299step0Labels = raw1299Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1299 raw1299Labels permutation8 permutation4
    mixedMoment B raw1299step0 raw1299step0Labels = mixedMoment B raw1299step1 raw1299step1Labels := by
      have ha : raw1299step1 = raw1299step0 := by apply Matrix.ext; unfold raw1299step1 raw1299step0; decide +kernel
      have hl : raw1299step0Labels = labelEmbedding7 ∘ raw1299step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1299step0 raw1299step0Labels raw1299step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1300 raw1300Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw1300 raw1300Labels = mixedMoment B raw1300step0 raw1300step0Labels := by
      have ha : raw1300step0 = (fun i j => raw1300 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1300step0 raw1300; decide +kernel
      have hl : raw1300step0Labels = raw1300Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1300 raw1300Labels permutation8 permutation4
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1301 raw1301Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw1301 raw1301Labels = mixedMoment B raw1301step0 raw1301step0Labels := by
      have ha : raw1301step0 = (fun i j => raw1301 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1301step0 raw1301; decide +kernel
      have hl : raw1301step0Labels = raw1301Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1301 raw1301Labels permutation9 permutation6
    mixedMoment B raw1301step0 raw1301step0Labels = mixedMoment B raw1301step1 raw1301step1Labels := by
      have ha : raw1301step1 = -raw1301step0 := by apply Matrix.ext; change ∀ i j, raw1301step1 i j = -(raw1301step0 i j); unfold raw1301step1 raw1301step0; decide +kernel
      have hl : raw1301step1Labels = raw1301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1301step1 raw1301step1Labels = mixedMoment B raw1301step2 raw1301step2Labels := by
      have ha : raw1301step2 = raw1301step1 := by apply Matrix.ext; unfold raw1301step2 raw1301step1; decide +kernel
      have hl : raw1301step1Labels = labelEmbedding1 ∘ raw1301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1301step1 raw1301step1Labels raw1301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17675 raw17675Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw17675 raw17675Labels = mixedMoment B raw17675step0 raw17675step0Labels := by
      have hz : ∀ j, raw17675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17675step0 = (fun i j => raw17675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17675step0 raw17675; decide +kernel
      have hl : raw17675step0Labels = raw17675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17675 raw17675Labels permutation434 hz
    mixedMoment B raw17675step0 raw17675step0Labels = mixedMoment B raw17675step1 raw17675step1Labels := by
      have hz : ∀ j, raw17675step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17675step1 = (fun i j => raw17675step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17675step1 raw17675step0; decide +kernel
      have hl : raw17675step1Labels = raw17675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17675step0 raw17675step0Labels permutation80 hz
    mixedMoment B raw17675step1 raw17675step1Labels = mixedMoment B raw17675step2 raw17675step2Labels := by
      have ha : raw17675step2 = (fun i j => raw17675step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17675step2 raw17675step1; decide +kernel
      have hl : raw17675step2Labels = raw17675step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17675step1 raw17675step1Labels permutation8 permutation3
    mixedMoment B raw17675step2 raw17675step2Labels = mixedMoment B raw17675step3 raw17675step3Labels := by
      have ha : raw17675step3 = raw17675step2 := by apply Matrix.ext; unfold raw17675step3 raw17675step2; decide +kernel
      have hl : raw17675step2Labels = labelEmbedding6 ∘ raw17675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17675step2 raw17675step2Labels raw17675step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2109 raw2109Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw2109 raw2109Labels = mixedMoment B raw2109step0 raw2109step0Labels := by
      have ha : raw2109step0 = (fun i j => raw2109 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2109step0 raw2109; decide +kernel
      have hl : raw2109step0Labels = raw2109Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2109 raw2109Labels permutation32 permutation4
    mixedMoment B raw2109step0 raw2109step0Labels = mixedMoment B raw2109step1 raw2109step1Labels := by
      have ha : raw2109step1 = raw2109step0 := by apply Matrix.ext; unfold raw2109step1 raw2109step0; decide +kernel
      have hl : raw2109step0Labels = labelEmbedding7 ∘ raw2109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2109step0 raw2109step0Labels raw2109step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2110 raw2110Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw2110 raw2110Labels = mixedMoment B raw2110step0 raw2110step0Labels := by
      have ha : raw2110step0 = (fun i j => raw2110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2110step0 raw2110; decide +kernel
      have hl : raw2110step0Labels = raw2110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2110 raw2110Labels permutation32 permutation4
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical2111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2111 raw2111Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw2111 raw2111Labels = mixedMoment B raw2111step0 raw2111step0Labels := by
      have ha : raw2111step0 = (fun i j => raw2111 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2111step0 raw2111; decide +kernel
      have hl : raw2111step0Labels = raw2111Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2111 raw2111Labels permutation32 permutation6
    mixedMoment B raw2111step0 raw2111step0Labels = mixedMoment B raw2111step1 raw2111step1Labels := by
      have ha : raw2111step1 = -raw2111step0 := by apply Matrix.ext; change ∀ i j, raw2111step1 i j = -(raw2111step0 i j); unfold raw2111step1 raw2111step0; decide +kernel
      have hl : raw2111step1Labels = raw2111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2111step1 raw2111step1Labels = mixedMoment B raw2111step2 raw2111step2Labels := by
      have ha : raw2111step2 = raw2111step1 := by apply Matrix.ext; unfold raw2111step2 raw2111step1; decide +kernel
      have hl : raw2111step1Labels = labelEmbedding1 ∘ raw2111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2111step1 raw2111step1Labels raw2111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21481 raw21481Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw21481 raw21481Labels = mixedMoment B raw21481step0 raw21481step0Labels := by
      have hz : ∀ j, raw21481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21481step0 = (fun i j => raw21481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21481step0 raw21481; decide +kernel
      have hl : raw21481step0Labels = raw21481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21481 raw21481Labels permutation434 hz
    mixedMoment B raw21481step0 raw21481step0Labels = mixedMoment B raw21481step1 raw21481step1Labels := by
      have hz : ∀ j, raw21481step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21481step1 = (fun i j => raw21481step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21481step1 raw21481step0; decide +kernel
      have hl : raw21481step1Labels = raw21481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21481step0 raw21481step0Labels permutation80 hz
    mixedMoment B raw21481step1 raw21481step1Labels = mixedMoment B raw21481step2 raw21481step2Labels := by
      have ha : raw21481step2 = (fun i j => raw21481step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21481step2 raw21481step1; decide +kernel
      have hl : raw21481step2Labels = raw21481step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21481step1 raw21481step1Labels permutation10 permutation3
    mixedMoment B raw21481step2 raw21481step2Labels = mixedMoment B raw21481step3 raw21481step3Labels := by
      have ha : raw21481step3 = raw21481step2 := by apply Matrix.ext; unfold raw21481step3 raw21481step2; decide +kernel
      have hl : raw21481step2Labels = labelEmbedding6 ∘ raw21481step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21481step2 raw21481step2Labels raw21481step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical21485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21485 raw21485Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw21485 raw21485Labels = mixedMoment B raw21485step0 raw21485step0Labels := by
      have hz : ∀ j, raw21485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21485step0 = (fun i j => raw21485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21485step0 raw21485; decide +kernel
      have hl : raw21485step0Labels = raw21485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21485 raw21485Labels permutation434 hz
    mixedMoment B raw21485step0 raw21485step0Labels = mixedMoment B raw21485step1 raw21485step1Labels := by
      have ha : raw21485step1 = (fun i j => raw21485step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21485step1 raw21485step0; decide +kernel
      have hl : raw21485step1Labels = raw21485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21485step0 raw21485step0Labels permutation34 permutation3
    mixedMoment B raw21485step1 raw21485step1Labels = mixedMoment B raw21485step2 raw21485step2Labels := by
      have ha : raw21485step2 = raw21485step1 := by apply Matrix.ext; unfold raw21485step2 raw21485step1; decide +kernel
      have hl : raw21485step1Labels = labelEmbedding6 ∘ raw21485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21485step1 raw21485step1Labels raw21485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical21489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21489 raw21489Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw21489 raw21489Labels = mixedMoment B raw21489step0 raw21489step0Labels := by
      have hz : ∀ j, raw21489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21489step0 = (fun i j => raw21489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21489step0 raw21489; decide +kernel
      have hl : raw21489step0Labels = raw21489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21489 raw21489Labels permutation346 hz
    mixedMoment B raw21489step0 raw21489step0Labels = mixedMoment B raw21489step1 raw21489step1Labels := by
      have ha : raw21489step1 = (fun i j => raw21489step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21489step1 raw21489step0; decide +kernel
      have hl : raw21489step1Labels = raw21489step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21489step0 raw21489step0Labels permutation34 permutation3
    mixedMoment B raw21489step1 raw21489step1Labels = mixedMoment B raw21489step2 raw21489step2Labels := by
      have ha : raw21489step2 = raw21489step1 := by apply Matrix.ext; unfold raw21489step2 raw21489step1; decide +kernel
      have hl : raw21489step1Labels = labelEmbedding6 ∘ raw21489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21489step1 raw21489step1Labels raw21489step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical21490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21490 raw21490Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw21490 raw21490Labels = mixedMoment B raw21490step0 raw21490step0Labels := by
      have hz : ∀ j, raw21490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21490step0 = (fun i j => raw21490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21490step0 raw21490; decide +kernel
      have hl : raw21490step0Labels = raw21490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21490 raw21490Labels permutation434 hz
    mixedMoment B raw21490step0 raw21490step0Labels = mixedMoment B raw21490step1 raw21490step1Labels := by
      have hz : ∀ j, raw21490step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21490step1 = (fun i j => raw21490step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21490step1 raw21490step0; decide +kernel
      have hl : raw21490step1Labels = raw21490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21490step0 raw21490step0Labels permutation80 hz
    mixedMoment B raw21490step1 raw21490step1Labels = mixedMoment B raw21490step2 raw21490step2Labels := by
      have ha : raw21490step2 = (fun i j => raw21490step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21490step2 raw21490step1; decide +kernel
      have hl : raw21490step2Labels = raw21490step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21490step1 raw21490step1Labels permutation8 permutation3
    mixedMoment B raw21490step2 raw21490step2Labels = mixedMoment B raw21490step3 raw21490step3Labels := by
      have ha : raw21490step3 = raw21490step2 := by apply Matrix.ext; unfold raw21490step3 raw21490step2; decide +kernel
      have hl : raw21490step2Labels = labelEmbedding6 ∘ raw21490step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21490step2 raw21490step2Labels raw21490step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4110 node4110Labels := by rfl

theorem canonical21491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21491 raw21491Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw21491 raw21491Labels = mixedMoment B raw21491step0 raw21491step0Labels := by
      have hz : ∀ j, raw21491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21491step0 = (fun i j => raw21491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21491step0 raw21491; decide +kernel
      have hl : raw21491step0Labels = raw21491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21491 raw21491Labels permutation434 hz
    mixedMoment B raw21491step0 raw21491step0Labels = mixedMoment B raw21491step1 raw21491step1Labels := by
      have hz : ∀ j, raw21491step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21491step1 = (fun i j => raw21491step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21491step1 raw21491step0; decide +kernel
      have hl : raw21491step1Labels = raw21491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21491step0 raw21491step0Labels permutation80 hz
    mixedMoment B raw21491step1 raw21491step1Labels = mixedMoment B raw21491step2 raw21491step2Labels := by
      have ha : raw21491step2 = (fun i j => raw21491step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21491step2 raw21491step1; decide +kernel
      have hl : raw21491step2Labels = raw21491step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21491step1 raw21491step1Labels permutation8 permutation3
    mixedMoment B raw21491step2 raw21491step2Labels = mixedMoment B raw21491step3 raw21491step3Labels := by
      have ha : raw21491step3 = raw21491step2 := by apply Matrix.ext; unfold raw21491step3 raw21491step2; decide +kernel
      have hl : raw21491step2Labels = labelEmbedding6 ∘ raw21491step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21491step2 raw21491step2Labels raw21491step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical21492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21492 raw21492Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw21492 raw21492Labels = mixedMoment B raw21492step0 raw21492step0Labels := by
      have hz : ∀ j, raw21492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21492step0 = (fun i j => raw21492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21492step0 raw21492; decide +kernel
      have hl : raw21492step0Labels = raw21492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21492 raw21492Labels permutation434 hz
    mixedMoment B raw21492step0 raw21492step0Labels = mixedMoment B raw21492step1 raw21492step1Labels := by
      have ha : raw21492step1 = (fun i j => raw21492step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21492step1 raw21492step0; decide +kernel
      have hl : raw21492step1Labels = raw21492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21492step0 raw21492step0Labels permutation38 permutation3
    mixedMoment B raw21492step1 raw21492step1Labels = mixedMoment B raw21492step2 raw21492step2Labels := by
      have ha : raw21492step2 = raw21492step1 := by apply Matrix.ext; unfold raw21492step2 raw21492step1; decide +kernel
      have hl : raw21492step1Labels = labelEmbedding6 ∘ raw21492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21492step1 raw21492step1Labels raw21492step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical21493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21493 raw21493Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw21493 raw21493Labels = mixedMoment B raw21493step0 raw21493step0Labels := by
      have hz : ∀ j, raw21493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21493step0 = (fun i j => raw21493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21493step0 raw21493; decide +kernel
      have hl : raw21493step0Labels = raw21493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21493 raw21493Labels permutation346 hz
    mixedMoment B raw21493step0 raw21493step0Labels = mixedMoment B raw21493step1 raw21493step1Labels := by
      have ha : raw21493step1 = (fun i j => raw21493step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21493step1 raw21493step0; decide +kernel
      have hl : raw21493step1Labels = raw21493step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21493step0 raw21493step0Labels permutation38 permutation3
    mixedMoment B raw21493step1 raw21493step1Labels = mixedMoment B raw21493step2 raw21493step2Labels := by
      have ha : raw21493step2 = raw21493step1 := by apply Matrix.ext; unfold raw21493step2 raw21493step1; decide +kernel
      have hl : raw21493step1Labels = labelEmbedding6 ∘ raw21493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21493step1 raw21493step1Labels raw21493step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

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

theorem canonical2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2217 raw2217Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw2217 raw2217Labels = mixedMoment B raw2217step0 raw2217step0Labels := by
      have ha : raw2217step0 = (fun i j => raw2217 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2217step0 raw2217; decide +kernel
      have hl : raw2217step0Labels = raw2217Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2217 raw2217Labels permutation8 permutation4
    mixedMoment B raw2217step0 raw2217step0Labels = mixedMoment B raw2217step1 raw2217step1Labels := by
      have ha : raw2217step1 = raw2217step0 := by apply Matrix.ext; unfold raw2217step1 raw2217step0; decide +kernel
      have hl : raw2217step0Labels = labelEmbedding7 ∘ raw2217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2217step0 raw2217step0Labels raw2217step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

theorem canonical2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2218 raw2218Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw2218 raw2218Labels = mixedMoment B raw2218step0 raw2218step0Labels := by
      have ha : raw2218step0 = (fun i j => raw2218 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2218step0 raw2218; decide +kernel
      have hl : raw2218step0Labels = raw2218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2218 raw2218Labels permutation8 permutation4
    _ = mixedMoment B node2605 node2605Labels := by rfl

theorem canonical2219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2219 raw2219Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw2219 raw2219Labels = mixedMoment B raw2219step0 raw2219step0Labels := by
      have ha : raw2219step0 = (fun i j => raw2219 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2219step0 raw2219; decide +kernel
      have hl : raw2219step0Labels = raw2219Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2219 raw2219Labels permutation8 permutation6
    mixedMoment B raw2219step0 raw2219step0Labels = mixedMoment B raw2219step1 raw2219step1Labels := by
      have ha : raw2219step1 = -raw2219step0 := by apply Matrix.ext; change ∀ i j, raw2219step1 i j = -(raw2219step0 i j); unfold raw2219step1 raw2219step0; decide +kernel
      have hl : raw2219step1Labels = raw2219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2219step1 raw2219step1Labels = mixedMoment B raw2219step2 raw2219step2Labels := by
      have ha : raw2219step2 = raw2219step1 := by apply Matrix.ext; unfold raw2219step2 raw2219step1; decide +kernel
      have hl : raw2219step1Labels = labelEmbedding1 ∘ raw2219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2219step1 raw2219step1Labels raw2219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3616 node3616Labels := by rfl

theorem canonical2301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2301 raw2301Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2301 raw2301Labels = mixedMoment B raw2301step0 raw2301step0Labels := by
      have ha : raw2301step0 = (fun i j => raw2301 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2301step0 raw2301; decide +kernel
      have hl : raw2301step0Labels = raw2301Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2301 raw2301Labels permutation8 permutation4
    mixedMoment B raw2301step0 raw2301step0Labels = mixedMoment B raw2301step1 raw2301step1Labels := by
      have ha : raw2301step1 = raw2301step0 := by apply Matrix.ext; unfold raw2301step1 raw2301step0; decide +kernel
      have hl : raw2301step0Labels = labelEmbedding7 ∘ raw2301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2301step0 raw2301step0Labels raw2301step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical2302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2302 raw2302Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2302 raw2302Labels = mixedMoment B raw2302step0 raw2302step0Labels := by
      have ha : raw2302step0 = (fun i j => raw2302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2302step0 raw2302; decide +kernel
      have hl : raw2302step0Labels = raw2302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2302 raw2302Labels permutation8 permutation4
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical2303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2303 raw2303Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw2303 raw2303Labels = mixedMoment B raw2303step0 raw2303step0Labels := by
      have ha : raw2303step0 = (fun i j => raw2303 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2303step0 raw2303; decide +kernel
      have hl : raw2303step0Labels = raw2303Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2303 raw2303Labels permutation10 permutation6
    mixedMoment B raw2303step0 raw2303step0Labels = mixedMoment B raw2303step1 raw2303step1Labels := by
      have ha : raw2303step1 = -raw2303step0 := by apply Matrix.ext; change ∀ i j, raw2303step1 i j = -(raw2303step0 i j); unfold raw2303step1 raw2303step0; decide +kernel
      have hl : raw2303step1Labels = raw2303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2303step1 raw2303step1Labels = mixedMoment B raw2303step2 raw2303step2Labels := by
      have ha : raw2303step2 = raw2303step1 := by apply Matrix.ext; unfold raw2303step2 raw2303step1; decide +kernel
      have hl : raw2303step1Labels = labelEmbedding1 ∘ raw2303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2303step1 raw2303step1Labels raw2303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3627 node3627Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23219 raw23219Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw23219 raw23219Labels = mixedMoment B raw23219step0 raw23219step0Labels := by
      have hz : ∀ j, raw23219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23219step0 = (fun i j => raw23219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23219step0 raw23219; decide +kernel
      have hl : raw23219step0Labels = raw23219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23219 raw23219Labels permutation434 hz
    mixedMoment B raw23219step0 raw23219step0Labels = mixedMoment B raw23219step1 raw23219step1Labels := by
      have ha : raw23219step1 = (fun i j => raw23219step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23219step1 raw23219step0; decide +kernel
      have hl : raw23219step1Labels = raw23219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23219step0 raw23219step0Labels permutation38 permutation3
    mixedMoment B raw23219step1 raw23219step1Labels = mixedMoment B raw23219step2 raw23219step2Labels := by
      have ha : raw23219step2 = raw23219step1 := by apply Matrix.ext; unfold raw23219step2 raw23219step1; decide +kernel
      have hl : raw23219step1Labels = labelEmbedding6 ∘ raw23219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23219step1 raw23219step1Labels raw23219step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical23220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23220 raw23220Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw23220 raw23220Labels = mixedMoment B raw23220step0 raw23220step0Labels := by
      have hz : ∀ j, raw23220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23220step0 = (fun i j => raw23220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23220step0 raw23220; decide +kernel
      have hl : raw23220step0Labels = raw23220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23220 raw23220Labels permutation346 hz
    mixedMoment B raw23220step0 raw23220step0Labels = mixedMoment B raw23220step1 raw23220step1Labels := by
      have ha : raw23220step1 = (fun i j => raw23220step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23220step1 raw23220step0; decide +kernel
      have hl : raw23220step1Labels = raw23220step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23220step0 raw23220step0Labels permutation38 permutation3
    mixedMoment B raw23220step1 raw23220step1Labels = mixedMoment B raw23220step2 raw23220step2Labels := by
      have ha : raw23220step2 = raw23220step1 := by apply Matrix.ext; unfold raw23220step2 raw23220step1; decide +kernel
      have hl : raw23220step1Labels = labelEmbedding6 ∘ raw23220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23220step1 raw23220step1Labels raw23220step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical23221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23221 raw23221Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw23221 raw23221Labels = mixedMoment B raw23221step0 raw23221step0Labels := by
      have hz : ∀ j, raw23221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23221step0 = (fun i j => raw23221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23221step0 raw23221; decide +kernel
      have hl : raw23221step0Labels = raw23221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23221 raw23221Labels permutation434 hz
    mixedMoment B raw23221step0 raw23221step0Labels = mixedMoment B raw23221step1 raw23221step1Labels := by
      have hz : ∀ j, raw23221step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23221step1 = (fun i j => raw23221step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23221step1 raw23221step0; decide +kernel
      have hl : raw23221step1Labels = raw23221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23221step0 raw23221step0Labels permutation80 hz
    mixedMoment B raw23221step1 raw23221step1Labels = mixedMoment B raw23221step2 raw23221step2Labels := by
      have ha : raw23221step2 = (fun i j => raw23221step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23221step2 raw23221step1; decide +kernel
      have hl : raw23221step2Labels = raw23221step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23221step1 raw23221step1Labels permutation9 permutation3
    mixedMoment B raw23221step2 raw23221step2Labels = mixedMoment B raw23221step3 raw23221step3Labels := by
      have ha : raw23221step3 = raw23221step2 := by apply Matrix.ext; unfold raw23221step3 raw23221step2; decide +kernel
      have hl : raw23221step2Labels = labelEmbedding6 ∘ raw23221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23221step2 raw23221step2Labels raw23221step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical23222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23222 raw23222Labels = mixedMoment B node4133 node4133Labels := by
  calc
    mixedMoment B raw23222 raw23222Labels = mixedMoment B raw23222step0 raw23222step0Labels := by
      have hz : ∀ j, raw23222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23222step0 = (fun i j => raw23222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23222step0 raw23222; decide +kernel
      have hl : raw23222step0Labels = raw23222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23222 raw23222Labels permutation434 hz
    mixedMoment B raw23222step0 raw23222step0Labels = mixedMoment B raw23222step1 raw23222step1Labels := by
      have hz : ∀ j, raw23222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23222step1 = (fun i j => raw23222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23222step1 raw23222step0; decide +kernel
      have hl : raw23222step1Labels = raw23222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23222step0 raw23222step0Labels permutation80 hz
    mixedMoment B raw23222step1 raw23222step1Labels = mixedMoment B raw23222step2 raw23222step2Labels := by
      have ha : raw23222step2 = (fun i j => raw23222step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23222step2 raw23222step1; decide +kernel
      have hl : raw23222step2Labels = raw23222step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23222step1 raw23222step1Labels permutation8 permutation3
    mixedMoment B raw23222step2 raw23222step2Labels = mixedMoment B raw23222step3 raw23222step3Labels := by
      have ha : raw23222step3 = raw23222step2 := by apply Matrix.ext; unfold raw23222step3 raw23222step2; decide +kernel
      have hl : raw23222step2Labels = labelEmbedding6 ∘ raw23222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23222step2 raw23222step2Labels raw23222step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4133 node4133Labels := by rfl

theorem canonical23223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23223 raw23223Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw23223 raw23223Labels = mixedMoment B raw23223step0 raw23223step0Labels := by
      have hz : ∀ j, raw23223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23223step0 = (fun i j => raw23223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23223step0 raw23223; decide +kernel
      have hl : raw23223step0Labels = raw23223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23223 raw23223Labels permutation434 hz
    mixedMoment B raw23223step0 raw23223step0Labels = mixedMoment B raw23223step1 raw23223step1Labels := by
      have ha : raw23223step1 = (fun i j => raw23223step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23223step1 raw23223step0; decide +kernel
      have hl : raw23223step1Labels = raw23223step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23223step0 raw23223step0Labels permutation38 permutation3
    mixedMoment B raw23223step1 raw23223step1Labels = mixedMoment B raw23223step2 raw23223step2Labels := by
      have ha : raw23223step2 = raw23223step1 := by apply Matrix.ext; unfold raw23223step2 raw23223step1; decide +kernel
      have hl : raw23223step1Labels = labelEmbedding6 ∘ raw23223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23223step1 raw23223step1Labels raw23223step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

theorem canonical23224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23224 raw23224Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw23224 raw23224Labels = mixedMoment B raw23224step0 raw23224step0Labels := by
      have hz : ∀ j, raw23224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23224step0 = (fun i j => raw23224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23224step0 raw23224; decide +kernel
      have hl : raw23224step0Labels = raw23224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23224 raw23224Labels permutation346 hz
    mixedMoment B raw23224step0 raw23224step0Labels = mixedMoment B raw23224step1 raw23224step1Labels := by
      have ha : raw23224step1 = (fun i j => raw23224step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23224step1 raw23224step0; decide +kernel
      have hl : raw23224step1Labels = raw23224step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23224step0 raw23224step0Labels permutation38 permutation3
    mixedMoment B raw23224step1 raw23224step1Labels = mixedMoment B raw23224step2 raw23224step2Labels := by
      have ha : raw23224step2 = raw23224step1 := by apply Matrix.ext; unfold raw23224step2 raw23224step1; decide +kernel
      have hl : raw23224step1Labels = labelEmbedding6 ∘ raw23224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23224step1 raw23224step1Labels raw23224step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

theorem canonical23225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23225 raw23225Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw23225 raw23225Labels = mixedMoment B raw23225step0 raw23225step0Labels := by
      have hz : ∀ j, raw23225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23225step0 = (fun i j => raw23225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23225step0 raw23225; decide +kernel
      have hl : raw23225step0Labels = raw23225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23225 raw23225Labels permutation434 hz
    mixedMoment B raw23225step0 raw23225step0Labels = mixedMoment B raw23225step1 raw23225step1Labels := by
      have hz : ∀ j, raw23225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23225step1 = (fun i j => raw23225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23225step1 raw23225step0; decide +kernel
      have hl : raw23225step1Labels = raw23225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23225step0 raw23225step0Labels permutation80 hz
    mixedMoment B raw23225step1 raw23225step1Labels = mixedMoment B raw23225step2 raw23225step2Labels := by
      have ha : raw23225step2 = (fun i j => raw23225step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23225step2 raw23225step1; decide +kernel
      have hl : raw23225step2Labels = raw23225step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23225step1 raw23225step1Labels permutation12 permutation3
    mixedMoment B raw23225step2 raw23225step2Labels = mixedMoment B raw23225step3 raw23225step3Labels := by
      have ha : raw23225step3 = raw23225step2 := by apply Matrix.ext; unfold raw23225step3 raw23225step2; decide +kernel
      have hl : raw23225step2Labels = labelEmbedding6 ∘ raw23225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23225step2 raw23225step2Labels raw23225step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical23226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23226 raw23226Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw23226 raw23226Labels = mixedMoment B raw23226step0 raw23226step0Labels := by
      have hz : ∀ j, raw23226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23226step0 = (fun i j => raw23226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23226step0 raw23226; decide +kernel
      have hl : raw23226step0Labels = raw23226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23226 raw23226Labels permutation434 hz
    mixedMoment B raw23226step0 raw23226step0Labels = mixedMoment B raw23226step1 raw23226step1Labels := by
      have ha : raw23226step1 = (fun i j => raw23226step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23226step1 raw23226step0; decide +kernel
      have hl : raw23226step1Labels = raw23226step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23226step0 raw23226step0Labels permutation32 permutation3
    mixedMoment B raw23226step1 raw23226step1Labels = mixedMoment B raw23226step2 raw23226step2Labels := by
      have ha : raw23226step2 = raw23226step1 := by apply Matrix.ext; unfold raw23226step2 raw23226step1; decide +kernel
      have hl : raw23226step1Labels = labelEmbedding6 ∘ raw23226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23226step1 raw23226step1Labels raw23226step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

theorem canonical23227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23227 raw23227Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23227 raw23227Labels = mixedMoment B raw23227step0 raw23227step0Labels := by
      have hz : ∀ j, raw23227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23227step0 = (fun i j => raw23227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23227step0 raw23227; decide +kernel
      have hl : raw23227step0Labels = raw23227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23227 raw23227Labels permutation434 hz
    mixedMoment B raw23227step0 raw23227step0Labels = mixedMoment B raw23227step1 raw23227step1Labels := by
      have ha : raw23227step1 = (fun i j => raw23227step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23227step1 raw23227step0; decide +kernel
      have hl : raw23227step1Labels = raw23227step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23227step0 raw23227step0Labels permutation32 permutation3
    mixedMoment B raw23227step1 raw23227step1Labels = mixedMoment B raw23227step2 raw23227step2Labels := by
      have ha : raw23227step2 = raw23227step1 := by apply Matrix.ext; unfold raw23227step2 raw23227step1; decide +kernel
      have hl : raw23227step1Labels = labelEmbedding6 ∘ raw23227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23227step1 raw23227step1Labels raw23227step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical23228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23228 raw23228Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw23228 raw23228Labels = mixedMoment B raw23228step0 raw23228step0Labels := by
      have ha : raw23228step0 = (fun i j => raw23228 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23228step0 raw23228; decide +kernel
      have hl : raw23228step0Labels = raw23228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23228 raw23228Labels permutation200 permutation3
    mixedMoment B raw23228step0 raw23228step0Labels = mixedMoment B raw23228step1 raw23228step1Labels := by
      have ha : raw23228step1 = raw23228step0 := by apply Matrix.ext; unfold raw23228step1 raw23228step0; decide +kernel
      have hl : raw23228step0Labels = labelEmbedding6 ∘ raw23228step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23228step0 raw23228step0Labels raw23228step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

theorem canonical23229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23229 raw23229Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23229 raw23229Labels = mixedMoment B raw23229step0 raw23229step0Labels := by
      have hz : ∀ j, raw23229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23229step0 = (fun i j => raw23229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23229step0 raw23229; decide +kernel
      have hl : raw23229step0Labels = raw23229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23229 raw23229Labels permutation434 hz
    mixedMoment B raw23229step0 raw23229step0Labels = mixedMoment B raw23229step1 raw23229step1Labels := by
      have ha : raw23229step1 = (fun i j => raw23229step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23229step1 raw23229step0; decide +kernel
      have hl : raw23229step1Labels = raw23229step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23229step0 raw23229step0Labels permutation36 permutation3
    mixedMoment B raw23229step1 raw23229step1Labels = mixedMoment B raw23229step2 raw23229step2Labels := by
      have ha : raw23229step2 = raw23229step1 := by apply Matrix.ext; unfold raw23229step2 raw23229step1; decide +kernel
      have hl : raw23229step1Labels = labelEmbedding6 ∘ raw23229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23229step1 raw23229step1Labels raw23229step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical23230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23230 raw23230Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw23230 raw23230Labels = mixedMoment B raw23230step0 raw23230step0Labels := by
      have hz : ∀ j, raw23230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23230step0 = (fun i j => raw23230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23230step0 raw23230; decide +kernel
      have hl : raw23230step0Labels = raw23230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23230 raw23230Labels permutation346 hz
    mixedMoment B raw23230step0 raw23230step0Labels = mixedMoment B raw23230step1 raw23230step1Labels := by
      have ha : raw23230step1 = (fun i j => raw23230step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23230step1 raw23230step0; decide +kernel
      have hl : raw23230step1Labels = raw23230step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23230step0 raw23230step0Labels permutation32 permutation3
    mixedMoment B raw23230step1 raw23230step1Labels = mixedMoment B raw23230step2 raw23230step2Labels := by
      have ha : raw23230step2 = raw23230step1 := by apply Matrix.ext; unfold raw23230step2 raw23230step1; decide +kernel
      have hl : raw23230step1Labels = labelEmbedding6 ∘ raw23230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23230step1 raw23230step1Labels raw23230step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

theorem canonical23231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23231 raw23231Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23231 raw23231Labels = mixedMoment B raw23231step0 raw23231step0Labels := by
      have hz : ∀ j, raw23231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23231step0 = (fun i j => raw23231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23231step0 raw23231; decide +kernel
      have hl : raw23231step0Labels = raw23231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23231 raw23231Labels permutation346 hz
    mixedMoment B raw23231step0 raw23231step0Labels = mixedMoment B raw23231step1 raw23231step1Labels := by
      have ha : raw23231step1 = (fun i j => raw23231step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23231step1 raw23231step0; decide +kernel
      have hl : raw23231step1Labels = raw23231step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23231step0 raw23231step0Labels permutation32 permutation3
    mixedMoment B raw23231step1 raw23231step1Labels = mixedMoment B raw23231step2 raw23231step2Labels := by
      have ha : raw23231step2 = raw23231step1 := by apply Matrix.ext; unfold raw23231step2 raw23231step1; decide +kernel
      have hl : raw23231step1Labels = labelEmbedding6 ∘ raw23231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23231step1 raw23231step1Labels raw23231step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical23232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23232 raw23232Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw23232 raw23232Labels = mixedMoment B raw23232step0 raw23232step0Labels := by
      have ha : raw23232step0 = (fun i j => raw23232 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23232step0 raw23232; decide +kernel
      have hl : raw23232step0Labels = raw23232Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23232 raw23232Labels permutation176 permutation3
    mixedMoment B raw23232step0 raw23232step0Labels = mixedMoment B raw23232step1 raw23232step1Labels := by
      have ha : raw23232step1 = raw23232step0 := by apply Matrix.ext; unfold raw23232step1 raw23232step0; decide +kernel
      have hl : raw23232step0Labels = labelEmbedding6 ∘ raw23232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23232step0 raw23232step0Labels raw23232step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

theorem canonical23233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23233 raw23233Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23233 raw23233Labels = mixedMoment B raw23233step0 raw23233step0Labels := by
      have hz : ∀ j, raw23233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23233step0 = (fun i j => raw23233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23233step0 raw23233; decide +kernel
      have hl : raw23233step0Labels = raw23233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23233 raw23233Labels permutation346 hz
    mixedMoment B raw23233step0 raw23233step0Labels = mixedMoment B raw23233step1 raw23233step1Labels := by
      have ha : raw23233step1 = (fun i j => raw23233step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23233step1 raw23233step0; decide +kernel
      have hl : raw23233step1Labels = raw23233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23233step0 raw23233step0Labels permutation36 permutation3
    mixedMoment B raw23233step1 raw23233step1Labels = mixedMoment B raw23233step2 raw23233step2Labels := by
      have ha : raw23233step2 = raw23233step1 := by apply Matrix.ext; unfold raw23233step2 raw23233step1; decide +kernel
      have hl : raw23233step1Labels = labelEmbedding6 ∘ raw23233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23233step1 raw23233step1Labels raw23233step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical23234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23234 raw23234Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw23234 raw23234Labels = mixedMoment B raw23234step0 raw23234step0Labels := by
      have hz : ∀ j, raw23234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23234step0 = (fun i j => raw23234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23234step0 raw23234; decide +kernel
      have hl : raw23234step0Labels = raw23234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23234 raw23234Labels permutation434 hz
    mixedMoment B raw23234step0 raw23234step0Labels = mixedMoment B raw23234step1 raw23234step1Labels := by
      have hz : ∀ j, raw23234step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23234step1 = (fun i j => raw23234step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23234step1 raw23234step0; decide +kernel
      have hl : raw23234step1Labels = raw23234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23234step0 raw23234step0Labels permutation80 hz
    mixedMoment B raw23234step1 raw23234step1Labels = mixedMoment B raw23234step2 raw23234step2Labels := by
      have ha : raw23234step2 = (fun i j => raw23234step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23234step2 raw23234step1; decide +kernel
      have hl : raw23234step2Labels = raw23234step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23234step1 raw23234step1Labels permutation9 permutation3
    mixedMoment B raw23234step2 raw23234step2Labels = mixedMoment B raw23234step3 raw23234step3Labels := by
      have ha : raw23234step3 = raw23234step2 := by apply Matrix.ext; unfold raw23234step3 raw23234step2; decide +kernel
      have hl : raw23234step2Labels = labelEmbedding6 ∘ raw23234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23234step2 raw23234step2Labels raw23234step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4110 node4110Labels := by rfl

theorem canonical23235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23235 raw23235Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23235 raw23235Labels = mixedMoment B raw23235step0 raw23235step0Labels := by
      have hz : ∀ j, raw23235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23235step0 = (fun i j => raw23235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23235step0 raw23235; decide +kernel
      have hl : raw23235step0Labels = raw23235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23235 raw23235Labels permutation434 hz
    mixedMoment B raw23235step0 raw23235step0Labels = mixedMoment B raw23235step1 raw23235step1Labels := by
      have hz : ∀ j, raw23235step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23235step1 = (fun i j => raw23235step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23235step1 raw23235step0; decide +kernel
      have hl : raw23235step1Labels = raw23235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23235step0 raw23235step0Labels permutation80 hz
    mixedMoment B raw23235step1 raw23235step1Labels = mixedMoment B raw23235step2 raw23235step2Labels := by
      have ha : raw23235step2 = (fun i j => raw23235step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23235step2 raw23235step1; decide +kernel
      have hl : raw23235step2Labels = raw23235step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23235step1 raw23235step1Labels permutation9 permutation3
    mixedMoment B raw23235step2 raw23235step2Labels = mixedMoment B raw23235step3 raw23235step3Labels := by
      have ha : raw23235step3 = raw23235step2 := by apply Matrix.ext; unfold raw23235step3 raw23235step2; decide +kernel
      have hl : raw23235step2Labels = labelEmbedding6 ∘ raw23235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23235step2 raw23235step2Labels raw23235step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical23236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23236 raw23236Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw23236 raw23236Labels = mixedMoment B raw23236step0 raw23236step0Labels := by
      have hz : ∀ j, raw23236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23236step0 = (fun i j => raw23236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23236step0 raw23236; decide +kernel
      have hl : raw23236step0Labels = raw23236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23236 raw23236Labels permutation434 hz
    mixedMoment B raw23236step0 raw23236step0Labels = mixedMoment B raw23236step1 raw23236step1Labels := by
      have ha : raw23236step1 = (fun i j => raw23236step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23236step1 raw23236step0; decide +kernel
      have hl : raw23236step1Labels = raw23236step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23236step0 raw23236step0Labels permutation39 permutation3
    mixedMoment B raw23236step1 raw23236step1Labels = mixedMoment B raw23236step2 raw23236step2Labels := by
      have ha : raw23236step2 = raw23236step1 := by apply Matrix.ext; unfold raw23236step2 raw23236step1; decide +kernel
      have hl : raw23236step1Labels = labelEmbedding6 ∘ raw23236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23236step1 raw23236step1Labels raw23236step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical23237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23237 raw23237Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw23237 raw23237Labels = mixedMoment B raw23237step0 raw23237step0Labels := by
      have hz : ∀ j, raw23237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23237step0 = (fun i j => raw23237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23237step0 raw23237; decide +kernel
      have hl : raw23237step0Labels = raw23237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23237 raw23237Labels permutation346 hz
    mixedMoment B raw23237step0 raw23237step0Labels = mixedMoment B raw23237step1 raw23237step1Labels := by
      have ha : raw23237step1 = (fun i j => raw23237step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23237step1 raw23237step0; decide +kernel
      have hl : raw23237step1Labels = raw23237step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23237step0 raw23237step0Labels permutation39 permutation3
    mixedMoment B raw23237step1 raw23237step1Labels = mixedMoment B raw23237step2 raw23237step2Labels := by
      have ha : raw23237step2 = raw23237step1 := by apply Matrix.ext; unfold raw23237step2 raw23237step1; decide +kernel
      have hl : raw23237step1Labels = labelEmbedding6 ∘ raw23237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23237step1 raw23237step1Labels raw23237step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical23238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23238 raw23238Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw23238 raw23238Labels = mixedMoment B raw23238step0 raw23238step0Labels := by
      have hz : ∀ j, raw23238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23238step0 = (fun i j => raw23238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23238step0 raw23238; decide +kernel
      have hl : raw23238step0Labels = raw23238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23238 raw23238Labels permutation434 hz
    mixedMoment B raw23238step0 raw23238step0Labels = mixedMoment B raw23238step1 raw23238step1Labels := by
      have hz : ∀ j, raw23238step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23238step1 = (fun i j => raw23238step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23238step1 raw23238step0; decide +kernel
      have hl : raw23238step1Labels = raw23238step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23238step0 raw23238step0Labels permutation80 hz
    mixedMoment B raw23238step1 raw23238step1Labels = mixedMoment B raw23238step2 raw23238step2Labels := by
      have ha : raw23238step2 = (fun i j => raw23238step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23238step2 raw23238step1; decide +kernel
      have hl : raw23238step2Labels = raw23238step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23238step1 raw23238step1Labels permutation9 permutation3
    mixedMoment B raw23238step2 raw23238step2Labels = mixedMoment B raw23238step3 raw23238step3Labels := by
      have ha : raw23238step3 = raw23238step2 := by apply Matrix.ext; unfold raw23238step3 raw23238step2; decide +kernel
      have hl : raw23238step2Labels = labelEmbedding6 ∘ raw23238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23238step2 raw23238step2Labels raw23238step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

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

theorem canonical270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw270 raw270Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw270 raw270Labels = mixedMoment B raw270step0 raw270step0Labels := by
      have ha : raw270step0 = (fun i j => raw270 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw270step0 raw270; decide +kernel
      have hl : raw270step0Labels = raw270Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw270 raw270Labels permutation8 permutation5
    mixedMoment B raw270step0 raw270step0Labels = mixedMoment B raw270step1 raw270step1Labels := by
      have ha : raw270step1 = raw270step0 := by apply Matrix.ext; unfold raw270step1 raw270step0; decide +kernel
      have hl : raw270step0Labels = labelEmbedding1 ∘ raw270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw270step0 raw270step0Labels raw270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw271 raw271Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw271 raw271Labels = mixedMoment B raw271step0 raw271step0Labels := by
      have ha : raw271step0 = (fun i j => raw271 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw271step0 raw271; decide +kernel
      have hl : raw271step0Labels = raw271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw271 raw271Labels permutation8 permutation5
    _ = mixedMoment B node404 node404Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2771 raw2771Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2771 raw2771Labels = mixedMoment B raw2771step0 raw2771step0Labels := by
      have hz : ∀ j, raw2771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2771step0 = (fun i j => raw2771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2771step0 raw2771; decide +kernel
      have hl : raw2771step0Labels = raw2771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2771 raw2771Labels permutation434 hz
    mixedMoment B raw2771step0 raw2771step0Labels = mixedMoment B raw2771step1 raw2771step1Labels := by
      have hz : ∀ j, raw2771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2771step1 = (fun i j => raw2771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2771step1 raw2771step0; decide +kernel
      have hl : raw2771step1Labels = raw2771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2771step0 raw2771step0Labels permutation80 hz
    mixedMoment B raw2771step1 raw2771step1Labels = mixedMoment B raw2771step2 raw2771step2Labels := by
      have ha : raw2771step2 = (fun i j => raw2771step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2771step2 raw2771step1; decide +kernel
      have hl : raw2771step2Labels = raw2771step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2771step1 raw2771step1Labels permutation8 permutation3
    mixedMoment B raw2771step2 raw2771step2Labels = mixedMoment B raw2771step3 raw2771step3Labels := by
      have ha : raw2771step3 = raw2771step2 := by apply Matrix.ext; unfold raw2771step3 raw2771step2; decide +kernel
      have hl : raw2771step2Labels = labelEmbedding6 ∘ raw2771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2771step2 raw2771step2Labels raw2771step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4935 raw4935Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw4935 raw4935Labels = mixedMoment B raw4935step0 raw4935step0Labels := by
      have hz : ∀ j, raw4935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4935step0 = (fun i j => raw4935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4935step0 raw4935; decide +kernel
      have hl : raw4935step0Labels = raw4935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4935 raw4935Labels permutation434 hz
    mixedMoment B raw4935step0 raw4935step0Labels = mixedMoment B raw4935step1 raw4935step1Labels := by
      have hz : ∀ j, raw4935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4935step1 = (fun i j => raw4935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4935step1 raw4935step0; decide +kernel
      have hl : raw4935step1Labels = raw4935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4935step0 raw4935step0Labels permutation80 hz
    mixedMoment B raw4935step1 raw4935step1Labels = mixedMoment B raw4935step2 raw4935step2Labels := by
      have ha : raw4935step2 = (fun i j => raw4935step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4935step2 raw4935step1; decide +kernel
      have hl : raw4935step2Labels = raw4935step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4935step1 raw4935step1Labels permutation8 permutation3
    mixedMoment B raw4935step2 raw4935step2Labels = mixedMoment B raw4935step3 raw4935step3Labels := by
      have ha : raw4935step3 = raw4935step2 := by apply Matrix.ext; unfold raw4935step3 raw4935step2; decide +kernel
      have hl : raw4935step2Labels = labelEmbedding6 ∘ raw4935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4935step2 raw4935step2Labels raw4935step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

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

theorem canonical693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw693 raw693Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw693 raw693Labels = mixedMoment B raw693step0 raw693step0Labels := by
      have ha : raw693step0 = (fun i j => raw693 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw693step0 raw693; decide +kernel
      have hl : raw693step0Labels = raw693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw693 raw693Labels permutation32 permutation4
    mixedMoment B raw693step0 raw693step0Labels = mixedMoment B raw693step1 raw693step1Labels := by
      have ha : raw693step1 = raw693step0 := by apply Matrix.ext; unfold raw693step1 raw693step0; decide +kernel
      have hl : raw693step0Labels = labelEmbedding7 ∘ raw693step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw693step0 raw693step0Labels raw693step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

theorem canonical694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw694 raw694Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw694 raw694Labels = mixedMoment B raw694step0 raw694step0Labels := by
      have ha : raw694step0 = (fun i j => raw694 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw694step0 raw694; decide +kernel
      have hl : raw694step0Labels = raw694Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw694 raw694Labels permutation32 permutation4
    _ = mixedMoment B node544 node544Labels := by rfl

theorem canonical695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw695 raw695Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw695 raw695Labels = mixedMoment B raw695step0 raw695step0Labels := by
      have ha : raw695step0 = (fun i j => raw695 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw695step0 raw695; decide +kernel
      have hl : raw695step0Labels = raw695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw695 raw695Labels permutation32 permutation6
    mixedMoment B raw695step0 raw695step0Labels = mixedMoment B raw695step1 raw695step1Labels := by
      have ha : raw695step1 = -raw695step0 := by apply Matrix.ext; change ∀ i j, raw695step1 i j = -(raw695step0 i j); unfold raw695step1 raw695step0; decide +kernel
      have hl : raw695step1Labels = raw695step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw695step1 raw695step1Labels = mixedMoment B raw695step2 raw695step2Labels := by
      have ha : raw695step2 = raw695step1 := by apply Matrix.ext; unfold raw695step2 raw695step1; decide +kernel
      have hl : raw695step1Labels = labelEmbedding1 ∘ raw695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw695step1 raw695step1Labels raw695step2Labels labelEmbedding1 hl
    _ = mixedMoment B node682 node682Labels := by rfl

theorem canonical702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw702 raw702Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw702 raw702Labels = mixedMoment B raw702step0 raw702step0Labels := by
      have ha : raw702step0 = (fun i j => raw702 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw702step0 raw702; decide +kernel
      have hl : raw702step0Labels = raw702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw702 raw702Labels permutation8 permutation4
    mixedMoment B raw702step0 raw702step0Labels = mixedMoment B raw702step1 raw702step1Labels := by
      have ha : raw702step1 = raw702step0 := by apply Matrix.ext; unfold raw702step1 raw702step0; decide +kernel
      have hl : raw702step0Labels = labelEmbedding7 ∘ raw702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw702step0 raw702step0Labels raw702step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4110 node4110Labels := by rfl

theorem canonical703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw703 raw703Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw703 raw703Labels = mixedMoment B raw703step0 raw703step0Labels := by
      have ha : raw703step0 = (fun i j => raw703 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw703step0 raw703; decide +kernel
      have hl : raw703step0Labels = raw703Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw703 raw703Labels permutation8 permutation4
    _ = mixedMoment B node547 node547Labels := by rfl

theorem canonical704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw704 raw704Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw704 raw704Labels = mixedMoment B raw704step0 raw704step0Labels := by
      have ha : raw704step0 = (fun i j => raw704 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw704step0 raw704; decide +kernel
      have hl : raw704step0Labels = raw704Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw704 raw704Labels permutation8 permutation6
    mixedMoment B raw704step0 raw704step0Labels = mixedMoment B raw704step1 raw704step1Labels := by
      have ha : raw704step1 = -raw704step0 := by apply Matrix.ext; change ∀ i j, raw704step1 i j = -(raw704step0 i j); unfold raw704step1 raw704step0; decide +kernel
      have hl : raw704step1Labels = raw704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw704step1 raw704step1Labels = mixedMoment B raw704step2 raw704step2Labels := by
      have ha : raw704step2 = raw704step1 := by apply Matrix.ext; unfold raw704step2 raw704step1; decide +kernel
      have hl : raw704step1Labels = labelEmbedding1 ∘ raw704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw704step1 raw704step1Labels raw704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node684 node684Labels := by rfl

theorem canonical744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw744 raw744Labels = mixedMoment B node4133 node4133Labels := by
  calc
    mixedMoment B raw744 raw744Labels = mixedMoment B raw744step0 raw744step0Labels := by
      have ha : raw744step0 = (fun i j => raw744 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw744step0 raw744; decide +kernel
      have hl : raw744step0Labels = raw744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw744 raw744Labels permutation8 permutation4
    mixedMoment B raw744step0 raw744step0Labels = mixedMoment B raw744step1 raw744step1Labels := by
      have ha : raw744step1 = raw744step0 := by apply Matrix.ext; unfold raw744step1 raw744step0; decide +kernel
      have hl : raw744step0Labels = labelEmbedding7 ∘ raw744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw744step0 raw744step0Labels raw744step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4133 node4133Labels := by rfl

theorem canonical745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw745 raw745Labels = mixedMoment B node563 node563Labels := by
  calc
    mixedMoment B raw745 raw745Labels = mixedMoment B raw745step0 raw745step0Labels := by
      have ha : raw745step0 = (fun i j => raw745 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw745step0 raw745; decide +kernel
      have hl : raw745step0Labels = raw745Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw745 raw745Labels permutation8 permutation4
    _ = mixedMoment B node563 node563Labels := by rfl

theorem canonical746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw746 raw746Labels = mixedMoment B node692 node692Labels := by
  calc
    mixedMoment B raw746 raw746Labels = mixedMoment B raw746step0 raw746step0Labels := by
      have ha : raw746step0 = (fun i j => raw746 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw746step0 raw746; decide +kernel
      have hl : raw746step0Labels = raw746Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw746 raw746Labels permutation11 permutation6
    mixedMoment B raw746step0 raw746step0Labels = mixedMoment B raw746step1 raw746step1Labels := by
      have ha : raw746step1 = -raw746step0 := by apply Matrix.ext; change ∀ i j, raw746step1 i j = -(raw746step0 i j); unfold raw746step1 raw746step0; decide +kernel
      have hl : raw746step1Labels = raw746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw746step1 raw746step1Labels = mixedMoment B raw746step2 raw746step2Labels := by
      have ha : raw746step2 = raw746step1 := by apply Matrix.ext; unfold raw746step2 raw746step1; decide +kernel
      have hl : raw746step1Labels = labelEmbedding1 ∘ raw746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw746step1 raw746step1Labels raw746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node692 node692Labels := by rfl

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

theorem canonical1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1038 raw1038Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw1038 raw1038Labels = mixedMoment B raw1038step0 raw1038step0Labels := by
      have ha : raw1038step0 = (fun i j => raw1038 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1038step0 raw1038; decide +kernel
      have hl : raw1038step0Labels = raw1038Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1038 raw1038Labels permutation152 permutation4
    mixedMoment B raw1038step0 raw1038step0Labels = mixedMoment B raw1038step1 raw1038step1Labels := by
      have ha : raw1038step1 = raw1038step0 := by apply Matrix.ext; unfold raw1038step1 raw1038step0; decide +kernel
      have hl : raw1038step0Labels = labelEmbedding7 ∘ raw1038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1038step0 raw1038step0Labels raw1038step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

theorem canonical1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1039 raw1039Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw1039 raw1039Labels = mixedMoment B raw1039step0 raw1039step0Labels := by
      have ha : raw1039step0 = (fun i j => raw1039 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1039step0 raw1039; decide +kernel
      have hl : raw1039step0Labels = raw1039Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1039 raw1039Labels permutation152 permutation4
    _ = mixedMoment B node870 node870Labels := by rfl

theorem canonical1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1040 raw1040Labels = mixedMoment B node1567 node1567Labels := by
  calc
    mixedMoment B raw1040 raw1040Labels = mixedMoment B raw1040step0 raw1040step0Labels := by
      have ha : raw1040step0 = (fun i j => raw1040 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1040step0 raw1040; decide +kernel
      have hl : raw1040step0Labels = raw1040Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1040 raw1040Labels permutation152 permutation6
    mixedMoment B raw1040step0 raw1040step0Labels = mixedMoment B raw1040step1 raw1040step1Labels := by
      have ha : raw1040step1 = -raw1040step0 := by apply Matrix.ext; change ∀ i j, raw1040step1 i j = -(raw1040step0 i j); unfold raw1040step1 raw1040step0; decide +kernel
      have hl : raw1040step1Labels = raw1040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1040step1 raw1040step1Labels = mixedMoment B raw1040step2 raw1040step2Labels := by
      have ha : raw1040step2 = raw1040step1 := by apply Matrix.ext; unfold raw1040step2 raw1040step1; decide +kernel
      have hl : raw1040step1Labels = labelEmbedding1 ∘ raw1040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1040step1 raw1040step1Labels raw1040step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1567 node1567Labels := by rfl

theorem canonical1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1047 raw1047Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw1047 raw1047Labels = mixedMoment B raw1047step0 raw1047step0Labels := by
      have ha : raw1047step0 = (fun i j => raw1047 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1047step0 raw1047; decide +kernel
      have hl : raw1047step0Labels = raw1047Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1047 raw1047Labels permutation32 permutation4
    mixedMoment B raw1047step0 raw1047step0Labels = mixedMoment B raw1047step1 raw1047step1Labels := by
      have ha : raw1047step1 = raw1047step0 := by apply Matrix.ext; unfold raw1047step1 raw1047step0; decide +kernel
      have hl : raw1047step0Labels = labelEmbedding7 ∘ raw1047step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1047step0 raw1047step0Labels raw1047step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical1048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1048 raw1048Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw1048 raw1048Labels = mixedMoment B raw1048step0 raw1048step0Labels := by
      have ha : raw1048step0 = (fun i j => raw1048 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1048step0 raw1048; decide +kernel
      have hl : raw1048step0Labels = raw1048Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1048 raw1048Labels permutation32 permutation4
    _ = mixedMoment B node873 node873Labels := by rfl

theorem canonical1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1049 raw1049Labels = mixedMoment B node1569 node1569Labels := by
  calc
    mixedMoment B raw1049 raw1049Labels = mixedMoment B raw1049step0 raw1049step0Labels := by
      have ha : raw1049step0 = (fun i j => raw1049 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1049step0 raw1049; decide +kernel
      have hl : raw1049step0Labels = raw1049Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1049 raw1049Labels permutation32 permutation6
    mixedMoment B raw1049step0 raw1049step0Labels = mixedMoment B raw1049step1 raw1049step1Labels := by
      have ha : raw1049step1 = -raw1049step0 := by apply Matrix.ext; change ∀ i j, raw1049step1 i j = -(raw1049step0 i j); unfold raw1049step1 raw1049step0; decide +kernel
      have hl : raw1049step1Labels = raw1049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1049step1 raw1049step1Labels = mixedMoment B raw1049step2 raw1049step2Labels := by
      have ha : raw1049step2 = raw1049step1 := by apply Matrix.ext; unfold raw1049step2 raw1049step1; decide +kernel
      have hl : raw1049step1Labels = labelEmbedding1 ∘ raw1049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1049step1 raw1049step1Labels raw1049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1569 node1569Labels := by rfl

theorem canonical1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1083 raw1083Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw1083 raw1083Labels = mixedMoment B raw1083step0 raw1083step0Labels := by
      have ha : raw1083step0 = (fun i j => raw1083 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1083step0 raw1083; decide +kernel
      have hl : raw1083step0Labels = raw1083Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1083 raw1083Labels permutation32 permutation4
    mixedMoment B raw1083step0 raw1083step0Labels = mixedMoment B raw1083step1 raw1083step1Labels := by
      have ha : raw1083step1 = raw1083step0 := by apply Matrix.ext; unfold raw1083step1 raw1083step0; decide +kernel
      have hl : raw1083step0Labels = labelEmbedding7 ∘ raw1083step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1083step0 raw1083step0Labels raw1083step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

theorem canonical1084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1084 raw1084Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw1084 raw1084Labels = mixedMoment B raw1084step0 raw1084step0Labels := by
      have ha : raw1084step0 = (fun i j => raw1084 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1084step0 raw1084; decide +kernel
      have hl : raw1084step0Labels = raw1084Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1084 raw1084Labels permutation32 permutation4
    _ = mixedMoment B node892 node892Labels := by rfl

theorem canonical1085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1085 raw1085Labels = mixedMoment B node1575 node1575Labels := by
  calc
    mixedMoment B raw1085 raw1085Labels = mixedMoment B raw1085step0 raw1085step0Labels := by
      have ha : raw1085step0 = (fun i j => raw1085 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1085step0 raw1085; decide +kernel
      have hl : raw1085step0Labels = raw1085Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1085 raw1085Labels permutation35 permutation6
    mixedMoment B raw1085step0 raw1085step0Labels = mixedMoment B raw1085step1 raw1085step1Labels := by
      have ha : raw1085step1 = -raw1085step0 := by apply Matrix.ext; change ∀ i j, raw1085step1 i j = -(raw1085step0 i j); unfold raw1085step1 raw1085step0; decide +kernel
      have hl : raw1085step1Labels = raw1085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1085step1 raw1085step1Labels = mixedMoment B raw1085step2 raw1085step2Labels := by
      have ha : raw1085step2 = raw1085step1 := by apply Matrix.ext; unfold raw1085step2 raw1085step1; decide +kernel
      have hl : raw1085step1Labels = labelEmbedding1 ∘ raw1085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1085step1 raw1085step1Labels raw1085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1575 node1575Labels := by rfl

theorem canonical1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1149 raw1149Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw1149 raw1149Labels = mixedMoment B raw1149step0 raw1149step0Labels := by
      have ha : raw1149step0 = (fun i j => raw1149 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1149step0 raw1149; decide +kernel
      have hl : raw1149step0Labels = raw1149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1149 raw1149Labels permutation32 permutation4
    mixedMoment B raw1149step0 raw1149step0Labels = mixedMoment B raw1149step1 raw1149step1Labels := by
      have ha : raw1149step1 = raw1149step0 := by apply Matrix.ext; unfold raw1149step1 raw1149step0; decide +kernel
      have hl : raw1149step0Labels = labelEmbedding7 ∘ raw1149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1149step0 raw1149step0Labels raw1149step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1150 raw1150Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw1150 raw1150Labels = mixedMoment B raw1150step0 raw1150step0Labels := by
      have ha : raw1150step0 = (fun i j => raw1150 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1150step0 raw1150; decide +kernel
      have hl : raw1150step0Labels = raw1150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1150 raw1150Labels permutation32 permutation4
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1151 raw1151Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw1151 raw1151Labels = mixedMoment B raw1151step0 raw1151step0Labels := by
      have ha : raw1151step0 = (fun i j => raw1151 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1151step0 raw1151; decide +kernel
      have hl : raw1151step0Labels = raw1151Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1151 raw1151Labels permutation32 permutation6
    mixedMoment B raw1151step0 raw1151step0Labels = mixedMoment B raw1151step1 raw1151step1Labels := by
      have ha : raw1151step1 = -raw1151step0 := by apply Matrix.ext; change ∀ i j, raw1151step1 i j = -(raw1151step0 i j); unfold raw1151step1 raw1151step0; decide +kernel
      have hl : raw1151step1Labels = raw1151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1151step1 raw1151step1Labels = mixedMoment B raw1151step2 raw1151step2Labels := by
      have ha : raw1151step2 = raw1151step1 := by apply Matrix.ext; unfold raw1151step2 raw1151step1; decide +kernel
      have hl : raw1151step1Labels = labelEmbedding1 ∘ raw1151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1151step1 raw1151step1Labels raw1151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

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

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

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

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw672 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw672 = injectiveMoment H raw672step0 := by
      have heq : raw672step0 = -raw672 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw672).symm
    injectiveMoment H raw672step0 = injectiveMoment H raw672step1 := by
      have heq : raw672step1 = (fun i j => raw672step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw672step0 permutation9 permutation8
    _ = injectiveMoment H node175 := by rfl

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

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
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

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw872 = injectiveMoment H node25 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
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

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

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

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
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

theorem sound25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node25 = Sparse.eval value25 (momentVector H) := by
  have heq : pivotMatrix25 = (fun u v => node25 (pivotPermutation25 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node25 = injectiveMoment H pivotMatrix25 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix25 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix25 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (1 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (2 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node25 + (injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value25, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw781 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw781 = injectiveMoment H raw781step0 := by
      have heq : raw781step0 = -raw781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw781).symm
    injectiveMoment H raw781step0 = injectiveMoment H raw781step1 := by
      have heq : raw781step1 = (fun i j => raw781step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw781step0 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

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

theorem sound175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node175 = Sparse.eval value175 (momentVector H) := by
  have heq : pivotMatrix175 = (fun u v => node175 (pivotPermutation175 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node175 = injectiveMoment H pivotMatrix175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix175 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix175 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (0 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (2 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node175 + (injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value175, value35, value56, Sparse.eval] at hc ⊢
  linarith

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node344 node344Labels = Sparse.eval singlePairValue344 (familyPairVector B) := by
  have hp := single_label_three B hB node344
  have hl : node344Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node344 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node344 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node344 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node344 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value175 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 4) = PairSemantics.raw672 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node344 PairSemantics.raw672; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical672 hH).trans (PairSemantics.sound175 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue344, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value65, PairSemantics.value175, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node404 node404Labels = Sparse.eval singlePairValue404 (familyPairVector B) := by
  have hp := single_label_three B hB node404
  have hl : node404Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node404 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node404 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node404 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node404 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value181 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 4) = PairSemantics.raw781 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node404 PairSemantics.raw781; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical781 hH).trans (PairSemantics.sound181 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue404, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value65, PairSemantics.value181, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2605 node2605Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node344 node344Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw248 singletonSmall2605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2605) = raw248Labels := by decide +kernel
  rw [hl, canonical248 B hB] at h
  have hc0 : mixedMoment B raw248 (Fin.cases (0 : Fin 1) singletonSmall2605) =
      mixedMoment B node344 node344Labels := by
    have ha : raw248 = raw249 := by apply Matrix.ext; unfold raw248 raw249; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2605 = raw249Labels := by decide +kernel
    rw [ha, hj, canonical249 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2767 node2767Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw270 singletonSmall2767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2767) = raw270Labels := by decide +kernel
  rw [hl, canonical270 B hB] at h
  have hc0 : mixedMoment B raw270 (Fin.cases (0 : Fin 1) singletonSmall2767) =
      mixedMoment B node404 node404Labels := by
    have ha : raw270 = raw271 := by apply Matrix.ext; unfold raw270 raw271; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2767 = raw271Labels := by decide +kernel
    rw [ha, hj, canonical271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4107 node4107Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node544 node544Labels + mixedMoment B node682 node682Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw693 singletonSmall4107
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4107) = raw693Labels := by decide +kernel
  rw [hl, canonical693 B hB] at h
  have hc0 : mixedMoment B raw693 (Fin.cases (0 : Fin 2) singletonSmall4107) =
      mixedMoment B node544 node544Labels := by
    have ha : raw693 = raw694 := by apply Matrix.ext; unfold raw693 raw694; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4107 = raw694Labels := by decide +kernel
    rw [ha, hj, canonical694 B hB]
  have hc1 : mixedMoment B raw693 (Fin.cases (1 : Fin 2) singletonSmall4107) =
      mixedMoment B node682 node682Labels := by
    have ha : raw693 = raw695 := by apply Matrix.ext; unfold raw693 raw695; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4107 = raw695Labels := by decide +kernel
    rw [ha, hj, canonical695 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4110 node4110Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node547 node547Labels + mixedMoment B node684 node684Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw702 singletonSmall4110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4110) = raw702Labels := by decide +kernel
  rw [hl, canonical702 B hB] at h
  have hc0 : mixedMoment B raw702 (Fin.cases (0 : Fin 2) singletonSmall4110) =
      mixedMoment B node547 node547Labels := by
    have ha : raw702 = raw703 := by apply Matrix.ext; unfold raw702 raw703; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4110 = raw703Labels := by decide +kernel
    rw [ha, hj, canonical703 B hB]
  have hc1 : mixedMoment B raw702 (Fin.cases (1 : Fin 2) singletonSmall4110) =
      mixedMoment B node684 node684Labels := by
    have ha : raw702 = raw704 := by apply Matrix.ext; unfold raw702 raw704; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4110 = raw704Labels := by decide +kernel
    rw [ha, hj, canonical704 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4133 node4133Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node563 node563Labels + mixedMoment B node692 node692Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw744 singletonSmall4133
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4133) = raw744Labels := by decide +kernel
  rw [hl, canonical744 B hB] at h
  have hc0 : mixedMoment B raw744 (Fin.cases (0 : Fin 2) singletonSmall4133) =
      mixedMoment B node563 node563Labels := by
    have ha : raw744 = raw745 := by apply Matrix.ext; unfold raw744 raw745; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4133 = raw745Labels := by decide +kernel
    rw [ha, hj, canonical745 B hB]
  have hc1 : mixedMoment B raw744 (Fin.cases (1 : Fin 2) singletonSmall4133) =
      mixedMoment B node692 node692Labels := by
    have ha : raw744 = raw746 := by apply Matrix.ext; unfold raw744 raw746; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4133 = raw746Labels := by decide +kernel
    rw [ha, hj, canonical746 B hB]
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

theorem singleton4292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4292 node4292Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node870 node870Labels + mixedMoment B node1567 node1567Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1038 singletonSmall4292
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4292) = raw1038Labels := by decide +kernel
  rw [hl, canonical1038 B hB] at h
  have hc0 : mixedMoment B raw1038 (Fin.cases (0 : Fin 2) singletonSmall4292) =
      mixedMoment B node870 node870Labels := by
    have ha : raw1038 = raw1039 := by apply Matrix.ext; unfold raw1038 raw1039; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4292 = raw1039Labels := by decide +kernel
    rw [ha, hj, canonical1039 B hB]
  have hc1 : mixedMoment B raw1038 (Fin.cases (1 : Fin 2) singletonSmall4292) =
      mixedMoment B node1567 node1567Labels := by
    have ha : raw1038 = raw1040 := by apply Matrix.ext; unfold raw1038 raw1040; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4292 = raw1040Labels := by decide +kernel
    rw [ha, hj, canonical1040 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4295 node4295Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node873 node873Labels + mixedMoment B node1569 node1569Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1047 singletonSmall4295
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4295) = raw1047Labels := by decide +kernel
  rw [hl, canonical1047 B hB] at h
  have hc0 : mixedMoment B raw1047 (Fin.cases (0 : Fin 2) singletonSmall4295) =
      mixedMoment B node873 node873Labels := by
    have ha : raw1047 = raw1048 := by apply Matrix.ext; unfold raw1047 raw1048; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4295 = raw1048Labels := by decide +kernel
    rw [ha, hj, canonical1048 B hB]
  have hc1 : mixedMoment B raw1047 (Fin.cases (1 : Fin 2) singletonSmall4295) =
      mixedMoment B node1569 node1569Labels := by
    have ha : raw1047 = raw1049 := by apply Matrix.ext; unfold raw1047 raw1049; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4295 = raw1049Labels := by decide +kernel
    rw [ha, hj, canonical1049 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4314 node4314Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node892 node892Labels + mixedMoment B node1575 node1575Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1083 singletonSmall4314
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4314) = raw1083Labels := by decide +kernel
  rw [hl, canonical1083 B hB] at h
  have hc0 : mixedMoment B raw1083 (Fin.cases (0 : Fin 2) singletonSmall4314) =
      mixedMoment B node892 node892Labels := by
    have ha : raw1083 = raw1084 := by apply Matrix.ext; unfold raw1083 raw1084; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4314 = raw1084Labels := by decide +kernel
    rw [ha, hj, canonical1084 B hB]
  have hc1 : mixedMoment B raw1083 (Fin.cases (1 : Fin 2) singletonSmall4314) =
      mixedMoment B node1575 node1575Labels := by
    have ha : raw1083 = raw1085 := by apply Matrix.ext; unfold raw1083 raw1085; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4314 = raw1085Labels := by decide +kernel
    rw [ha, hj, canonical1085 B hB]
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

theorem singleton4355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4355 node4355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node933 node933Labels + mixedMoment B node1691 node1691Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1149 singletonSmall4355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4355) = raw1149Labels := by decide +kernel
  rw [hl, canonical1149 B hB] at h
  have hc0 : mixedMoment B raw1149 (Fin.cases (0 : Fin 2) singletonSmall4355) =
      mixedMoment B node933 node933Labels := by
    have ha : raw1149 = raw1150 := by apply Matrix.ext; unfold raw1149 raw1150; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4355 = raw1150Labels := by decide +kernel
    rw [ha, hj, canonical1150 B hB]
  have hc1 : mixedMoment B raw1149 (Fin.cases (1 : Fin 2) singletonSmall4355) =
      mixedMoment B node1691 node1691Labels := by
    have ha : raw1149 = raw1151 := by apply Matrix.ext; unfold raw1149 raw1151; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4355 = raw1151Labels := by decide +kernel
    rw [ha, hj, canonical1151 B hB]
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

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
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

theorem singleton4499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4499 node4499Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1083 node1083Labels + mixedMoment B node1728 node1728Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1299 singletonSmall4499
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4499) = raw1299Labels := by decide +kernel
  rw [hl, canonical1299 B hB] at h
  have hc0 : mixedMoment B raw1299 (Fin.cases (0 : Fin 2) singletonSmall4499) =
      mixedMoment B node1083 node1083Labels := by
    have ha : raw1299 = raw1300 := by apply Matrix.ext; unfold raw1299 raw1300; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4499 = raw1300Labels := by decide +kernel
    rw [ha, hj, canonical1300 B hB]
  have hc1 : mixedMoment B raw1299 (Fin.cases (1 : Fin 2) singletonSmall4499) =
      mixedMoment B node1728 node1728Labels := by
    have ha : raw1299 = raw1301 := by apply Matrix.ext; unfold raw1299 raw1301; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4499 = raw1301Labels := by decide +kernel
    rw [ha, hj, canonical1301 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5081 node5081Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2489 node2489Labels + mixedMoment B node3482 node3482Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2109 singletonSmall5081
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5081) = raw2109Labels := by decide +kernel
  rw [hl, canonical2109 B hB] at h
  have hc0 : mixedMoment B raw2109 (Fin.cases (0 : Fin 2) singletonSmall5081) =
      mixedMoment B node2489 node2489Labels := by
    have ha : raw2109 = raw2110 := by apply Matrix.ext; unfold raw2109 raw2110; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5081 = raw2110Labels := by decide +kernel
    rw [ha, hj, canonical2110 B hB]
  have hc1 : mixedMoment B raw2109 (Fin.cases (1 : Fin 2) singletonSmall5081) =
      mixedMoment B node3482 node3482Labels := by
    have ha : raw2109 = raw2111 := by apply Matrix.ext; unfold raw2109 raw2111; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5081 = raw2111Labels := by decide +kernel
    rw [ha, hj, canonical2111 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5177 node5177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2605 node2605Labels + mixedMoment B node3616 node3616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2217 singletonSmall5177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5177) = raw2217Labels := by decide +kernel
  rw [hl, canonical2217 B hB] at h
  have hc0 : mixedMoment B raw2217 (Fin.cases (0 : Fin 2) singletonSmall5177) =
      mixedMoment B node2605 node2605Labels := by
    have ha : raw2217 = raw2218 := by apply Matrix.ext; unfold raw2217 raw2218; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5177 = raw2218Labels := by decide +kernel
    rw [ha, hj, canonical2218 B hB]
  have hc1 : mixedMoment B raw2217 (Fin.cases (1 : Fin 2) singletonSmall5177) =
      mixedMoment B node3616 node3616Labels := by
    have ha : raw2217 = raw2219 := by apply Matrix.ext; unfold raw2217 raw2219; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5177 = raw2219Labels := by decide +kernel
    rw [ha, hj, canonical2219 B hB]
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

theorem singleton5293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5293 node5293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2767 node2767Labels + mixedMoment B node3627 node3627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2301 singletonSmall5293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5293) = raw2301Labels := by decide +kernel
  rw [hl, canonical2301 B hB] at h
  have hc0 : mixedMoment B raw2301 (Fin.cases (0 : Fin 2) singletonSmall5293) =
      mixedMoment B node2767 node2767Labels := by
    have ha : raw2301 = raw2302 := by apply Matrix.ext; unfold raw2301 raw2302; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5293 = raw2302Labels := by decide +kernel
    rw [ha, hj, canonical2302 B hB]
  have hc1 : mixedMoment B raw2301 (Fin.cases (1 : Fin 2) singletonSmall5293) =
      mixedMoment B node3627 node3627Labels := by
    have ha : raw2301 = raw2303 := by apply Matrix.ext; unfold raw2301 raw2303; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5293 = raw2303Labels := by decide +kernel
    rw [ha, hj, canonical2303 B hB]
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

theorem sound682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node682 node682Labels = Sparse.eval nodeValue682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 682) = mixedMoment B node682 node682Labels := rfl
  simpa [nodeValue682, Sparse.eval] using hc.symm

theorem sound684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node684 node684Labels = Sparse.eval nodeValue684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 684) = mixedMoment B node684 node684Labels := rfl
  simpa [nodeValue684, Sparse.eval] using hc.symm

theorem sound692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node692 node692Labels = Sparse.eval nodeValue692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 692) = mixedMoment B node692 node692Labels := rfl
  simpa [nodeValue692, Sparse.eval] using hc.symm

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

theorem sound870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node870 node870Labels = Sparse.eval nodeValue870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 870) = mixedMoment B node870 node870Labels := rfl
  simpa [nodeValue870, Sparse.eval] using hc.symm

theorem sound873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node873 node873Labels = Sparse.eval nodeValue873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 873) = mixedMoment B node873 node873Labels := rfl
  simpa [nodeValue873, Sparse.eval] using hc.symm

theorem sound892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node892 node892Labels = Sparse.eval nodeValue892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 892) = mixedMoment B node892 node892Labels := rfl
  simpa [nodeValue892, Sparse.eval] using hc.symm

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

theorem sound933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node933 node933Labels = Sparse.eval nodeValue933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 933) = mixedMoment B node933 node933Labels := rfl
  simpa [nodeValue933, Sparse.eval] using hc.symm

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

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

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

theorem sound1567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1567 node1567Labels = Sparse.eval nodeValue1567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1567) = mixedMoment B node1567 node1567Labels := rfl
  simpa [nodeValue1567, Sparse.eval] using hc.symm

theorem sound1569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1569 node1569Labels = Sparse.eval nodeValue1569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1569) = mixedMoment B node1569 node1569Labels := rfl
  simpa [nodeValue1569, Sparse.eval] using hc.symm

theorem sound1575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1575 node1575Labels = Sparse.eval nodeValue1575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1575) = mixedMoment B node1575 node1575Labels := rfl
  simpa [nodeValue1575, Sparse.eval] using hc.symm

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

theorem sound1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1691 node1691Labels = Sparse.eval nodeValue1691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1691) = mixedMoment B node1691 node1691Labels := rfl
  simpa [nodeValue1691, Sparse.eval] using hc.symm

theorem sound1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1693 node1693Labels = Sparse.eval nodeValue1693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1693) = mixedMoment B node1693 node1693Labels := rfl
  simpa [nodeValue1693, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

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

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node344 node344Labels = Sparse.eval nodeValue344 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue344 (familyPairVector B) := singlePair344 B _hB
    _ = _ := by norm_num [singlePairValue344, nodeValue344, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2605 node2605Labels = Sparse.eval nodeValue2605 (mixedVector B) := by
  have h := singleton2605 B _hB
  rw [sound344 B _hB _hF] at h
  norm_num [nodeValue2605, nodeValue344, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node404 node404Labels = Sparse.eval nodeValue404 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue404 (familyPairVector B) := singlePair404 B _hB
    _ = _ := by
      norm_num [singlePairValue404, nodeValue404, Sparse.eval, mixedVector]
      ring

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

theorem sound2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2767 node2767Labels = Sparse.eval nodeValue2767 (mixedVector B) := by
  have h := singleton2767 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue2767, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

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

theorem sound3616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3616 node3616Labels = Sparse.eval nodeValue3616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3616) = mixedMoment B node3616 node3616Labels := rfl
  simpa [nodeValue3616, Sparse.eval] using hc.symm

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

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

theorem sound544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node544 node544Labels = Sparse.eval nodeValue544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 544) = mixedMoment B node544 node544Labels := rfl
  simpa [nodeValue544, Sparse.eval] using hc.symm

theorem sound547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node547 node547Labels = Sparse.eval nodeValue547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 547) = mixedMoment B node547 node547Labels := rfl
  simpa [nodeValue547, Sparse.eval] using hc.symm

theorem sound563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node563 node563Labels = Sparse.eval nodeValue563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 563) = mixedMoment B node563 node563Labels := rfl
  simpa [nodeValue563, Sparse.eval] using hc.symm

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

theorem sound4107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4107 node4107Labels = Sparse.eval nodeValue4107 (mixedVector B) := by
  have h := singleton4107 B _hB
  rw [sound544 B _hB _hF, sound682 B _hB _hF] at h
  norm_num [nodeValue4107, nodeValue544, nodeValue682, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4110 node4110Labels = Sparse.eval nodeValue4110 (mixedVector B) := by
  have h := singleton4110 B _hB
  rw [sound547 B _hB _hF, sound684 B _hB _hF] at h
  norm_num [nodeValue4110, nodeValue547, nodeValue684, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4133 node4133Labels = Sparse.eval nodeValue4133 (mixedVector B) := by
  have h := singleton4133 B _hB
  rw [sound563 B _hB _hF, sound692 B _hB _hF] at h
  norm_num [nodeValue4133, nodeValue563, nodeValue692, Sparse.eval] at h ⊢
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

theorem sound4292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4292 node4292Labels = Sparse.eval nodeValue4292 (mixedVector B) := by
  have h := singleton4292 B _hB
  rw [sound870 B _hB _hF, sound1567 B _hB _hF] at h
  norm_num [nodeValue4292, nodeValue870, nodeValue1567, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4295 node4295Labels = Sparse.eval nodeValue4295 (mixedVector B) := by
  have h := singleton4295 B _hB
  rw [sound873 B _hB _hF, sound1569 B _hB _hF] at h
  norm_num [nodeValue4295, nodeValue873, nodeValue1569, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4314 node4314Labels = Sparse.eval nodeValue4314 (mixedVector B) := by
  have h := singleton4314 B _hB
  rw [sound892 B _hB _hF, sound1575 B _hB _hF] at h
  norm_num [nodeValue4314, nodeValue892, nodeValue1575, Sparse.eval] at h ⊢
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

theorem sound4355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4355 node4355Labels = Sparse.eval nodeValue4355 (mixedVector B) := by
  have h := singleton4355 B _hB
  rw [sound933 B _hB _hF, sound1691 B _hB _hF] at h
  norm_num [nodeValue4355, nodeValue933, nodeValue1691, Sparse.eval] at h ⊢
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

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
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

theorem sound4499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4499 node4499Labels = Sparse.eval nodeValue4499 (mixedVector B) := by
  have h := singleton4499 B _hB
  rw [sound1083 B _hB _hF, sound1728 B _hB _hF] at h
  norm_num [nodeValue4499, nodeValue1083, nodeValue1728, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5081 node5081Labels = Sparse.eval nodeValue5081 (mixedVector B) := by
  have h := singleton5081 B _hB
  rw [sound2489 B _hB _hF, sound3482 B _hB _hF] at h
  norm_num [nodeValue5081, nodeValue2489, nodeValue3482, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5177 node5177Labels = Sparse.eval nodeValue5177 (mixedVector B) := by
  have h := singleton5177 B _hB
  rw [sound2605 B _hB _hF, sound3616 B _hB _hF] at h
  norm_num [nodeValue5177, nodeValue2605, nodeValue3616, Sparse.eval] at h ⊢
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

theorem sound5293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5293 node5293Labels = Sparse.eval nodeValue5293 (mixedVector B) := by
  have h := singleton5293 B _hB
  rw [sound2767 B _hB _hF, sound3627 B _hB _hF] at h
  norm_num [nodeValue5293, nodeValue2767, nodeValue3627, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources47
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1529 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 1) (sourceB1529 + difference 1 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 1) (sourceB1529 + difference 1 0) sourceC1529) = raw17675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw17675; decide +kernel
    rw [ha]
    exact (canonical17675 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 2) (sourceB1529 + difference 2 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 2) (sourceB1529 + difference 2 0) sourceC1529) = raw23219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23219; decide +kernel
    rw [ha]
    exact (canonical23219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 3) (sourceB1529 + difference 3 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 3) (sourceB1529 + difference 3 0) sourceC1529) = raw23220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23220; decide +kernel
    rw [ha]
    exact (canonical23220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 4) (sourceB1529 + difference 4 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 4) (sourceB1529 + difference 4 0) sourceC1529) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1529 + difference 0 5) (sourceB1529 + difference 5 0) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1529 + difference 0 5) (sourceB1529 + difference 5 0) sourceC1529) = raw23221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23221; decide +kernel
    rw [ha]
    exact (canonical23221 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 0) (sourceB1529 + difference 0 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4133) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 0) (sourceB1529 + difference 0 1) sourceC1529) = raw23222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23222; decide +kernel
    rw [ha]
    exact (canonical23222 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 2) (sourceB1529 + difference 2 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4314) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 2) (sourceB1529 + difference 2 1) sourceC1529) = raw23223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23223; decide +kernel
    rw [ha]
    exact (canonical23223 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 3) (sourceB1529 + difference 3 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4314) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 3) (sourceB1529 + difference 3 1) sourceC1529) = raw23224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23224; decide +kernel
    rw [ha]
    exact (canonical23224 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 4) (sourceB1529 + difference 4 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 4) (sourceB1529 + difference 4 1) sourceC1529) = raw21481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21481; decide +kernel
    rw [ha]
    exact (canonical21481 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1529 + difference 1 5) (sourceB1529 + difference 5 1) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1529 + difference 1 5) (sourceB1529 + difference 5 1) sourceC1529) = raw23225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23225; decide +kernel
    rw [ha]
    exact (canonical23225 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 0) (sourceB1529 + difference 0 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 0) (sourceB1529 + difference 0 2) sourceC1529) = raw23226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23226; decide +kernel
    rw [ha]
    exact (canonical23226 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 1) (sourceB1529 + difference 1 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 1) (sourceB1529 + difference 1 2) sourceC1529) = raw23227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23227; decide +kernel
    rw [ha]
    exact (canonical23227 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 3) (sourceB1529 + difference 3 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4292) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 3) (sourceB1529 + difference 3 2) sourceC1529) = raw23228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23228; decide +kernel
    rw [ha]
    exact (canonical23228 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 4) (sourceB1529 + difference 4 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 4) (sourceB1529 + difference 4 2) sourceC1529) = raw21485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21485; decide +kernel
    rw [ha]
    exact (canonical21485 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1529 + difference 2 5) (sourceB1529 + difference 5 2) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1529 + difference 2 5) (sourceB1529 + difference 5 2) sourceC1529) = raw23229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23229; decide +kernel
    rw [ha]
    exact (canonical23229 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 0) (sourceB1529 + difference 0 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 0) (sourceB1529 + difference 0 3) sourceC1529) = raw23230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23230; decide +kernel
    rw [ha]
    exact (canonical23230 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 1) (sourceB1529 + difference 1 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 1) (sourceB1529 + difference 1 3) sourceC1529) = raw23231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23231; decide +kernel
    rw [ha]
    exact (canonical23231 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 2) (sourceB1529 + difference 2 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4292) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 2) (sourceB1529 + difference 2 3) sourceC1529) = raw23232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23232; decide +kernel
    rw [ha]
    exact (canonical23232 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 4) (sourceB1529 + difference 4 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 4) (sourceB1529 + difference 4 3) sourceC1529) = raw21489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21489; decide +kernel
    rw [ha]
    exact (canonical21489 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1529 + difference 3 5) (sourceB1529 + difference 5 3) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1529 + difference 3 5) (sourceB1529 + difference 5 3) sourceC1529) = raw23233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23233; decide +kernel
    rw [ha]
    exact (canonical23233 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 0) (sourceB1529 + difference 0 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 0) (sourceB1529 + difference 0 4) sourceC1529) = raw23234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23234; decide +kernel
    rw [ha]
    exact (canonical23234 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 1) (sourceB1529 + difference 1 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 1) (sourceB1529 + difference 1 4) sourceC1529) = raw23235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23235; decide +kernel
    rw [ha]
    exact (canonical23235 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 2) (sourceB1529 + difference 2 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 2) (sourceB1529 + difference 2 4) sourceC1529) = raw23236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23236; decide +kernel
    rw [ha]
    exact (canonical23236 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 3) (sourceB1529 + difference 3 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 3) (sourceB1529 + difference 3 4) sourceC1529) = raw23237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23237; decide +kernel
    rw [ha]
    exact (canonical23237 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1529 + difference 4 5) (sourceB1529 + difference 5 4) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1529 + difference 4 5) (sourceB1529 + difference 5 4) sourceC1529) = raw23238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw23238; decide +kernel
    rw [ha]
    exact (canonical23238 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 0) (sourceB1529 + difference 0 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 0) (sourceB1529 + difference 0 5) sourceC1529) = raw21490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21490; decide +kernel
    rw [ha]
    exact (canonical21490 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 1) (sourceB1529 + difference 1 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 1) (sourceB1529 + difference 1 5) sourceC1529) = raw21491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21491; decide +kernel
    rw [ha]
    exact (canonical21491 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 2) (sourceB1529 + difference 2 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 2) (sourceB1529 + difference 2 5) sourceC1529) = raw21492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21492; decide +kernel
    rw [ha]
    exact (canonical21492 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 3) (sourceB1529 + difference 3 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 3) (sourceB1529 + difference 3 5) sourceC1529) = raw21493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw21493; decide +kernel
    rw [ha]
    exact (canonical21493 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1529 + difference 5 4) (sourceB1529 + difference 4 5) sourceC1529) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1529 + difference 5 4) (sourceB1529 + difference 4 5) sourceC1529) = raw4935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1529 sourceB1529 sourceC1529 difference raw4935; decide +kernel
    rw [ha]
    exact (canonical4935 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1529 sourceB1529 sourceC1529
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1529, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1309 : Integer.Sparse.reindex keyMap MixedData.row1309 = numericRow1309 := by decide +kernel

theorem numericCheck1309 (x : Master → ℝ) : Integer.Sparse.eval numericRow1309 x =
    (2160 : ℝ) * reducedSource1309 x := by
  norm_num [numericRow1309, reducedSource1309, Integer.Sparse.eval, Sparse.eval, nodeValue4107, nodeValue4110, nodeValue4133, nodeValue4292, nodeValue4295, nodeValue4314, nodeValue4355, nodeValue4360, nodeValue4458, nodeValue4460, nodeValue4499, nodeValue5081, nodeValue5177, nodeValue5293] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1309 (mixedVector B) = 0 := by
  have h4107 : mixedVector B (Sum.inr 4107) = Sparse.eval nodeValue4107 (mixedVector B) := by
    change mixedMoment B node4107 node4107Labels = _
    exact sound4107 B hB hF
  have h4110 : mixedVector B (Sum.inr 4110) = Sparse.eval nodeValue4110 (mixedVector B) := by
    change mixedMoment B node4110 node4110Labels = _
    exact sound4110 B hB hF
  have h4133 : mixedVector B (Sum.inr 4133) = Sparse.eval nodeValue4133 (mixedVector B) := by
    change mixedMoment B node4133 node4133Labels = _
    exact sound4133 B hB hF
  have h4292 : mixedVector B (Sum.inr 4292) = Sparse.eval nodeValue4292 (mixedVector B) := by
    change mixedMoment B node4292 node4292Labels = _
    exact sound4292 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4314 : mixedVector B (Sum.inr 4314) = Sparse.eval nodeValue4314 (mixedVector B) := by
    change mixedMoment B node4314 node4314Labels = _
    exact sound4314 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  simpa only [sourceForm1529, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4107, h4110, h4133, h4292, h4295, h4314, h4355, h4360, h4458, h4460, h4499, h5081, h5177, h5293, reducedSource1309] using sourceEq1529 B hB

theorem rowSound1309_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1309 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1309, numericCheck1309, reducedZero1309 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e_oai
