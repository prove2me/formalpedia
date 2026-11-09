-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:34:02.390825+00:00
-- url     : https://prove2.me/submissions/73239258-39f6-4fa1-83af-774c1fa17144

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1314 raw1314Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw1314 raw1314Labels = mixedMoment B raw1314step0 raw1314step0Labels := by
      have ha : raw1314step0 = (fun i j => raw1314 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1314step0 raw1314; decide +kernel
      have hl : raw1314step0Labels = raw1314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1314 raw1314Labels permutation32 permutation4
    mixedMoment B raw1314step0 raw1314step0Labels = mixedMoment B raw1314step1 raw1314step1Labels := by
      have ha : raw1314step1 = raw1314step0 := by apply Matrix.ext; unfold raw1314step1 raw1314step0; decide +kernel
      have hl : raw1314step0Labels = labelEmbedding7 ∘ raw1314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1314step0 raw1314step0Labels raw1314step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

theorem canonical1315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1315 raw1315Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw1315 raw1315Labels = mixedMoment B raw1315step0 raw1315step0Labels := by
      have ha : raw1315step0 = (fun i j => raw1315 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1315step0 raw1315; decide +kernel
      have hl : raw1315step0Labels = raw1315Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1315 raw1315Labels permutation32 permutation4
    _ = mixedMoment B node1098 node1098Labels := by rfl

theorem canonical1316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1316 raw1316Labels = mixedMoment B node1894 node1894Labels := by
  calc
    mixedMoment B raw1316 raw1316Labels = mixedMoment B raw1316step0 raw1316step0Labels := by
      have ha : raw1316step0 = (fun i j => raw1316 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1316step0 raw1316; decide +kernel
      have hl : raw1316step0Labels = raw1316Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1316 raw1316Labels permutation151 permutation6
    mixedMoment B raw1316step0 raw1316step0Labels = mixedMoment B raw1316step1 raw1316step1Labels := by
      have ha : raw1316step1 = raw1316step0 := by apply Matrix.ext; unfold raw1316step1 raw1316step0; decide +kernel
      have hl : raw1316step0Labels = labelEmbedding1 ∘ raw1316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1316step0 raw1316step0Labels raw1316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1894 node1894Labels := by rfl

theorem canonical1329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1329 raw1329Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw1329 raw1329Labels = mixedMoment B raw1329step0 raw1329step0Labels := by
      have ha : raw1329step0 = (fun i j => raw1329 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1329step0 raw1329; decide +kernel
      have hl : raw1329step0Labels = raw1329Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1329 raw1329Labels permutation8 permutation4
    mixedMoment B raw1329step0 raw1329step0Labels = mixedMoment B raw1329step1 raw1329step1Labels := by
      have ha : raw1329step1 = raw1329step0 := by apply Matrix.ext; unfold raw1329step1 raw1329step0; decide +kernel
      have hl : raw1329step0Labels = labelEmbedding7 ∘ raw1329step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1329step0 raw1329step0Labels raw1329step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

theorem canonical1330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1330 raw1330Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw1330 raw1330Labels = mixedMoment B raw1330step0 raw1330step0Labels := by
      have ha : raw1330step0 = (fun i j => raw1330 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1330step0 raw1330; decide +kernel
      have hl : raw1330step0Labels = raw1330Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1330 raw1330Labels permutation8 permutation4
    _ = mixedMoment B node1103 node1103Labels := by rfl

theorem canonical1331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1331 raw1331Labels = mixedMoment B node1858 node1858Labels := by
  calc
    mixedMoment B raw1331 raw1331Labels = mixedMoment B raw1331step0 raw1331step0Labels := by
      have ha : raw1331step0 = (fun i j => raw1331 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1331step0 raw1331; decide +kernel
      have hl : raw1331step0Labels = raw1331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1331 raw1331Labels permutation31 permutation6
    mixedMoment B raw1331step0 raw1331step0Labels = mixedMoment B raw1331step1 raw1331step1Labels := by
      have ha : raw1331step1 = raw1331step0 := by apply Matrix.ext; unfold raw1331step1 raw1331step0; decide +kernel
      have hl : raw1331step0Labels = labelEmbedding1 ∘ raw1331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1331step0 raw1331step0Labels raw1331step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1858 node1858Labels := by rfl

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

theorem canonical1428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1428 raw1428Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw1428 raw1428Labels = mixedMoment B raw1428step0 raw1428step0Labels := by
      have ha : raw1428step0 = (fun i j => raw1428 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1428step0 raw1428; decide +kernel
      have hl : raw1428step0Labels = raw1428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1428 raw1428Labels permutation8 permutation4
    mixedMoment B raw1428step0 raw1428step0Labels = mixedMoment B raw1428step1 raw1428step1Labels := by
      have ha : raw1428step1 = raw1428step0 := by apply Matrix.ext; unfold raw1428step1 raw1428step0; decide +kernel
      have hl : raw1428step0Labels = labelEmbedding7 ∘ raw1428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1428step0 raw1428step0Labels raw1428step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical1429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1429 raw1429Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw1429 raw1429Labels = mixedMoment B raw1429step0 raw1429step0Labels := by
      have ha : raw1429step0 = (fun i j => raw1429 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1429step0 raw1429; decide +kernel
      have hl : raw1429step0Labels = raw1429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1429 raw1429Labels permutation8 permutation4
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical1430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1430 raw1430Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw1430 raw1430Labels = mixedMoment B raw1430step0 raw1430step0Labels := by
      have ha : raw1430step0 = (fun i j => raw1430 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1430step0 raw1430; decide +kernel
      have hl : raw1430step0Labels = raw1430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1430 raw1430Labels permutation31 permutation6
    mixedMoment B raw1430step0 raw1430step0Labels = mixedMoment B raw1430step1 raw1430step1Labels := by
      have ha : raw1430step1 = raw1430step0 := by apply Matrix.ext; unfold raw1430step1 raw1430step0; decide +kernel
      have hl : raw1430step0Labels = labelEmbedding1 ∘ raw1430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1430step0 raw1430step0Labels raw1430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1515 raw1515Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw1515 raw1515Labels = mixedMoment B raw1515step0 raw1515step0Labels := by
      have ha : raw1515step0 = (fun i j => raw1515 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1515step0 raw1515; decide +kernel
      have hl : raw1515step0Labels = raw1515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1515 raw1515Labels permutation32 permutation4
    mixedMoment B raw1515step0 raw1515step0Labels = mixedMoment B raw1515step1 raw1515step1Labels := by
      have ha : raw1515step1 = raw1515step0 := by apply Matrix.ext; unfold raw1515step1 raw1515step0; decide +kernel
      have hl : raw1515step0Labels = labelEmbedding7 ∘ raw1515step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1515step0 raw1515step0Labels raw1515step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

theorem canonical1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1516 raw1516Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw1516 raw1516Labels = mixedMoment B raw1516step0 raw1516step0Labels := by
      have ha : raw1516step0 = (fun i j => raw1516 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1516step0 raw1516; decide +kernel
      have hl : raw1516step0Labels = raw1516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1516 raw1516Labels permutation32 permutation4
    _ = mixedMoment B node1778 node1778Labels := by rfl

theorem canonical1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1517 raw1517Labels = mixedMoment B node1854 node1854Labels := by
  calc
    mixedMoment B raw1517 raw1517Labels = mixedMoment B raw1517step0 raw1517step0Labels := by
      have ha : raw1517step0 = (fun i j => raw1517 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1517step0 raw1517; decide +kernel
      have hl : raw1517step0Labels = raw1517Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1517 raw1517Labels permutation33 permutation6
    mixedMoment B raw1517step0 raw1517step0Labels = mixedMoment B raw1517step1 raw1517step1Labels := by
      have ha : raw1517step1 = -raw1517step0 := by apply Matrix.ext; change ∀ i j, raw1517step1 i j = -(raw1517step0 i j); unfold raw1517step1 raw1517step0; decide +kernel
      have hl : raw1517step1Labels = raw1517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1517step1 raw1517step1Labels = mixedMoment B raw1517step2 raw1517step2Labels := by
      have ha : raw1517step2 = raw1517step1 := by apply Matrix.ext; unfold raw1517step2 raw1517step1; decide +kernel
      have hl : raw1517step1Labels = labelEmbedding1 ∘ raw1517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1517step1 raw1517step1Labels raw1517step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1854 node1854Labels := by rfl

theorem canonical1527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1527 raw1527Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw1527 raw1527Labels = mixedMoment B raw1527step0 raw1527step0Labels := by
      have ha : raw1527step0 = (fun i j => raw1527 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1527step0 raw1527; decide +kernel
      have hl : raw1527step0Labels = raw1527Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1527 raw1527Labels permutation8 permutation4
    mixedMoment B raw1527step0 raw1527step0Labels = mixedMoment B raw1527step1 raw1527step1Labels := by
      have ha : raw1527step1 = raw1527step0 := by apply Matrix.ext; unfold raw1527step1 raw1527step0; decide +kernel
      have hl : raw1527step0Labels = labelEmbedding7 ∘ raw1527step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1527step0 raw1527step0Labels raw1527step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

theorem canonical1528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1528 raw1528Labels = mixedMoment B node1783 node1783Labels := by
  calc
    mixedMoment B raw1528 raw1528Labels = mixedMoment B raw1528step0 raw1528step0Labels := by
      have ha : raw1528step0 = (fun i j => raw1528 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1528step0 raw1528; decide +kernel
      have hl : raw1528step0Labels = raw1528Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1528 raw1528Labels permutation8 permutation4
    _ = mixedMoment B node1783 node1783Labels := by rfl

theorem canonical1529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1529 raw1529Labels = mixedMoment B node1857 node1857Labels := by
  calc
    mixedMoment B raw1529 raw1529Labels = mixedMoment B raw1529step0 raw1529step0Labels := by
      have ha : raw1529step0 = (fun i j => raw1529 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1529step0 raw1529; decide +kernel
      have hl : raw1529step0Labels = raw1529Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1529 raw1529Labels permutation9 permutation6
    mixedMoment B raw1529step0 raw1529step0Labels = mixedMoment B raw1529step1 raw1529step1Labels := by
      have ha : raw1529step1 = -raw1529step0 := by apply Matrix.ext; change ∀ i j, raw1529step1 i j = -(raw1529step0 i j); unfold raw1529step1 raw1529step0; decide +kernel
      have hl : raw1529step1Labels = raw1529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1529step1 raw1529step1Labels = mixedMoment B raw1529step2 raw1529step2Labels := by
      have ha : raw1529step2 = raw1529step1 := by apply Matrix.ext; unfold raw1529step2 raw1529step1; decide +kernel
      have hl : raw1529step1Labels = labelEmbedding1 ∘ raw1529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1529step1 raw1529step1Labels raw1529step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1857 node1857Labels := by rfl

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

theorem canonical1602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1602 raw1602Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw1602 raw1602Labels = mixedMoment B raw1602step0 raw1602step0Labels := by
      have ha : raw1602step0 = (fun i j => raw1602 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1602step0 raw1602; decide +kernel
      have hl : raw1602step0Labels = raw1602Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1602 raw1602Labels permutation152 permutation4
    mixedMoment B raw1602step0 raw1602step0Labels = mixedMoment B raw1602step1 raw1602step1Labels := by
      have ha : raw1602step1 = raw1602step0 := by apply Matrix.ext; unfold raw1602step1 raw1602step0; decide +kernel
      have hl : raw1602step0Labels = labelEmbedding7 ∘ raw1602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1602step0 raw1602step0Labels raw1602step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

theorem canonical1603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1603 raw1603Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw1603 raw1603Labels = mixedMoment B raw1603step0 raw1603step0Labels := by
      have ha : raw1603step0 = (fun i j => raw1603 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1603step0 raw1603; decide +kernel
      have hl : raw1603step0Labels = raw1603Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1603 raw1603Labels permutation152 permutation4
    _ = mixedMoment B node1867 node1867Labels := by rfl

theorem canonical1604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1604 raw1604Labels = mixedMoment B node1891 node1891Labels := by
  calc
    mixedMoment B raw1604 raw1604Labels = mixedMoment B raw1604step0 raw1604step0Labels := by
      have ha : raw1604step0 = (fun i j => raw1604 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1604step0 raw1604; decide +kernel
      have hl : raw1604step0Labels = raw1604Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1604 raw1604Labels permutation153 permutation6
    mixedMoment B raw1604step0 raw1604step0Labels = mixedMoment B raw1604step1 raw1604step1Labels := by
      have ha : raw1604step1 = -raw1604step0 := by apply Matrix.ext; change ∀ i j, raw1604step1 i j = -(raw1604step0 i j); unfold raw1604step1 raw1604step0; decide +kernel
      have hl : raw1604step1Labels = raw1604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1604step1 raw1604step1Labels = mixedMoment B raw1604step2 raw1604step2Labels := by
      have ha : raw1604step2 = raw1604step1 := by apply Matrix.ext; unfold raw1604step2 raw1604step1; decide +kernel
      have hl : raw1604step1Labels = labelEmbedding1 ∘ raw1604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1604step1 raw1604step1Labels raw1604step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1891 node1891Labels := by rfl

theorem canonical1614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1614 raw1614Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw1614 raw1614Labels = mixedMoment B raw1614step0 raw1614step0Labels := by
      have ha : raw1614step0 = (fun i j => raw1614 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1614step0 raw1614; decide +kernel
      have hl : raw1614step0Labels = raw1614Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1614 raw1614Labels permutation32 permutation4
    mixedMoment B raw1614step0 raw1614step0Labels = mixedMoment B raw1614step1 raw1614step1Labels := by
      have ha : raw1614step1 = raw1614step0 := by apply Matrix.ext; unfold raw1614step1 raw1614step0; decide +kernel
      have hl : raw1614step0Labels = labelEmbedding7 ∘ raw1614step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1614step0 raw1614step0Labels raw1614step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

theorem canonical1615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1615 raw1615Labels = mixedMoment B node1873 node1873Labels := by
  calc
    mixedMoment B raw1615 raw1615Labels = mixedMoment B raw1615step0 raw1615step0Labels := by
      have ha : raw1615step0 = (fun i j => raw1615 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1615step0 raw1615; decide +kernel
      have hl : raw1615step0Labels = raw1615Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1615 raw1615Labels permutation32 permutation4
    _ = mixedMoment B node1873 node1873Labels := by rfl

theorem canonical1616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1616 raw1616Labels = mixedMoment B node1893 node1893Labels := by
  calc
    mixedMoment B raw1616 raw1616Labels = mixedMoment B raw1616step0 raw1616step0Labels := by
      have ha : raw1616step0 = (fun i j => raw1616 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1616step0 raw1616; decide +kernel
      have hl : raw1616step0Labels = raw1616Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1616 raw1616Labels permutation33 permutation6
    mixedMoment B raw1616step0 raw1616step0Labels = mixedMoment B raw1616step1 raw1616step1Labels := by
      have ha : raw1616step1 = -raw1616step0 := by apply Matrix.ext; change ∀ i j, raw1616step1 i j = -(raw1616step0 i j); unfold raw1616step1 raw1616step0; decide +kernel
      have hl : raw1616step1Labels = raw1616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1616step1 raw1616step1Labels = mixedMoment B raw1616step2 raw1616step2Labels := by
      have ha : raw1616step2 = raw1616step1 := by apply Matrix.ext; unfold raw1616step2 raw1616step1; decide +kernel
      have hl : raw1616step1Labels = labelEmbedding1 ∘ raw1616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1616step1 raw1616step1Labels raw1616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1893 node1893Labels := by rfl

theorem canonical1659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1659 raw1659Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw1659 raw1659Labels = mixedMoment B raw1659step0 raw1659step0Labels := by
      have ha : raw1659step0 = (fun i j => raw1659 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1659step0 raw1659; decide +kernel
      have hl : raw1659step0Labels = raw1659Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1659 raw1659Labels permutation32 permutation4
    mixedMoment B raw1659step0 raw1659step0Labels = mixedMoment B raw1659step1 raw1659step1Labels := by
      have ha : raw1659step1 = raw1659step0 := by apply Matrix.ext; unfold raw1659step1 raw1659step0; decide +kernel
      have hl : raw1659step0Labels = labelEmbedding7 ∘ raw1659step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1659step0 raw1659step0Labels raw1659step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical1660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1660 raw1660Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw1660 raw1660Labels = mixedMoment B raw1660step0 raw1660step0Labels := by
      have ha : raw1660step0 = (fun i j => raw1660 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1660step0 raw1660; decide +kernel
      have hl : raw1660step0Labels = raw1660Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1660 raw1660Labels permutation32 permutation4
    _ = mixedMoment B node1915 node1915Labels := by rfl

theorem canonical1661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1661 raw1661Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw1661 raw1661Labels = mixedMoment B raw1661step0 raw1661step0Labels := by
      have ha : raw1661step0 = (fun i j => raw1661 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1661step0 raw1661; decide +kernel
      have hl : raw1661step0Labels = raw1661Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1661 raw1661Labels permutation33 permutation6
    mixedMoment B raw1661step0 raw1661step0Labels = mixedMoment B raw1661step1 raw1661step1Labels := by
      have ha : raw1661step1 = -raw1661step0 := by apply Matrix.ext; change ∀ i j, raw1661step1 i j = -(raw1661step0 i j); unfold raw1661step1 raw1661step0; decide +kernel
      have hl : raw1661step1Labels = raw1661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1661step1 raw1661step1Labels = mixedMoment B raw1661step2 raw1661step2Labels := by
      have ha : raw1661step2 = raw1661step1 := by apply Matrix.ext; unfold raw1661step2 raw1661step1; decide +kernel
      have hl : raw1661step1Labels = labelEmbedding1 ∘ raw1661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1661step1 raw1661step1Labels raw1661step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1946 node1946Labels := by rfl

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

theorem canonical1776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1776 raw1776Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw1776 raw1776Labels = mixedMoment B raw1776step0 raw1776step0Labels := by
      have ha : raw1776step0 = (fun i j => raw1776 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1776step0 raw1776; decide +kernel
      have hl : raw1776step0Labels = raw1776Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1776 raw1776Labels permutation8 permutation4
    mixedMoment B raw1776step0 raw1776step0Labels = mixedMoment B raw1776step1 raw1776step1Labels := by
      have ha : raw1776step1 = raw1776step0 := by apply Matrix.ext; unfold raw1776step1 raw1776step0; decide +kernel
      have hl : raw1776step0Labels = labelEmbedding7 ∘ raw1776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1776step0 raw1776step0Labels raw1776step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical1777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1777 raw1777Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw1777 raw1777Labels = mixedMoment B raw1777step0 raw1777step0Labels := by
      have ha : raw1777step0 = (fun i j => raw1777 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1777step0 raw1777; decide +kernel
      have hl : raw1777step0Labels = raw1777Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1777 raw1777Labels permutation8 permutation4
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical1778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1778 raw1778Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw1778 raw1778Labels = mixedMoment B raw1778step0 raw1778step0Labels := by
      have ha : raw1778step0 = (fun i j => raw1778 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1778step0 raw1778; decide +kernel
      have hl : raw1778step0Labels = raw1778Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1778 raw1778Labels permutation8 permutation6
    mixedMoment B raw1778step0 raw1778step0Labels = mixedMoment B raw1778step1 raw1778step1Labels := by
      have ha : raw1778step1 = -raw1778step0 := by apply Matrix.ext; change ∀ i j, raw1778step1 i j = -(raw1778step0 i j); unfold raw1778step1 raw1778step0; decide +kernel
      have hl : raw1778step1Labels = raw1778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1778step1 raw1778step1Labels = mixedMoment B raw1778step2 raw1778step2Labels := by
      have ha : raw1778step2 = raw1778step1 := by apply Matrix.ext; unfold raw1778step2 raw1778step1; decide +kernel
      have hl : raw1778step1Labels = labelEmbedding1 ∘ raw1778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1778step1 raw1778step1Labels raw1778step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

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

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical2235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2235 raw2235Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw2235 raw2235Labels = mixedMoment B raw2235step0 raw2235step0Labels := by
      have ha : raw2235step0 = (fun i j => raw2235 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2235step0 raw2235; decide +kernel
      have hl : raw2235step0Labels = raw2235Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2235 raw2235Labels permutation8 permutation5
    mixedMoment B raw2235step0 raw2235step0Labels = mixedMoment B raw2235step1 raw2235step1Labels := by
      have ha : raw2235step1 = raw2235step0 := by apply Matrix.ext; unfold raw2235step1 raw2235step0; decide +kernel
      have hl : raw2235step0Labels = labelEmbedding8 ∘ raw2235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2235step0 raw2235step0Labels raw2235step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical2236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2236 raw2236Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw2236 raw2236Labels = mixedMoment B raw2236step0 raw2236step0Labels := by
      have ha : raw2236step0 = (fun i j => raw2236 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2236step0 raw2236; decide +kernel
      have hl : raw2236step0Labels = raw2236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2236 raw2236Labels permutation9 permutation4
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical2237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2237 raw2237Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw2237 raw2237Labels = mixedMoment B raw2237step0 raw2237step0Labels := by
      have ha : raw2237step0 = (fun i j => raw2237 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2237step0 raw2237; decide +kernel
      have hl : raw2237step0Labels = raw2237Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2237 raw2237Labels permutation10 permutation3
    mixedMoment B raw2237step0 raw2237step0Labels = mixedMoment B raw2237step1 raw2237step1Labels := by
      have ha : raw2237step1 = -raw2237step0 := by apply Matrix.ext; change ∀ i j, raw2237step1 i j = -(raw2237step0 i j); unfold raw2237step1 raw2237step0; decide +kernel
      have hl : raw2237step1Labels = raw2237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2237step1 raw2237step1Labels = mixedMoment B raw2237step2 raw2237step2Labels := by
      have ha : raw2237step2 = raw2237step1 := by apply Matrix.ext; unfold raw2237step2 raw2237step1; decide +kernel
      have hl : raw2237step1Labels = labelEmbedding1 ∘ raw2237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2237step1 raw2237step1Labels raw2237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

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

theorem canonical2304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2304 raw2304Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2304 raw2304Labels = mixedMoment B raw2304step0 raw2304step0Labels := by
      have ha : raw2304step0 = (fun i j => raw2304 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2304step0 raw2304; decide +kernel
      have hl : raw2304step0Labels = raw2304Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2304 raw2304Labels permutation8 permutation4
    mixedMoment B raw2304step0 raw2304step0Labels = mixedMoment B raw2304step1 raw2304step1Labels := by
      have ha : raw2304step1 = raw2304step0 := by apply Matrix.ext; unfold raw2304step1 raw2304step0; decide +kernel
      have hl : raw2304step0Labels = labelEmbedding7 ∘ raw2304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2304step0 raw2304step0Labels raw2304step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical2305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2305 raw2305Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw2305 raw2305Labels = mixedMoment B raw2305step0 raw2305step0Labels := by
      have ha : raw2305step0 = (fun i j => raw2305 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2305step0 raw2305; decide +kernel
      have hl : raw2305step0Labels = raw2305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2305 raw2305Labels permutation8 permutation4
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2306 raw2306Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw2306 raw2306Labels = mixedMoment B raw2306step0 raw2306step0Labels := by
      have ha : raw2306step0 = (fun i j => raw2306 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2306step0 raw2306; decide +kernel
      have hl : raw2306step0Labels = raw2306Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2306 raw2306Labels permutation12 permutation6
    mixedMoment B raw2306step0 raw2306step0Labels = mixedMoment B raw2306step1 raw2306step1Labels := by
      have ha : raw2306step1 = -raw2306step0 := by apply Matrix.ext; change ∀ i j, raw2306step1 i j = -(raw2306step0 i j); unfold raw2306step1 raw2306step0; decide +kernel
      have hl : raw2306step1Labels = raw2306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2306step1 raw2306step1Labels = mixedMoment B raw2306step2 raw2306step2Labels := by
      have ha : raw2306step2 = raw2306step1 := by apply Matrix.ext; unfold raw2306step2 raw2306step1; decide +kernel
      have hl : raw2306step1Labels = labelEmbedding1 ∘ raw2306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2306step1 raw2306step1Labels raw2306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3632 node3632Labels := by rfl

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

theorem canonical2544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2544 raw2544Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2544 raw2544Labels = mixedMoment B raw2544step0 raw2544step0Labels := by
      have ha : raw2544step0 = (fun i j => raw2544 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2544step0 raw2544; decide +kernel
      have hl : raw2544step0Labels = raw2544Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2544 raw2544Labels permutation8 permutation4
    mixedMoment B raw2544step0 raw2544step0Labels = mixedMoment B raw2544step1 raw2544step1Labels := by
      have ha : raw2544step1 = raw2544step0 := by apply Matrix.ext; unfold raw2544step1 raw2544step0; decide +kernel
      have hl : raw2544step0Labels = labelEmbedding7 ∘ raw2544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2544step0 raw2544step0Labels raw2544step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2545 raw2545Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw2545 raw2545Labels = mixedMoment B raw2545step0 raw2545step0Labels := by
      have ha : raw2545step0 = (fun i j => raw2545 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2545step0 raw2545; decide +kernel
      have hl : raw2545step0Labels = raw2545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2545 raw2545Labels permutation8 permutation4
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2546 raw2546Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw2546 raw2546Labels = mixedMoment B raw2546step0 raw2546step0Labels := by
      have ha : raw2546step0 = (fun i j => raw2546 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2546step0 raw2546; decide +kernel
      have hl : raw2546step0Labels = raw2546Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2546 raw2546Labels permutation9 permutation6
    mixedMoment B raw2546step0 raw2546step0Labels = mixedMoment B raw2546step1 raw2546step1Labels := by
      have ha : raw2546step1 = -raw2546step0 := by apply Matrix.ext; change ∀ i j, raw2546step1 i j = -(raw2546step0 i j); unfold raw2546step1 raw2546step0; decide +kernel
      have hl : raw2546step1Labels = raw2546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2546step1 raw2546step1Labels = mixedMoment B raw2546step2 raw2546step2Labels := by
      have ha : raw2546step2 = raw2546step1 := by apply Matrix.ext; unfold raw2546step2 raw2546step1; decide +kernel
      have hl : raw2546step1Labels = labelEmbedding1 ∘ raw2546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2546step1 raw2546step1Labels raw2546step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3907 node3907Labels := by rfl

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

theorem canonical272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw272 raw272Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw272 raw272Labels = mixedMoment B raw272step0 raw272step0Labels := by
      have ha : raw272step0 = (fun i j => raw272 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw272step0 raw272; decide +kernel
      have hl : raw272step0Labels = raw272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw272 raw272Labels permutation8 permutation5
    mixedMoment B raw272step0 raw272step0Labels = mixedMoment B raw272step1 raw272step1Labels := by
      have ha : raw272step1 = raw272step0 := by apply Matrix.ext; unfold raw272step1 raw272step0; decide +kernel
      have hl : raw272step0Labels = labelEmbedding1 ∘ raw272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw272step0 raw272step0Labels raw272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw273 raw273Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw273 raw273Labels = mixedMoment B raw273step0 raw273step0Labels := by
      have ha : raw273step0 = (fun i j => raw273 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw273step0 raw273; decide +kernel
      have hl : raw273step0Labels = raw273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw273 raw273Labels permutation8 permutation5
    _ = mixedMoment B node405 node405Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28337 raw28337Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw28337 raw28337Labels = mixedMoment B raw28337step0 raw28337step0Labels := by
      have hz : ∀ j, raw28337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28337step0 = (fun i j => raw28337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28337step0 raw28337; decide +kernel
      have hl : raw28337step0Labels = raw28337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28337 raw28337Labels permutation434 hz
    mixedMoment B raw28337step0 raw28337step0Labels = mixedMoment B raw28337step1 raw28337step1Labels := by
      have hz : ∀ j, raw28337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28337step1 = (fun i j => raw28337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28337step1 raw28337step0; decide +kernel
      have hl : raw28337step1Labels = raw28337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28337step0 raw28337step0Labels permutation80 hz
    mixedMoment B raw28337step1 raw28337step1Labels = mixedMoment B raw28337step2 raw28337step2Labels := by
      have ha : raw28337step2 = (fun i j => raw28337step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28337step2 raw28337step1; decide +kernel
      have hl : raw28337step2Labels = raw28337step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28337step1 raw28337step1Labels permutation30 permutation3
    mixedMoment B raw28337step2 raw28337step2Labels = mixedMoment B raw28337step3 raw28337step3Labels := by
      have ha : raw28337step3 = -raw28337step2 := by apply Matrix.ext; change ∀ i j, raw28337step3 i j = -(raw28337step2 i j); unfold raw28337step3 raw28337step2; decide +kernel
      have hl : raw28337step3Labels = raw28337step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28337step3 raw28337step3Labels = mixedMoment B raw28337step4 raw28337step4Labels := by
      have ha : raw28337step4 = raw28337step3 := by apply Matrix.ext; unfold raw28337step4 raw28337step3; decide +kernel
      have hl : raw28337step3Labels = labelEmbedding6 ∘ raw28337step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28337step3 raw28337step3Labels raw28337step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical28338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28338 raw28338Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw28338 raw28338Labels = mixedMoment B raw28338step0 raw28338step0Labels := by
      have hz : ∀ j, raw28338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28338step0 = (fun i j => raw28338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28338step0 raw28338; decide +kernel
      have hl : raw28338step0Labels = raw28338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28338 raw28338Labels permutation434 hz
    mixedMoment B raw28338step0 raw28338step0Labels = mixedMoment B raw28338step1 raw28338step1Labels := by
      have ha : raw28338step1 = (fun i j => raw28338step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28338step1 raw28338step0; decide +kernel
      have hl : raw28338step1Labels = raw28338step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28338step0 raw28338step0Labels permutation151 permutation3
    mixedMoment B raw28338step1 raw28338step1Labels = mixedMoment B raw28338step2 raw28338step2Labels := by
      have ha : raw28338step2 = -raw28338step1 := by apply Matrix.ext; change ∀ i j, raw28338step2 i j = -(raw28338step1 i j); unfold raw28338step2 raw28338step1; decide +kernel
      have hl : raw28338step2Labels = raw28338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28338step2 raw28338step2Labels = mixedMoment B raw28338step3 raw28338step3Labels := by
      have ha : raw28338step3 = raw28338step2 := by apply Matrix.ext; unfold raw28338step3 raw28338step2; decide +kernel
      have hl : raw28338step2Labels = labelEmbedding6 ∘ raw28338step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28338step2 raw28338step2Labels raw28338step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical28339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28339 raw28339Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw28339 raw28339Labels = mixedMoment B raw28339step0 raw28339step0Labels := by
      have hz : ∀ j, raw28339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28339step0 = (fun i j => raw28339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28339step0 raw28339; decide +kernel
      have hl : raw28339step0Labels = raw28339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28339 raw28339Labels permutation346 hz
    mixedMoment B raw28339step0 raw28339step0Labels = mixedMoment B raw28339step1 raw28339step1Labels := by
      have ha : raw28339step1 = (fun i j => raw28339step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28339step1 raw28339step0; decide +kernel
      have hl : raw28339step1Labels = raw28339step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28339step0 raw28339step0Labels permutation151 permutation3
    mixedMoment B raw28339step1 raw28339step1Labels = mixedMoment B raw28339step2 raw28339step2Labels := by
      have ha : raw28339step2 = -raw28339step1 := by apply Matrix.ext; change ∀ i j, raw28339step2 i j = -(raw28339step1 i j); unfold raw28339step2 raw28339step1; decide +kernel
      have hl : raw28339step2Labels = raw28339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28339step2 raw28339step2Labels = mixedMoment B raw28339step3 raw28339step3Labels := by
      have ha : raw28339step3 = raw28339step2 := by apply Matrix.ext; unfold raw28339step3 raw28339step2; decide +kernel
      have hl : raw28339step2Labels = labelEmbedding6 ∘ raw28339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28339step2 raw28339step2Labels raw28339step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical28340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28340 raw28340Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw28340 raw28340Labels = mixedMoment B raw28340step0 raw28340step0Labels := by
      have hz : ∀ j, raw28340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28340step0 = (fun i j => raw28340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28340step0 raw28340; decide +kernel
      have hl : raw28340step0Labels = raw28340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28340 raw28340Labels permutation434 hz
    mixedMoment B raw28340step0 raw28340step0Labels = mixedMoment B raw28340step1 raw28340step1Labels := by
      have hz : ∀ j, raw28340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28340step1 = (fun i j => raw28340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28340step1 raw28340step0; decide +kernel
      have hl : raw28340step1Labels = raw28340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28340step0 raw28340step0Labels permutation80 hz
    mixedMoment B raw28340step1 raw28340step1Labels = mixedMoment B raw28340step2 raw28340step2Labels := by
      have ha : raw28340step2 = (fun i j => raw28340step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28340step2 raw28340step1; decide +kernel
      have hl : raw28340step2Labels = raw28340step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28340step1 raw28340step1Labels permutation31 permutation3
    mixedMoment B raw28340step2 raw28340step2Labels = mixedMoment B raw28340step3 raw28340step3Labels := by
      have ha : raw28340step3 = -raw28340step2 := by apply Matrix.ext; change ∀ i j, raw28340step3 i j = -(raw28340step2 i j); unfold raw28340step3 raw28340step2; decide +kernel
      have hl : raw28340step3Labels = raw28340step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28340step3 raw28340step3Labels = mixedMoment B raw28340step4 raw28340step4Labels := by
      have ha : raw28340step4 = raw28340step3 := by apply Matrix.ext; unfold raw28340step4 raw28340step3; decide +kernel
      have hl : raw28340step3Labels = labelEmbedding6 ∘ raw28340step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28340step3 raw28340step3Labels raw28340step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical28341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28341 raw28341Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw28341 raw28341Labels = mixedMoment B raw28341step0 raw28341step0Labels := by
      have hz : ∀ j, raw28341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28341step0 = (fun i j => raw28341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28341step0 raw28341; decide +kernel
      have hl : raw28341step0Labels = raw28341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28341 raw28341Labels permutation434 hz
    mixedMoment B raw28341step0 raw28341step0Labels = mixedMoment B raw28341step1 raw28341step1Labels := by
      have hz : ∀ j, raw28341step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28341step1 = (fun i j => raw28341step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28341step1 raw28341step0; decide +kernel
      have hl : raw28341step1Labels = raw28341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28341step0 raw28341step0Labels permutation80 hz
    mixedMoment B raw28341step1 raw28341step1Labels = mixedMoment B raw28341step2 raw28341step2Labels := by
      have ha : raw28341step2 = (fun i j => raw28341step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28341step2 raw28341step1; decide +kernel
      have hl : raw28341step2Labels = raw28341step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28341step1 raw28341step1Labels permutation8 permutation3
    mixedMoment B raw28341step2 raw28341step2Labels = mixedMoment B raw28341step3 raw28341step3Labels := by
      have ha : raw28341step3 = raw28341step2 := by apply Matrix.ext; unfold raw28341step3 raw28341step2; decide +kernel
      have hl : raw28341step2Labels = labelEmbedding6 ∘ raw28341step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28341step2 raw28341step2Labels raw28341step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical28342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28342 raw28342Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28342 raw28342Labels = mixedMoment B raw28342step0 raw28342step0Labels := by
      have hz : ∀ j, raw28342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28342step0 = (fun i j => raw28342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28342step0 raw28342; decide +kernel
      have hl : raw28342step0Labels = raw28342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28342 raw28342Labels permutation434 hz
    mixedMoment B raw28342step0 raw28342step0Labels = mixedMoment B raw28342step1 raw28342step1Labels := by
      have ha : raw28342step1 = (fun i j => raw28342step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28342step1 raw28342step0; decide +kernel
      have hl : raw28342step1Labels = raw28342step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28342step0 raw28342step0Labels permutation149 permutation3
    mixedMoment B raw28342step1 raw28342step1Labels = mixedMoment B raw28342step2 raw28342step2Labels := by
      have ha : raw28342step2 = -raw28342step1 := by apply Matrix.ext; change ∀ i j, raw28342step2 i j = -(raw28342step1 i j); unfold raw28342step2 raw28342step1; decide +kernel
      have hl : raw28342step2Labels = raw28342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28342step2 raw28342step2Labels = mixedMoment B raw28342step3 raw28342step3Labels := by
      have ha : raw28342step3 = raw28342step2 := by apply Matrix.ext; unfold raw28342step3 raw28342step2; decide +kernel
      have hl : raw28342step2Labels = labelEmbedding6 ∘ raw28342step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28342step2 raw28342step2Labels raw28342step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical28343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28343 raw28343Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28343 raw28343Labels = mixedMoment B raw28343step0 raw28343step0Labels := by
      have hz : ∀ j, raw28343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28343step0 = (fun i j => raw28343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28343step0 raw28343; decide +kernel
      have hl : raw28343step0Labels = raw28343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28343 raw28343Labels permutation346 hz
    mixedMoment B raw28343step0 raw28343step0Labels = mixedMoment B raw28343step1 raw28343step1Labels := by
      have ha : raw28343step1 = (fun i j => raw28343step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28343step1 raw28343step0; decide +kernel
      have hl : raw28343step1Labels = raw28343step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28343step0 raw28343step0Labels permutation149 permutation3
    mixedMoment B raw28343step1 raw28343step1Labels = mixedMoment B raw28343step2 raw28343step2Labels := by
      have ha : raw28343step2 = -raw28343step1 := by apply Matrix.ext; change ∀ i j, raw28343step2 i j = -(raw28343step1 i j); unfold raw28343step2 raw28343step1; decide +kernel
      have hl : raw28343step2Labels = raw28343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28343step2 raw28343step2Labels = mixedMoment B raw28343step3 raw28343step3Labels := by
      have ha : raw28343step3 = raw28343step2 := by apply Matrix.ext; unfold raw28343step3 raw28343step2; decide +kernel
      have hl : raw28343step2Labels = labelEmbedding6 ∘ raw28343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28343step2 raw28343step2Labels raw28343step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical28344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28344 raw28344Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw28344 raw28344Labels = mixedMoment B raw28344step0 raw28344step0Labels := by
      have hz : ∀ j, raw28344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28344step0 = (fun i j => raw28344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28344step0 raw28344; decide +kernel
      have hl : raw28344step0Labels = raw28344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28344 raw28344Labels permutation434 hz
    mixedMoment B raw28344step0 raw28344step0Labels = mixedMoment B raw28344step1 raw28344step1Labels := by
      have hz : ∀ j, raw28344step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28344step1 = (fun i j => raw28344step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28344step1 raw28344step0; decide +kernel
      have hl : raw28344step1Labels = raw28344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28344step0 raw28344step0Labels permutation80 hz
    mixedMoment B raw28344step1 raw28344step1Labels = mixedMoment B raw28344step2 raw28344step2Labels := by
      have ha : raw28344step2 = (fun i j => raw28344step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28344step2 raw28344step1; decide +kernel
      have hl : raw28344step2Labels = raw28344step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28344step1 raw28344step1Labels permutation29 permutation3
    mixedMoment B raw28344step2 raw28344step2Labels = mixedMoment B raw28344step3 raw28344step3Labels := by
      have ha : raw28344step3 = -raw28344step2 := by apply Matrix.ext; change ∀ i j, raw28344step3 i j = -(raw28344step2 i j); unfold raw28344step3 raw28344step2; decide +kernel
      have hl : raw28344step3Labels = raw28344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28344step3 raw28344step3Labels = mixedMoment B raw28344step4 raw28344step4Labels := by
      have ha : raw28344step4 = raw28344step3 := by apply Matrix.ext; unfold raw28344step4 raw28344step3; decide +kernel
      have hl : raw28344step3Labels = labelEmbedding6 ∘ raw28344step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28344step3 raw28344step3Labels raw28344step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical28345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28345 raw28345Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw28345 raw28345Labels = mixedMoment B raw28345step0 raw28345step0Labels := by
      have hz : ∀ j, raw28345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28345step0 = (fun i j => raw28345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28345step0 raw28345; decide +kernel
      have hl : raw28345step0Labels = raw28345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28345 raw28345Labels permutation434 hz
    mixedMoment B raw28345step0 raw28345step0Labels = mixedMoment B raw28345step1 raw28345step1Labels := by
      have ha : raw28345step1 = (fun i j => raw28345step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28345step1 raw28345step0; decide +kernel
      have hl : raw28345step1Labels = raw28345step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28345step0 raw28345step0Labels permutation34 permutation3
    mixedMoment B raw28345step1 raw28345step1Labels = mixedMoment B raw28345step2 raw28345step2Labels := by
      have ha : raw28345step2 = raw28345step1 := by apply Matrix.ext; unfold raw28345step2 raw28345step1; decide +kernel
      have hl : raw28345step1Labels = labelEmbedding6 ∘ raw28345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28345step1 raw28345step1Labels raw28345step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

theorem canonical28346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28346 raw28346Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw28346 raw28346Labels = mixedMoment B raw28346step0 raw28346step0Labels := by
      have hz : ∀ j, raw28346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28346step0 = (fun i j => raw28346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28346step0 raw28346; decide +kernel
      have hl : raw28346step0Labels = raw28346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28346 raw28346Labels permutation434 hz
    mixedMoment B raw28346step0 raw28346step0Labels = mixedMoment B raw28346step1 raw28346step1Labels := by
      have ha : raw28346step1 = (fun i j => raw28346step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28346step1 raw28346step0; decide +kernel
      have hl : raw28346step1Labels = raw28346step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28346step0 raw28346step0Labels permutation145 permutation3
    mixedMoment B raw28346step1 raw28346step1Labels = mixedMoment B raw28346step2 raw28346step2Labels := by
      have ha : raw28346step2 = -raw28346step1 := by apply Matrix.ext; change ∀ i j, raw28346step2 i j = -(raw28346step1 i j); unfold raw28346step2 raw28346step1; decide +kernel
      have hl : raw28346step2Labels = raw28346step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28346step2 raw28346step2Labels = mixedMoment B raw28346step3 raw28346step3Labels := by
      have ha : raw28346step3 = raw28346step2 := by apply Matrix.ext; unfold raw28346step3 raw28346step2; decide +kernel
      have hl : raw28346step2Labels = labelEmbedding6 ∘ raw28346step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28346step2 raw28346step2Labels raw28346step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

theorem canonical28347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28347 raw28347Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw28347 raw28347Labels = mixedMoment B raw28347step0 raw28347step0Labels := by
      have ha : raw28347step0 = (fun i j => raw28347 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28347step0 raw28347; decide +kernel
      have hl : raw28347step0Labels = raw28347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28347 raw28347Labels permutation646 permutation3
    mixedMoment B raw28347step0 raw28347step0Labels = mixedMoment B raw28347step1 raw28347step1Labels := by
      have ha : raw28347step1 = -raw28347step0 := by apply Matrix.ext; change ∀ i j, raw28347step1 i j = -(raw28347step0 i j); unfold raw28347step1 raw28347step0; decide +kernel
      have hl : raw28347step1Labels = raw28347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28347step1 raw28347step1Labels = mixedMoment B raw28347step2 raw28347step2Labels := by
      have ha : raw28347step2 = raw28347step1 := by apply Matrix.ext; unfold raw28347step2 raw28347step1; decide +kernel
      have hl : raw28347step1Labels = labelEmbedding6 ∘ raw28347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28347step1 raw28347step1Labels raw28347step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

theorem canonical28348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28348 raw28348Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw28348 raw28348Labels = mixedMoment B raw28348step0 raw28348step0Labels := by
      have hz : ∀ j, raw28348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28348step0 = (fun i j => raw28348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28348step0 raw28348; decide +kernel
      have hl : raw28348step0Labels = raw28348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28348 raw28348Labels permutation434 hz
    mixedMoment B raw28348step0 raw28348step0Labels = mixedMoment B raw28348step1 raw28348step1Labels := by
      have ha : raw28348step1 = (fun i j => raw28348step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28348step1 raw28348step0; decide +kernel
      have hl : raw28348step1Labels = raw28348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28348step0 raw28348step0Labels permutation145 permutation3
    mixedMoment B raw28348step1 raw28348step1Labels = mixedMoment B raw28348step2 raw28348step2Labels := by
      have ha : raw28348step2 = -raw28348step1 := by apply Matrix.ext; change ∀ i j, raw28348step2 i j = -(raw28348step1 i j); unfold raw28348step2 raw28348step1; decide +kernel
      have hl : raw28348step2Labels = raw28348step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28348step2 raw28348step2Labels = mixedMoment B raw28348step3 raw28348step3Labels := by
      have ha : raw28348step3 = raw28348step2 := by apply Matrix.ext; unfold raw28348step3 raw28348step2; decide +kernel
      have hl : raw28348step2Labels = labelEmbedding6 ∘ raw28348step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28348step2 raw28348step2Labels raw28348step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical28349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28349 raw28349Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw28349 raw28349Labels = mixedMoment B raw28349step0 raw28349step0Labels := by
      have hz : ∀ j, raw28349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28349step0 = (fun i j => raw28349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28349step0 raw28349; decide +kernel
      have hl : raw28349step0Labels = raw28349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28349 raw28349Labels permutation434 hz
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical28350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28350 raw28350Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw28350 raw28350Labels = mixedMoment B raw28350step0 raw28350step0Labels := by
      have hz : ∀ j, raw28350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28350step0 = (fun i j => raw28350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28350step0 raw28350; decide +kernel
      have hl : raw28350step0Labels = raw28350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28350 raw28350Labels permutation346 hz
    mixedMoment B raw28350step0 raw28350step0Labels = mixedMoment B raw28350step1 raw28350step1Labels := by
      have ha : raw28350step1 = (fun i j => raw28350step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28350step1 raw28350step0; decide +kernel
      have hl : raw28350step1Labels = raw28350step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28350step0 raw28350step0Labels permutation34 permutation3
    mixedMoment B raw28350step1 raw28350step1Labels = mixedMoment B raw28350step2 raw28350step2Labels := by
      have ha : raw28350step2 = raw28350step1 := by apply Matrix.ext; unfold raw28350step2 raw28350step1; decide +kernel
      have hl : raw28350step1Labels = labelEmbedding6 ∘ raw28350step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28350step1 raw28350step1Labels raw28350step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

theorem canonical28351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28351 raw28351Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw28351 raw28351Labels = mixedMoment B raw28351step0 raw28351step0Labels := by
      have hz : ∀ j, raw28351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28351step0 = (fun i j => raw28351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28351step0 raw28351; decide +kernel
      have hl : raw28351step0Labels = raw28351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28351 raw28351Labels permutation346 hz
    mixedMoment B raw28351step0 raw28351step0Labels = mixedMoment B raw28351step1 raw28351step1Labels := by
      have ha : raw28351step1 = (fun i j => raw28351step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28351step1 raw28351step0; decide +kernel
      have hl : raw28351step1Labels = raw28351step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28351step0 raw28351step0Labels permutation145 permutation3
    mixedMoment B raw28351step1 raw28351step1Labels = mixedMoment B raw28351step2 raw28351step2Labels := by
      have ha : raw28351step2 = -raw28351step1 := by apply Matrix.ext; change ∀ i j, raw28351step2 i j = -(raw28351step1 i j); unfold raw28351step2 raw28351step1; decide +kernel
      have hl : raw28351step2Labels = raw28351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28351step2 raw28351step2Labels = mixedMoment B raw28351step3 raw28351step3Labels := by
      have ha : raw28351step3 = raw28351step2 := by apply Matrix.ext; unfold raw28351step3 raw28351step2; decide +kernel
      have hl : raw28351step2Labels = labelEmbedding6 ∘ raw28351step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28351step2 raw28351step2Labels raw28351step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

theorem canonical28352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28352 raw28352Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw28352 raw28352Labels = mixedMoment B raw28352step0 raw28352step0Labels := by
      have ha : raw28352step0 = (fun i j => raw28352 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28352step0 raw28352; decide +kernel
      have hl : raw28352step0Labels = raw28352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28352 raw28352Labels permutation664 permutation3
    mixedMoment B raw28352step0 raw28352step0Labels = mixedMoment B raw28352step1 raw28352step1Labels := by
      have ha : raw28352step1 = -raw28352step0 := by apply Matrix.ext; change ∀ i j, raw28352step1 i j = -(raw28352step0 i j); unfold raw28352step1 raw28352step0; decide +kernel
      have hl : raw28352step1Labels = raw28352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28352step1 raw28352step1Labels = mixedMoment B raw28352step2 raw28352step2Labels := by
      have ha : raw28352step2 = raw28352step1 := by apply Matrix.ext; unfold raw28352step2 raw28352step1; decide +kernel
      have hl : raw28352step1Labels = labelEmbedding6 ∘ raw28352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28352step1 raw28352step1Labels raw28352step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

theorem canonical28353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28353 raw28353Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw28353 raw28353Labels = mixedMoment B raw28353step0 raw28353step0Labels := by
      have hz : ∀ j, raw28353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28353step0 = (fun i j => raw28353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28353step0 raw28353; decide +kernel
      have hl : raw28353step0Labels = raw28353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28353 raw28353Labels permutation346 hz
    mixedMoment B raw28353step0 raw28353step0Labels = mixedMoment B raw28353step1 raw28353step1Labels := by
      have ha : raw28353step1 = (fun i j => raw28353step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28353step1 raw28353step0; decide +kernel
      have hl : raw28353step1Labels = raw28353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28353step0 raw28353step0Labels permutation145 permutation3
    mixedMoment B raw28353step1 raw28353step1Labels = mixedMoment B raw28353step2 raw28353step2Labels := by
      have ha : raw28353step2 = -raw28353step1 := by apply Matrix.ext; change ∀ i j, raw28353step2 i j = -(raw28353step1 i j); unfold raw28353step2 raw28353step1; decide +kernel
      have hl : raw28353step2Labels = raw28353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28353step2 raw28353step2Labels = mixedMoment B raw28353step3 raw28353step3Labels := by
      have ha : raw28353step3 = raw28353step2 := by apply Matrix.ext; unfold raw28353step3 raw28353step2; decide +kernel
      have hl : raw28353step2Labels = labelEmbedding6 ∘ raw28353step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28353step2 raw28353step2Labels raw28353step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical28354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28354 raw28354Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw28354 raw28354Labels = mixedMoment B raw28354step0 raw28354step0Labels := by
      have hz : ∀ j, raw28354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28354step0 = (fun i j => raw28354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28354step0 raw28354; decide +kernel
      have hl : raw28354step0Labels = raw28354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28354 raw28354Labels permutation346 hz
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical28355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28355 raw28355Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw28355 raw28355Labels = mixedMoment B raw28355step0 raw28355step0Labels := by
      have hz : ∀ j, raw28355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28355step0 = (fun i j => raw28355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28355step0 raw28355; decide +kernel
      have hl : raw28355step0Labels = raw28355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28355 raw28355Labels permutation434 hz
    mixedMoment B raw28355step0 raw28355step0Labels = mixedMoment B raw28355step1 raw28355step1Labels := by
      have hz : ∀ j, raw28355step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28355step1 = (fun i j => raw28355step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28355step1 raw28355step0; decide +kernel
      have hl : raw28355step1Labels = raw28355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28355step0 raw28355step0Labels permutation80 hz
    mixedMoment B raw28355step1 raw28355step1Labels = mixedMoment B raw28355step2 raw28355step2Labels := by
      have ha : raw28355step2 = (fun i j => raw28355step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28355step2 raw28355step1; decide +kernel
      have hl : raw28355step2Labels = raw28355step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28355step1 raw28355step1Labels permutation8 permutation3
    mixedMoment B raw28355step2 raw28355step2Labels = mixedMoment B raw28355step3 raw28355step3Labels := by
      have ha : raw28355step3 = raw28355step2 := by apply Matrix.ext; unfold raw28355step3 raw28355step2; decide +kernel
      have hl : raw28355step2Labels = labelEmbedding6 ∘ raw28355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28355step2 raw28355step2Labels raw28355step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

theorem canonical28356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28356 raw28356Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw28356 raw28356Labels = mixedMoment B raw28356step0 raw28356step0Labels := by
      have hz : ∀ j, raw28356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28356step0 = (fun i j => raw28356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28356step0 raw28356; decide +kernel
      have hl : raw28356step0Labels = raw28356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28356 raw28356Labels permutation434 hz
    mixedMoment B raw28356step0 raw28356step0Labels = mixedMoment B raw28356step1 raw28356step1Labels := by
      have hz : ∀ j, raw28356step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28356step1 = (fun i j => raw28356step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28356step1 raw28356step0; decide +kernel
      have hl : raw28356step1Labels = raw28356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28356step0 raw28356step0Labels permutation80 hz
    mixedMoment B raw28356step1 raw28356step1Labels = mixedMoment B raw28356step2 raw28356step2Labels := by
      have ha : raw28356step2 = (fun i j => raw28356step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28356step2 raw28356step1; decide +kernel
      have hl : raw28356step2Labels = raw28356step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28356step1 raw28356step1Labels permutation31 permutation3
    mixedMoment B raw28356step2 raw28356step2Labels = mixedMoment B raw28356step3 raw28356step3Labels := by
      have ha : raw28356step3 = -raw28356step2 := by apply Matrix.ext; change ∀ i j, raw28356step3 i j = -(raw28356step2 i j); unfold raw28356step3 raw28356step2; decide +kernel
      have hl : raw28356step3Labels = raw28356step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28356step3 raw28356step3Labels = mixedMoment B raw28356step4 raw28356step4Labels := by
      have ha : raw28356step4 = raw28356step3 := by apply Matrix.ext; unfold raw28356step4 raw28356step3; decide +kernel
      have hl : raw28356step3Labels = labelEmbedding6 ∘ raw28356step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28356step3 raw28356step3Labels raw28356step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

theorem canonical28357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28357 raw28357Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw28357 raw28357Labels = mixedMoment B raw28357step0 raw28357step0Labels := by
      have hz : ∀ j, raw28357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28357step0 = (fun i j => raw28357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28357step0 raw28357; decide +kernel
      have hl : raw28357step0Labels = raw28357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28357 raw28357Labels permutation434 hz
    mixedMoment B raw28357step0 raw28357step0Labels = mixedMoment B raw28357step1 raw28357step1Labels := by
      have ha : raw28357step1 = (fun i j => raw28357step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28357step1 raw28357step0; decide +kernel
      have hl : raw28357step1Labels = raw28357step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28357step0 raw28357step0Labels permutation151 permutation3
    mixedMoment B raw28357step1 raw28357step1Labels = mixedMoment B raw28357step2 raw28357step2Labels := by
      have ha : raw28357step2 = -raw28357step1 := by apply Matrix.ext; change ∀ i j, raw28357step2 i j = -(raw28357step1 i j); unfold raw28357step2 raw28357step1; decide +kernel
      have hl : raw28357step2Labels = raw28357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28357step2 raw28357step2Labels = mixedMoment B raw28357step3 raw28357step3Labels := by
      have ha : raw28357step3 = raw28357step2 := by apply Matrix.ext; unfold raw28357step3 raw28357step2; decide +kernel
      have hl : raw28357step2Labels = labelEmbedding6 ∘ raw28357step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28357step2 raw28357step2Labels raw28357step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

theorem canonical28358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28358 raw28358Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw28358 raw28358Labels = mixedMoment B raw28358step0 raw28358step0Labels := by
      have hz : ∀ j, raw28358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28358step0 = (fun i j => raw28358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28358step0 raw28358; decide +kernel
      have hl : raw28358step0Labels = raw28358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28358 raw28358Labels permutation346 hz
    mixedMoment B raw28358step0 raw28358step0Labels = mixedMoment B raw28358step1 raw28358step1Labels := by
      have ha : raw28358step1 = (fun i j => raw28358step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28358step1 raw28358step0; decide +kernel
      have hl : raw28358step1Labels = raw28358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28358step0 raw28358step0Labels permutation151 permutation3
    mixedMoment B raw28358step1 raw28358step1Labels = mixedMoment B raw28358step2 raw28358step2Labels := by
      have ha : raw28358step2 = -raw28358step1 := by apply Matrix.ext; change ∀ i j, raw28358step2 i j = -(raw28358step1 i j); unfold raw28358step2 raw28358step1; decide +kernel
      have hl : raw28358step2Labels = raw28358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28358step2 raw28358step2Labels = mixedMoment B raw28358step3 raw28358step3Labels := by
      have ha : raw28358step3 = raw28358step2 := by apply Matrix.ext; unfold raw28358step3 raw28358step2; decide +kernel
      have hl : raw28358step2Labels = labelEmbedding6 ∘ raw28358step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28358step2 raw28358step2Labels raw28358step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

theorem canonical28359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28359 raw28359Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw28359 raw28359Labels = mixedMoment B raw28359step0 raw28359step0Labels := by
      have hz : ∀ j, raw28359 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28359step0 = (fun i j => raw28359 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28359step0 raw28359; decide +kernel
      have hl : raw28359step0Labels = raw28359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28359 raw28359Labels permutation434 hz
    mixedMoment B raw28359step0 raw28359step0Labels = mixedMoment B raw28359step1 raw28359step1Labels := by
      have hz : ∀ j, raw28359step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28359step1 = (fun i j => raw28359step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28359step1 raw28359step0; decide +kernel
      have hl : raw28359step1Labels = raw28359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28359step0 raw28359step0Labels permutation80 hz
    mixedMoment B raw28359step1 raw28359step1Labels = mixedMoment B raw28359step2 raw28359step2Labels := by
      have ha : raw28359step2 = (fun i j => raw28359step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28359step2 raw28359step1; decide +kernel
      have hl : raw28359step2Labels = raw28359step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28359step1 raw28359step1Labels permutation9 permutation2
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical28360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28360 raw28360Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw28360 raw28360Labels = mixedMoment B raw28360step0 raw28360step0Labels := by
      have hz : ∀ j, raw28360 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28360step0 = (fun i j => raw28360 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28360step0 raw28360; decide +kernel
      have hl : raw28360step0Labels = raw28360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28360 raw28360Labels permutation434 hz
    mixedMoment B raw28360step0 raw28360step0Labels = mixedMoment B raw28360step1 raw28360step1Labels := by
      have hz : ∀ j, raw28360step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28360step1 = (fun i j => raw28360step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28360step1 raw28360step0; decide +kernel
      have hl : raw28360step1Labels = raw28360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28360step0 raw28360step0Labels permutation80 hz
    mixedMoment B raw28360step1 raw28360step1Labels = mixedMoment B raw28360step2 raw28360step2Labels := by
      have ha : raw28360step2 = (fun i j => raw28360step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28360step2 raw28360step1; decide +kernel
      have hl : raw28360step2Labels = raw28360step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28360step1 raw28360step1Labels permutation31 permutation3
    mixedMoment B raw28360step2 raw28360step2Labels = mixedMoment B raw28360step3 raw28360step3Labels := by
      have ha : raw28360step3 = -raw28360step2 := by apply Matrix.ext; change ∀ i j, raw28360step3 i j = -(raw28360step2 i j); unfold raw28360step3 raw28360step2; decide +kernel
      have hl : raw28360step3Labels = raw28360step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28360step3 raw28360step3Labels = mixedMoment B raw28360step4 raw28360step4Labels := by
      have ha : raw28360step4 = raw28360step3 := by apply Matrix.ext; unfold raw28360step4 raw28360step3; decide +kernel
      have hl : raw28360step3Labels = labelEmbedding6 ∘ raw28360step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28360step3 raw28360step3Labels raw28360step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4225 node4225Labels := by rfl

theorem canonical28361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28361 raw28361Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw28361 raw28361Labels = mixedMoment B raw28361step0 raw28361step0Labels := by
      have hz : ∀ j, raw28361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28361step0 = (fun i j => raw28361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28361step0 raw28361; decide +kernel
      have hl : raw28361step0Labels = raw28361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28361 raw28361Labels permutation434 hz
    mixedMoment B raw28361step0 raw28361step0Labels = mixedMoment B raw28361step1 raw28361step1Labels := by
      have hz : ∀ j, raw28361step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28361step1 = (fun i j => raw28361step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28361step1 raw28361step0; decide +kernel
      have hl : raw28361step1Labels = raw28361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28361step0 raw28361step0Labels permutation80 hz
    mixedMoment B raw28361step1 raw28361step1Labels = mixedMoment B raw28361step2 raw28361step2Labels := by
      have ha : raw28361step2 = (fun i j => raw28361step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28361step2 raw28361step1; decide +kernel
      have hl : raw28361step2Labels = raw28361step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28361step1 raw28361step1Labels permutation31 permutation3
    mixedMoment B raw28361step2 raw28361step2Labels = mixedMoment B raw28361step3 raw28361step3Labels := by
      have ha : raw28361step3 = -raw28361step2 := by apply Matrix.ext; change ∀ i j, raw28361step3 i j = -(raw28361step2 i j); unfold raw28361step3 raw28361step2; decide +kernel
      have hl : raw28361step3Labels = raw28361step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28361step3 raw28361step3Labels = mixedMoment B raw28361step4 raw28361step4Labels := by
      have ha : raw28361step4 = raw28361step3 := by apply Matrix.ext; unfold raw28361step4 raw28361step3; decide +kernel
      have hl : raw28361step3Labels = labelEmbedding6 ∘ raw28361step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28361step3 raw28361step3Labels raw28361step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

theorem canonical28362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28362 raw28362Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw28362 raw28362Labels = mixedMoment B raw28362step0 raw28362step0Labels := by
      have hz : ∀ j, raw28362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28362step0 = (fun i j => raw28362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28362step0 raw28362; decide +kernel
      have hl : raw28362step0Labels = raw28362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28362 raw28362Labels permutation434 hz
    mixedMoment B raw28362step0 raw28362step0Labels = mixedMoment B raw28362step1 raw28362step1Labels := by
      have ha : raw28362step1 = (fun i j => raw28362step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28362step1 raw28362step0; decide +kernel
      have hl : raw28362step1Labels = raw28362step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28362step0 raw28362step0Labels permutation151 permutation3
    mixedMoment B raw28362step1 raw28362step1Labels = mixedMoment B raw28362step2 raw28362step2Labels := by
      have ha : raw28362step2 = -raw28362step1 := by apply Matrix.ext; change ∀ i j, raw28362step2 i j = -(raw28362step1 i j); unfold raw28362step2 raw28362step1; decide +kernel
      have hl : raw28362step2Labels = raw28362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28362step2 raw28362step2Labels = mixedMoment B raw28362step3 raw28362step3Labels := by
      have ha : raw28362step3 = raw28362step2 := by apply Matrix.ext; unfold raw28362step3 raw28362step2; decide +kernel
      have hl : raw28362step2Labels = labelEmbedding6 ∘ raw28362step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28362step2 raw28362step2Labels raw28362step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

theorem canonical28363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28363 raw28363Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw28363 raw28363Labels = mixedMoment B raw28363step0 raw28363step0Labels := by
      have hz : ∀ j, raw28363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28363step0 = (fun i j => raw28363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28363step0 raw28363; decide +kernel
      have hl : raw28363step0Labels = raw28363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28363 raw28363Labels permutation346 hz
    mixedMoment B raw28363step0 raw28363step0Labels = mixedMoment B raw28363step1 raw28363step1Labels := by
      have ha : raw28363step1 = (fun i j => raw28363step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28363step1 raw28363step0; decide +kernel
      have hl : raw28363step1Labels = raw28363step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28363step0 raw28363step0Labels permutation151 permutation3
    mixedMoment B raw28363step1 raw28363step1Labels = mixedMoment B raw28363step2 raw28363step2Labels := by
      have ha : raw28363step2 = -raw28363step1 := by apply Matrix.ext; change ∀ i j, raw28363step2 i j = -(raw28363step1 i j); unfold raw28363step2 raw28363step1; decide +kernel
      have hl : raw28363step2Labels = raw28363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28363step2 raw28363step2Labels = mixedMoment B raw28363step3 raw28363step3Labels := by
      have ha : raw28363step3 = raw28363step2 := by apply Matrix.ext; unfold raw28363step3 raw28363step2; decide +kernel
      have hl : raw28363step2Labels = labelEmbedding6 ∘ raw28363step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28363step2 raw28363step2Labels raw28363step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

theorem canonical28364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28364 raw28364Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw28364 raw28364Labels = mixedMoment B raw28364step0 raw28364step0Labels := by
      have hz : ∀ j, raw28364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28364step0 = (fun i j => raw28364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28364step0 raw28364; decide +kernel
      have hl : raw28364step0Labels = raw28364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28364 raw28364Labels permutation434 hz
    mixedMoment B raw28364step0 raw28364step0Labels = mixedMoment B raw28364step1 raw28364step1Labels := by
      have hz : ∀ j, raw28364step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28364step1 = (fun i j => raw28364step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28364step1 raw28364step0; decide +kernel
      have hl : raw28364step1Labels = raw28364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28364step0 raw28364step0Labels permutation80 hz
    mixedMoment B raw28364step1 raw28364step1Labels = mixedMoment B raw28364step2 raw28364step2Labels := by
      have ha : raw28364step2 = (fun i j => raw28364step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28364step2 raw28364step1; decide +kernel
      have hl : raw28364step2Labels = raw28364step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28364step1 raw28364step1Labels permutation31 permutation3
    mixedMoment B raw28364step2 raw28364step2Labels = mixedMoment B raw28364step3 raw28364step3Labels := by
      have ha : raw28364step3 = -raw28364step2 := by apply Matrix.ext; change ∀ i j, raw28364step3 i j = -(raw28364step2 i j); unfold raw28364step3 raw28364step2; decide +kernel
      have hl : raw28364step3Labels = raw28364step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28364step3 raw28364step3Labels = mixedMoment B raw28364step4 raw28364step4Labels := by
      have ha : raw28364step4 = raw28364step3 := by apply Matrix.ext; unfold raw28364step4 raw28364step3; decide +kernel
      have hl : raw28364step3Labels = labelEmbedding6 ∘ raw28364step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28364step3 raw28364step3Labels raw28364step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3314 raw3314Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw3314 raw3314Labels = mixedMoment B raw3314step0 raw3314step0Labels := by
      have hz : ∀ j, raw3314 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3314step0 = (fun i j => raw3314 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3314step0 raw3314; decide +kernel
      have hl : raw3314step0Labels = raw3314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3314 raw3314Labels permutation434 hz
    mixedMoment B raw3314step0 raw3314step0Labels = mixedMoment B raw3314step1 raw3314step1Labels := by
      have hz : ∀ j, raw3314step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3314step1 = (fun i j => raw3314step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3314step1 raw3314step0; decide +kernel
      have hl : raw3314step1Labels = raw3314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3314step0 raw3314step0Labels permutation80 hz
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical3315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3315 raw3315Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw3315 raw3315Labels = mixedMoment B raw3315step0 raw3315step0Labels := by
      have hz : ∀ j, raw3315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3315step0 = (fun i j => raw3315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3315step0 raw3315; decide +kernel
      have hl : raw3315step0Labels = raw3315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3315 raw3315Labels permutation434 hz
    mixedMoment B raw3315step0 raw3315step0Labels = mixedMoment B raw3315step1 raw3315step1Labels := by
      have hz : ∀ j, raw3315step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3315step1 = (fun i j => raw3315step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3315step1 raw3315step0; decide +kernel
      have hl : raw3315step1Labels = raw3315step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3315step0 raw3315step0Labels permutation80 hz
    mixedMoment B raw3315step1 raw3315step1Labels = mixedMoment B raw3315step2 raw3315step2Labels := by
      have ha : raw3315step2 = (fun i j => raw3315step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3315step2 raw3315step1; decide +kernel
      have hl : raw3315step2Labels = raw3315step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3315step1 raw3315step1Labels permutation31 permutation3
    mixedMoment B raw3315step2 raw3315step2Labels = mixedMoment B raw3315step3 raw3315step3Labels := by
      have ha : raw3315step3 = -raw3315step2 := by apply Matrix.ext; change ∀ i j, raw3315step3 i j = -(raw3315step2 i j); unfold raw3315step3 raw3315step2; decide +kernel
      have hl : raw3315step3Labels = raw3315step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3315step3 raw3315step3Labels = mixedMoment B raw3315step4 raw3315step4Labels := by
      have ha : raw3315step4 = raw3315step3 := by apply Matrix.ext; unfold raw3315step4 raw3315step3; decide +kernel
      have hl : raw3315step3Labels = labelEmbedding6 ∘ raw3315step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3315step3 raw3315step3Labels raw3315step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

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

theorem canonical536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw536 raw536Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw536 raw536Labels = mixedMoment B raw536step0 raw536step0Labels := by
      have ha : raw536step0 = (fun i j => raw536 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw536step0 raw536; decide +kernel
      have hl : raw536step0Labels = raw536Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw536 raw536Labels permutation8 permutation5
    mixedMoment B raw536step0 raw536step0Labels = mixedMoment B raw536step1 raw536step1Labels := by
      have ha : raw536step1 = raw536step0 := by apply Matrix.ext; unfold raw536step1 raw536step0; decide +kernel
      have hl : raw536step0Labels = labelEmbedding1 ∘ raw536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw536step0 raw536step0Labels raw536step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw537 raw537Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw537 raw537Labels = mixedMoment B raw537step0 raw537step0Labels := by
      have ha : raw537step0 = (fun i j => raw537 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw537step0 raw537; decide +kernel
      have hl : raw537step0Labels = raw537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw537 raw537Labels permutation8 permutation5
    _ = mixedMoment B node496 node496Labels := by rfl

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

theorem canonical903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw903 raw903Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw903 raw903Labels = mixedMoment B raw903step0 raw903step0Labels := by
      have ha : raw903step0 = (fun i j => raw903 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw903step0 raw903; decide +kernel
      have hl : raw903step0Labels = raw903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw903 raw903Labels permutation32 permutation4
    mixedMoment B raw903step0 raw903step0Labels = mixedMoment B raw903step1 raw903step1Labels := by
      have ha : raw903step1 = raw903step0 := by apply Matrix.ext; unfold raw903step1 raw903step0; decide +kernel
      have hl : raw903step0Labels = labelEmbedding7 ∘ raw903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw903step0 raw903step0Labels raw903step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

theorem canonical904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw904 raw904Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw904 raw904Labels = mixedMoment B raw904step0 raw904step0Labels := by
      have ha : raw904step0 = (fun i j => raw904 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw904step0 raw904; decide +kernel
      have hl : raw904step0Labels = raw904Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw904 raw904Labels permutation32 permutation4
    _ = mixedMoment B node720 node720Labels := by rfl

theorem canonical905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw905 raw905Labels = mixedMoment B node769 node769Labels := by
  calc
    mixedMoment B raw905 raw905Labels = mixedMoment B raw905step0 raw905step0Labels := by
      have ha : raw905step0 = (fun i j => raw905 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw905step0 raw905; decide +kernel
      have hl : raw905step0Labels = raw905Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw905 raw905Labels permutation33 permutation6
    mixedMoment B raw905step0 raw905step0Labels = mixedMoment B raw905step1 raw905step1Labels := by
      have ha : raw905step1 = -raw905step0 := by apply Matrix.ext; change ∀ i j, raw905step1 i j = -(raw905step0 i j); unfold raw905step1 raw905step0; decide +kernel
      have hl : raw905step1Labels = raw905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw905step1 raw905step1Labels = mixedMoment B raw905step2 raw905step2Labels := by
      have ha : raw905step2 = raw905step1 := by apply Matrix.ext; unfold raw905step2 raw905step1; decide +kernel
      have hl : raw905step1Labels = labelEmbedding1 ∘ raw905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw905step1 raw905step1Labels raw905step2Labels labelEmbedding1 hl
    _ = mixedMoment B node769 node769Labels := by rfl

theorem canonical915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw915 raw915Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw915 raw915Labels = mixedMoment B raw915step0 raw915step0Labels := by
      have ha : raw915step0 = (fun i j => raw915 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw915step0 raw915; decide +kernel
      have hl : raw915step0Labels = raw915Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw915 raw915Labels permutation8 permutation4
    mixedMoment B raw915step0 raw915step0Labels = mixedMoment B raw915step1 raw915step1Labels := by
      have ha : raw915step1 = raw915step0 := by apply Matrix.ext; unfold raw915step1 raw915step0; decide +kernel
      have hl : raw915step0Labels = labelEmbedding7 ∘ raw915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw915step0 raw915step0Labels raw915step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4225 node4225Labels := by rfl

theorem canonical916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw916 raw916Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw916 raw916Labels = mixedMoment B raw916step0 raw916step0Labels := by
      have ha : raw916step0 = (fun i j => raw916 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw916step0 raw916; decide +kernel
      have hl : raw916step0Labels = raw916Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw916 raw916Labels permutation8 permutation4
    _ = mixedMoment B node726 node726Labels := by rfl

theorem canonical917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw917 raw917Labels = mixedMoment B node774 node774Labels := by
  calc
    mixedMoment B raw917 raw917Labels = mixedMoment B raw917step0 raw917step0Labels := by
      have ha : raw917step0 = (fun i j => raw917 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw917step0 raw917; decide +kernel
      have hl : raw917step0Labels = raw917Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw917 raw917Labels permutation8 permutation6
    mixedMoment B raw917step0 raw917step0Labels = mixedMoment B raw917step1 raw917step1Labels := by
      have ha : raw917step1 = -raw917step0 := by apply Matrix.ext; change ∀ i j, raw917step1 i j = -(raw917step0 i j); unfold raw917step1 raw917step0; decide +kernel
      have hl : raw917step1Labels = raw917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw917step1 raw917step1Labels = mixedMoment B raw917step2 raw917step2Labels := by
      have ha : raw917step2 = raw917step1 := by apply Matrix.ext; unfold raw917step2 raw917step1; decide +kernel
      have hl : raw917step1Labels = labelEmbedding1 ∘ raw917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw917step1 raw917step1Labels raw917step2Labels labelEmbedding1 hl
    _ = mixedMoment B node774 node774Labels := by rfl

theorem canonical921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw921 raw921Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw921 raw921Labels = mixedMoment B raw921step0 raw921step0Labels := by
      have ha : raw921step0 = (fun i j => raw921 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw921step0 raw921; decide +kernel
      have hl : raw921step0Labels = raw921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw921 raw921Labels permutation8 permutation4
    mixedMoment B raw921step0 raw921step0Labels = mixedMoment B raw921step1 raw921step1Labels := by
      have ha : raw921step1 = raw921step0 := by apply Matrix.ext; unfold raw921step1 raw921step0; decide +kernel
      have hl : raw921step0Labels = labelEmbedding7 ∘ raw921step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw921step0 raw921step0Labels raw921step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

theorem canonical922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw922 raw922Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw922 raw922Labels = mixedMoment B raw922step0 raw922step0Labels := by
      have ha : raw922step0 = (fun i j => raw922 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw922step0 raw922; decide +kernel
      have hl : raw922step0Labels = raw922Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw922 raw922Labels permutation8 permutation4
    _ = mixedMoment B node729 node729Labels := by rfl

theorem canonical923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw923 raw923Labels = mixedMoment B node773 node773Labels := by
  calc
    mixedMoment B raw923 raw923Labels = mixedMoment B raw923step0 raw923step0Labels := by
      have ha : raw923step0 = (fun i j => raw923 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw923step0 raw923; decide +kernel
      have hl : raw923step0Labels = raw923Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw923 raw923Labels permutation9 permutation6
    mixedMoment B raw923step0 raw923step0Labels = mixedMoment B raw923step1 raw923step1Labels := by
      have ha : raw923step1 = -raw923step0 := by apply Matrix.ext; change ∀ i j, raw923step1 i j = -(raw923step0 i j); unfold raw923step1 raw923step0; decide +kernel
      have hl : raw923step1Labels = raw923step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw923step1 raw923step1Labels = mixedMoment B raw923step2 raw923step2Labels := by
      have ha : raw923step2 = raw923step1 := by apply Matrix.ext; unfold raw923step2 raw923step1; decide +kernel
      have hl : raw923step1Labels = labelEmbedding1 ∘ raw923step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw923step1 raw923step1Labels raw923step2Labels labelEmbedding1 hl
    _ = mixedMoment B node773 node773Labels := by rfl

theorem canonical996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw996 raw996Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw996 raw996Labels = mixedMoment B raw996step0 raw996step0Labels := by
      have ha : raw996step0 = (fun i j => raw996 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw996step0 raw996; decide +kernel
      have hl : raw996step0Labels = raw996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw996 raw996Labels permutation8 permutation4
    mixedMoment B raw996step0 raw996step0Labels = mixedMoment B raw996step1 raw996step1Labels := by
      have ha : raw996step1 = raw996step0 := by apply Matrix.ext; unfold raw996step1 raw996step0; decide +kernel
      have hl : raw996step0Labels = labelEmbedding7 ∘ raw996step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw996step0 raw996step0Labels raw996step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

theorem canonical997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw997 raw997Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw997 raw997Labels = mixedMoment B raw997step0 raw997step0Labels := by
      have ha : raw997step0 = (fun i j => raw997 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw997step0 raw997; decide +kernel
      have hl : raw997step0Labels = raw997Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw997 raw997Labels permutation8 permutation4
    _ = mixedMoment B node813 node813Labels := by rfl

theorem canonical998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw998 raw998Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw998 raw998Labels = mixedMoment B raw998step0 raw998step0Labels := by
      have ha : raw998step0 = (fun i j => raw998 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw998step0 raw998; decide +kernel
      have hl : raw998step0Labels = raw998Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw998 raw998Labels permutation9 permutation6
    mixedMoment B raw998step0 raw998step0Labels = mixedMoment B raw998step1 raw998step1Labels := by
      have ha : raw998step1 = -raw998step0 := by apply Matrix.ext; change ∀ i j, raw998step1 i j = -(raw998step0 i j); unfold raw998step1 raw998step0; decide +kernel
      have hl : raw998step1Labels = raw998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw998step1 raw998step1Labels = mixedMoment B raw998step2 raw998step2Labels := by
      have ha : raw998step2 = raw998step1 := by apply Matrix.ext; unfold raw998step2 raw998step1; decide +kernel
      have hl : raw998step1Labels = labelEmbedding1 ∘ raw998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw998step1 raw998step1Labels raw998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node853 node853Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw782 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw782 = injectiveMoment H raw782step0 := by
      have heq : raw782step0 = -raw782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw782).symm
    injectiveMoment H raw782step0 = injectiveMoment H raw782step1 := by
      have heq : raw782step1 = (fun i j => raw782step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw782step0 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

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

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

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

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
  linarith

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

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3963 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3963 = injectiveMoment H raw3963step0 := by
      have heq : raw3963step0 = -raw3963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3963).symm
    injectiveMoment H raw3963step0 = injectiveMoment H raw3963step1 := by
      have heq : raw3963step1 = (fun i j => raw3963step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3963step0 permutation10 permutation8
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem singlePair405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node405 node405Labels = Sparse.eval singlePairValue405 (familyPairVector B) := by
  have hp := single_label_three B hB node405
  have hl : node405Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node405 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node405 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node405 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node405 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value185 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 4) = PairSemantics.raw782 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node405 PairSemantics.raw782; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical782 hH).trans (PairSemantics.sound185 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue405, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value185, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9013 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9013 = injectiveMoment H raw9013step0 := by
      have hz : ∀ j, raw9013 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9013step0 = (fun i j => raw9013 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9013 permutation9 hz
    injectiveMoment H raw9013step0 = injectiveMoment H raw9013step1 := by
      have heq : raw9013step1 = (fun i j => raw9013step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9013step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem singlePair496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node496 node496Labels = Sparse.eval singlePairValue496 (familyPairVector B) := by
  have hp := single_label_three B hB node496
  have hl : node496Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node496 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 1) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node496 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node496 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node496 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value203 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 4) = PairSemantics.raw3963 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node496 PairSemantics.raw3963; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3963 hH).trans (PairSemantics.sound203 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue496, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value46, PairSemantics.value203, Sparse.eval] at hp ⊢
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

theorem singleton2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2768 node2768Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw272 singletonSmall2768
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2768) = raw272Labels := by decide +kernel
  rw [hl, canonical272 B hB] at h
  have hc0 : mixedMoment B raw272 (Fin.cases (0 : Fin 1) singletonSmall2768) =
      mixedMoment B node405 node405Labels := by
    have ha : raw272 = raw273 := by apply Matrix.ext; unfold raw272 raw273; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2768 = raw273Labels := by decide +kernel
    rw [ha, hj, canonical273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3862 node3862Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node496 node496Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw536 singletonSmall3862
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3862) = raw536Labels := by decide +kernel
  rw [hl, canonical536 B hB] at h
  have hc0 : mixedMoment B raw536 (Fin.cases (0 : Fin 1) singletonSmall3862) =
      mixedMoment B node496 node496Labels := by
    have ha : raw536 = raw537 := by apply Matrix.ext; unfold raw536 raw537; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3862 = raw537Labels := by decide +kernel
    rw [ha, hj, canonical537 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4219 node4219Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node720 node720Labels + mixedMoment B node769 node769Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw903 singletonSmall4219
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4219) = raw903Labels := by decide +kernel
  rw [hl, canonical903 B hB] at h
  have hc0 : mixedMoment B raw903 (Fin.cases (0 : Fin 2) singletonSmall4219) =
      mixedMoment B node720 node720Labels := by
    have ha : raw903 = raw904 := by apply Matrix.ext; unfold raw903 raw904; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4219 = raw904Labels := by decide +kernel
    rw [ha, hj, canonical904 B hB]
  have hc1 : mixedMoment B raw903 (Fin.cases (1 : Fin 2) singletonSmall4219) =
      mixedMoment B node769 node769Labels := by
    have ha : raw903 = raw905 := by apply Matrix.ext; unfold raw903 raw905; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4219 = raw905Labels := by decide +kernel
    rw [ha, hj, canonical905 B hB]
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

theorem singleton4225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4225 node4225Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node726 node726Labels + mixedMoment B node774 node774Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw915 singletonSmall4225
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4225) = raw915Labels := by decide +kernel
  rw [hl, canonical915 B hB] at h
  have hc0 : mixedMoment B raw915 (Fin.cases (0 : Fin 2) singletonSmall4225) =
      mixedMoment B node726 node726Labels := by
    have ha : raw915 = raw916 := by apply Matrix.ext; unfold raw915 raw916; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4225 = raw916Labels := by decide +kernel
    rw [ha, hj, canonical916 B hB]
  have hc1 : mixedMoment B raw915 (Fin.cases (1 : Fin 2) singletonSmall4225) =
      mixedMoment B node774 node774Labels := by
    have ha : raw915 = raw917 := by apply Matrix.ext; unfold raw915 raw917; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4225 = raw917Labels := by decide +kernel
    rw [ha, hj, canonical917 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4229 node4229Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node729 node729Labels + mixedMoment B node773 node773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw921 singletonSmall4229
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4229) = raw921Labels := by decide +kernel
  rw [hl, canonical921 B hB] at h
  have hc0 : mixedMoment B raw921 (Fin.cases (0 : Fin 2) singletonSmall4229) =
      mixedMoment B node729 node729Labels := by
    have ha : raw921 = raw922 := by apply Matrix.ext; unfold raw921 raw922; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4229 = raw922Labels := by decide +kernel
    rw [ha, hj, canonical922 B hB]
  have hc1 : mixedMoment B raw921 (Fin.cases (1 : Fin 2) singletonSmall4229) =
      mixedMoment B node773 node773Labels := by
    have ha : raw921 = raw923 := by apply Matrix.ext; unfold raw921 raw923; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4229 = raw923Labels := by decide +kernel
    rw [ha, hj, canonical923 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4270 node4270Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node813 node813Labels + mixedMoment B node853 node853Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw996 singletonSmall4270
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4270) = raw996Labels := by decide +kernel
  rw [hl, canonical996 B hB] at h
  have hc0 : mixedMoment B raw996 (Fin.cases (0 : Fin 2) singletonSmall4270) =
      mixedMoment B node813 node813Labels := by
    have ha : raw996 = raw997 := by apply Matrix.ext; unfold raw996 raw997; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4270 = raw997Labels := by decide +kernel
    rw [ha, hj, canonical997 B hB]
  have hc1 : mixedMoment B raw996 (Fin.cases (1 : Fin 2) singletonSmall4270) =
      mixedMoment B node853 node853Labels := by
    have ha : raw996 = raw998 := by apply Matrix.ext; unfold raw996 raw998; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4270 = raw998Labels := by decide +kernel
    rw [ha, hj, canonical998 B hB]
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

theorem singleton4514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4514 node4514Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1098 node1098Labels + mixedMoment B node1894 node1894Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1314 singletonSmall4514
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4514) = raw1314Labels := by decide +kernel
  rw [hl, canonical1314 B hB] at h
  have hc0 : mixedMoment B raw1314 (Fin.cases (0 : Fin 2) singletonSmall4514) =
      mixedMoment B node1098 node1098Labels := by
    have ha : raw1314 = raw1315 := by apply Matrix.ext; unfold raw1314 raw1315; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4514 = raw1315Labels := by decide +kernel
    rw [ha, hj, canonical1315 B hB]
  have hc1 : mixedMoment B raw1314 (Fin.cases (1 : Fin 2) singletonSmall4514) =
      mixedMoment B node1894 node1894Labels := by
    have ha : raw1314 = raw1316 := by apply Matrix.ext; unfold raw1314 raw1316; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4514 = raw1316Labels := by decide +kernel
    rw [ha, hj, canonical1316 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4519 node4519Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1103 node1103Labels + mixedMoment B node1858 node1858Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1329 singletonSmall4519
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4519) = raw1329Labels := by decide +kernel
  rw [hl, canonical1329 B hB] at h
  have hc0 : mixedMoment B raw1329 (Fin.cases (0 : Fin 2) singletonSmall4519) =
      mixedMoment B node1103 node1103Labels := by
    have ha : raw1329 = raw1330 := by apply Matrix.ext; unfold raw1329 raw1330; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4519 = raw1330Labels := by decide +kernel
    rw [ha, hj, canonical1330 B hB]
  have hc1 : mixedMoment B raw1329 (Fin.cases (1 : Fin 2) singletonSmall4519) =
      mixedMoment B node1858 node1858Labels := by
    have ha : raw1329 = raw1331 := by apply Matrix.ext; unfold raw1329 raw1331; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4519 = raw1331Labels := by decide +kernel
    rw [ha, hj, canonical1331 B hB]
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

theorem singleton4605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4605 node4605Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1239 node1239Labels + mixedMoment B node2226 node2226Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1428 singletonSmall4605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4605) = raw1428Labels := by decide +kernel
  rw [hl, canonical1428 B hB] at h
  have hc0 : mixedMoment B raw1428 (Fin.cases (0 : Fin 2) singletonSmall4605) =
      mixedMoment B node1239 node1239Labels := by
    have ha : raw1428 = raw1429 := by apply Matrix.ext; unfold raw1428 raw1429; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4605 = raw1429Labels := by decide +kernel
    rw [ha, hj, canonical1429 B hB]
  have hc1 : mixedMoment B raw1428 (Fin.cases (1 : Fin 2) singletonSmall4605) =
      mixedMoment B node2226 node2226Labels := by
    have ha : raw1428 = raw1430 := by apply Matrix.ext; unfold raw1428 raw1430; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4605 = raw1430Labels := by decide +kernel
    rw [ha, hj, canonical1430 B hB]
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

theorem singleton4650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4650 node4650Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1778 node1778Labels + mixedMoment B node1854 node1854Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1515 singletonSmall4650
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4650) = raw1515Labels := by decide +kernel
  rw [hl, canonical1515 B hB] at h
  have hc0 : mixedMoment B raw1515 (Fin.cases (0 : Fin 2) singletonSmall4650) =
      mixedMoment B node1778 node1778Labels := by
    have ha : raw1515 = raw1516 := by apply Matrix.ext; unfold raw1515 raw1516; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4650 = raw1516Labels := by decide +kernel
    rw [ha, hj, canonical1516 B hB]
  have hc1 : mixedMoment B raw1515 (Fin.cases (1 : Fin 2) singletonSmall4650) =
      mixedMoment B node1854 node1854Labels := by
    have ha : raw1515 = raw1517 := by apply Matrix.ext; unfold raw1515 raw1517; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4650 = raw1517Labels := by decide +kernel
    rw [ha, hj, canonical1517 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4657 node4657Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1783 node1783Labels + mixedMoment B node1857 node1857Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1527 singletonSmall4657
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4657) = raw1527Labels := by decide +kernel
  rw [hl, canonical1527 B hB] at h
  have hc0 : mixedMoment B raw1527 (Fin.cases (0 : Fin 2) singletonSmall4657) =
      mixedMoment B node1783 node1783Labels := by
    have ha : raw1527 = raw1528 := by apply Matrix.ext; unfold raw1527 raw1528; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4657 = raw1528Labels := by decide +kernel
    rw [ha, hj, canonical1528 B hB]
  have hc1 : mixedMoment B raw1527 (Fin.cases (1 : Fin 2) singletonSmall4657) =
      mixedMoment B node1857 node1857Labels := by
    have ha : raw1527 = raw1529 := by apply Matrix.ext; unfold raw1527 raw1529; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4657 = raw1529Labels := by decide +kernel
    rw [ha, hj, canonical1529 B hB]
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

theorem singleton4713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4713 node4713Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1867 node1867Labels + mixedMoment B node1891 node1891Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1602 singletonSmall4713
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4713) = raw1602Labels := by decide +kernel
  rw [hl, canonical1602 B hB] at h
  have hc0 : mixedMoment B raw1602 (Fin.cases (0 : Fin 2) singletonSmall4713) =
      mixedMoment B node1867 node1867Labels := by
    have ha : raw1602 = raw1603 := by apply Matrix.ext; unfold raw1602 raw1603; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4713 = raw1603Labels := by decide +kernel
    rw [ha, hj, canonical1603 B hB]
  have hc1 : mixedMoment B raw1602 (Fin.cases (1 : Fin 2) singletonSmall4713) =
      mixedMoment B node1891 node1891Labels := by
    have ha : raw1602 = raw1604 := by apply Matrix.ext; unfold raw1602 raw1604; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4713 = raw1604Labels := by decide +kernel
    rw [ha, hj, canonical1604 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4719 node4719Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1873 node1873Labels + mixedMoment B node1893 node1893Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1614 singletonSmall4719
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4719) = raw1614Labels := by decide +kernel
  rw [hl, canonical1614 B hB] at h
  have hc0 : mixedMoment B raw1614 (Fin.cases (0 : Fin 2) singletonSmall4719) =
      mixedMoment B node1873 node1873Labels := by
    have ha : raw1614 = raw1615 := by apply Matrix.ext; unfold raw1614 raw1615; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4719 = raw1615Labels := by decide +kernel
    rw [ha, hj, canonical1615 B hB]
  have hc1 : mixedMoment B raw1614 (Fin.cases (1 : Fin 2) singletonSmall4719) =
      mixedMoment B node1893 node1893Labels := by
    have ha : raw1614 = raw1616 := by apply Matrix.ext; unfold raw1614 raw1616; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4719 = raw1616Labels := by decide +kernel
    rw [ha, hj, canonical1616 B hB]
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

theorem singleton4742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4742 node4742Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1915 node1915Labels + mixedMoment B node1946 node1946Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1659 singletonSmall4742
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4742) = raw1659Labels := by decide +kernel
  rw [hl, canonical1659 B hB] at h
  have hc0 : mixedMoment B raw1659 (Fin.cases (0 : Fin 2) singletonSmall4742) =
      mixedMoment B node1915 node1915Labels := by
    have ha : raw1659 = raw1660 := by apply Matrix.ext; unfold raw1659 raw1660; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4742 = raw1660Labels := by decide +kernel
    rw [ha, hj, canonical1660 B hB]
  have hc1 : mixedMoment B raw1659 (Fin.cases (1 : Fin 2) singletonSmall4742) =
      mixedMoment B node1946 node1946Labels := by
    have ha : raw1659 = raw1661 := by apply Matrix.ext; unfold raw1659 raw1661; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4742 = raw1661Labels := by decide +kernel
    rw [ha, hj, canonical1661 B hB]
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

theorem singleton4845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4845 node4845Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2065 node2065Labels + mixedMoment B node2218 node2218Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1776 singletonSmall4845
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4845) = raw1776Labels := by decide +kernel
  rw [hl, canonical1776 B hB] at h
  have hc0 : mixedMoment B raw1776 (Fin.cases (0 : Fin 2) singletonSmall4845) =
      mixedMoment B node2065 node2065Labels := by
    have ha : raw1776 = raw1777 := by apply Matrix.ext; unfold raw1776 raw1777; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4845 = raw1777Labels := by decide +kernel
    rw [ha, hj, canonical1777 B hB]
  have hc1 : mixedMoment B raw1776 (Fin.cases (1 : Fin 2) singletonSmall4845) =
      mixedMoment B node2218 node2218Labels := by
    have ha : raw1776 = raw1778 := by apply Matrix.ext; unfold raw1776 raw1778; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4845 = raw1778Labels := by decide +kernel
    rw [ha, hj, canonical1778 B hB]
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

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton5207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5207 node5207Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2889 node2889Labels + mixedMoment B node3631 node3631Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2235 singletonSmall5207
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5207) = raw2235Labels := by decide +kernel
  rw [hl, canonical2235 B hB] at h
  have hc0 : mixedMoment B raw2235 (Fin.cases (0 : Fin 2) singletonSmall5207) =
      mixedMoment B node2889 node2889Labels := by
    have ha : raw2235 = raw2236 := by apply Matrix.ext; unfold raw2235 raw2236; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5207 = raw2236Labels := by decide +kernel
    rw [ha, hj, canonical2236 B hB]
  have hc1 : mixedMoment B raw2235 (Fin.cases (1 : Fin 2) singletonSmall5207) =
      mixedMoment B node3631 node3631Labels := by
    have ha : raw2235 = raw2237 := by apply Matrix.ext; unfold raw2235 raw2237; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5207 = raw2237Labels := by decide +kernel
    rw [ha, hj, canonical2237 B hB]
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

theorem singleton5294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5294 node5294Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2768 node2768Labels + mixedMoment B node3632 node3632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2304 singletonSmall5294
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5294) = raw2304Labels := by decide +kernel
  rw [hl, canonical2304 B hB] at h
  have hc0 : mixedMoment B raw2304 (Fin.cases (0 : Fin 2) singletonSmall5294) =
      mixedMoment B node2768 node2768Labels := by
    have ha : raw2304 = raw2305 := by apply Matrix.ext; unfold raw2304 raw2305; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5294 = raw2305Labels := by decide +kernel
    rw [ha, hj, canonical2305 B hB]
  have hc1 : mixedMoment B raw2304 (Fin.cases (1 : Fin 2) singletonSmall5294) =
      mixedMoment B node3632 node3632Labels := by
    have ha : raw2304 = raw2306 := by apply Matrix.ext; unfold raw2304 raw2306; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5294 = raw2306Labels := by decide +kernel
    rw [ha, hj, canonical2306 B hB]
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

theorem singleton5443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5443 node5443Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3862 node3862Labels + mixedMoment B node3907 node3907Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2544 singletonSmall5443
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5443) = raw2544Labels := by decide +kernel
  rw [hl, canonical2544 B hB] at h
  have hc0 : mixedMoment B raw2544 (Fin.cases (0 : Fin 2) singletonSmall5443) =
      mixedMoment B node3862 node3862Labels := by
    have ha : raw2544 = raw2545 := by apply Matrix.ext; unfold raw2544 raw2545; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5443 = raw2545Labels := by decide +kernel
    rw [ha, hj, canonical2545 B hB]
  have hc1 : mixedMoment B raw2544 (Fin.cases (1 : Fin 2) singletonSmall5443) =
      mixedMoment B node3907 node3907Labels := by
    have ha : raw2544 = raw2546 := by apply Matrix.ext; unfold raw2544 raw2546; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5443 = raw2546Labels := by decide +kernel
    rw [ha, hj, canonical2546 B hB]
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

theorem sound496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node496 node496Labels = Sparse.eval nodeValue496 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue496 (familyPairVector B) := singlePair496 B _hB
    _ = _ := by norm_num [singlePairValue496, nodeValue496, Sparse.eval, mixedVector] <;> ring

theorem sound3862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3862 node3862Labels = Sparse.eval nodeValue3862 (mixedVector B) := by
  have h := singleton3862 B _hB
  rw [sound496 B _hB _hF] at h
  norm_num [nodeValue3862, nodeValue496, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

theorem sound5443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5443 node5443Labels = Sparse.eval nodeValue5443 (mixedVector B) := by
  have h := singleton5443 B _hB
  rw [sound3862 B _hB _hF, sound3907 B _hB _hF] at h
  norm_num [nodeValue5443, nodeValue3862, nodeValue3907, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node720 node720Labels = Sparse.eval nodeValue720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 720) = mixedMoment B node720 node720Labels := rfl
  simpa [nodeValue720, Sparse.eval] using hc.symm

theorem sound726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node726 node726Labels = Sparse.eval nodeValue726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 726) = mixedMoment B node726 node726Labels := rfl
  simpa [nodeValue726, Sparse.eval] using hc.symm

theorem sound729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node729 node729Labels = Sparse.eval nodeValue729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 729) = mixedMoment B node729 node729Labels := rfl
  simpa [nodeValue729, Sparse.eval] using hc.symm

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

theorem sound769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node769 node769Labels = Sparse.eval nodeValue769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 769) = mixedMoment B node769 node769Labels := rfl
  simpa [nodeValue769, Sparse.eval] using hc.symm

theorem sound773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node773 node773Labels = Sparse.eval nodeValue773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 773) = mixedMoment B node773 node773Labels := rfl
  simpa [nodeValue773, Sparse.eval] using hc.symm

theorem sound774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node774 node774Labels = Sparse.eval nodeValue774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 774) = mixedMoment B node774 node774Labels := rfl
  simpa [nodeValue774, Sparse.eval] using hc.symm

theorem sound813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node813 node813Labels = Sparse.eval nodeValue813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 813) = mixedMoment B node813 node813Labels := rfl
  simpa [nodeValue813, Sparse.eval] using hc.symm

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

theorem sound853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node853 node853Labels = Sparse.eval nodeValue853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 853) = mixedMoment B node853 node853Labels := rfl
  simpa [nodeValue853, Sparse.eval] using hc.symm

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

theorem sound1098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1098 node1098Labels = Sparse.eval nodeValue1098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1098) = mixedMoment B node1098 node1098Labels := rfl
  simpa [nodeValue1098, Sparse.eval] using hc.symm

theorem sound1103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1103 node1103Labels = Sparse.eval nodeValue1103 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1103) = mixedMoment B node1103 node1103Labels := rfl
  simpa [nodeValue1103, Sparse.eval] using hc.symm

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

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

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

theorem sound1778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1778 node1778Labels = Sparse.eval nodeValue1778 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1778) = mixedMoment B node1778 node1778Labels := rfl
  simpa [nodeValue1778, Sparse.eval] using hc.symm

theorem sound1783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1783 node1783Labels = Sparse.eval nodeValue1783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1783) = mixedMoment B node1783 node1783Labels := rfl
  simpa [nodeValue1783, Sparse.eval] using hc.symm

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

theorem sound1854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1854 node1854Labels = Sparse.eval nodeValue1854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1854) = mixedMoment B node1854 node1854Labels := rfl
  simpa [nodeValue1854, Sparse.eval] using hc.symm

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

theorem sound1857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1857 node1857Labels = Sparse.eval nodeValue1857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1857) = mixedMoment B node1857 node1857Labels := rfl
  simpa [nodeValue1857, Sparse.eval] using hc.symm

theorem sound1858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1858 node1858Labels = Sparse.eval nodeValue1858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1858) = mixedMoment B node1858 node1858Labels := rfl
  simpa [nodeValue1858, Sparse.eval] using hc.symm

theorem sound1867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1867 node1867Labels = Sparse.eval nodeValue1867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1867) = mixedMoment B node1867 node1867Labels := rfl
  simpa [nodeValue1867, Sparse.eval] using hc.symm

theorem sound1873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1873 node1873Labels = Sparse.eval nodeValue1873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1873) = mixedMoment B node1873 node1873Labels := rfl
  simpa [nodeValue1873, Sparse.eval] using hc.symm

theorem sound1891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1891 node1891Labels = Sparse.eval nodeValue1891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1891) = mixedMoment B node1891 node1891Labels := rfl
  simpa [nodeValue1891, Sparse.eval] using hc.symm

theorem sound1893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1893 node1893Labels = Sparse.eval nodeValue1893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1893) = mixedMoment B node1893 node1893Labels := rfl
  simpa [nodeValue1893, Sparse.eval] using hc.symm

theorem sound1894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1894 node1894Labels = Sparse.eval nodeValue1894 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1894) = mixedMoment B node1894 node1894Labels := rfl
  simpa [nodeValue1894, Sparse.eval] using hc.symm

theorem sound1915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1915 node1915Labels = Sparse.eval nodeValue1915 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1915) = mixedMoment B node1915 node1915Labels := rfl
  simpa [nodeValue1915, Sparse.eval] using hc.symm

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

theorem sound1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1946 node1946Labels = Sparse.eval nodeValue1946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1946) = mixedMoment B node1946 node1946Labels := rfl
  simpa [nodeValue1946, Sparse.eval] using hc.symm

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

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

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

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

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

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

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

theorem sound405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node405 node405Labels = Sparse.eval nodeValue405 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue405 (familyPairVector B) := singlePair405 B _hB
    _ = _ := by
      norm_num [singlePairValue405, nodeValue405, Sparse.eval, mixedVector]
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

theorem sound2768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2768 node2768Labels = Sparse.eval nodeValue2768 (mixedVector B) := by
  have h := singleton2768 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue2768, nodeValue405, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2889 node2889Labels = Sparse.eval nodeValue2889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2889) = mixedMoment B node2889 node2889Labels := rfl
  simpa [nodeValue2889, Sparse.eval] using hc.symm

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

theorem sound3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3624 node3624Labels = Sparse.eval nodeValue3624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3624) = mixedMoment B node3624 node3624Labels := rfl
  simpa [nodeValue3624, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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

theorem sound4219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4219 node4219Labels = Sparse.eval nodeValue4219 (mixedVector B) := by
  have h := singleton4219 B _hB
  rw [sound720 B _hB _hF, sound769 B _hB _hF] at h
  norm_num [nodeValue4219, nodeValue720, nodeValue769, Sparse.eval] at h ⊢
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

theorem sound4225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4225 node4225Labels = Sparse.eval nodeValue4225 (mixedVector B) := by
  have h := singleton4225 B _hB
  rw [sound726 B _hB _hF, sound774 B _hB _hF] at h
  norm_num [nodeValue4225, nodeValue726, nodeValue774, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4229 node4229Labels = Sparse.eval nodeValue4229 (mixedVector B) := by
  have h := singleton4229 B _hB
  rw [sound729 B _hB _hF, sound773 B _hB _hF] at h
  norm_num [nodeValue4229, nodeValue729, nodeValue773, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4270 node4270Labels = Sparse.eval nodeValue4270 (mixedVector B) := by
  have h := singleton4270 B _hB
  rw [sound813 B _hB _hF, sound853 B _hB _hF] at h
  norm_num [nodeValue4270, nodeValue813, nodeValue853, Sparse.eval] at h ⊢
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

theorem sound4514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4514 node4514Labels = Sparse.eval nodeValue4514 (mixedVector B) := by
  have h := singleton4514 B _hB
  rw [sound1098 B _hB _hF, sound1894 B _hB _hF] at h
  norm_num [nodeValue4514, nodeValue1098, nodeValue1894, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4519 node4519Labels = Sparse.eval nodeValue4519 (mixedVector B) := by
  have h := singleton4519 B _hB
  rw [sound1103 B _hB _hF, sound1858 B _hB _hF] at h
  norm_num [nodeValue4519, nodeValue1103, nodeValue1858, Sparse.eval] at h ⊢
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

theorem sound4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4605 node4605Labels = Sparse.eval nodeValue4605 (mixedVector B) := by
  have h := singleton4605 B _hB
  rw [sound1239 B _hB _hF, sound2226 B _hB _hF] at h
  norm_num [nodeValue4605, nodeValue1239, nodeValue2226, Sparse.eval] at h ⊢
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

theorem sound4650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4650 node4650Labels = Sparse.eval nodeValue4650 (mixedVector B) := by
  have h := singleton4650 B _hB
  rw [sound1778 B _hB _hF, sound1854 B _hB _hF] at h
  norm_num [nodeValue4650, nodeValue1778, nodeValue1854, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4657 node4657Labels = Sparse.eval nodeValue4657 (mixedVector B) := by
  have h := singleton4657 B _hB
  rw [sound1783 B _hB _hF, sound1857 B _hB _hF] at h
  norm_num [nodeValue4657, nodeValue1783, nodeValue1857, Sparse.eval] at h ⊢
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

theorem sound4713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4713 node4713Labels = Sparse.eval nodeValue4713 (mixedVector B) := by
  have h := singleton4713 B _hB
  rw [sound1867 B _hB _hF, sound1891 B _hB _hF] at h
  norm_num [nodeValue4713, nodeValue1867, nodeValue1891, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4719 node4719Labels = Sparse.eval nodeValue4719 (mixedVector B) := by
  have h := singleton4719 B _hB
  rw [sound1873 B _hB _hF, sound1893 B _hB _hF] at h
  norm_num [nodeValue4719, nodeValue1873, nodeValue1893, Sparse.eval] at h ⊢
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

theorem sound4742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4742 node4742Labels = Sparse.eval nodeValue4742 (mixedVector B) := by
  have h := singleton4742 B _hB
  rw [sound1915 B _hB _hF, sound1946 B _hB _hF] at h
  norm_num [nodeValue4742, nodeValue1915, nodeValue1946, Sparse.eval] at h ⊢
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

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4845 node4845Labels = Sparse.eval nodeValue4845 (mixedVector B) := by
  have h := singleton4845 B _hB
  rw [sound2065 B _hB _hF, sound2218 B _hB _hF] at h
  norm_num [nodeValue4845, nodeValue2065, nodeValue2218, Sparse.eval] at h ⊢
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

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5204 node5204Labels = Sparse.eval nodeValue5204 (mixedVector B) := by
  have h := singleton5204 B _hB
  rw [sound2881 B _hB _hF, sound3624 B _hB _hF] at h
  norm_num [nodeValue5204, nodeValue2881, nodeValue3624, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5207 node5207Labels = Sparse.eval nodeValue5207 (mixedVector B) := by
  have h := singleton5207 B _hB
  rw [sound2889 B _hB _hF, sound3631 B _hB _hF] at h
  norm_num [nodeValue5207, nodeValue2889, nodeValue3631, Sparse.eval] at h ⊢
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

theorem sound5294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5294 node5294Labels = Sparse.eval nodeValue5294 (mixedVector B) := by
  have h := singleton5294 B _hB
  rw [sound2768 B _hB _hF, sound3632 B _hB _hF] at h
  norm_num [nodeValue5294, nodeValue2768, nodeValue3632, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources62
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1998 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 1) (sourceB1998 + difference 1 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 1) (sourceB1998 + difference 1 0) sourceC1998) = raw28337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28337; decide +kernel
    rw [ha]
    exact (canonical28337 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 2) (sourceB1998 + difference 2 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 2) (sourceB1998 + difference 2 0) sourceC1998) = raw28338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28338; decide +kernel
    rw [ha]
    exact (canonical28338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 3) (sourceB1998 + difference 3 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 3) (sourceB1998 + difference 3 0) sourceC1998) = raw28339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28339; decide +kernel
    rw [ha]
    exact (canonical28339 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 4) (sourceB1998 + difference 4 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 4) (sourceB1998 + difference 4 0) sourceC1998) = raw28340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28340; decide +kernel
    rw [ha]
    exact (canonical28340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1998 + difference 0 5) (sourceB1998 + difference 5 0) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1998 + difference 0 5) (sourceB1998 + difference 5 0) sourceC1998) = raw3315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw3315; decide +kernel
    rw [ha]
    exact (canonical3315 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 0) (sourceB1998 + difference 0 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 0) (sourceB1998 + difference 0 1) sourceC1998) = raw28341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28341; decide +kernel
    rw [ha]
    exact (canonical28341 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 2) (sourceB1998 + difference 2 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 2) (sourceB1998 + difference 2 1) sourceC1998) = raw28342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28342; decide +kernel
    rw [ha]
    exact (canonical28342 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 3) (sourceB1998 + difference 3 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 3) (sourceB1998 + difference 3 1) sourceC1998) = raw28343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28343; decide +kernel
    rw [ha]
    exact (canonical28343 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 4) (sourceB1998 + difference 4 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 4) (sourceB1998 + difference 4 1) sourceC1998) = raw28344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28344; decide +kernel
    rw [ha]
    exact (canonical28344 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1998 + difference 1 5) (sourceB1998 + difference 5 1) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1998 + difference 1 5) (sourceB1998 + difference 5 1) sourceC1998) = raw3314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw3314; decide +kernel
    rw [ha]
    exact (canonical3314 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 0) (sourceB1998 + difference 0 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 0) (sourceB1998 + difference 0 2) sourceC1998) = raw28345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28345; decide +kernel
    rw [ha]
    exact (canonical28345 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 1) (sourceB1998 + difference 1 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 1) (sourceB1998 + difference 1 2) sourceC1998) = raw28346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28346; decide +kernel
    rw [ha]
    exact (canonical28346 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 3) (sourceB1998 + difference 3 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 3) (sourceB1998 + difference 3 2) sourceC1998) = raw28347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28347; decide +kernel
    rw [ha]
    exact (canonical28347 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 4) (sourceB1998 + difference 4 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 4) (sourceB1998 + difference 4 2) sourceC1998) = raw28348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28348; decide +kernel
    rw [ha]
    exact (canonical28348 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1998 + difference 2 5) (sourceB1998 + difference 5 2) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1998 + difference 2 5) (sourceB1998 + difference 5 2) sourceC1998) = raw28349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28349; decide +kernel
    rw [ha]
    exact (canonical28349 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 0) (sourceB1998 + difference 0 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 0) (sourceB1998 + difference 0 3) sourceC1998) = raw28350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28350; decide +kernel
    rw [ha]
    exact (canonical28350 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 1) (sourceB1998 + difference 1 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 1) (sourceB1998 + difference 1 3) sourceC1998) = raw28351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28351; decide +kernel
    rw [ha]
    exact (canonical28351 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 2) (sourceB1998 + difference 2 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 2) (sourceB1998 + difference 2 3) sourceC1998) = raw28352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28352; decide +kernel
    rw [ha]
    exact (canonical28352 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 4) (sourceB1998 + difference 4 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 4) (sourceB1998 + difference 4 3) sourceC1998) = raw28353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28353; decide +kernel
    rw [ha]
    exact (canonical28353 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1998 + difference 3 5) (sourceB1998 + difference 5 3) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1998 + difference 3 5) (sourceB1998 + difference 5 3) sourceC1998) = raw28354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28354; decide +kernel
    rw [ha]
    exact (canonical28354 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 0) (sourceB1998 + difference 0 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4519) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 0) (sourceB1998 + difference 0 4) sourceC1998) = raw28355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28355; decide +kernel
    rw [ha]
    exact (canonical28355 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 1) (sourceB1998 + difference 1 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4657) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 1) (sourceB1998 + difference 1 4) sourceC1998) = raw28356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28356; decide +kernel
    rw [ha]
    exact (canonical28356 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 2) (sourceB1998 + difference 2 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 2) (sourceB1998 + difference 2 4) sourceC1998) = raw28357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28357; decide +kernel
    rw [ha]
    exact (canonical28357 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 3) (sourceB1998 + difference 3 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 3) (sourceB1998 + difference 3 4) sourceC1998) = raw28358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28358; decide +kernel
    rw [ha]
    exact (canonical28358 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1998 + difference 4 5) (sourceB1998 + difference 5 4) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA1998 + difference 4 5) (sourceB1998 + difference 5 4) sourceC1998) = raw28359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28359; decide +kernel
    rw [ha]
    exact (canonical28359 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 0) (sourceB1998 + difference 0 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4225) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 0) (sourceB1998 + difference 0 5) sourceC1998) = raw28360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28360; decide +kernel
    rw [ha]
    exact (canonical28360 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 1) (sourceB1998 + difference 1 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 1) (sourceB1998 + difference 1 5) sourceC1998) = raw28361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28361; decide +kernel
    rw [ha]
    exact (canonical28361 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 2) (sourceB1998 + difference 2 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 2) (sourceB1998 + difference 2 5) sourceC1998) = raw28362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28362; decide +kernel
    rw [ha]
    exact (canonical28362 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 3) (sourceB1998 + difference 3 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 3) (sourceB1998 + difference 3 5) sourceC1998) = raw28363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28363; decide +kernel
    rw [ha]
    exact (canonical28363 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1998 + difference 5 4) (sourceB1998 + difference 4 5) sourceC1998) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1998 + difference 5 4) (sourceB1998 + difference 4 5) sourceC1998) = raw28364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1998 sourceB1998 sourceC1998 difference raw28364; decide +kernel
    rw [ha]
    exact (canonical28364 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1998 sourceB1998 sourceC1998
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1998, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1686 : Integer.Sparse.reindex keyMap MixedData.row1686 = numericRow1686 := by decide +kernel

theorem numericCheck1686 (x : Master → ℝ) : Integer.Sparse.eval numericRow1686 x =
    (4320 : ℝ) * reducedSource1686 x := by
  norm_num [numericRow1686, reducedSource1686, Integer.Sparse.eval, Sparse.eval, nodeValue4219, nodeValue4225, nodeValue4229, nodeValue4270, nodeValue4514, nodeValue4519, nodeValue4605, nodeValue4650, nodeValue4657, nodeValue4713, nodeValue4719, nodeValue4742, nodeValue4807, nodeValue4839, nodeValue4845, nodeValue4890, nodeValue4896, nodeValue5204, nodeValue5207, nodeValue5294, nodeValue5443] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1686 (mixedVector B) = 0 := by
  have h4219 : mixedVector B (Sum.inr 4219) = Sparse.eval nodeValue4219 (mixedVector B) := by
    change mixedMoment B node4219 node4219Labels = _
    exact sound4219 B hB hF
  have h4225 : mixedVector B (Sum.inr 4225) = Sparse.eval nodeValue4225 (mixedVector B) := by
    change mixedMoment B node4225 node4225Labels = _
    exact sound4225 B hB hF
  have h4229 : mixedVector B (Sum.inr 4229) = Sparse.eval nodeValue4229 (mixedVector B) := by
    change mixedMoment B node4229 node4229Labels = _
    exact sound4229 B hB hF
  have h4270 : mixedVector B (Sum.inr 4270) = Sparse.eval nodeValue4270 (mixedVector B) := by
    change mixedMoment B node4270 node4270Labels = _
    exact sound4270 B hB hF
  have h4514 : mixedVector B (Sum.inr 4514) = Sparse.eval nodeValue4514 (mixedVector B) := by
    change mixedMoment B node4514 node4514Labels = _
    exact sound4514 B hB hF
  have h4519 : mixedVector B (Sum.inr 4519) = Sparse.eval nodeValue4519 (mixedVector B) := by
    change mixedMoment B node4519 node4519Labels = _
    exact sound4519 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4650 : mixedVector B (Sum.inr 4650) = Sparse.eval nodeValue4650 (mixedVector B) := by
    change mixedMoment B node4650 node4650Labels = _
    exact sound4650 B hB hF
  have h4657 : mixedVector B (Sum.inr 4657) = Sparse.eval nodeValue4657 (mixedVector B) := by
    change mixedMoment B node4657 node4657Labels = _
    exact sound4657 B hB hF
  have h4713 : mixedVector B (Sum.inr 4713) = Sparse.eval nodeValue4713 (mixedVector B) := by
    change mixedMoment B node4713 node4713Labels = _
    exact sound4713 B hB hF
  have h4719 : mixedVector B (Sum.inr 4719) = Sparse.eval nodeValue4719 (mixedVector B) := by
    change mixedMoment B node4719 node4719Labels = _
    exact sound4719 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  simpa only [sourceForm1998, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4219, h4225, h4229, h4270, h4514, h4519, h4605, h4650, h4657, h4713, h4719, h4742, h4807, h4839, h4845, h4890, h4896, h5204, h5207, h5294, h5443, reducedSource1686] using sourceEq1998 B hB

theorem rowSound1686_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1686 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1686, numericCheck1686, reducedZero1686 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e_oai
