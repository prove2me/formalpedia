-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:50:25.062234+00:00
-- url     : https://prove2.me/submissions/5543b28b-bc1a-44cc-aa32-5de333e5051e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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

theorem canonical1398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1398 raw1398Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw1398 raw1398Labels = mixedMoment B raw1398step0 raw1398step0Labels := by
      have ha : raw1398step0 = (fun i j => raw1398 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1398step0 raw1398; decide +kernel
      have hl : raw1398step0Labels = raw1398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1398 raw1398Labels permutation8 permutation4
    mixedMoment B raw1398step0 raw1398step0Labels = mixedMoment B raw1398step1 raw1398step1Labels := by
      have ha : raw1398step1 = raw1398step0 := by apply Matrix.ext; unfold raw1398step1 raw1398step0; decide +kernel
      have hl : raw1398step0Labels = labelEmbedding7 ∘ raw1398step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1398step0 raw1398step0Labels raw1398step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4559 node4559Labels := by rfl

theorem canonical1399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1399 raw1399Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw1399 raw1399Labels = mixedMoment B raw1399step0 raw1399step0Labels := by
      have ha : raw1399step0 = (fun i j => raw1399 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1399step0 raw1399; decide +kernel
      have hl : raw1399step0Labels = raw1399Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1399 raw1399Labels permutation8 permutation4
    _ = mixedMoment B node1145 node1145Labels := by rfl

theorem canonical1400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1400 raw1400Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw1400 raw1400Labels = mixedMoment B raw1400step0 raw1400step0Labels := by
      have ha : raw1400step0 = (fun i j => raw1400 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1400step0 raw1400; decide +kernel
      have hl : raw1400step0Labels = raw1400Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1400 raw1400Labels permutation9 permutation6
    mixedMoment B raw1400step0 raw1400step0Labels = mixedMoment B raw1400step1 raw1400step1Labels := by
      have ha : raw1400step1 = -raw1400step0 := by apply Matrix.ext; change ∀ i j, raw1400step1 i j = -(raw1400step0 i j); unfold raw1400step1 raw1400step0; decide +kernel
      have hl : raw1400step1Labels = raw1400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1400step1 raw1400step1Labels = mixedMoment B raw1400step2 raw1400step2Labels := by
      have ha : raw1400step2 = raw1400step1 := by apply Matrix.ext; unfold raw1400step2 raw1400step1; decide +kernel
      have hl : raw1400step1Labels = labelEmbedding1 ∘ raw1400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1400step1 raw1400step1Labels raw1400step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1929 raw1929Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw1929 raw1929Labels = mixedMoment B raw1929step0 raw1929step0Labels := by
      have ha : raw1929step0 = (fun i j => raw1929 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1929step0 raw1929; decide +kernel
      have hl : raw1929step0Labels = raw1929Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1929 raw1929Labels permutation8 permutation4
    mixedMoment B raw1929step0 raw1929step0Labels = mixedMoment B raw1929step1 raw1929step1Labels := by
      have ha : raw1929step1 = raw1929step0 := by apply Matrix.ext; unfold raw1929step1 raw1929step0; decide +kernel
      have hl : raw1929step0Labels = labelEmbedding7 ∘ raw1929step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1929step0 raw1929step0Labels raw1929step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4953 node4953Labels := by rfl

theorem canonical1930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1930 raw1930Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw1930 raw1930Labels = mixedMoment B raw1930step0 raw1930step0Labels := by
      have ha : raw1930step0 = (fun i j => raw1930 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1930step0 raw1930; decide +kernel
      have hl : raw1930step0Labels = raw1930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1930 raw1930Labels permutation8 permutation4
    _ = mixedMoment B node2345 node2345Labels := by rfl

theorem canonical1931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1931 raw1931Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw1931 raw1931Labels = mixedMoment B raw1931step0 raw1931step0Labels := by
      have ha : raw1931step0 = (fun i j => raw1931 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1931step0 raw1931; decide +kernel
      have hl : raw1931step0Labels = raw1931Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1931 raw1931Labels permutation9 permutation6
    mixedMoment B raw1931step0 raw1931step0Labels = mixedMoment B raw1931step1 raw1931step1Labels := by
      have ha : raw1931step1 = -raw1931step0 := by apply Matrix.ext; change ∀ i j, raw1931step1 i j = -(raw1931step0 i j); unfold raw1931step1 raw1931step0; decide +kernel
      have hl : raw1931step1Labels = raw1931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1931step1 raw1931step1Labels = mixedMoment B raw1931step2 raw1931step2Labels := by
      have ha : raw1931step2 = raw1931step1 := by apply Matrix.ext; unfold raw1931step2 raw1931step1; decide +kernel
      have hl : raw1931step1Labels = labelEmbedding1 ∘ raw1931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1931step1 raw1931step1Labels raw1931step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical1956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1956 raw1956Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw1956 raw1956Labels = mixedMoment B raw1956step0 raw1956step0Labels := by
      have ha : raw1956step0 = (fun i j => raw1956 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1956step0 raw1956; decide +kernel
      have hl : raw1956step0Labels = raw1956Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1956 raw1956Labels permutation32 permutation5
    mixedMoment B raw1956step0 raw1956step0Labels = mixedMoment B raw1956step1 raw1956step1Labels := by
      have ha : raw1956step1 = raw1956step0 := by apply Matrix.ext; unfold raw1956step1 raw1956step0; decide +kernel
      have hl : raw1956step0Labels = labelEmbedding8 ∘ raw1956step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1956step0 raw1956step0Labels raw1956step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

theorem canonical1957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1957 raw1957Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw1957 raw1957Labels = mixedMoment B raw1957step0 raw1957step0Labels := by
      have ha : raw1957step0 = (fun i j => raw1957 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1957step0 raw1957; decide +kernel
      have hl : raw1957step0Labels = raw1957Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1957 raw1957Labels permutation145 permutation4
    mixedMoment B raw1957step0 raw1957step0Labels = mixedMoment B raw1957step1 raw1957step1Labels := by
      have ha : raw1957step1 = -raw1957step0 := by apply Matrix.ext; change ∀ i j, raw1957step1 i j = -(raw1957step0 i j); unfold raw1957step1 raw1957step0; decide +kernel
      have hl : raw1957step1Labels = raw1957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

theorem canonical1958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1958 raw1958Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw1958 raw1958Labels = mixedMoment B raw1958step0 raw1958step0Labels := by
      have ha : raw1958step0 = (fun i j => raw1958 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1958step0 raw1958; decide +kernel
      have hl : raw1958step0Labels = raw1958Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1958 raw1958Labels permutation144 permutation6
    mixedMoment B raw1958step0 raw1958step0Labels = mixedMoment B raw1958step1 raw1958step1Labels := by
      have ha : raw1958step1 = raw1958step0 := by apply Matrix.ext; unfold raw1958step1 raw1958step0; decide +kernel
      have hl : raw1958step0Labels = labelEmbedding1 ∘ raw1958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1958step0 raw1958step0Labels raw1958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

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

theorem canonical2127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2127 raw2127Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw2127 raw2127Labels = mixedMoment B raw2127step0 raw2127step0Labels := by
      have ha : raw2127step0 = (fun i j => raw2127 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2127step0 raw2127; decide +kernel
      have hl : raw2127step0Labels = raw2127Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2127 raw2127Labels permutation32 permutation4
    mixedMoment B raw2127step0 raw2127step0Labels = mixedMoment B raw2127step1 raw2127step1Labels := by
      have ha : raw2127step1 = raw2127step0 := by apply Matrix.ext; unfold raw2127step1 raw2127step0; decide +kernel
      have hl : raw2127step0Labels = labelEmbedding7 ∘ raw2127step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2127step0 raw2127step0Labels raw2127step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2128 raw2128Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw2128 raw2128Labels = mixedMoment B raw2128step0 raw2128step0Labels := by
      have ha : raw2128step0 = (fun i j => raw2128 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2128step0 raw2128; decide +kernel
      have hl : raw2128step0Labels = raw2128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2128 raw2128Labels permutation32 permutation4
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2129 raw2129Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw2129 raw2129Labels = mixedMoment B raw2129step0 raw2129step0Labels := by
      have ha : raw2129step0 = (fun i j => raw2129 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2129step0 raw2129; decide +kernel
      have hl : raw2129step0Labels = raw2129Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2129 raw2129Labels permutation33 permutation6
    mixedMoment B raw2129step0 raw2129step0Labels = mixedMoment B raw2129step1 raw2129step1Labels := by
      have ha : raw2129step1 = -raw2129step0 := by apply Matrix.ext; change ∀ i j, raw2129step1 i j = -(raw2129step0 i j); unfold raw2129step1 raw2129step0; decide +kernel
      have hl : raw2129step1Labels = raw2129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2129step1 raw2129step1Labels = mixedMoment B raw2129step2 raw2129step2Labels := by
      have ha : raw2129step2 = raw2129step1 := by apply Matrix.ext; unfold raw2129step2 raw2129step1; decide +kernel
      have hl : raw2129step1Labels = labelEmbedding1 ∘ raw2129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2129step1 raw2129step1Labels raw2129step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

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

theorem canonical2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2286 raw2286Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2286 raw2286Labels = mixedMoment B raw2286step0 raw2286step0Labels := by
      have ha : raw2286step0 = (fun i j => raw2286 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2286step0 raw2286; decide +kernel
      have hl : raw2286step0Labels = raw2286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2286 raw2286Labels permutation8 permutation4
    mixedMoment B raw2286step0 raw2286step0Labels = mixedMoment B raw2286step1 raw2286step1Labels := by
      have ha : raw2286step1 = raw2286step0 := by apply Matrix.ext; unfold raw2286step1 raw2286step0; decide +kernel
      have hl : raw2286step0Labels = labelEmbedding7 ∘ raw2286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2286step0 raw2286step0Labels raw2286step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2287 raw2287Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2287 raw2287Labels = mixedMoment B raw2287step0 raw2287step0Labels := by
      have ha : raw2287step0 = (fun i j => raw2287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2287step0 raw2287; decide +kernel
      have hl : raw2287step0Labels = raw2287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2287 raw2287Labels permutation8 permutation4
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2288 raw2288Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw2288 raw2288Labels = mixedMoment B raw2288step0 raw2288step0Labels := by
      have ha : raw2288step0 = (fun i j => raw2288 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2288step0 raw2288; decide +kernel
      have hl : raw2288step0Labels = raw2288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2288 raw2288Labels permutation9 permutation6
    mixedMoment B raw2288step0 raw2288step0Labels = mixedMoment B raw2288step1 raw2288step1Labels := by
      have ha : raw2288step1 = -raw2288step0 := by apply Matrix.ext; change ∀ i j, raw2288step1 i j = -(raw2288step0 i j); unfold raw2288step1 raw2288step0; decide +kernel
      have hl : raw2288step1Labels = raw2288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2288step1 raw2288step1Labels = mixedMoment B raw2288step2 raw2288step2Labels := by
      have ha : raw2288step2 = raw2288step1 := by apply Matrix.ext; unfold raw2288step2 raw2288step1; decide +kernel
      have hl : raw2288step1Labels = labelEmbedding1 ∘ raw2288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2288step1 raw2288step1Labels raw2288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical220
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28277 raw28277Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw28277 raw28277Labels = mixedMoment B raw28277step0 raw28277step0Labels := by
      have hz : ∀ j, raw28277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28277step0 = (fun i j => raw28277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28277step0 raw28277; decide +kernel
      have hl : raw28277step0Labels = raw28277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28277 raw28277Labels permutation434 hz
    mixedMoment B raw28277step0 raw28277step0Labels = mixedMoment B raw28277step1 raw28277step1Labels := by
      have hz : ∀ j, raw28277step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28277step1 = (fun i j => raw28277step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28277step1 raw28277step0; decide +kernel
      have hl : raw28277step1Labels = raw28277step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28277step0 raw28277step0Labels permutation80 hz
    mixedMoment B raw28277step1 raw28277step1Labels = mixedMoment B raw28277step2 raw28277step2Labels := by
      have ha : raw28277step2 = (fun i j => raw28277step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28277step2 raw28277step1; decide +kernel
      have hl : raw28277step2Labels = raw28277step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28277step1 raw28277step1Labels permutation30 permutation2
    mixedMoment B raw28277step2 raw28277step2Labels = mixedMoment B raw28277step3 raw28277step3Labels := by
      have ha : raw28277step3 = -raw28277step2 := by apply Matrix.ext; change ∀ i j, raw28277step3 i j = -(raw28277step2 i j); unfold raw28277step3 raw28277step2; decide +kernel
      have hl : raw28277step3Labels = raw28277step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5111 node5111Labels := by rfl

theorem canonical28278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28278 raw28278Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw28278 raw28278Labels = mixedMoment B raw28278step0 raw28278step0Labels := by
      have hz : ∀ j, raw28278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28278step0 = (fun i j => raw28278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28278step0 raw28278; decide +kernel
      have hl : raw28278step0Labels = raw28278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28278 raw28278Labels permutation434 hz
    mixedMoment B raw28278step0 raw28278step0Labels = mixedMoment B raw28278step1 raw28278step1Labels := by
      have ha : raw28278step1 = (fun i j => raw28278step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28278step1 raw28278step0; decide +kernel
      have hl : raw28278step1Labels = raw28278step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28278step0 raw28278step0Labels permutation151 permutation2
    mixedMoment B raw28278step1 raw28278step1Labels = mixedMoment B raw28278step2 raw28278step2Labels := by
      have ha : raw28278step2 = -raw28278step1 := by apply Matrix.ext; change ∀ i j, raw28278step2 i j = -(raw28278step1 i j); unfold raw28278step2 raw28278step1; decide +kernel
      have hl : raw28278step2Labels = raw28278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical28279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28279 raw28279Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw28279 raw28279Labels = mixedMoment B raw28279step0 raw28279step0Labels := by
      have hz : ∀ j, raw28279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28279step0 = (fun i j => raw28279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28279step0 raw28279; decide +kernel
      have hl : raw28279step0Labels = raw28279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28279 raw28279Labels permutation346 hz
    mixedMoment B raw28279step0 raw28279step0Labels = mixedMoment B raw28279step1 raw28279step1Labels := by
      have ha : raw28279step1 = (fun i j => raw28279step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28279step1 raw28279step0; decide +kernel
      have hl : raw28279step1Labels = raw28279step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28279step0 raw28279step0Labels permutation151 permutation2
    mixedMoment B raw28279step1 raw28279step1Labels = mixedMoment B raw28279step2 raw28279step2Labels := by
      have ha : raw28279step2 = -raw28279step1 := by apply Matrix.ext; change ∀ i j, raw28279step2 i j = -(raw28279step1 i j); unfold raw28279step2 raw28279step1; decide +kernel
      have hl : raw28279step2Labels = raw28279step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical28280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28280 raw28280Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw28280 raw28280Labels = mixedMoment B raw28280step0 raw28280step0Labels := by
      have hz : ∀ j, raw28280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28280step0 = (fun i j => raw28280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28280step0 raw28280; decide +kernel
      have hl : raw28280step0Labels = raw28280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28280 raw28280Labels permutation434 hz
    mixedMoment B raw28280step0 raw28280step0Labels = mixedMoment B raw28280step1 raw28280step1Labels := by
      have hz : ∀ j, raw28280step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28280step1 = (fun i j => raw28280step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28280step1 raw28280step0; decide +kernel
      have hl : raw28280step1Labels = raw28280step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28280step0 raw28280step0Labels permutation80 hz
    mixedMoment B raw28280step1 raw28280step1Labels = mixedMoment B raw28280step2 raw28280step2Labels := by
      have ha : raw28280step2 = (fun i j => raw28280step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28280step2 raw28280step1; decide +kernel
      have hl : raw28280step2Labels = raw28280step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28280step1 raw28280step1Labels permutation31 permutation2
    mixedMoment B raw28280step2 raw28280step2Labels = mixedMoment B raw28280step3 raw28280step3Labels := by
      have ha : raw28280step3 = -raw28280step2 := by apply Matrix.ext; change ∀ i j, raw28280step3 i j = -(raw28280step2 i j); unfold raw28280step3 raw28280step2; decide +kernel
      have hl : raw28280step3Labels = raw28280step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical28281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28281 raw28281Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw28281 raw28281Labels = mixedMoment B raw28281step0 raw28281step0Labels := by
      have hz : ∀ j, raw28281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28281step0 = (fun i j => raw28281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28281step0 raw28281; decide +kernel
      have hl : raw28281step0Labels = raw28281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28281 raw28281Labels permutation434 hz
    mixedMoment B raw28281step0 raw28281step0Labels = mixedMoment B raw28281step1 raw28281step1Labels := by
      have hz : ∀ j, raw28281step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28281step1 = (fun i j => raw28281step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28281step1 raw28281step0; decide +kernel
      have hl : raw28281step1Labels = raw28281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28281step0 raw28281step0Labels permutation80 hz
    mixedMoment B raw28281step1 raw28281step1Labels = mixedMoment B raw28281step2 raw28281step2Labels := by
      have ha : raw28281step2 = (fun i j => raw28281step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28281step2 raw28281step1; decide +kernel
      have hl : raw28281step2Labels = raw28281step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28281step1 raw28281step1Labels permutation31 permutation2
    mixedMoment B raw28281step2 raw28281step2Labels = mixedMoment B raw28281step3 raw28281step3Labels := by
      have ha : raw28281step3 = -raw28281step2 := by apply Matrix.ext; change ∀ i j, raw28281step3 i j = -(raw28281step2 i j); unfold raw28281step3 raw28281step2; decide +kernel
      have hl : raw28281step3Labels = raw28281step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5413 node5413Labels := by rfl

theorem canonical28282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28282 raw28282Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw28282 raw28282Labels = mixedMoment B raw28282step0 raw28282step0Labels := by
      have hz : ∀ j, raw28282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28282step0 = (fun i j => raw28282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28282step0 raw28282; decide +kernel
      have hl : raw28282step0Labels = raw28282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28282 raw28282Labels permutation434 hz
    mixedMoment B raw28282step0 raw28282step0Labels = mixedMoment B raw28282step1 raw28282step1Labels := by
      have hz : ∀ j, raw28282step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28282step1 = (fun i j => raw28282step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28282step1 raw28282step0; decide +kernel
      have hl : raw28282step1Labels = raw28282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28282step0 raw28282step0Labels permutation80 hz
    mixedMoment B raw28282step1 raw28282step1Labels = mixedMoment B raw28282step2 raw28282step2Labels := by
      have ha : raw28282step2 = (fun i j => raw28282step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28282step2 raw28282step1; decide +kernel
      have hl : raw28282step2Labels = raw28282step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28282step1 raw28282step1Labels permutation8 permutation3
    mixedMoment B raw28282step2 raw28282step2Labels = mixedMoment B raw28282step3 raw28282step3Labels := by
      have ha : raw28282step3 = raw28282step2 := by apply Matrix.ext; unfold raw28282step3 raw28282step2; decide +kernel
      have hl : raw28282step2Labels = labelEmbedding6 ∘ raw28282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28282step2 raw28282step2Labels raw28282step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4476 node4476Labels := by rfl

theorem canonical28283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28283 raw28283Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw28283 raw28283Labels = mixedMoment B raw28283step0 raw28283step0Labels := by
      have hz : ∀ j, raw28283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28283step0 = (fun i j => raw28283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28283step0 raw28283; decide +kernel
      have hl : raw28283step0Labels = raw28283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28283 raw28283Labels permutation434 hz
    mixedMoment B raw28283step0 raw28283step0Labels = mixedMoment B raw28283step1 raw28283step1Labels := by
      have ha : raw28283step1 = (fun i j => raw28283step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28283step1 raw28283step0; decide +kernel
      have hl : raw28283step1Labels = raw28283step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28283step0 raw28283step0Labels permutation149 permutation2
    mixedMoment B raw28283step1 raw28283step1Labels = mixedMoment B raw28283step2 raw28283step2Labels := by
      have ha : raw28283step2 = -raw28283step1 := by apply Matrix.ext; change ∀ i j, raw28283step2 i j = -(raw28283step1 i j); unfold raw28283step2 raw28283step1; decide +kernel
      have hl : raw28283step2Labels = raw28283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5087 node5087Labels := by rfl

theorem canonical28284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28284 raw28284Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw28284 raw28284Labels = mixedMoment B raw28284step0 raw28284step0Labels := by
      have hz : ∀ j, raw28284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28284step0 = (fun i j => raw28284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28284step0 raw28284; decide +kernel
      have hl : raw28284step0Labels = raw28284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28284 raw28284Labels permutation346 hz
    mixedMoment B raw28284step0 raw28284step0Labels = mixedMoment B raw28284step1 raw28284step1Labels := by
      have ha : raw28284step1 = (fun i j => raw28284step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28284step1 raw28284step0; decide +kernel
      have hl : raw28284step1Labels = raw28284step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28284step0 raw28284step0Labels permutation149 permutation2
    mixedMoment B raw28284step1 raw28284step1Labels = mixedMoment B raw28284step2 raw28284step2Labels := by
      have ha : raw28284step2 = -raw28284step1 := by apply Matrix.ext; change ∀ i j, raw28284step2 i j = -(raw28284step1 i j); unfold raw28284step2 raw28284step1; decide +kernel
      have hl : raw28284step2Labels = raw28284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5087 node5087Labels := by rfl

theorem canonical28285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28285 raw28285Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw28285 raw28285Labels = mixedMoment B raw28285step0 raw28285step0Labels := by
      have hz : ∀ j, raw28285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28285step0 = (fun i j => raw28285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28285step0 raw28285; decide +kernel
      have hl : raw28285step0Labels = raw28285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28285 raw28285Labels permutation434 hz
    mixedMoment B raw28285step0 raw28285step0Labels = mixedMoment B raw28285step1 raw28285step1Labels := by
      have hz : ∀ j, raw28285step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28285step1 = (fun i j => raw28285step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28285step1 raw28285step0; decide +kernel
      have hl : raw28285step1Labels = raw28285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28285step0 raw28285step0Labels permutation80 hz
    mixedMoment B raw28285step1 raw28285step1Labels = mixedMoment B raw28285step2 raw28285step2Labels := by
      have ha : raw28285step2 = (fun i j => raw28285step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28285step2 raw28285step1; decide +kernel
      have hl : raw28285step2Labels = raw28285step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28285step1 raw28285step1Labels permutation31 permutation2
    mixedMoment B raw28285step2 raw28285step2Labels = mixedMoment B raw28285step3 raw28285step3Labels := by
      have ha : raw28285step3 = -raw28285step2 := by apply Matrix.ext; change ∀ i j, raw28285step3 i j = -(raw28285step2 i j); unfold raw28285step3 raw28285step2; decide +kernel
      have hl : raw28285step3Labels = raw28285step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5268 node5268Labels := by rfl

theorem canonical28286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28286 raw28286Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw28286 raw28286Labels = mixedMoment B raw28286step0 raw28286step0Labels := by
      have hz : ∀ j, raw28286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28286step0 = (fun i j => raw28286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28286step0 raw28286; decide +kernel
      have hl : raw28286step0Labels = raw28286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28286 raw28286Labels permutation434 hz
    mixedMoment B raw28286step0 raw28286step0Labels = mixedMoment B raw28286step1 raw28286step1Labels := by
      have hz : ∀ j, raw28286step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28286step1 = (fun i j => raw28286step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28286step1 raw28286step0; decide +kernel
      have hl : raw28286step1Labels = raw28286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28286step0 raw28286step0Labels permutation80 hz
    mixedMoment B raw28286step1 raw28286step1Labels = mixedMoment B raw28286step2 raw28286step2Labels := by
      have ha : raw28286step2 = (fun i j => raw28286step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28286step2 raw28286step1; decide +kernel
      have hl : raw28286step2Labels = raw28286step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28286step1 raw28286step1Labels permutation8 permutation3
    mixedMoment B raw28286step2 raw28286step2Labels = mixedMoment B raw28286step3 raw28286step3Labels := by
      have ha : raw28286step3 = raw28286step2 := by apply Matrix.ext; unfold raw28286step3 raw28286step2; decide +kernel
      have hl : raw28286step2Labels = labelEmbedding6 ∘ raw28286step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28286step2 raw28286step2Labels raw28286step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical28287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28287 raw28287Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw28287 raw28287Labels = mixedMoment B raw28287step0 raw28287step0Labels := by
      have hz : ∀ j, raw28287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28287step0 = (fun i j => raw28287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28287step0 raw28287; decide +kernel
      have hl : raw28287step0Labels = raw28287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28287 raw28287Labels permutation434 hz
    mixedMoment B raw28287step0 raw28287step0Labels = mixedMoment B raw28287step1 raw28287step1Labels := by
      have ha : raw28287step1 = (fun i j => raw28287step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28287step1 raw28287step0; decide +kernel
      have hl : raw28287step1Labels = raw28287step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28287step0 raw28287step0Labels permutation34 permutation3
    mixedMoment B raw28287step1 raw28287step1Labels = mixedMoment B raw28287step2 raw28287step2Labels := by
      have ha : raw28287step2 = raw28287step1 := by apply Matrix.ext; unfold raw28287step2 raw28287step1; decide +kernel
      have hl : raw28287step1Labels = labelEmbedding6 ∘ raw28287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28287step1 raw28287step1Labels raw28287step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4367 node4367Labels := by rfl

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

theorem canonical28288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28288 raw28288Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw28288 raw28288Labels = mixedMoment B raw28288step0 raw28288step0Labels := by
      have hz : ∀ j, raw28288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28288step0 = (fun i j => raw28288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28288step0 raw28288; decide +kernel
      have hl : raw28288step0Labels = raw28288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28288 raw28288Labels permutation434 hz
    mixedMoment B raw28288step0 raw28288step0Labels = mixedMoment B raw28288step1 raw28288step1Labels := by
      have ha : raw28288step1 = (fun i j => raw28288step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28288step1 raw28288step0; decide +kernel
      have hl : raw28288step1Labels = raw28288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28288step0 raw28288step0Labels permutation34 permutation3
    mixedMoment B raw28288step1 raw28288step1Labels = mixedMoment B raw28288step2 raw28288step2Labels := by
      have ha : raw28288step2 = raw28288step1 := by apply Matrix.ext; unfold raw28288step2 raw28288step1; decide +kernel
      have hl : raw28288step1Labels = labelEmbedding6 ∘ raw28288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28288step1 raw28288step1Labels raw28288step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

theorem canonical28289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28289 raw28289Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw28289 raw28289Labels = mixedMoment B raw28289step0 raw28289step0Labels := by
      have ha : raw28289step0 = (fun i j => raw28289 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28289step0 raw28289; decide +kernel
      have hl : raw28289step0Labels = raw28289Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28289 raw28289Labels permutation682 permutation2
    mixedMoment B raw28289step0 raw28289step0Labels = mixedMoment B raw28289step1 raw28289step1Labels := by
      have ha : raw28289step1 = -raw28289step0 := by apply Matrix.ext; change ∀ i j, raw28289step1 i j = -(raw28289step0 i j); unfold raw28289step1 raw28289step0; decide +kernel
      have hl : raw28289step1Labels = raw28289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5034 node5034Labels := by rfl

theorem canonical28290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28290 raw28290Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw28290 raw28290Labels = mixedMoment B raw28290step0 raw28290step0Labels := by
      have hz : ∀ j, raw28290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28290step0 = (fun i j => raw28290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28290step0 raw28290; decide +kernel
      have hl : raw28290step0Labels = raw28290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28290 raw28290Labels permutation434 hz
    mixedMoment B raw28290step0 raw28290step0Labels = mixedMoment B raw28290step1 raw28290step1Labels := by
      have ha : raw28290step1 = (fun i j => raw28290step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28290step1 raw28290step0; decide +kernel
      have hl : raw28290step1Labels = raw28290step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28290step0 raw28290step0Labels permutation145 permutation2
    mixedMoment B raw28290step1 raw28290step1Labels = mixedMoment B raw28290step2 raw28290step2Labels := by
      have ha : raw28290step2 = -raw28290step1 := by apply Matrix.ext; change ∀ i j, raw28290step2 i j = -(raw28290step1 i j); unfold raw28290step2 raw28290step1; decide +kernel
      have hl : raw28290step2Labels = raw28290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical28291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28291 raw28291Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw28291 raw28291Labels = mixedMoment B raw28291step0 raw28291step0Labels := by
      have hz : ∀ j, raw28291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28291step0 = (fun i j => raw28291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28291step0 raw28291; decide +kernel
      have hl : raw28291step0Labels = raw28291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28291 raw28291Labels permutation434 hz
    mixedMoment B raw28291step0 raw28291step0Labels = mixedMoment B raw28291step1 raw28291step1Labels := by
      have ha : raw28291step1 = (fun i j => raw28291step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28291step1 raw28291step0; decide +kernel
      have hl : raw28291step1Labels = raw28291step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28291step0 raw28291step0Labels permutation34 permutation3
    mixedMoment B raw28291step1 raw28291step1Labels = mixedMoment B raw28291step2 raw28291step2Labels := by
      have ha : raw28291step2 = raw28291step1 := by apply Matrix.ext; unfold raw28291step2 raw28291step1; decide +kernel
      have hl : raw28291step1Labels = labelEmbedding6 ∘ raw28291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28291step1 raw28291step1Labels raw28291step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical28292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28292 raw28292Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw28292 raw28292Labels = mixedMoment B raw28292step0 raw28292step0Labels := by
      have hz : ∀ j, raw28292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28292step0 = (fun i j => raw28292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28292step0 raw28292; decide +kernel
      have hl : raw28292step0Labels = raw28292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28292 raw28292Labels permutation346 hz
    mixedMoment B raw28292step0 raw28292step0Labels = mixedMoment B raw28292step1 raw28292step1Labels := by
      have ha : raw28292step1 = (fun i j => raw28292step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28292step1 raw28292step0; decide +kernel
      have hl : raw28292step1Labels = raw28292step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28292step0 raw28292step0Labels permutation34 permutation3
    mixedMoment B raw28292step1 raw28292step1Labels = mixedMoment B raw28292step2 raw28292step2Labels := by
      have ha : raw28292step2 = raw28292step1 := by apply Matrix.ext; unfold raw28292step2 raw28292step1; decide +kernel
      have hl : raw28292step1Labels = labelEmbedding6 ∘ raw28292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28292step1 raw28292step1Labels raw28292step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4367 node4367Labels := by rfl

theorem canonical28293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28293 raw28293Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw28293 raw28293Labels = mixedMoment B raw28293step0 raw28293step0Labels := by
      have hz : ∀ j, raw28293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28293step0 = (fun i j => raw28293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28293step0 raw28293; decide +kernel
      have hl : raw28293step0Labels = raw28293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28293 raw28293Labels permutation346 hz
    mixedMoment B raw28293step0 raw28293step0Labels = mixedMoment B raw28293step1 raw28293step1Labels := by
      have ha : raw28293step1 = (fun i j => raw28293step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28293step1 raw28293step0; decide +kernel
      have hl : raw28293step1Labels = raw28293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28293step0 raw28293step0Labels permutation34 permutation3
    mixedMoment B raw28293step1 raw28293step1Labels = mixedMoment B raw28293step2 raw28293step2Labels := by
      have ha : raw28293step2 = raw28293step1 := by apply Matrix.ext; unfold raw28293step2 raw28293step1; decide +kernel
      have hl : raw28293step1Labels = labelEmbedding6 ∘ raw28293step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28293step1 raw28293step1Labels raw28293step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

theorem canonical28294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28294 raw28294Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw28294 raw28294Labels = mixedMoment B raw28294step0 raw28294step0Labels := by
      have ha : raw28294step0 = (fun i j => raw28294 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28294step0 raw28294; decide +kernel
      have hl : raw28294step0Labels = raw28294Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28294 raw28294Labels permutation688 permutation2
    mixedMoment B raw28294step0 raw28294step0Labels = mixedMoment B raw28294step1 raw28294step1Labels := by
      have ha : raw28294step1 = -raw28294step0 := by apply Matrix.ext; change ∀ i j, raw28294step1 i j = -(raw28294step0 i j); unfold raw28294step1 raw28294step0; decide +kernel
      have hl : raw28294step1Labels = raw28294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5034 node5034Labels := by rfl

theorem canonical28295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28295 raw28295Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw28295 raw28295Labels = mixedMoment B raw28295step0 raw28295step0Labels := by
      have hz : ∀ j, raw28295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28295step0 = (fun i j => raw28295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28295step0 raw28295; decide +kernel
      have hl : raw28295step0Labels = raw28295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28295 raw28295Labels permutation346 hz
    mixedMoment B raw28295step0 raw28295step0Labels = mixedMoment B raw28295step1 raw28295step1Labels := by
      have ha : raw28295step1 = (fun i j => raw28295step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28295step1 raw28295step0; decide +kernel
      have hl : raw28295step1Labels = raw28295step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28295step0 raw28295step0Labels permutation145 permutation2
    mixedMoment B raw28295step1 raw28295step1Labels = mixedMoment B raw28295step2 raw28295step2Labels := by
      have ha : raw28295step2 = -raw28295step1 := by apply Matrix.ext; change ∀ i j, raw28295step2 i j = -(raw28295step1 i j); unfold raw28295step2 raw28295step1; decide +kernel
      have hl : raw28295step2Labels = raw28295step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical28296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28296 raw28296Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw28296 raw28296Labels = mixedMoment B raw28296step0 raw28296step0Labels := by
      have hz : ∀ j, raw28296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28296step0 = (fun i j => raw28296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28296step0 raw28296; decide +kernel
      have hl : raw28296step0Labels = raw28296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28296 raw28296Labels permutation346 hz
    mixedMoment B raw28296step0 raw28296step0Labels = mixedMoment B raw28296step1 raw28296step1Labels := by
      have ha : raw28296step1 = (fun i j => raw28296step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28296step1 raw28296step0; decide +kernel
      have hl : raw28296step1Labels = raw28296step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28296step0 raw28296step0Labels permutation34 permutation3
    mixedMoment B raw28296step1 raw28296step1Labels = mixedMoment B raw28296step2 raw28296step2Labels := by
      have ha : raw28296step2 = raw28296step1 := by apply Matrix.ext; unfold raw28296step2 raw28296step1; decide +kernel
      have hl : raw28296step1Labels = labelEmbedding6 ∘ raw28296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28296step1 raw28296step1Labels raw28296step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical28297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28297 raw28297Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw28297 raw28297Labels = mixedMoment B raw28297step0 raw28297step0Labels := by
      have hz : ∀ j, raw28297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28297step0 = (fun i j => raw28297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28297step0 raw28297; decide +kernel
      have hl : raw28297step0Labels = raw28297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28297 raw28297Labels permutation434 hz
    mixedMoment B raw28297step0 raw28297step0Labels = mixedMoment B raw28297step1 raw28297step1Labels := by
      have hz : ∀ j, raw28297step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28297step1 = (fun i j => raw28297step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28297step1 raw28297step0; decide +kernel
      have hl : raw28297step1Labels = raw28297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28297step0 raw28297step0Labels permutation80 hz
    mixedMoment B raw28297step1 raw28297step1Labels = mixedMoment B raw28297step2 raw28297step2Labels := by
      have ha : raw28297step2 = (fun i j => raw28297step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28297step2 raw28297step1; decide +kernel
      have hl : raw28297step2Labels = raw28297step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28297step1 raw28297step1Labels permutation8 permutation3
    mixedMoment B raw28297step2 raw28297step2Labels = mixedMoment B raw28297step3 raw28297step3Labels := by
      have ha : raw28297step3 = raw28297step2 := by apply Matrix.ext; unfold raw28297step3 raw28297step2; decide +kernel
      have hl : raw28297step2Labels = labelEmbedding6 ∘ raw28297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28297step2 raw28297step2Labels raw28297step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4374 node4374Labels := by rfl

theorem canonical28298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28298 raw28298Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw28298 raw28298Labels = mixedMoment B raw28298step0 raw28298step0Labels := by
      have hz : ∀ j, raw28298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28298step0 = (fun i j => raw28298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28298step0 raw28298; decide +kernel
      have hl : raw28298step0Labels = raw28298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28298 raw28298Labels permutation434 hz
    mixedMoment B raw28298step0 raw28298step0Labels = mixedMoment B raw28298step1 raw28298step1Labels := by
      have hz : ∀ j, raw28298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28298step1 = (fun i j => raw28298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28298step1 raw28298step0; decide +kernel
      have hl : raw28298step1Labels = raw28298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28298step0 raw28298step0Labels permutation80 hz
    mixedMoment B raw28298step1 raw28298step1Labels = mixedMoment B raw28298step2 raw28298step2Labels := by
      have ha : raw28298step2 = (fun i j => raw28298step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28298step2 raw28298step1; decide +kernel
      have hl : raw28298step2Labels = raw28298step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28298step1 raw28298step1Labels permutation31 permutation2
    mixedMoment B raw28298step2 raw28298step2Labels = mixedMoment B raw28298step3 raw28298step3Labels := by
      have ha : raw28298step3 = -raw28298step2 := by apply Matrix.ext; change ∀ i j, raw28298step3 i j = -(raw28298step2 i j); unfold raw28298step3 raw28298step2; decide +kernel
      have hl : raw28298step3Labels = raw28298step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4953 node4953Labels := by rfl

theorem canonical28299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28299 raw28299Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw28299 raw28299Labels = mixedMoment B raw28299step0 raw28299step0Labels := by
      have hz : ∀ j, raw28299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28299step0 = (fun i j => raw28299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28299step0 raw28299; decide +kernel
      have hl : raw28299step0Labels = raw28299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28299 raw28299Labels permutation434 hz
    mixedMoment B raw28299step0 raw28299step0Labels = mixedMoment B raw28299step1 raw28299step1Labels := by
      have ha : raw28299step1 = (fun i j => raw28299step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28299step1 raw28299step0; decide +kernel
      have hl : raw28299step1Labels = raw28299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28299step0 raw28299step0Labels permutation151 permutation2
    mixedMoment B raw28299step1 raw28299step1Labels = mixedMoment B raw28299step2 raw28299step2Labels := by
      have ha : raw28299step2 = -raw28299step1 := by apply Matrix.ext; change ∀ i j, raw28299step2 i j = -(raw28299step1 i j); unfold raw28299step2 raw28299step1; decide +kernel
      have hl : raw28299step2Labels = raw28299step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4944 node4944Labels := by rfl

theorem canonical28300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28300 raw28300Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw28300 raw28300Labels = mixedMoment B raw28300step0 raw28300step0Labels := by
      have hz : ∀ j, raw28300 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28300step0 = (fun i j => raw28300 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28300step0 raw28300; decide +kernel
      have hl : raw28300step0Labels = raw28300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28300 raw28300Labels permutation346 hz
    mixedMoment B raw28300step0 raw28300step0Labels = mixedMoment B raw28300step1 raw28300step1Labels := by
      have ha : raw28300step1 = (fun i j => raw28300step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28300step1 raw28300step0; decide +kernel
      have hl : raw28300step1Labels = raw28300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28300step0 raw28300step0Labels permutation151 permutation2
    mixedMoment B raw28300step1 raw28300step1Labels = mixedMoment B raw28300step2 raw28300step2Labels := by
      have ha : raw28300step2 = -raw28300step1 := by apply Matrix.ext; change ∀ i j, raw28300step2 i j = -(raw28300step1 i j); unfold raw28300step2 raw28300step1; decide +kernel
      have hl : raw28300step2Labels = raw28300step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4944 node4944Labels := by rfl

theorem canonical28301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28301 raw28301Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw28301 raw28301Labels = mixedMoment B raw28301step0 raw28301step0Labels := by
      have hz : ∀ j, raw28301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28301step0 = (fun i j => raw28301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28301step0 raw28301; decide +kernel
      have hl : raw28301step0Labels = raw28301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28301 raw28301Labels permutation434 hz
    mixedMoment B raw28301step0 raw28301step0Labels = mixedMoment B raw28301step1 raw28301step1Labels := by
      have hz : ∀ j, raw28301step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28301step1 = (fun i j => raw28301step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28301step1 raw28301step0; decide +kernel
      have hl : raw28301step1Labels = raw28301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28301step0 raw28301step0Labels permutation80 hz
    mixedMoment B raw28301step1 raw28301step1Labels = mixedMoment B raw28301step2 raw28301step2Labels := by
      have ha : raw28301step2 = (fun i j => raw28301step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28301step2 raw28301step1; decide +kernel
      have hl : raw28301step2Labels = raw28301step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28301step1 raw28301step1Labels permutation9 permutation3
    mixedMoment B raw28301step2 raw28301step2Labels = mixedMoment B raw28301step3 raw28301step3Labels := by
      have ha : raw28301step3 = raw28301step2 := by apply Matrix.ext; unfold raw28301step3 raw28301step2; decide +kernel
      have hl : raw28301step2Labels = labelEmbedding6 ∘ raw28301step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28301step2 raw28301step2Labels raw28301step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical28302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28302 raw28302Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw28302 raw28302Labels = mixedMoment B raw28302step0 raw28302step0Labels := by
      have hz : ∀ j, raw28302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28302step0 = (fun i j => raw28302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28302step0 raw28302; decide +kernel
      have hl : raw28302step0Labels = raw28302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28302 raw28302Labels permutation434 hz
    mixedMoment B raw28302step0 raw28302step0Labels = mixedMoment B raw28302step1 raw28302step1Labels := by
      have hz : ∀ j, raw28302step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28302step1 = (fun i j => raw28302step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28302step1 raw28302step0; decide +kernel
      have hl : raw28302step1Labels = raw28302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28302step0 raw28302step0Labels permutation80 hz
    mixedMoment B raw28302step1 raw28302step1Labels = mixedMoment B raw28302step2 raw28302step2Labels := by
      have ha : raw28302step2 = (fun i j => raw28302step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28302step2 raw28302step1; decide +kernel
      have hl : raw28302step2Labels = raw28302step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28302step1 raw28302step1Labels permutation8 permutation3
    mixedMoment B raw28302step2 raw28302step2Labels = mixedMoment B raw28302step3 raw28302step3Labels := by
      have ha : raw28302step3 = raw28302step2 := by apply Matrix.ext; unfold raw28302step3 raw28302step2; decide +kernel
      have hl : raw28302step2Labels = labelEmbedding6 ∘ raw28302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28302step2 raw28302step2Labels raw28302step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4370 node4370Labels := by rfl

theorem canonical28303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28303 raw28303Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw28303 raw28303Labels = mixedMoment B raw28303step0 raw28303step0Labels := by
      have hz : ∀ j, raw28303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28303step0 = (fun i j => raw28303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28303step0 raw28303; decide +kernel
      have hl : raw28303step0Labels = raw28303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28303 raw28303Labels permutation434 hz
    mixedMoment B raw28303step0 raw28303step0Labels = mixedMoment B raw28303step1 raw28303step1Labels := by
      have hz : ∀ j, raw28303step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28303step1 = (fun i j => raw28303step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28303step1 raw28303step0; decide +kernel
      have hl : raw28303step1Labels = raw28303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28303step0 raw28303step0Labels permutation80 hz
    mixedMoment B raw28303step1 raw28303step1Labels = mixedMoment B raw28303step2 raw28303step2Labels := by
      have ha : raw28303step2 = (fun i j => raw28303step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28303step2 raw28303step1; decide +kernel
      have hl : raw28303step2Labels = raw28303step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28303step1 raw28303step1Labels permutation31 permutation2
    mixedMoment B raw28303step2 raw28303step2Labels = mixedMoment B raw28303step3 raw28303step3Labels := by
      have ha : raw28303step3 = -raw28303step2 := by apply Matrix.ext; change ∀ i j, raw28303step3 i j = -(raw28303step2 i j); unfold raw28303step3 raw28303step2; decide +kernel
      have hl : raw28303step3Labels = raw28303step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4559 node4559Labels := by rfl

theorem canonical28304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28304 raw28304Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw28304 raw28304Labels = mixedMoment B raw28304step0 raw28304step0Labels := by
      have hz : ∀ j, raw28304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28304step0 = (fun i j => raw28304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28304step0 raw28304; decide +kernel
      have hl : raw28304step0Labels = raw28304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28304 raw28304Labels permutation434 hz
    mixedMoment B raw28304step0 raw28304step0Labels = mixedMoment B raw28304step1 raw28304step1Labels := by
      have ha : raw28304step1 = (fun i j => raw28304step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28304step1 raw28304step0; decide +kernel
      have hl : raw28304step1Labels = raw28304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28304step0 raw28304step0Labels permutation151 permutation2
    mixedMoment B raw28304step1 raw28304step1Labels = mixedMoment B raw28304step2 raw28304step2Labels := by
      have ha : raw28304step2 = -raw28304step1 := by apply Matrix.ext; change ∀ i j, raw28304step2 i j = -(raw28304step1 i j); unfold raw28304step2 raw28304step1; decide +kernel
      have hl : raw28304step2Labels = raw28304step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4547 node4547Labels := by rfl

theorem canonical28305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28305 raw28305Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw28305 raw28305Labels = mixedMoment B raw28305step0 raw28305step0Labels := by
      have hz : ∀ j, raw28305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28305step0 = (fun i j => raw28305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28305step0 raw28305; decide +kernel
      have hl : raw28305step0Labels = raw28305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28305 raw28305Labels permutation346 hz
    mixedMoment B raw28305step0 raw28305step0Labels = mixedMoment B raw28305step1 raw28305step1Labels := by
      have ha : raw28305step1 = (fun i j => raw28305step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28305step1 raw28305step0; decide +kernel
      have hl : raw28305step1Labels = raw28305step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28305step0 raw28305step0Labels permutation151 permutation2
    mixedMoment B raw28305step1 raw28305step1Labels = mixedMoment B raw28305step2 raw28305step2Labels := by
      have ha : raw28305step2 = -raw28305step1 := by apply Matrix.ext; change ∀ i j, raw28305step2 i j = -(raw28305step1 i j); unfold raw28305step2 raw28305step1; decide +kernel
      have hl : raw28305step2Labels = raw28305step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4547 node4547Labels := by rfl

theorem canonical28306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28306 raw28306Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw28306 raw28306Labels = mixedMoment B raw28306step0 raw28306step0Labels := by
      have hz : ∀ j, raw28306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28306step0 = (fun i j => raw28306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28306step0 raw28306; decide +kernel
      have hl : raw28306step0Labels = raw28306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28306 raw28306Labels permutation434 hz
    mixedMoment B raw28306step0 raw28306step0Labels = mixedMoment B raw28306step1 raw28306step1Labels := by
      have hz : ∀ j, raw28306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28306step1 = (fun i j => raw28306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28306step1 raw28306step0; decide +kernel
      have hl : raw28306step1Labels = raw28306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28306step0 raw28306step0Labels permutation80 hz
    mixedMoment B raw28306step1 raw28306step1Labels = mixedMoment B raw28306step2 raw28306step2Labels := by
      have ha : raw28306step2 = (fun i j => raw28306step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28306step2 raw28306step1; decide +kernel
      have hl : raw28306step2Labels = raw28306step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28306step1 raw28306step1Labels permutation31 permutation2
    mixedMoment B raw28306step2 raw28306step2Labels = mixedMoment B raw28306step3 raw28306step3Labels := by
      have ha : raw28306step3 = -raw28306step2 := by apply Matrix.ext; change ∀ i j, raw28306step3 i j = -(raw28306step2 i j); unfold raw28306step3 raw28306step2; decide +kernel
      have hl : raw28306step3Labels = raw28306step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4609 node4609Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4559 node4559Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1145 node1145Labels + mixedMoment B node3277 node3277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1398 singletonSmall4559
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4559) = raw1398Labels := by decide +kernel
  rw [hl, canonical1398 B hB] at h
  have hc0 : mixedMoment B raw1398 (Fin.cases (0 : Fin 2) singletonSmall4559) =
      mixedMoment B node1145 node1145Labels := by
    have ha : raw1398 = raw1399 := by apply Matrix.ext; unfold raw1398 raw1399; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4559 = raw1399Labels := by decide +kernel
    rw [ha, hj, canonical1399 B hB]
  have hc1 : mixedMoment B raw1398 (Fin.cases (1 : Fin 2) singletonSmall4559) =
      mixedMoment B node3277 node3277Labels := by
    have ha : raw1398 = raw1400 := by apply Matrix.ext; unfold raw1398 raw1400; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4559 = raw1400Labels := by decide +kernel
    rw [ha, hj, canonical1400 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4953 node4953Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2345 node2345Labels + mixedMoment B node3423 node3423Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1929 singletonSmall4953
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4953) = raw1929Labels := by decide +kernel
  rw [hl, canonical1929 B hB] at h
  have hc0 : mixedMoment B raw1929 (Fin.cases (0 : Fin 2) singletonSmall4953) =
      mixedMoment B node2345 node2345Labels := by
    have ha : raw1929 = raw1930 := by apply Matrix.ext; unfold raw1929 raw1930; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4953 = raw1930Labels := by decide +kernel
    rw [ha, hj, canonical1930 B hB]
  have hc1 : mixedMoment B raw1929 (Fin.cases (1 : Fin 2) singletonSmall4953) =
      mixedMoment B node3423 node3423Labels := by
    have ha : raw1929 = raw1931 := by apply Matrix.ext; unfold raw1929 raw1931; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4953 = raw1931Labels := by decide +kernel
    rw [ha, hj, canonical1931 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4972 node4972Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2434 node2434Labels + mixedMoment B node3457 node3457Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1956 singletonSmall4972
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4972) = raw1956Labels := by decide +kernel
  rw [hl, canonical1956 B hB] at h
  have hc0 : mixedMoment B raw1956 (Fin.cases (0 : Fin 2) singletonSmall4972) =
      mixedMoment B node2434 node2434Labels := by
    have ha : raw1956 = raw1957 := by apply Matrix.ext; unfold raw1956 raw1957; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4972 = raw1957Labels := by decide +kernel
    rw [ha, hj, canonical1957 B hB]
  have hc1 : mixedMoment B raw1956 (Fin.cases (1 : Fin 2) singletonSmall4972) =
      mixedMoment B node3457 node3457Labels := by
    have ha : raw1956 = raw1958 := by apply Matrix.ext; unfold raw1956 raw1958; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4972 = raw1958Labels := by decide +kernel
    rw [ha, hj, canonical1958 B hB]
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

theorem singleton5102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5102 node5102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2512 node2512Labels + mixedMoment B node3471 node3471Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2127 singletonSmall5102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5102) = raw2127Labels := by decide +kernel
  rw [hl, canonical2127 B hB] at h
  have hc0 : mixedMoment B raw2127 (Fin.cases (0 : Fin 2) singletonSmall5102) =
      mixedMoment B node2512 node2512Labels := by
    have ha : raw2127 = raw2128 := by apply Matrix.ext; unfold raw2127 raw2128; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5102 = raw2128Labels := by decide +kernel
    rw [ha, hj, canonical2128 B hB]
  have hc1 : mixedMoment B raw2127 (Fin.cases (1 : Fin 2) singletonSmall5102) =
      mixedMoment B node3471 node3471Labels := by
    have ha : raw2127 = raw2129 := by apply Matrix.ext; unfold raw2127 raw2129; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5102 = raw2129Labels := by decide +kernel
    rw [ha, hj, canonical2129 B hB]
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

theorem singleton5275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5275 node5275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2743 node2743Labels + mixedMoment B node3548 node3548Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2286 singletonSmall5275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5275) = raw2286Labels := by decide +kernel
  rw [hl, canonical2286 B hB] at h
  have hc0 : mixedMoment B raw2286 (Fin.cases (0 : Fin 2) singletonSmall5275) =
      mixedMoment B node2743 node2743Labels := by
    have ha : raw2286 = raw2287 := by apply Matrix.ext; unfold raw2286 raw2287; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5275 = raw2287Labels := by decide +kernel
    rw [ha, hj, canonical2287 B hB]
  have hc1 : mixedMoment B raw2286 (Fin.cases (1 : Fin 2) singletonSmall5275) =
      mixedMoment B node3548 node3548Labels := by
    have ha : raw2286 = raw2288 := by apply Matrix.ext; unfold raw2286 raw2288; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5275 = raw2288Labels := by decide +kernel
    rw [ha, hj, canonical2288 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound5302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5302 node5302Labels = Sparse.eval nodeValue5302 (mixedVector B) := by
  have h := singleton5302 B _hB
  rw [sound3054 B _hB _hF, sound3626 B _hB _hF] at h
  norm_num [nodeValue5302, nodeValue3054, nodeValue3626, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1145 node1145Labels = Sparse.eval nodeValue1145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1145) = mixedMoment B node1145 node1145Labels := rfl
  simpa [nodeValue1145, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2345 node2345Labels = Sparse.eval nodeValue2345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2345) = mixedMoment B node2345 node2345Labels := rfl
  simpa [nodeValue2345, Sparse.eval] using hc.symm

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

theorem sound2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2434 node2434Labels = Sparse.eval nodeValue2434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2434) = mixedMoment B node2434 node2434Labels := rfl
  simpa [nodeValue2434, Sparse.eval] using hc.symm

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

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

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

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3277 node3277Labels = Sparse.eval nodeValue3277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3277) = mixedMoment B node3277 node3277Labels := rfl
  simpa [nodeValue3277, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3423 node3423Labels = Sparse.eval nodeValue3423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3423) = mixedMoment B node3423 node3423Labels := rfl
  simpa [nodeValue3423, Sparse.eval] using hc.symm

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

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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

theorem sound4367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4367 node4367Labels = Sparse.eval nodeValue4367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4367) = mixedMoment B node4367 node4367Labels := rfl
  simpa [nodeValue4367, Sparse.eval] using hc.symm

theorem sound4370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4370 node4370Labels = Sparse.eval nodeValue4370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4370) = mixedMoment B node4370 node4370Labels := rfl
  simpa [nodeValue4370, Sparse.eval] using hc.symm

theorem sound4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4374 node4374Labels = Sparse.eval nodeValue4374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4374) = mixedMoment B node4374 node4374Labels := rfl
  simpa [nodeValue4374, Sparse.eval] using hc.symm

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

theorem sound4476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4476 node4476Labels = Sparse.eval nodeValue4476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4476) = mixedMoment B node4476 node4476Labels := rfl
  simpa [nodeValue4476, Sparse.eval] using hc.symm

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

theorem sound4547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4547 node4547Labels = Sparse.eval nodeValue4547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4547) = mixedMoment B node4547 node4547Labels := rfl
  simpa [nodeValue4547, Sparse.eval] using hc.symm

theorem sound4559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4559 node4559Labels = Sparse.eval nodeValue4559 (mixedVector B) := by
  have h := singleton4559 B _hB
  rw [sound1145 B _hB _hF, sound3277 B _hB _hF] at h
  norm_num [nodeValue4559, nodeValue1145, nodeValue3277, Sparse.eval] at h ⊢
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

theorem sound4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4609 node4609Labels = Sparse.eval nodeValue4609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4609) = mixedMoment B node4609 node4609Labels := rfl
  simpa [nodeValue4609, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4944 node4944Labels = Sparse.eval nodeValue4944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4944) = mixedMoment B node4944 node4944Labels := rfl
  simpa [nodeValue4944, Sparse.eval] using hc.symm

theorem sound4953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4953 node4953Labels = Sparse.eval nodeValue4953 (mixedVector B) := by
  have h := singleton4953 B _hB
  rw [sound2345 B _hB _hF, sound3423 B _hB _hF] at h
  norm_num [nodeValue4953, nodeValue2345, nodeValue3423, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4972 node4972Labels = Sparse.eval nodeValue4972 (mixedVector B) := by
  have h := singleton4972 B _hB
  rw [sound2434 B _hB _hF, sound3457 B _hB _hF] at h
  norm_num [nodeValue4972, nodeValue2434, nodeValue3457, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5034 node5034Labels = Sparse.eval nodeValue5034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5034) = mixedMoment B node5034 node5034Labels := rfl
  simpa [nodeValue5034, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = 0 := by
  exact mixedMoment_order_one B hB node5111 node5111Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5087 node5087Labels = Sparse.eval nodeValue5087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5087) = mixedMoment B node5087 node5087Labels := rfl
  simpa [nodeValue5087, Sparse.eval] using hc.symm

theorem sound5102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5102 node5102Labels = Sparse.eval nodeValue5102 (mixedVector B) := by
  have h := singleton5102 B _hB
  rw [sound2512 B _hB _hF, sound3471 B _hB _hF] at h
  norm_num [nodeValue5102, nodeValue2512, nodeValue3471, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = Sparse.eval nodeValue5111 (mixedVector B) := by
  simpa only [nodeValue5111, Sparse.eval_nil] using zero5111 B _hB _hF

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

theorem sound5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5139 node5139Labels = Sparse.eval nodeValue5139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5139) = mixedMoment B node5139 node5139Labels := rfl
  simpa [nodeValue5139, Sparse.eval] using hc.symm

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

theorem sound5268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5268 node5268Labels = Sparse.eval nodeValue5268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5268) = mixedMoment B node5268 node5268Labels := rfl
  simpa [nodeValue5268, Sparse.eval] using hc.symm

theorem sound5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5275 node5275Labels = Sparse.eval nodeValue5275 (mixedVector B) := by
  have h := singleton5275 B _hB
  rw [sound2743 B _hB _hF, sound3548 B _hB _hF] at h
  norm_num [nodeValue5275, nodeValue2743, nodeValue3548, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5413 node5413Labels = 0 := by
  exact mixedMoment_order_one B hB node5413 node5413Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5413 node5413Labels = Sparse.eval nodeValue5413 (mixedVector B) := by
  simpa only [nodeValue5413, Sparse.eval_nil] using zero5413 B _hB _hF

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

theorem sourceEq1996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1996 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 1) (sourceB1996 + difference 1 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 1) (sourceB1996 + difference 1 0) sourceC1996) = raw28277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28277; decide +kernel
    rw [ha]
    exact (canonical28277 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 2) (sourceB1996 + difference 2 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 2) (sourceB1996 + difference 2 0) sourceC1996) = raw28278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28278; decide +kernel
    rw [ha]
    exact (canonical28278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 3) (sourceB1996 + difference 3 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 3) (sourceB1996 + difference 3 0) sourceC1996) = raw28279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28279; decide +kernel
    rw [ha]
    exact (canonical28279 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 4) (sourceB1996 + difference 4 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 4) (sourceB1996 + difference 4 0) sourceC1996) = raw28280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28280; decide +kernel
    rw [ha]
    exact (canonical28280 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1996 + difference 0 5) (sourceB1996 + difference 5 0) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA1996 + difference 0 5) (sourceB1996 + difference 5 0) sourceC1996) = raw28281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28281; decide +kernel
    rw [ha]
    exact (canonical28281 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 0) (sourceB1996 + difference 0 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 0) (sourceB1996 + difference 0 1) sourceC1996) = raw28282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28282; decide +kernel
    rw [ha]
    exact (canonical28282 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 2) (sourceB1996 + difference 2 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 2) (sourceB1996 + difference 2 1) sourceC1996) = raw28283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28283; decide +kernel
    rw [ha]
    exact (canonical28283 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 3) (sourceB1996 + difference 3 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 3) (sourceB1996 + difference 3 1) sourceC1996) = raw28284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28284; decide +kernel
    rw [ha]
    exact (canonical28284 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 4) (sourceB1996 + difference 4 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 4) (sourceB1996 + difference 4 1) sourceC1996) = raw28285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28285; decide +kernel
    rw [ha]
    exact (canonical28285 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1996 + difference 1 5) (sourceB1996 + difference 5 1) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA1996 + difference 1 5) (sourceB1996 + difference 5 1) sourceC1996) = raw28286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28286; decide +kernel
    rw [ha]
    exact (canonical28286 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 0) (sourceB1996 + difference 0 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 0) (sourceB1996 + difference 0 2) sourceC1996) = raw28287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28287; decide +kernel
    rw [ha]
    exact (canonical28287 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 1) (sourceB1996 + difference 1 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 1) (sourceB1996 + difference 1 2) sourceC1996) = raw28288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28288; decide +kernel
    rw [ha]
    exact (canonical28288 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 3) (sourceB1996 + difference 3 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 3) (sourceB1996 + difference 3 2) sourceC1996) = raw28289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28289; decide +kernel
    rw [ha]
    exact (canonical28289 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 4) (sourceB1996 + difference 4 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 4) (sourceB1996 + difference 4 2) sourceC1996) = raw28290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28290; decide +kernel
    rw [ha]
    exact (canonical28290 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1996 + difference 2 5) (sourceB1996 + difference 5 2) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1996 + difference 2 5) (sourceB1996 + difference 5 2) sourceC1996) = raw28291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28291; decide +kernel
    rw [ha]
    exact (canonical28291 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 0) (sourceB1996 + difference 0 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 0) (sourceB1996 + difference 0 3) sourceC1996) = raw28292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28292; decide +kernel
    rw [ha]
    exact (canonical28292 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 1) (sourceB1996 + difference 1 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 1) (sourceB1996 + difference 1 3) sourceC1996) = raw28293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28293; decide +kernel
    rw [ha]
    exact (canonical28293 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 2) (sourceB1996 + difference 2 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 2) (sourceB1996 + difference 2 3) sourceC1996) = raw28294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28294; decide +kernel
    rw [ha]
    exact (canonical28294 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 4) (sourceB1996 + difference 4 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 4) (sourceB1996 + difference 4 3) sourceC1996) = raw28295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28295; decide +kernel
    rw [ha]
    exact (canonical28295 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1996 + difference 3 5) (sourceB1996 + difference 5 3) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1996 + difference 3 5) (sourceB1996 + difference 5 3) sourceC1996) = raw28296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28296; decide +kernel
    rw [ha]
    exact (canonical28296 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 0) (sourceB1996 + difference 0 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 0) (sourceB1996 + difference 0 4) sourceC1996) = raw28297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28297; decide +kernel
    rw [ha]
    exact (canonical28297 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 1) (sourceB1996 + difference 1 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 1) (sourceB1996 + difference 1 4) sourceC1996) = raw28298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28298; decide +kernel
    rw [ha]
    exact (canonical28298 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 2) (sourceB1996 + difference 2 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 2) (sourceB1996 + difference 2 4) sourceC1996) = raw28299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28299; decide +kernel
    rw [ha]
    exact (canonical28299 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 3) (sourceB1996 + difference 3 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 3) (sourceB1996 + difference 3 4) sourceC1996) = raw28300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28300; decide +kernel
    rw [ha]
    exact (canonical28300 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1996 + difference 4 5) (sourceB1996 + difference 5 4) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA1996 + difference 4 5) (sourceB1996 + difference 5 4) sourceC1996) = raw28301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28301; decide +kernel
    rw [ha]
    exact (canonical28301 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 0) (sourceB1996 + difference 0 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 0) (sourceB1996 + difference 0 5) sourceC1996) = raw28302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28302; decide +kernel
    rw [ha]
    exact (canonical28302 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 1) (sourceB1996 + difference 1 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 1) (sourceB1996 + difference 1 5) sourceC1996) = raw28303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28303; decide +kernel
    rw [ha]
    exact (canonical28303 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 2) (sourceB1996 + difference 2 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 2) (sourceB1996 + difference 2 5) sourceC1996) = raw28304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28304; decide +kernel
    rw [ha]
    exact (canonical28304 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 3) (sourceB1996 + difference 3 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 3) (sourceB1996 + difference 3 5) sourceC1996) = raw28305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28305; decide +kernel
    rw [ha]
    exact (canonical28305 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1996 + difference 5 4) (sourceB1996 + difference 4 5) sourceC1996) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1996 + difference 5 4) (sourceB1996 + difference 4 5) sourceC1996) = raw28306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1996 sourceB1996 sourceC1996 difference raw28306; decide +kernel
    rw [ha]
    exact (canonical28306 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1996 sourceB1996 sourceC1996
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1996, Integer.Sparse.eval]
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

theorem reindexCheck1684 : Integer.Sparse.reindex keyMap MixedData.row1684 = numericRow1684 := by decide +kernel

theorem numericCheck1684 (x : Master → ℝ) : Integer.Sparse.eval numericRow1684 x =
    (4 : ℝ) * reducedSource1684 x := by
  norm_num [numericRow1684, reducedSource1684, Integer.Sparse.eval, Sparse.eval, nodeValue4367, nodeValue4370, nodeValue4374, nodeValue4476, nodeValue4547, nodeValue4559, nodeValue4609, nodeValue4944, nodeValue4953, nodeValue4972, nodeValue5034, nodeValue5087, nodeValue5102, nodeValue5111, nodeValue5139, nodeValue5204, nodeValue5207, nodeValue5268, nodeValue5275, nodeValue5302, nodeValue5413] <;> ring

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

theorem reducedZero1684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1684 (mixedVector B) = 0 := by
  have h4367 : mixedVector B (Sum.inr 4367) = Sparse.eval nodeValue4367 (mixedVector B) := by
    change mixedMoment B node4367 node4367Labels = _
    exact sound4367 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4476 : mixedVector B (Sum.inr 4476) = Sparse.eval nodeValue4476 (mixedVector B) := by
    change mixedMoment B node4476 node4476Labels = _
    exact sound4476 B hB hF
  have h4547 : mixedVector B (Sum.inr 4547) = Sparse.eval nodeValue4547 (mixedVector B) := by
    change mixedMoment B node4547 node4547Labels = _
    exact sound4547 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h5034 : mixedVector B (Sum.inr 5034) = Sparse.eval nodeValue5034 (mixedVector B) := by
    change mixedMoment B node5034 node5034Labels = _
    exact sound5034 B hB hF
  have h5087 : mixedVector B (Sum.inr 5087) = Sparse.eval nodeValue5087 (mixedVector B) := by
    change mixedMoment B node5087 node5087Labels = _
    exact sound5087 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5268 : mixedVector B (Sum.inr 5268) = Sparse.eval nodeValue5268 (mixedVector B) := by
    change mixedMoment B node5268 node5268Labels = _
    exact sound5268 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  simpa only [sourceForm1996, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4367, h4370, h4374, h4476, h4547, h4559, h4609, h4944, h4953, h4972, h5034, h5087, h5102, h5111, h5139, h5204, h5207, h5268, h5275, h5302, h5413, reducedSource1684] using sourceEq1996 B hB

theorem rowSound1684_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1684 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1684, numericCheck1684, reducedZero1684 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e_oai
