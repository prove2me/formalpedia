-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:37:55.366278+00:00
-- url     : https://prove2.me/submissions/884da949-dd08-44ee-a0e1-f09c169ef1be

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e

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

theorem canonical1473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1473 raw1473Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw1473 raw1473Labels = mixedMoment B raw1473step0 raw1473step0Labels := by
      have ha : raw1473step0 = (fun i j => raw1473 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1473step0 raw1473; decide +kernel
      have hl : raw1473step0Labels = raw1473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1473 raw1473Labels permutation152 permutation4
    mixedMoment B raw1473step0 raw1473step0Labels = mixedMoment B raw1473step1 raw1473step1Labels := by
      have ha : raw1473step1 = raw1473step0 := by apply Matrix.ext; unfold raw1473step1 raw1473step0; decide +kernel
      have hl : raw1473step0Labels = labelEmbedding7 ∘ raw1473step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1473step0 raw1473step0Labels raw1473step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

theorem canonical1474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1474 raw1474Labels = mixedMoment B node1760 node1760Labels := by
  calc
    mixedMoment B raw1474 raw1474Labels = mixedMoment B raw1474step0 raw1474step0Labels := by
      have ha : raw1474step0 = (fun i j => raw1474 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1474step0 raw1474; decide +kernel
      have hl : raw1474step0Labels = raw1474Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1474 raw1474Labels permutation152 permutation4
    _ = mixedMoment B node1760 node1760Labels := by rfl

theorem canonical1475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1475 raw1475Labels = mixedMoment B node1836 node1836Labels := by
  calc
    mixedMoment B raw1475 raw1475Labels = mixedMoment B raw1475step0 raw1475step0Labels := by
      have ha : raw1475step0 = (fun i j => raw1475 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1475step0 raw1475; decide +kernel
      have hl : raw1475step0Labels = raw1475Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1475 raw1475Labels permutation158 permutation6
    mixedMoment B raw1475step0 raw1475step0Labels = mixedMoment B raw1475step1 raw1475step1Labels := by
      have ha : raw1475step1 = -raw1475step0 := by apply Matrix.ext; change ∀ i j, raw1475step1 i j = -(raw1475step0 i j); unfold raw1475step1 raw1475step0; decide +kernel
      have hl : raw1475step1Labels = raw1475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1475step1 raw1475step1Labels = mixedMoment B raw1475step2 raw1475step2Labels := by
      have ha : raw1475step2 = raw1475step1 := by apply Matrix.ext; unfold raw1475step2 raw1475step1; decide +kernel
      have hl : raw1475step1Labels = labelEmbedding1 ∘ raw1475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1475step1 raw1475step1Labels raw1475step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1836 node1836Labels := by rfl

theorem canonical1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1491 raw1491Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw1491 raw1491Labels = mixedMoment B raw1491step0 raw1491step0Labels := by
      have ha : raw1491step0 = (fun i j => raw1491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1491step0 raw1491; decide +kernel
      have hl : raw1491step0Labels = raw1491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1491 raw1491Labels permutation32 permutation4
    mixedMoment B raw1491step0 raw1491step0Labels = mixedMoment B raw1491step1 raw1491step1Labels := by
      have ha : raw1491step1 = raw1491step0 := by apply Matrix.ext; unfold raw1491step1 raw1491step0; decide +kernel
      have hl : raw1491step0Labels = labelEmbedding7 ∘ raw1491step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1491step0 raw1491step0Labels raw1491step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical1492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1492 raw1492Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw1492 raw1492Labels = mixedMoment B raw1492step0 raw1492step0Labels := by
      have ha : raw1492step0 = (fun i j => raw1492 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1492step0 raw1492; decide +kernel
      have hl : raw1492step0Labels = raw1492Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1492 raw1492Labels permutation32 permutation4
    _ = mixedMoment B node1766 node1766Labels := by rfl

theorem canonical1493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1493 raw1493Labels = mixedMoment B node1850 node1850Labels := by
  calc
    mixedMoment B raw1493 raw1493Labels = mixedMoment B raw1493step0 raw1493step0Labels := by
      have ha : raw1493step0 = (fun i j => raw1493 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1493step0 raw1493; decide +kernel
      have hl : raw1493step0Labels = raw1493Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1493 raw1493Labels permutation32 permutation6
    mixedMoment B raw1493step0 raw1493step0Labels = mixedMoment B raw1493step1 raw1493step1Labels := by
      have ha : raw1493step1 = -raw1493step0 := by apply Matrix.ext; change ∀ i j, raw1493step1 i j = -(raw1493step0 i j); unfold raw1493step1 raw1493step0; decide +kernel
      have hl : raw1493step1Labels = raw1493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1493step1 raw1493step1Labels = mixedMoment B raw1493step2 raw1493step2Labels := by
      have ha : raw1493step2 = raw1493step1 := by apply Matrix.ext; unfold raw1493step2 raw1493step1; decide +kernel
      have hl : raw1493step1Labels = labelEmbedding1 ∘ raw1493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1493step1 raw1493step1Labels raw1493step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1850 node1850Labels := by rfl

theorem canonical1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1506 raw1506Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw1506 raw1506Labels = mixedMoment B raw1506step0 raw1506step0Labels := by
      have ha : raw1506step0 = (fun i j => raw1506 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1506step0 raw1506; decide +kernel
      have hl : raw1506step0Labels = raw1506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1506 raw1506Labels permutation32 permutation4
    mixedMoment B raw1506step0 raw1506step0Labels = mixedMoment B raw1506step1 raw1506step1Labels := by
      have ha : raw1506step1 = raw1506step0 := by apply Matrix.ext; unfold raw1506step1 raw1506step0; decide +kernel
      have hl : raw1506step0Labels = labelEmbedding7 ∘ raw1506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1506step0 raw1506step0Labels raw1506step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

theorem canonical1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1507 raw1507Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw1507 raw1507Labels = mixedMoment B raw1507step0 raw1507step0Labels := by
      have ha : raw1507step0 = (fun i j => raw1507 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1507step0 raw1507; decide +kernel
      have hl : raw1507step0Labels = raw1507Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1507 raw1507Labels permutation32 permutation4
    _ = mixedMoment B node1773 node1773Labels := by rfl

theorem canonical1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1508 raw1508Labels = mixedMoment B node1841 node1841Labels := by
  calc
    mixedMoment B raw1508 raw1508Labels = mixedMoment B raw1508step0 raw1508step0Labels := by
      have ha : raw1508step0 = (fun i j => raw1508 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1508step0 raw1508; decide +kernel
      have hl : raw1508step0Labels = raw1508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1508 raw1508Labels permutation32 permutation6
    mixedMoment B raw1508step0 raw1508step0Labels = mixedMoment B raw1508step1 raw1508step1Labels := by
      have ha : raw1508step1 = -raw1508step0 := by apply Matrix.ext; change ∀ i j, raw1508step1 i j = -(raw1508step0 i j); unfold raw1508step1 raw1508step0; decide +kernel
      have hl : raw1508step1Labels = raw1508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1508step1 raw1508step1Labels = mixedMoment B raw1508step2 raw1508step2Labels := by
      have ha : raw1508step2 = raw1508step1 := by apply Matrix.ext; unfold raw1508step2 raw1508step1; decide +kernel
      have hl : raw1508step1Labels = labelEmbedding1 ∘ raw1508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1508step1 raw1508step1Labels raw1508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1841 node1841Labels := by rfl

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

theorem canonical1590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1590 raw1590Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw1590 raw1590Labels = mixedMoment B raw1590step0 raw1590step0Labels := by
      have ha : raw1590step0 = (fun i j => raw1590 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1590step0 raw1590; decide +kernel
      have hl : raw1590step0Labels = raw1590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1590 raw1590Labels permutation152 permutation4
    mixedMoment B raw1590step0 raw1590step0Labels = mixedMoment B raw1590step1 raw1590step1Labels := by
      have ha : raw1590step1 = raw1590step0 := by apply Matrix.ext; unfold raw1590step1 raw1590step0; decide +kernel
      have hl : raw1590step0Labels = labelEmbedding7 ∘ raw1590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1590step0 raw1590step0Labels raw1590step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

theorem canonical1591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1591 raw1591Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw1591 raw1591Labels = mixedMoment B raw1591step0 raw1591step0Labels := by
      have ha : raw1591step0 = (fun i j => raw1591 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1591step0 raw1591; decide +kernel
      have hl : raw1591step0Labels = raw1591Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1591 raw1591Labels permutation152 permutation4
    _ = mixedMoment B node1860 node1860Labels := by rfl

theorem canonical1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1592 raw1592Labels = mixedMoment B node1888 node1888Labels := by
  calc
    mixedMoment B raw1592 raw1592Labels = mixedMoment B raw1592step0 raw1592step0Labels := by
      have ha : raw1592step0 = (fun i j => raw1592 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1592step0 raw1592; decide +kernel
      have hl : raw1592step0Labels = raw1592Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1592 raw1592Labels permutation152 permutation6
    mixedMoment B raw1592step0 raw1592step0Labels = mixedMoment B raw1592step1 raw1592step1Labels := by
      have ha : raw1592step1 = -raw1592step0 := by apply Matrix.ext; change ∀ i j, raw1592step1 i j = -(raw1592step0 i j); unfold raw1592step1 raw1592step0; decide +kernel
      have hl : raw1592step1Labels = raw1592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1592step1 raw1592step1Labels = mixedMoment B raw1592step2 raw1592step2Labels := by
      have ha : raw1592step2 = raw1592step1 := by apply Matrix.ext; unfold raw1592step2 raw1592step1; decide +kernel
      have hl : raw1592step1Labels = labelEmbedding1 ∘ raw1592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1592step1 raw1592step1Labels raw1592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1888 node1888Labels := by rfl

theorem canonical1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1596 raw1596Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw1596 raw1596Labels = mixedMoment B raw1596step0 raw1596step0Labels := by
      have ha : raw1596step0 = (fun i j => raw1596 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1596step0 raw1596; decide +kernel
      have hl : raw1596step0Labels = raw1596Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1596 raw1596Labels permutation152 permutation4
    mixedMoment B raw1596step0 raw1596step0Labels = mixedMoment B raw1596step1 raw1596step1Labels := by
      have ha : raw1596step1 = raw1596step0 := by apply Matrix.ext; unfold raw1596step1 raw1596step0; decide +kernel
      have hl : raw1596step0Labels = labelEmbedding7 ∘ raw1596step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1596step0 raw1596step0Labels raw1596step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

theorem canonical1597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1597 raw1597Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw1597 raw1597Labels = mixedMoment B raw1597step0 raw1597step0Labels := by
      have ha : raw1597step0 = (fun i j => raw1597 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1597step0 raw1597; decide +kernel
      have hl : raw1597step0Labels = raw1597Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1597 raw1597Labels permutation152 permutation4
    _ = mixedMoment B node1863 node1863Labels := by rfl

theorem canonical1598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1598 raw1598Labels = mixedMoment B node1883 node1883Labels := by
  calc
    mixedMoment B raw1598 raw1598Labels = mixedMoment B raw1598step0 raw1598step0Labels := by
      have ha : raw1598step0 = (fun i j => raw1598 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1598step0 raw1598; decide +kernel
      have hl : raw1598step0Labels = raw1598Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1598 raw1598Labels permutation152 permutation6
    mixedMoment B raw1598step0 raw1598step0Labels = mixedMoment B raw1598step1 raw1598step1Labels := by
      have ha : raw1598step1 = -raw1598step0 := by apply Matrix.ext; change ∀ i j, raw1598step1 i j = -(raw1598step0 i j); unfold raw1598step1 raw1598step0; decide +kernel
      have hl : raw1598step1Labels = raw1598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1598step1 raw1598step1Labels = mixedMoment B raw1598step2 raw1598step2Labels := by
      have ha : raw1598step2 = raw1598step1 := by apply Matrix.ext; unfold raw1598step2 raw1598step1; decide +kernel
      have hl : raw1598step1Labels = labelEmbedding1 ∘ raw1598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1598step1 raw1598step1Labels raw1598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1883 node1883Labels := by rfl

theorem canonical1641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1641 raw1641Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw1641 raw1641Labels = mixedMoment B raw1641step0 raw1641step0Labels := by
      have ha : raw1641step0 = (fun i j => raw1641 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1641step0 raw1641; decide +kernel
      have hl : raw1641step0Labels = raw1641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1641 raw1641Labels permutation152 permutation4
    mixedMoment B raw1641step0 raw1641step0Labels = mixedMoment B raw1641step1 raw1641step1Labels := by
      have ha : raw1641step1 = raw1641step0 := by apply Matrix.ext; unfold raw1641step1 raw1641step0; decide +kernel
      have hl : raw1641step0Labels = labelEmbedding7 ∘ raw1641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1641step0 raw1641step0Labels raw1641step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

theorem canonical1642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1642 raw1642Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw1642 raw1642Labels = mixedMoment B raw1642step0 raw1642step0Labels := by
      have ha : raw1642step0 = (fun i j => raw1642 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1642step0 raw1642; decide +kernel
      have hl : raw1642step0Labels = raw1642Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1642 raw1642Labels permutation152 permutation4
    _ = mixedMoment B node1897 node1897Labels := by rfl

theorem canonical1643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1643 raw1643Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw1643 raw1643Labels = mixedMoment B raw1643step0 raw1643step0Labels := by
      have ha : raw1643step0 = (fun i j => raw1643 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1643step0 raw1643; decide +kernel
      have hl : raw1643step0Labels = raw1643Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1643 raw1643Labels permutation164 permutation6
    mixedMoment B raw1643step0 raw1643step0Labels = mixedMoment B raw1643step1 raw1643step1Labels := by
      have ha : raw1643step1 = -raw1643step0 := by apply Matrix.ext; change ∀ i j, raw1643step1 i j = -(raw1643step0 i j); unfold raw1643step1 raw1643step0; decide +kernel
      have hl : raw1643step1Labels = raw1643step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1643step1 raw1643step1Labels = mixedMoment B raw1643step2 raw1643step2Labels := by
      have ha : raw1643step2 = raw1643step1 := by apply Matrix.ext; unfold raw1643step2 raw1643step1; decide +kernel
      have hl : raw1643step1Labels = labelEmbedding1 ∘ raw1643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1643step1 raw1643step1Labels raw1643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1907 node1907Labels := by rfl

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

theorem canonical1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1689 raw1689Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw1689 raw1689Labels = mixedMoment B raw1689step0 raw1689step0Labels := by
      have ha : raw1689step0 = (fun i j => raw1689 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1689step0 raw1689; decide +kernel
      have hl : raw1689step0Labels = raw1689Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1689 raw1689Labels permutation152 permutation4
    mixedMoment B raw1689step0 raw1689step0Labels = mixedMoment B raw1689step1 raw1689step1Labels := by
      have ha : raw1689step1 = raw1689step0 := by apply Matrix.ext; unfold raw1689step1 raw1689step0; decide +kernel
      have hl : raw1689step0Labels = labelEmbedding7 ∘ raw1689step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1689step0 raw1689step0Labels raw1689step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1690 raw1690Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw1690 raw1690Labels = mixedMoment B raw1690step0 raw1690step0Labels := by
      have ha : raw1690step0 = (fun i j => raw1690 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1690step0 raw1690; decide +kernel
      have hl : raw1690step0Labels = raw1690Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1690 raw1690Labels permutation152 permutation4
    _ = mixedMoment B node1960 node1960Labels := by rfl

theorem canonical1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1691 raw1691Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw1691 raw1691Labels = mixedMoment B raw1691step0 raw1691step0Labels := by
      have ha : raw1691step0 = (fun i j => raw1691 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1691step0 raw1691; decide +kernel
      have hl : raw1691step0Labels = raw1691Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1691 raw1691Labels permutation152 permutation6
    mixedMoment B raw1691step0 raw1691step0Labels = mixedMoment B raw1691step1 raw1691step1Labels := by
      have ha : raw1691step1 = -raw1691step0 := by apply Matrix.ext; change ∀ i j, raw1691step1 i j = -(raw1691step0 i j); unfold raw1691step1 raw1691step0; decide +kernel
      have hl : raw1691step1Labels = raw1691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1691step1 raw1691step1Labels = mixedMoment B raw1691step2 raw1691step2Labels := by
      have ha : raw1691step2 = raw1691step1 := by apply Matrix.ext; unfold raw1691step2 raw1691step1; decide +kernel
      have hl : raw1691step1Labels = labelEmbedding1 ∘ raw1691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1691step1 raw1691step1Labels raw1691step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

theorem canonical1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1704 raw1704Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw1704 raw1704Labels = mixedMoment B raw1704step0 raw1704step0Labels := by
      have ha : raw1704step0 = (fun i j => raw1704 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1704step0 raw1704; decide +kernel
      have hl : raw1704step0Labels = raw1704Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1704 raw1704Labels permutation32 permutation4
    mixedMoment B raw1704step0 raw1704step0Labels = mixedMoment B raw1704step1 raw1704step1Labels := by
      have ha : raw1704step1 = raw1704step0 := by apply Matrix.ext; unfold raw1704step1 raw1704step0; decide +kernel
      have hl : raw1704step0Labels = labelEmbedding7 ∘ raw1704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1704step0 raw1704step0Labels raw1704step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1705 raw1705Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw1705 raw1705Labels = mixedMoment B raw1705step0 raw1705step0Labels := by
      have ha : raw1705step0 = (fun i j => raw1705 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1705step0 raw1705; decide +kernel
      have hl : raw1705step0Labels = raw1705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1705 raw1705Labels permutation32 permutation4
    _ = mixedMoment B node1969 node1969Labels := by rfl

theorem canonical1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1706 raw1706Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw1706 raw1706Labels = mixedMoment B raw1706step0 raw1706step0Labels := by
      have ha : raw1706step0 = (fun i j => raw1706 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1706step0 raw1706; decide +kernel
      have hl : raw1706step0Labels = raw1706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1706 raw1706Labels permutation32 permutation6
    mixedMoment B raw1706step0 raw1706step0Labels = mixedMoment B raw1706step1 raw1706step1Labels := by
      have ha : raw1706step1 = -raw1706step0 := by apply Matrix.ext; change ∀ i j, raw1706step1 i j = -(raw1706step0 i j); unfold raw1706step1 raw1706step0; decide +kernel
      have hl : raw1706step1Labels = raw1706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1706step1 raw1706step1Labels = mixedMoment B raw1706step2 raw1706step2Labels := by
      have ha : raw1706step2 = raw1706step1 := by apply Matrix.ext; unfold raw1706step2 raw1706step1; decide +kernel
      have hl : raw1706step1Labels = labelEmbedding1 ∘ raw1706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1706step1 raw1706step1Labels raw1706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1713 raw1713Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw1713 raw1713Labels = mixedMoment B raw1713step0 raw1713step0Labels := by
      have ha : raw1713step0 = (fun i j => raw1713 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1713step0 raw1713; decide +kernel
      have hl : raw1713step0Labels = raw1713Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1713 raw1713Labels permutation152 permutation4
    mixedMoment B raw1713step0 raw1713step0Labels = mixedMoment B raw1713step1 raw1713step1Labels := by
      have ha : raw1713step1 = raw1713step0 := by apply Matrix.ext; unfold raw1713step1 raw1713step0; decide +kernel
      have hl : raw1713step0Labels = labelEmbedding7 ∘ raw1713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1713step0 raw1713step0Labels raw1713step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

theorem canonical1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1714 raw1714Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw1714 raw1714Labels = mixedMoment B raw1714step0 raw1714step0Labels := by
      have ha : raw1714step0 = (fun i j => raw1714 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1714step0 raw1714; decide +kernel
      have hl : raw1714step0Labels = raw1714Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1714 raw1714Labels permutation152 permutation4
    _ = mixedMoment B node1987 node1987Labels := by rfl

theorem canonical1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1715 raw1715Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw1715 raw1715Labels = mixedMoment B raw1715step0 raw1715step0Labels := by
      have ha : raw1715step0 = (fun i j => raw1715 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1715step0 raw1715; decide +kernel
      have hl : raw1715step0Labels = raw1715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1715 raw1715Labels permutation176 permutation6
    mixedMoment B raw1715step0 raw1715step0Labels = mixedMoment B raw1715step1 raw1715step1Labels := by
      have ha : raw1715step1 = -raw1715step0 := by apply Matrix.ext; change ∀ i j, raw1715step1 i j = -(raw1715step0 i j); unfold raw1715step1 raw1715step0; decide +kernel
      have hl : raw1715step1Labels = raw1715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1715step1 raw1715step1Labels = mixedMoment B raw1715step2 raw1715step2Labels := by
      have ha : raw1715step2 = raw1715step1 := by apply Matrix.ext; unfold raw1715step2 raw1715step1; decide +kernel
      have hl : raw1715step1Labels = labelEmbedding1 ∘ raw1715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1715step1 raw1715step1Labels raw1715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1996 node1996Labels := by rfl

theorem canonical1722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1722 raw1722Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw1722 raw1722Labels = mixedMoment B raw1722step0 raw1722step0Labels := by
      have ha : raw1722step0 = (fun i j => raw1722 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1722step0 raw1722; decide +kernel
      have hl : raw1722step0Labels = raw1722Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1722 raw1722Labels permutation32 permutation4
    mixedMoment B raw1722step0 raw1722step0Labels = mixedMoment B raw1722step1 raw1722step1Labels := by
      have ha : raw1722step1 = raw1722step0 := by apply Matrix.ext; unfold raw1722step1 raw1722step0; decide +kernel
      have hl : raw1722step0Labels = labelEmbedding7 ∘ raw1722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1722step0 raw1722step0Labels raw1722step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

theorem canonical1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1723 raw1723Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw1723 raw1723Labels = mixedMoment B raw1723step0 raw1723step0Labels := by
      have ha : raw1723step0 = (fun i j => raw1723 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1723step0 raw1723; decide +kernel
      have hl : raw1723step0Labels = raw1723Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1723 raw1723Labels permutation32 permutation4
    _ = mixedMoment B node2003 node2003Labels := by rfl

theorem canonical1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1724 raw1724Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw1724 raw1724Labels = mixedMoment B raw1724step0 raw1724step0Labels := by
      have ha : raw1724step0 = (fun i j => raw1724 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1724step0 raw1724; decide +kernel
      have hl : raw1724step0Labels = raw1724Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1724 raw1724Labels permutation38 permutation6
    mixedMoment B raw1724step0 raw1724step0Labels = mixedMoment B raw1724step1 raw1724step1Labels := by
      have ha : raw1724step1 = -raw1724step0 := by apply Matrix.ext; change ∀ i j, raw1724step1 i j = -(raw1724step0 i j); unfold raw1724step1 raw1724step0; decide +kernel
      have hl : raw1724step1Labels = raw1724step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1724step1 raw1724step1Labels = mixedMoment B raw1724step2 raw1724step2Labels := by
      have ha : raw1724step2 = raw1724step1 := by apply Matrix.ext; unfold raw1724step2 raw1724step1; decide +kernel
      have hl : raw1724step1Labels = labelEmbedding1 ∘ raw1724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1724step1 raw1724step1Labels raw1724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2006 node2006Labels := by rfl

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

theorem canonical1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1737 raw1737Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw1737 raw1737Labels = mixedMoment B raw1737step0 raw1737step0Labels := by
      have ha : raw1737step0 = (fun i j => raw1737 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1737step0 raw1737; decide +kernel
      have hl : raw1737step0Labels = raw1737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1737 raw1737Labels permutation32 permutation4
    mixedMoment B raw1737step0 raw1737step0Labels = mixedMoment B raw1737step1 raw1737step1Labels := by
      have ha : raw1737step1 = raw1737step0 := by apply Matrix.ext; unfold raw1737step1 raw1737step0; decide +kernel
      have hl : raw1737step0Labels = labelEmbedding7 ∘ raw1737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1737step0 raw1737step0Labels raw1737step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1738 raw1738Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw1738 raw1738Labels = mixedMoment B raw1738step0 raw1738step0Labels := by
      have ha : raw1738step0 = (fun i j => raw1738 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1738step0 raw1738; decide +kernel
      have hl : raw1738step0Labels = raw1738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1738 raw1738Labels permutation32 permutation4
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1739 raw1739Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw1739 raw1739Labels = mixedMoment B raw1739step0 raw1739step0Labels := by
      have ha : raw1739step0 = (fun i j => raw1739 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1739step0 raw1739; decide +kernel
      have hl : raw1739step0Labels = raw1739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1739 raw1739Labels permutation34 permutation6
    mixedMoment B raw1739step0 raw1739step0Labels = mixedMoment B raw1739step1 raw1739step1Labels := by
      have ha : raw1739step1 = -raw1739step0 := by apply Matrix.ext; change ∀ i j, raw1739step1 i j = -(raw1739step0 i j); unfold raw1739step1 raw1739step0; decide +kernel
      have hl : raw1739step1Labels = raw1739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1739step1 raw1739step1Labels = mixedMoment B raw1739step2 raw1739step2Labels := by
      have ha : raw1739step2 = raw1739step1 := by apply Matrix.ext; unfold raw1739step2 raw1739step1; decide +kernel
      have hl : raw1739step1Labels = labelEmbedding1 ∘ raw1739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1739step1 raw1739step1Labels raw1739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1749 raw1749Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw1749 raw1749Labels = mixedMoment B raw1749step0 raw1749step0Labels := by
      have ha : raw1749step0 = (fun i j => raw1749 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1749step0 raw1749; decide +kernel
      have hl : raw1749step0Labels = raw1749Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1749 raw1749Labels permutation32 permutation4
    mixedMoment B raw1749step0 raw1749step0Labels = mixedMoment B raw1749step1 raw1749step1Labels := by
      have ha : raw1749step1 = raw1749step0 := by apply Matrix.ext; unfold raw1749step1 raw1749step0; decide +kernel
      have hl : raw1749step0Labels = labelEmbedding7 ∘ raw1749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1749step0 raw1749step0Labels raw1749step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1750 raw1750Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw1750 raw1750Labels = mixedMoment B raw1750step0 raw1750step0Labels := by
      have ha : raw1750step0 = (fun i j => raw1750 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1750step0 raw1750; decide +kernel
      have hl : raw1750step0Labels = raw1750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1750 raw1750Labels permutation32 permutation4
    _ = mixedMoment B node2029 node2029Labels := by rfl

theorem canonical1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1751 raw1751Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw1751 raw1751Labels = mixedMoment B raw1751step0 raw1751step0Labels := by
      have ha : raw1751step0 = (fun i j => raw1751 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1751step0 raw1751; decide +kernel
      have hl : raw1751step0Labels = raw1751Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1751 raw1751Labels permutation32 permutation6
    mixedMoment B raw1751step0 raw1751step0Labels = mixedMoment B raw1751step1 raw1751step1Labels := by
      have ha : raw1751step1 = -raw1751step0 := by apply Matrix.ext; change ∀ i j, raw1751step1 i j = -(raw1751step0 i j); unfold raw1751step1 raw1751step0; decide +kernel
      have hl : raw1751step1Labels = raw1751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1751step1 raw1751step1Labels = mixedMoment B raw1751step2 raw1751step2Labels := by
      have ha : raw1751step2 = raw1751step1 := by apply Matrix.ext; unfold raw1751step2 raw1751step1; decide +kernel
      have hl : raw1751step1Labels = labelEmbedding1 ∘ raw1751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1751step1 raw1751step1Labels raw1751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical1764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1764 raw1764Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw1764 raw1764Labels = mixedMoment B raw1764step0 raw1764step0Labels := by
      have ha : raw1764step0 = (fun i j => raw1764 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1764step0 raw1764; decide +kernel
      have hl : raw1764step0Labels = raw1764Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1764 raw1764Labels permutation32 permutation4
    mixedMoment B raw1764step0 raw1764step0Labels = mixedMoment B raw1764step1 raw1764step1Labels := by
      have ha : raw1764step1 = raw1764step0 := by apply Matrix.ext; unfold raw1764step1 raw1764step0; decide +kernel
      have hl : raw1764step0Labels = labelEmbedding7 ∘ raw1764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1764step0 raw1764step0Labels raw1764step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical1765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1765 raw1765Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw1765 raw1765Labels = mixedMoment B raw1765step0 raw1765step0Labels := by
      have ha : raw1765step0 = (fun i j => raw1765 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1765step0 raw1765; decide +kernel
      have hl : raw1765step0Labels = raw1765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1765 raw1765Labels permutation32 permutation4
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1766 raw1766Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw1766 raw1766Labels = mixedMoment B raw1766step0 raw1766step0Labels := by
      have ha : raw1766step0 = (fun i j => raw1766 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1766step0 raw1766; decide +kernel
      have hl : raw1766step0Labels = raw1766Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1766 raw1766Labels permutation32 permutation6
    mixedMoment B raw1766step0 raw1766step0Labels = mixedMoment B raw1766step1 raw1766step1Labels := by
      have ha : raw1766step1 = -raw1766step0 := by apply Matrix.ext; change ∀ i j, raw1766step1 i j = -(raw1766step0 i j); unfold raw1766step1 raw1766step0; decide +kernel
      have hl : raw1766step1Labels = raw1766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1766step1 raw1766step1Labels = mixedMoment B raw1766step2 raw1766step2Labels := by
      have ha : raw1766step2 = raw1766step1 := by apply Matrix.ext; unfold raw1766step2 raw1766step1; decide +kernel
      have hl : raw1766step1Labels = labelEmbedding1 ∘ raw1766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1766step1 raw1766step1Labels raw1766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

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

theorem canonical1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1815 raw1815Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw1815 raw1815Labels = mixedMoment B raw1815step0 raw1815step0Labels := by
      have ha : raw1815step0 = (fun i j => raw1815 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1815step0 raw1815; decide +kernel
      have hl : raw1815step0Labels = raw1815Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1815 raw1815Labels permutation32 permutation4
    mixedMoment B raw1815step0 raw1815step0Labels = mixedMoment B raw1815step1 raw1815step1Labels := by
      have ha : raw1815step1 = raw1815step0 := by apply Matrix.ext; unfold raw1815step1 raw1815step0; decide +kernel
      have hl : raw1815step0Labels = labelEmbedding7 ∘ raw1815step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1815step0 raw1815step0Labels raw1815step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1816 raw1816Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw1816 raw1816Labels = mixedMoment B raw1816step0 raw1816step0Labels := by
      have ha : raw1816step0 = (fun i j => raw1816 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1816step0 raw1816; decide +kernel
      have hl : raw1816step0Labels = raw1816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1816 raw1816Labels permutation32 permutation4
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1817 raw1817Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw1817 raw1817Labels = mixedMoment B raw1817step0 raw1817step0Labels := by
      have ha : raw1817step0 = (fun i j => raw1817 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1817step0 raw1817; decide +kernel
      have hl : raw1817step0Labels = raw1817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1817 raw1817Labels permutation44 permutation6
    mixedMoment B raw1817step0 raw1817step0Labels = mixedMoment B raw1817step1 raw1817step1Labels := by
      have ha : raw1817step1 = -raw1817step0 := by apply Matrix.ext; change ∀ i j, raw1817step1 i j = -(raw1817step0 i j); unfold raw1817step1 raw1817step0; decide +kernel
      have hl : raw1817step1Labels = raw1817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1817step1 raw1817step1Labels = mixedMoment B raw1817step2 raw1817step2Labels := by
      have ha : raw1817step2 = raw1817step1 := by apply Matrix.ext; unfold raw1817step2 raw1817step1; decide +kernel
      have hl : raw1817step1Labels = labelEmbedding1 ∘ raw1817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1817step1 raw1817step1Labels raw1817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

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

theorem canonical2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2163 raw2163Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw2163 raw2163Labels = mixedMoment B raw2163step0 raw2163step0Labels := by
      have ha : raw2163step0 = (fun i j => raw2163 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2163step0 raw2163; decide +kernel
      have hl : raw2163step0Labels = raw2163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2163 raw2163Labels permutation152 permutation4
    mixedMoment B raw2163step0 raw2163step0Labels = mixedMoment B raw2163step1 raw2163step1Labels := by
      have ha : raw2163step1 = raw2163step0 := by apply Matrix.ext; unfold raw2163step1 raw2163step0; decide +kernel
      have hl : raw2163step0Labels = labelEmbedding7 ∘ raw2163step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2163step0 raw2163step0Labels raw2163step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2164 raw2164Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw2164 raw2164Labels = mixedMoment B raw2164step0 raw2164step0Labels := by
      have ha : raw2164step0 = (fun i j => raw2164 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2164step0 raw2164; decide +kernel
      have hl : raw2164step0Labels = raw2164Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2164 raw2164Labels permutation152 permutation4
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2165 raw2165Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw2165 raw2165Labels = mixedMoment B raw2165step0 raw2165step0Labels := by
      have ha : raw2165step0 = (fun i j => raw2165 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2165step0 raw2165; decide +kernel
      have hl : raw2165step0Labels = raw2165Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2165 raw2165Labels permutation176 permutation6
    mixedMoment B raw2165step0 raw2165step0Labels = mixedMoment B raw2165step1 raw2165step1Labels := by
      have ha : raw2165step1 = -raw2165step0 := by apply Matrix.ext; change ∀ i j, raw2165step1 i j = -(raw2165step0 i j); unfold raw2165step1 raw2165step0; decide +kernel
      have hl : raw2165step1Labels = raw2165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2165step1 raw2165step1Labels = mixedMoment B raw2165step2 raw2165step2Labels := by
      have ha : raw2165step2 = raw2165step1 := by apply Matrix.ext; unfold raw2165step2 raw2165step1; decide +kernel
      have hl : raw2165step1Labels = labelEmbedding1 ∘ raw2165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2165step1 raw2165step1Labels raw2165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

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

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25427 raw25427Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw25427 raw25427Labels = mixedMoment B raw25427step0 raw25427step0Labels := by
      have hz : ∀ j, raw25427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25427step0 = (fun i j => raw25427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25427step0 raw25427; decide +kernel
      have hl : raw25427step0Labels = raw25427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25427 raw25427Labels permutation346 hz
    mixedMoment B raw25427step0 raw25427step0Labels = mixedMoment B raw25427step1 raw25427step1Labels := by
      have ha : raw25427step1 = (fun i j => raw25427step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25427step1 raw25427step0; decide +kernel
      have hl : raw25427step1Labels = raw25427step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25427step0 raw25427step0Labels permutation38 permutation3
    mixedMoment B raw25427step1 raw25427step1Labels = mixedMoment B raw25427step2 raw25427step2Labels := by
      have ha : raw25427step2 = raw25427step1 := by apply Matrix.ext; unfold raw25427step2 raw25427step1; decide +kernel
      have hl : raw25427step1Labels = labelEmbedding6 ∘ raw25427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25427step1 raw25427step1Labels raw25427step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical25446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25446 raw25446Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw25446 raw25446Labels = mixedMoment B raw25446step0 raw25446step0Labels := by
      have hz : ∀ j, raw25446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25446step0 = (fun i j => raw25446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25446step0 raw25446; decide +kernel
      have hl : raw25446step0Labels = raw25446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25446 raw25446Labels permutation346 hz
    mixedMoment B raw25446step0 raw25446step0Labels = mixedMoment B raw25446step1 raw25446step1Labels := by
      have ha : raw25446step1 = (fun i j => raw25446step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25446step1 raw25446step0; decide +kernel
      have hl : raw25446step1Labels = raw25446step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25446step0 raw25446step0Labels permutation32 permutation3
    mixedMoment B raw25446step1 raw25446step1Labels = mixedMoment B raw25446step2 raw25446step2Labels := by
      have ha : raw25446step2 = raw25446step1 := by apply Matrix.ext; unfold raw25446step2 raw25446step1; decide +kernel
      have hl : raw25446step1Labels = labelEmbedding6 ∘ raw25446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25446step1 raw25446step1Labels raw25446step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4343 node4343Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28885 raw28885Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw28885 raw28885Labels = mixedMoment B raw28885step0 raw28885step0Labels := by
      have hz : ∀ j, raw28885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28885step0 = (fun i j => raw28885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28885step0 raw28885; decide +kernel
      have hl : raw28885step0Labels = raw28885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28885 raw28885Labels permutation346 hz
    mixedMoment B raw28885step0 raw28885step0Labels = mixedMoment B raw28885step1 raw28885step1Labels := by
      have ha : raw28885step1 = (fun i j => raw28885step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28885step1 raw28885step0; decide +kernel
      have hl : raw28885step1Labels = raw28885step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28885step0 raw28885step0Labels permutation150 permutation3
    mixedMoment B raw28885step1 raw28885step1Labels = mixedMoment B raw28885step2 raw28885step2Labels := by
      have ha : raw28885step2 = -raw28885step1 := by apply Matrix.ext; change ∀ i j, raw28885step2 i j = -(raw28885step1 i j); unfold raw28885step2 raw28885step1; decide +kernel
      have hl : raw28885step2Labels = raw28885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28885step2 raw28885step2Labels = mixedMoment B raw28885step3 raw28885step3Labels := by
      have ha : raw28885step3 = raw28885step2 := by apply Matrix.ext; unfold raw28885step3 raw28885step2; decide +kernel
      have hl : raw28885step2Labels = labelEmbedding6 ∘ raw28885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28885step2 raw28885step2Labels raw28885step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical28886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28886 raw28886Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw28886 raw28886Labels = mixedMoment B raw28886step0 raw28886step0Labels := by
      have ha : raw28886step0 = (fun i j => raw28886 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28886step0 raw28886; decide +kernel
      have hl : raw28886step0Labels = raw28886Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28886 raw28886Labels permutation686 permutation3
    mixedMoment B raw28886step0 raw28886step0Labels = mixedMoment B raw28886step1 raw28886step1Labels := by
      have ha : raw28886step1 = -raw28886step0 := by apply Matrix.ext; change ∀ i j, raw28886step1 i j = -(raw28886step0 i j); unfold raw28886step1 raw28886step0; decide +kernel
      have hl : raw28886step1Labels = raw28886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28886step1 raw28886step1Labels = mixedMoment B raw28886step2 raw28886step2Labels := by
      have ha : raw28886step2 = raw28886step1 := by apply Matrix.ext; unfold raw28886step2 raw28886step1; decide +kernel
      have hl : raw28886step1Labels = labelEmbedding6 ∘ raw28886step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28886step1 raw28886step1Labels raw28886step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical28887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28887 raw28887Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw28887 raw28887Labels = mixedMoment B raw28887step0 raw28887step0Labels := by
      have hz : ∀ j, raw28887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28887step0 = (fun i j => raw28887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28887step0 raw28887; decide +kernel
      have hl : raw28887step0Labels = raw28887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28887 raw28887Labels permutation346 hz
    mixedMoment B raw28887step0 raw28887step0Labels = mixedMoment B raw28887step1 raw28887step1Labels := by
      have ha : raw28887step1 = (fun i j => raw28887step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28887step1 raw28887step0; decide +kernel
      have hl : raw28887step1Labels = raw28887step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28887step0 raw28887step0Labels permutation149 permutation3
    mixedMoment B raw28887step1 raw28887step1Labels = mixedMoment B raw28887step2 raw28887step2Labels := by
      have ha : raw28887step2 = -raw28887step1 := by apply Matrix.ext; change ∀ i j, raw28887step2 i j = -(raw28887step1 i j); unfold raw28887step2 raw28887step1; decide +kernel
      have hl : raw28887step2Labels = raw28887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28887step2 raw28887step2Labels = mixedMoment B raw28887step3 raw28887step3Labels := by
      have ha : raw28887step3 = raw28887step2 := by apply Matrix.ext; unfold raw28887step3 raw28887step2; decide +kernel
      have hl : raw28887step2Labels = labelEmbedding6 ∘ raw28887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28887step2 raw28887step2Labels raw28887step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical28888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28888 raw28888Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw28888 raw28888Labels = mixedMoment B raw28888step0 raw28888step0Labels := by
      have hz : ∀ j, raw28888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28888step0 = (fun i j => raw28888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28888step0 raw28888; decide +kernel
      have hl : raw28888step0Labels = raw28888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28888 raw28888Labels permutation346 hz
    mixedMoment B raw28888step0 raw28888step0Labels = mixedMoment B raw28888step1 raw28888step1Labels := by
      have ha : raw28888step1 = (fun i j => raw28888step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28888step1 raw28888step0; decide +kernel
      have hl : raw28888step1Labels = raw28888step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28888step0 raw28888step0Labels permutation145 permutation3
    mixedMoment B raw28888step1 raw28888step1Labels = mixedMoment B raw28888step2 raw28888step2Labels := by
      have ha : raw28888step2 = -raw28888step1 := by apply Matrix.ext; change ∀ i j, raw28888step2 i j = -(raw28888step1 i j); unfold raw28888step2 raw28888step1; decide +kernel
      have hl : raw28888step2Labels = raw28888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28888step2 raw28888step2Labels = mixedMoment B raw28888step3 raw28888step3Labels := by
      have ha : raw28888step3 = raw28888step2 := by apply Matrix.ext; unfold raw28888step3 raw28888step2; decide +kernel
      have hl : raw28888step2Labels = labelEmbedding6 ∘ raw28888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28888step2 raw28888step2Labels raw28888step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical28889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28889 raw28889Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw28889 raw28889Labels = mixedMoment B raw28889step0 raw28889step0Labels := by
      have ha : raw28889step0 = (fun i j => raw28889 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28889step0 raw28889; decide +kernel
      have hl : raw28889step0Labels = raw28889Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28889 raw28889Labels permutation160 permutation3
    mixedMoment B raw28889step0 raw28889step0Labels = mixedMoment B raw28889step1 raw28889step1Labels := by
      have ha : raw28889step1 = raw28889step0 := by apply Matrix.ext; unfold raw28889step1 raw28889step0; decide +kernel
      have hl : raw28889step0Labels = labelEmbedding6 ∘ raw28889step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28889step0 raw28889step0Labels raw28889step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4320 node4320Labels := by rfl

theorem canonical28890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28890 raw28890Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw28890 raw28890Labels = mixedMoment B raw28890step0 raw28890step0Labels := by
      have ha : raw28890step0 = (fun i j => raw28890 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28890step0 raw28890; decide +kernel
      have hl : raw28890step0Labels = raw28890Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28890 raw28890Labels permutation646 permutation3
    mixedMoment B raw28890step0 raw28890step0Labels = mixedMoment B raw28890step1 raw28890step1Labels := by
      have ha : raw28890step1 = -raw28890step0 := by apply Matrix.ext; change ∀ i j, raw28890step1 i j = -(raw28890step0 i j); unfold raw28890step1 raw28890step0; decide +kernel
      have hl : raw28890step1Labels = raw28890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28890step1 raw28890step1Labels = mixedMoment B raw28890step2 raw28890step2Labels := by
      have ha : raw28890step2 = raw28890step1 := by apply Matrix.ext; unfold raw28890step2 raw28890step1; decide +kernel
      have hl : raw28890step1Labels = labelEmbedding6 ∘ raw28890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28890step1 raw28890step1Labels raw28890step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

theorem canonical28891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28891 raw28891Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw28891 raw28891Labels = mixedMoment B raw28891step0 raw28891step0Labels := by
      have ha : raw28891step0 = (fun i j => raw28891 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28891step0 raw28891; decide +kernel
      have hl : raw28891step0Labels = raw28891Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28891 raw28891Labels permutation644 permutation3
    mixedMoment B raw28891step0 raw28891step0Labels = mixedMoment B raw28891step1 raw28891step1Labels := by
      have ha : raw28891step1 = -raw28891step0 := by apply Matrix.ext; change ∀ i j, raw28891step1 i j = -(raw28891step0 i j); unfold raw28891step1 raw28891step0; decide +kernel
      have hl : raw28891step1Labels = raw28891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28891step1 raw28891step1Labels = mixedMoment B raw28891step2 raw28891step2Labels := by
      have ha : raw28891step2 = raw28891step1 := by apply Matrix.ext; unfold raw28891step2 raw28891step1; decide +kernel
      have hl : raw28891step1Labels = labelEmbedding6 ∘ raw28891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28891step1 raw28891step1Labels raw28891step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

theorem canonical28892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28892 raw28892Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw28892 raw28892Labels = mixedMoment B raw28892step0 raw28892step0Labels := by
      have ha : raw28892step0 = (fun i j => raw28892 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28892step0 raw28892; decide +kernel
      have hl : raw28892step0Labels = raw28892Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28892 raw28892Labels permutation640 permutation3
    mixedMoment B raw28892step0 raw28892step0Labels = mixedMoment B raw28892step1 raw28892step1Labels := by
      have ha : raw28892step1 = -raw28892step0 := by apply Matrix.ext; change ∀ i j, raw28892step1 i j = -(raw28892step0 i j); unfold raw28892step1 raw28892step0; decide +kernel
      have hl : raw28892step1Labels = raw28892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28892step1 raw28892step1Labels = mixedMoment B raw28892step2 raw28892step2Labels := by
      have ha : raw28892step2 = raw28892step1 := by apply Matrix.ext; unfold raw28892step2 raw28892step1; decide +kernel
      have hl : raw28892step1Labels = labelEmbedding6 ∘ raw28892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28892step1 raw28892step1Labels raw28892step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

theorem canonical28893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28893 raw28893Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw28893 raw28893Labels = mixedMoment B raw28893step0 raw28893step0Labels := by
      have hz : ∀ j, raw28893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28893step0 = (fun i j => raw28893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28893step0 raw28893; decide +kernel
      have hl : raw28893step0Labels = raw28893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28893 raw28893Labels permutation346 hz
    mixedMoment B raw28893step0 raw28893step0Labels = mixedMoment B raw28893step1 raw28893step1Labels := by
      have ha : raw28893step1 = (fun i j => raw28893step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28893step1 raw28893step0; decide +kernel
      have hl : raw28893step1Labels = raw28893step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28893step0 raw28893step0Labels permutation145 permutation3
    mixedMoment B raw28893step1 raw28893step1Labels = mixedMoment B raw28893step2 raw28893step2Labels := by
      have ha : raw28893step2 = -raw28893step1 := by apply Matrix.ext; change ∀ i j, raw28893step2 i j = -(raw28893step1 i j); unfold raw28893step2 raw28893step1; decide +kernel
      have hl : raw28893step2Labels = raw28893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28893step2 raw28893step2Labels = mixedMoment B raw28893step3 raw28893step3Labels := by
      have ha : raw28893step3 = raw28893step2 := by apply Matrix.ext; unfold raw28893step3 raw28893step2; decide +kernel
      have hl : raw28893step2Labels = labelEmbedding6 ∘ raw28893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28893step2 raw28893step2Labels raw28893step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical28894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28894 raw28894Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw28894 raw28894Labels = mixedMoment B raw28894step0 raw28894step0Labels := by
      have ha : raw28894step0 = (fun i j => raw28894 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28894step0 raw28894; decide +kernel
      have hl : raw28894step0Labels = raw28894Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28894 raw28894Labels permutation662 permutation3
    mixedMoment B raw28894step0 raw28894step0Labels = mixedMoment B raw28894step1 raw28894step1Labels := by
      have ha : raw28894step1 = -raw28894step0 := by apply Matrix.ext; change ∀ i j, raw28894step1 i j = -(raw28894step0 i j); unfold raw28894step1 raw28894step0; decide +kernel
      have hl : raw28894step1Labels = raw28894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28894step1 raw28894step1Labels = mixedMoment B raw28894step2 raw28894step2Labels := by
      have ha : raw28894step2 = raw28894step1 := by apply Matrix.ext; unfold raw28894step2 raw28894step1; decide +kernel
      have hl : raw28894step1Labels = labelEmbedding6 ∘ raw28894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28894step1 raw28894step1Labels raw28894step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical28895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28895 raw28895Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw28895 raw28895Labels = mixedMoment B raw28895step0 raw28895step0Labels := by
      have hz : ∀ j, raw28895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28895step0 = (fun i j => raw28895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28895step0 raw28895; decide +kernel
      have hl : raw28895step0Labels = raw28895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28895 raw28895Labels permutation346 hz
    mixedMoment B raw28895step0 raw28895step0Labels = mixedMoment B raw28895step1 raw28895step1Labels := by
      have ha : raw28895step1 = (fun i j => raw28895step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28895step1 raw28895step0; decide +kernel
      have hl : raw28895step1Labels = raw28895step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28895step0 raw28895step0Labels permutation145 permutation3
    mixedMoment B raw28895step1 raw28895step1Labels = mixedMoment B raw28895step2 raw28895step2Labels := by
      have ha : raw28895step2 = -raw28895step1 := by apply Matrix.ext; change ∀ i j, raw28895step2 i j = -(raw28895step1 i j); unfold raw28895step2 raw28895step1; decide +kernel
      have hl : raw28895step2Labels = raw28895step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28895step2 raw28895step2Labels = mixedMoment B raw28895step3 raw28895step3Labels := by
      have ha : raw28895step3 = raw28895step2 := by apply Matrix.ext; unfold raw28895step3 raw28895step2; decide +kernel
      have hl : raw28895step2Labels = labelEmbedding6 ∘ raw28895step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28895step2 raw28895step2Labels raw28895step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical28896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28896 raw28896Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw28896 raw28896Labels = mixedMoment B raw28896step0 raw28896step0Labels := by
      have hz : ∀ j, raw28896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28896step0 = (fun i j => raw28896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28896step0 raw28896; decide +kernel
      have hl : raw28896step0Labels = raw28896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28896 raw28896Labels permutation346 hz
    mixedMoment B raw28896step0 raw28896step0Labels = mixedMoment B raw28896step1 raw28896step1Labels := by
      have ha : raw28896step1 = (fun i j => raw28896step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28896step1 raw28896step0; decide +kernel
      have hl : raw28896step1Labels = raw28896step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28896step0 raw28896step0Labels permutation32 permutation3
    mixedMoment B raw28896step1 raw28896step1Labels = mixedMoment B raw28896step2 raw28896step2Labels := by
      have ha : raw28896step2 = raw28896step1 := by apply Matrix.ext; unfold raw28896step2 raw28896step1; decide +kernel
      have hl : raw28896step1Labels = labelEmbedding6 ∘ raw28896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28896step1 raw28896step1Labels raw28896step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4324 node4324Labels := by rfl

theorem canonical28897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28897 raw28897Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw28897 raw28897Labels = mixedMoment B raw28897step0 raw28897step0Labels := by
      have hz : ∀ j, raw28897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28897step0 = (fun i j => raw28897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28897step0 raw28897; decide +kernel
      have hl : raw28897step0Labels = raw28897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28897 raw28897Labels permutation346 hz
    mixedMoment B raw28897step0 raw28897step0Labels = mixedMoment B raw28897step1 raw28897step1Labels := by
      have ha : raw28897step1 = (fun i j => raw28897step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28897step1 raw28897step0; decide +kernel
      have hl : raw28897step1Labels = raw28897step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28897step0 raw28897step0Labels permutation151 permutation3
    mixedMoment B raw28897step1 raw28897step1Labels = mixedMoment B raw28897step2 raw28897step2Labels := by
      have ha : raw28897step2 = -raw28897step1 := by apply Matrix.ext; change ∀ i j, raw28897step2 i j = -(raw28897step1 i j); unfold raw28897step2 raw28897step1; decide +kernel
      have hl : raw28897step2Labels = raw28897step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28897step2 raw28897step2Labels = mixedMoment B raw28897step3 raw28897step3Labels := by
      have ha : raw28897step3 = raw28897step2 := by apply Matrix.ext; unfold raw28897step3 raw28897step2; decide +kernel
      have hl : raw28897step2Labels = labelEmbedding6 ∘ raw28897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28897step2 raw28897step2Labels raw28897step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical28898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28898 raw28898Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw28898 raw28898Labels = mixedMoment B raw28898step0 raw28898step0Labels := by
      have ha : raw28898step0 = (fun i j => raw28898 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28898step0 raw28898; decide +kernel
      have hl : raw28898step0Labels = raw28898Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28898 raw28898Labels permutation686 permutation3
    mixedMoment B raw28898step0 raw28898step0Labels = mixedMoment B raw28898step1 raw28898step1Labels := by
      have ha : raw28898step1 = -raw28898step0 := by apply Matrix.ext; change ∀ i j, raw28898step1 i j = -(raw28898step0 i j); unfold raw28898step1 raw28898step0; decide +kernel
      have hl : raw28898step1Labels = raw28898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28898step1 raw28898step1Labels = mixedMoment B raw28898step2 raw28898step2Labels := by
      have ha : raw28898step2 = raw28898step1 := by apply Matrix.ext; unfold raw28898step2 raw28898step1; decide +kernel
      have hl : raw28898step1Labels = labelEmbedding6 ∘ raw28898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28898step1 raw28898step1Labels raw28898step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

theorem canonical28899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28899 raw28899Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw28899 raw28899Labels = mixedMoment B raw28899step0 raw28899step0Labels := by
      have hz : ∀ j, raw28899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28899step0 = (fun i j => raw28899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28899step0 raw28899; decide +kernel
      have hl : raw28899step0Labels = raw28899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28899 raw28899Labels permutation346 hz
    mixedMoment B raw28899step0 raw28899step0Labels = mixedMoment B raw28899step1 raw28899step1Labels := by
      have ha : raw28899step1 = (fun i j => raw28899step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28899step1 raw28899step0; decide +kernel
      have hl : raw28899step1Labels = raw28899step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28899step0 raw28899step0Labels permutation149 permutation3
    mixedMoment B raw28899step1 raw28899step1Labels = mixedMoment B raw28899step2 raw28899step2Labels := by
      have ha : raw28899step2 = -raw28899step1 := by apply Matrix.ext; change ∀ i j, raw28899step2 i j = -(raw28899step1 i j); unfold raw28899step2 raw28899step1; decide +kernel
      have hl : raw28899step2Labels = raw28899step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28899step2 raw28899step2Labels = mixedMoment B raw28899step3 raw28899step3Labels := by
      have ha : raw28899step3 = raw28899step2 := by apply Matrix.ext; unfold raw28899step3 raw28899step2; decide +kernel
      have hl : raw28899step2Labels = labelEmbedding6 ∘ raw28899step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28899step2 raw28899step2Labels raw28899step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

theorem canonical28900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28900 raw28900Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw28900 raw28900Labels = mixedMoment B raw28900step0 raw28900step0Labels := by
      have hz : ∀ j, raw28900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28900step0 = (fun i j => raw28900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28900step0 raw28900; decide +kernel
      have hl : raw28900step0Labels = raw28900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28900 raw28900Labels permutation346 hz
    mixedMoment B raw28900step0 raw28900step0Labels = mixedMoment B raw28900step1 raw28900step1Labels := by
      have ha : raw28900step1 = (fun i j => raw28900step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28900step1 raw28900step0; decide +kernel
      have hl : raw28900step1Labels = raw28900step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28900step0 raw28900step0Labels permutation151 permutation3
    mixedMoment B raw28900step1 raw28900step1Labels = mixedMoment B raw28900step2 raw28900step2Labels := by
      have ha : raw28900step2 = -raw28900step1 := by apply Matrix.ext; change ∀ i j, raw28900step2 i j = -(raw28900step1 i j); unfold raw28900step2 raw28900step1; decide +kernel
      have hl : raw28900step2Labels = raw28900step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28900step2 raw28900step2Labels = mixedMoment B raw28900step3 raw28900step3Labels := by
      have ha : raw28900step3 = raw28900step2 := by apply Matrix.ext; unfold raw28900step3 raw28900step2; decide +kernel
      have hl : raw28900step2Labels = labelEmbedding6 ∘ raw28900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28900step2 raw28900step2Labels raw28900step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4198 node4198Labels := by rfl

theorem canonical28901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28901 raw28901Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw28901 raw28901Labels = mixedMoment B raw28901step0 raw28901step0Labels := by
      have hz : ∀ j, raw28901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28901step0 = (fun i j => raw28901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28901step0 raw28901; decide +kernel
      have hl : raw28901step0Labels = raw28901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28901 raw28901Labels permutation346 hz
    mixedMoment B raw28901step0 raw28901step0Labels = mixedMoment B raw28901step1 raw28901step1Labels := by
      have ha : raw28901step1 = (fun i j => raw28901step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28901step1 raw28901step0; decide +kernel
      have hl : raw28901step1Labels = raw28901step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28901step0 raw28901step0Labels permutation151 permutation3
    mixedMoment B raw28901step1 raw28901step1Labels = mixedMoment B raw28901step2 raw28901step2Labels := by
      have ha : raw28901step2 = -raw28901step1 := by apply Matrix.ext; change ∀ i j, raw28901step2 i j = -(raw28901step1 i j); unfold raw28901step2 raw28901step1; decide +kernel
      have hl : raw28901step2Labels = raw28901step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28901step2 raw28901step2Labels = mixedMoment B raw28901step3 raw28901step3Labels := by
      have ha : raw28901step3 = raw28901step2 := by apply Matrix.ext; unfold raw28901step3 raw28901step2; decide +kernel
      have hl : raw28901step2Labels = labelEmbedding6 ∘ raw28901step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28901step2 raw28901step2Labels raw28901step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical28902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28902 raw28902Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw28902 raw28902Labels = mixedMoment B raw28902step0 raw28902step0Labels := by
      have ha : raw28902step0 = (fun i j => raw28902 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28902step0 raw28902; decide +kernel
      have hl : raw28902step0Labels = raw28902Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28902 raw28902Labels permutation686 permutation3
    mixedMoment B raw28902step0 raw28902step0Labels = mixedMoment B raw28902step1 raw28902step1Labels := by
      have ha : raw28902step1 = -raw28902step0 := by apply Matrix.ext; change ∀ i j, raw28902step1 i j = -(raw28902step0 i j); unfold raw28902step1 raw28902step0; decide +kernel
      have hl : raw28902step1Labels = raw28902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28902step1 raw28902step1Labels = mixedMoment B raw28902step2 raw28902step2Labels := by
      have ha : raw28902step2 = raw28902step1 := by apply Matrix.ext; unfold raw28902step2 raw28902step1; decide +kernel
      have hl : raw28902step1Labels = labelEmbedding6 ∘ raw28902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28902step1 raw28902step1Labels raw28902step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4196 node4196Labels := by rfl

theorem canonical28903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28903 raw28903Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw28903 raw28903Labels = mixedMoment B raw28903step0 raw28903step0Labels := by
      have hz : ∀ j, raw28903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28903step0 = (fun i j => raw28903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28903step0 raw28903; decide +kernel
      have hl : raw28903step0Labels = raw28903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28903 raw28903Labels permutation346 hz
    mixedMoment B raw28903step0 raw28903step0Labels = mixedMoment B raw28903step1 raw28903step1Labels := by
      have ha : raw28903step1 = (fun i j => raw28903step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28903step1 raw28903step0; decide +kernel
      have hl : raw28903step1Labels = raw28903step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28903step0 raw28903step0Labels permutation149 permutation3
    mixedMoment B raw28903step1 raw28903step1Labels = mixedMoment B raw28903step2 raw28903step2Labels := by
      have ha : raw28903step2 = -raw28903step1 := by apply Matrix.ext; change ∀ i j, raw28903step2 i j = -(raw28903step1 i j); unfold raw28903step2 raw28903step1; decide +kernel
      have hl : raw28903step2Labels = raw28903step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28903step2 raw28903step2Labels = mixedMoment B raw28903step3 raw28903step3Labels := by
      have ha : raw28903step3 = raw28903step2 := by apply Matrix.ext; unfold raw28903step3 raw28903step2; decide +kernel
      have hl : raw28903step2Labels = labelEmbedding6 ∘ raw28903step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28903step2 raw28903step2Labels raw28903step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

theorem canonical28904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28904 raw28904Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw28904 raw28904Labels = mixedMoment B raw28904step0 raw28904step0Labels := by
      have hz : ∀ j, raw28904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28904step0 = (fun i j => raw28904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28904step0 raw28904; decide +kernel
      have hl : raw28904step0Labels = raw28904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28904 raw28904Labels permutation346 hz
    mixedMoment B raw28904step0 raw28904step0Labels = mixedMoment B raw28904step1 raw28904step1Labels := by
      have ha : raw28904step1 = (fun i j => raw28904step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28904step1 raw28904step0; decide +kernel
      have hl : raw28904step1Labels = raw28904step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28904step0 raw28904step0Labels permutation145 permutation3
    mixedMoment B raw28904step1 raw28904step1Labels = mixedMoment B raw28904step2 raw28904step2Labels := by
      have ha : raw28904step2 = -raw28904step1 := by apply Matrix.ext; change ∀ i j, raw28904step2 i j = -(raw28904step1 i j); unfold raw28904step2 raw28904step1; decide +kernel
      have hl : raw28904step2Labels = raw28904step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28904step2 raw28904step2Labels = mixedMoment B raw28904step3 raw28904step3Labels := by
      have ha : raw28904step3 = raw28904step2 := by apply Matrix.ext; unfold raw28904step3 raw28904step2; decide +kernel
      have hl : raw28904step2Labels = labelEmbedding6 ∘ raw28904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28904step2 raw28904step2Labels raw28904step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

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

theorem canonical852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw852 raw852Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw852 raw852Labels = mixedMoment B raw852step0 raw852step0Labels := by
      have ha : raw852step0 = (fun i j => raw852 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw852step0 raw852; decide +kernel
      have hl : raw852step0Labels = raw852Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw852 raw852Labels permutation152 permutation4
    mixedMoment B raw852step0 raw852step0Labels = mixedMoment B raw852step1 raw852step1Labels := by
      have ha : raw852step1 = raw852step0 := by apply Matrix.ext; unfold raw852step1 raw852step0; decide +kernel
      have hl : raw852step0Labels = labelEmbedding7 ∘ raw852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw852step0 raw852step0Labels raw852step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4196 node4196Labels := by rfl

theorem canonical853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw853 raw853Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw853 raw853Labels = mixedMoment B raw853step0 raw853step0Labels := by
      have ha : raw853step0 = (fun i j => raw853 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw853step0 raw853; decide +kernel
      have hl : raw853step0Labels = raw853Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw853 raw853Labels permutation152 permutation4
    _ = mixedMoment B node699 node699Labels := by rfl

theorem canonical854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw854 raw854Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw854 raw854Labels = mixedMoment B raw854step0 raw854step0Labels := by
      have ha : raw854step0 = (fun i j => raw854 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw854step0 raw854; decide +kernel
      have hl : raw854step0Labels = raw854Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw854 raw854Labels permutation158 permutation6
    mixedMoment B raw854step0 raw854step0Labels = mixedMoment B raw854step1 raw854step1Labels := by
      have ha : raw854step1 = -raw854step0 := by apply Matrix.ext; change ∀ i j, raw854step1 i j = -(raw854step0 i j); unfold raw854step1 raw854step0; decide +kernel
      have hl : raw854step1Labels = raw854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw854step1 raw854step1Labels = mixedMoment B raw854step2 raw854step2Labels := by
      have ha : raw854step2 = raw854step1 := by apply Matrix.ext; unfold raw854step2 raw854step1; decide +kernel
      have hl : raw854step1Labels = labelEmbedding1 ∘ raw854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw854step1 raw854step1Labels raw854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node748 node748Labels := by rfl

theorem canonical858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw858 raw858Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw858 raw858Labels = mixedMoment B raw858step0 raw858step0Labels := by
      have ha : raw858step0 = (fun i j => raw858 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw858step0 raw858; decide +kernel
      have hl : raw858step0Labels = raw858Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw858 raw858Labels permutation32 permutation4
    mixedMoment B raw858step0 raw858step0Labels = mixedMoment B raw858step1 raw858step1Labels := by
      have ha : raw858step1 = raw858step0 := by apply Matrix.ext; unfold raw858step1 raw858step0; decide +kernel
      have hl : raw858step0Labels = labelEmbedding7 ∘ raw858step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw858step0 raw858step0Labels raw858step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4198 node4198Labels := by rfl

theorem canonical859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw859 raw859Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw859 raw859Labels = mixedMoment B raw859step0 raw859step0Labels := by
      have ha : raw859step0 = (fun i j => raw859 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw859step0 raw859; decide +kernel
      have hl : raw859step0Labels = raw859Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw859 raw859Labels permutation32 permutation4
    _ = mixedMoment B node701 node701Labels := by rfl

theorem canonical860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw860 raw860Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw860 raw860Labels = mixedMoment B raw860step0 raw860step0Labels := by
      have ha : raw860step0 = (fun i j => raw860 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw860step0 raw860; decide +kernel
      have hl : raw860step0Labels = raw860Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw860 raw860Labels permutation34 permutation6
    mixedMoment B raw860step0 raw860step0Labels = mixedMoment B raw860step1 raw860step1Labels := by
      have ha : raw860step1 = -raw860step0 := by apply Matrix.ext; change ∀ i j, raw860step1 i j = -(raw860step0 i j); unfold raw860step1 raw860step0; decide +kernel
      have hl : raw860step1Labels = raw860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw860step1 raw860step1Labels = mixedMoment B raw860step2 raw860step2Labels := by
      have ha : raw860step2 = raw860step1 := by apply Matrix.ext; unfold raw860step2 raw860step1; decide +kernel
      have hl : raw860step1Labels = labelEmbedding1 ∘ raw860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw860step1 raw860step1Labels raw860step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

theorem canonical876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw876 raw876Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw876 raw876Labels = mixedMoment B raw876step0 raw876step0Labels := by
      have ha : raw876step0 = (fun i j => raw876 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw876step0 raw876; decide +kernel
      have hl : raw876step0Labels = raw876Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw876 raw876Labels permutation32 permutation4
    mixedMoment B raw876step0 raw876step0Labels = mixedMoment B raw876step1 raw876step1Labels := by
      have ha : raw876step1 = raw876step0 := by apply Matrix.ext; unfold raw876step1 raw876step0; decide +kernel
      have hl : raw876step0Labels = labelEmbedding7 ∘ raw876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw876step0 raw876step0Labels raw876step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw877 raw877Labels = mixedMoment B node707 node707Labels := by
  calc
    mixedMoment B raw877 raw877Labels = mixedMoment B raw877step0 raw877step0Labels := by
      have ha : raw877step0 = (fun i j => raw877 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw877step0 raw877; decide +kernel
      have hl : raw877step0Labels = raw877Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw877 raw877Labels permutation32 permutation4
    _ = mixedMoment B node707 node707Labels := by rfl

theorem canonical878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw878 raw878Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw878 raw878Labels = mixedMoment B raw878step0 raw878step0Labels := by
      have ha : raw878step0 = (fun i j => raw878 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw878step0 raw878; decide +kernel
      have hl : raw878step0Labels = raw878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw878 raw878Labels permutation32 permutation6
    mixedMoment B raw878step0 raw878step0Labels = mixedMoment B raw878step1 raw878step1Labels := by
      have ha : raw878step1 = -raw878step0 := by apply Matrix.ext; change ∀ i j, raw878step1 i j = -(raw878step0 i j); unfold raw878step1 raw878step0; decide +kernel
      have hl : raw878step1Labels = raw878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw878step1 raw878step1Labels = mixedMoment B raw878step2 raw878step2Labels := by
      have ha : raw878step2 = raw878step1 := by apply Matrix.ext; unfold raw878step2 raw878step1; decide +kernel
      have hl : raw878step1Labels = labelEmbedding1 ∘ raw878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw878step1 raw878step1Labels raw878step2Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

theorem canonical894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw894 raw894Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw894 raw894Labels = mixedMoment B raw894step0 raw894step0Labels := by
      have ha : raw894step0 = (fun i j => raw894 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw894step0 raw894; decide +kernel
      have hl : raw894step0Labels = raw894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw894 raw894Labels permutation32 permutation4
    mixedMoment B raw894step0 raw894step0Labels = mixedMoment B raw894step1 raw894step1Labels := by
      have ha : raw894step1 = raw894step0 := by apply Matrix.ext; unfold raw894step1 raw894step0; decide +kernel
      have hl : raw894step0Labels = labelEmbedding7 ∘ raw894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw894step0 raw894step0Labels raw894step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

theorem canonical895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw895 raw895Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw895 raw895Labels = mixedMoment B raw895step0 raw895step0Labels := by
      have ha : raw895step0 = (fun i j => raw895 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw895step0 raw895; decide +kernel
      have hl : raw895step0Labels = raw895Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw895 raw895Labels permutation32 permutation4
    _ = mixedMoment B node715 node715Labels := by rfl

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

theorem canonical896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw896 raw896Labels = mixedMoment B node753 node753Labels := by
  calc
    mixedMoment B raw896 raw896Labels = mixedMoment B raw896step0 raw896step0Labels := by
      have ha : raw896step0 = (fun i j => raw896 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw896step0 raw896; decide +kernel
      have hl : raw896step0Labels = raw896Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw896 raw896Labels permutation32 permutation6
    mixedMoment B raw896step0 raw896step0Labels = mixedMoment B raw896step1 raw896step1Labels := by
      have ha : raw896step1 = -raw896step0 := by apply Matrix.ext; change ∀ i j, raw896step1 i j = -(raw896step0 i j); unfold raw896step1 raw896step0; decide +kernel
      have hl : raw896step1Labels = raw896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw896step1 raw896step1Labels = mixedMoment B raw896step2 raw896step2Labels := by
      have ha : raw896step2 = raw896step1 := by apply Matrix.ext; unfold raw896step2 raw896step1; decide +kernel
      have hl : raw896step1Labels = labelEmbedding1 ∘ raw896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw896step1 raw896step1Labels raw896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node753 node753Labels := by rfl

theorem canonical972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw972 raw972Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw972 raw972Labels = mixedMoment B raw972step0 raw972step0Labels := by
      have ha : raw972step0 = (fun i j => raw972 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw972step0 raw972; decide +kernel
      have hl : raw972step0Labels = raw972Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw972 raw972Labels permutation32 permutation4
    mixedMoment B raw972step0 raw972step0Labels = mixedMoment B raw972step1 raw972step1Labels := by
      have ha : raw972step1 = raw972step0 := by apply Matrix.ext; unfold raw972step1 raw972step0; decide +kernel
      have hl : raw972step0Labels = labelEmbedding7 ∘ raw972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw972step0 raw972step0Labels raw972step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

theorem canonical973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw973 raw973Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw973 raw973Labels = mixedMoment B raw973step0 raw973step0Labels := by
      have ha : raw973step0 = (fun i j => raw973 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw973step0 raw973; decide +kernel
      have hl : raw973step0Labels = raw973Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw973 raw973Labels permutation32 permutation4
    _ = mixedMoment B node785 node785Labels := by rfl

theorem canonical974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw974 raw974Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw974 raw974Labels = mixedMoment B raw974step0 raw974step0Labels := by
      have ha : raw974step0 = (fun i j => raw974 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw974step0 raw974; decide +kernel
      have hl : raw974step0Labels = raw974Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw974 raw974Labels permutation44 permutation6
    mixedMoment B raw974step0 raw974step0Labels = mixedMoment B raw974step1 raw974step1Labels := by
      have ha : raw974step1 = -raw974step0 := by apply Matrix.ext; change ∀ i j, raw974step1 i j = -(raw974step0 i j); unfold raw974step1 raw974step0; decide +kernel
      have hl : raw974step1Labels = raw974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw974step1 raw974step1Labels = mixedMoment B raw974step2 raw974step2Labels := by
      have ha : raw974step2 = raw974step1 := by apply Matrix.ext; unfold raw974step2 raw974step1; decide +kernel
      have hl : raw974step1Labels = labelEmbedding1 ∘ raw974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw974step1 raw974step1Labels raw974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node804 node804Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10085 raw10085Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw10085 raw10085Labels = mixedMoment B raw10085step0 raw10085step0Labels := by
      have hz : ∀ j, raw10085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10085step0 = (fun i j => raw10085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10085step0 raw10085; decide +kernel
      have hl : raw10085step0Labels = raw10085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10085 raw10085Labels permutation346 hz
    mixedMoment B raw10085step0 raw10085step0Labels = mixedMoment B raw10085step1 raw10085step1Labels := by
      have ha : raw10085step1 = (fun i j => raw10085step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10085step1 raw10085step0; decide +kernel
      have hl : raw10085step1Labels = raw10085step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10085step0 raw10085step0Labels permutation151 permutation3
    mixedMoment B raw10085step1 raw10085step1Labels = mixedMoment B raw10085step2 raw10085step2Labels := by
      have ha : raw10085step2 = -raw10085step1 := by apply Matrix.ext; change ∀ i j, raw10085step2 i j = -(raw10085step1 i j); unfold raw10085step2 raw10085step1; decide +kernel
      have hl : raw10085step2Labels = raw10085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10085step2 raw10085step2Labels = mixedMoment B raw10085step3 raw10085step3Labels := by
      have ha : raw10085step3 = raw10085step2 := by apply Matrix.ext; unfold raw10085step3 raw10085step2; decide +kernel
      have hl : raw10085step2Labels = labelEmbedding6 ∘ raw10085step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10085step2 raw10085step2Labels raw10085step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical10096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10096 raw10096Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw10096 raw10096Labels = mixedMoment B raw10096step0 raw10096step0Labels := by
      have ha : raw10096step0 = (fun i j => raw10096 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10096step0 raw10096; decide +kernel
      have hl : raw10096step0Labels = raw10096Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10096 raw10096Labels permutation160 permutation3
    mixedMoment B raw10096step0 raw10096step0Labels = mixedMoment B raw10096step1 raw10096step1Labels := by
      have ha : raw10096step1 = raw10096step0 := by apply Matrix.ext; unfold raw10096step1 raw10096step0; decide +kernel
      have hl : raw10096step0Labels = labelEmbedding6 ∘ raw10096step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10096step0 raw10096step0Labels raw10096step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical10101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10101 raw10101Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10101 raw10101Labels = mixedMoment B raw10101step0 raw10101step0Labels := by
      have hz : ∀ j, raw10101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10101step0 = (fun i j => raw10101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10101step0 raw10101; decide +kernel
      have hl : raw10101step0Labels = raw10101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10101 raw10101Labels permutation346 hz
    mixedMoment B raw10101step0 raw10101step0Labels = mixedMoment B raw10101step1 raw10101step1Labels := by
      have ha : raw10101step1 = (fun i j => raw10101step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10101step1 raw10101step0; decide +kernel
      have hl : raw10101step1Labels = raw10101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10101step0 raw10101step0Labels permutation32 permutation3
    mixedMoment B raw10101step1 raw10101step1Labels = mixedMoment B raw10101step2 raw10101step2Labels := by
      have ha : raw10101step2 = raw10101step1 := by apply Matrix.ext; unfold raw10101step2 raw10101step1; decide +kernel
      have hl : raw10101step1Labels = labelEmbedding6 ∘ raw10101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10101step1 raw10101step1Labels raw10101step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

theorem canonical10106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10106 raw10106Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10106 raw10106Labels = mixedMoment B raw10106step0 raw10106step0Labels := by
      have hz : ∀ j, raw10106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10106step0 = (fun i j => raw10106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10106step0 raw10106; decide +kernel
      have hl : raw10106step0Labels = raw10106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10106 raw10106Labels permutation346 hz
    mixedMoment B raw10106step0 raw10106step0Labels = mixedMoment B raw10106step1 raw10106step1Labels := by
      have ha : raw10106step1 = (fun i j => raw10106step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10106step1 raw10106step0; decide +kernel
      have hl : raw10106step1Labels = raw10106step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10106step0 raw10106step0Labels permutation32 permutation3
    mixedMoment B raw10106step1 raw10106step1Labels = mixedMoment B raw10106step2 raw10106step2Labels := by
      have ha : raw10106step2 = raw10106step1 := by apply Matrix.ext; unfold raw10106step2 raw10106step1; decide +kernel
      have hl : raw10106step1Labels = labelEmbedding6 ∘ raw10106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10106step1 raw10106step1Labels raw10106step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical10110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10110 raw10110Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw10110 raw10110Labels = mixedMoment B raw10110step0 raw10110step0Labels := by
      have hz : ∀ j, raw10110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10110step0 = (fun i j => raw10110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10110step0 raw10110; decide +kernel
      have hl : raw10110step0Labels = raw10110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10110 raw10110Labels permutation346 hz
    mixedMoment B raw10110step0 raw10110step0Labels = mixedMoment B raw10110step1 raw10110step1Labels := by
      have ha : raw10110step1 = (fun i j => raw10110step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10110step1 raw10110step0; decide +kernel
      have hl : raw10110step1Labels = raw10110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10110step0 raw10110step0Labels permutation38 permutation3
    mixedMoment B raw10110step1 raw10110step1Labels = mixedMoment B raw10110step2 raw10110step2Labels := by
      have ha : raw10110step2 = raw10110step1 := by apply Matrix.ext; unfold raw10110step2 raw10110step1; decide +kernel
      have hl : raw10110step1Labels = labelEmbedding6 ∘ raw10110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10110step1 raw10110step1Labels raw10110step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10112 raw10112Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw10112 raw10112Labels = mixedMoment B raw10112step0 raw10112step0Labels := by
      have ha : raw10112step0 = (fun i j => raw10112 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10112step0 raw10112; decide +kernel
      have hl : raw10112step0Labels = raw10112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10112 raw10112Labels permutation676 permutation3
    mixedMoment B raw10112step0 raw10112step0Labels = mixedMoment B raw10112step1 raw10112step1Labels := by
      have ha : raw10112step1 = -raw10112step0 := by apply Matrix.ext; change ∀ i j, raw10112step1 i j = -(raw10112step0 i j); unfold raw10112step1 raw10112step0; decide +kernel
      have hl : raw10112step1Labels = raw10112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10112step1 raw10112step1Labels = mixedMoment B raw10112step2 raw10112step2Labels := by
      have ha : raw10112step2 = raw10112step1 := by apply Matrix.ext; unfold raw10112step2 raw10112step1; decide +kernel
      have hl : raw10112step1Labels = labelEmbedding6 ∘ raw10112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10112step1 raw10112step1Labels raw10112step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

theorem canonical10113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10113 raw10113Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw10113 raw10113Labels = mixedMoment B raw10113step0 raw10113step0Labels := by
      have hz : ∀ j, raw10113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10113step0 = (fun i j => raw10113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10113step0 raw10113; decide +kernel
      have hl : raw10113step0Labels = raw10113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10113 raw10113Labels permutation346 hz
    mixedMoment B raw10113step0 raw10113step0Labels = mixedMoment B raw10113step1 raw10113step1Labels := by
      have ha : raw10113step1 = (fun i j => raw10113step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10113step1 raw10113step0; decide +kernel
      have hl : raw10113step1Labels = raw10113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10113step0 raw10113step0Labels permutation149 permutation3
    mixedMoment B raw10113step1 raw10113step1Labels = mixedMoment B raw10113step2 raw10113step2Labels := by
      have ha : raw10113step2 = -raw10113step1 := by apply Matrix.ext; change ∀ i j, raw10113step2 i j = -(raw10113step1 i j); unfold raw10113step2 raw10113step1; decide +kernel
      have hl : raw10113step2Labels = raw10113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10113step2 raw10113step2Labels = mixedMoment B raw10113step3 raw10113step3Labels := by
      have ha : raw10113step3 = raw10113step2 := by apply Matrix.ext; unfold raw10113step3 raw10113step2; decide +kernel
      have hl : raw10113step2Labels = labelEmbedding6 ∘ raw10113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10113step2 raw10113step2Labels raw10113step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

theorem canonical10114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10114 raw10114Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw10114 raw10114Labels = mixedMoment B raw10114step0 raw10114step0Labels := by
      have hz : ∀ j, raw10114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10114step0 = (fun i j => raw10114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10114step0 raw10114; decide +kernel
      have hl : raw10114step0Labels = raw10114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10114 raw10114Labels permutation346 hz
    mixedMoment B raw10114step0 raw10114step0Labels = mixedMoment B raw10114step1 raw10114step1Labels := by
      have ha : raw10114step1 = (fun i j => raw10114step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10114step1 raw10114step0; decide +kernel
      have hl : raw10114step1Labels = raw10114step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10114step0 raw10114step0Labels permutation137 permutation5
    mixedMoment B raw10114step1 raw10114step1Labels = mixedMoment B raw10114step2 raw10114step2Labels := by
      have ha : raw10114step2 = raw10114step1 := by apply Matrix.ext; unfold raw10114step2 raw10114step1; decide +kernel
      have hl : raw10114step1Labels = labelEmbedding8 ∘ raw10114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10114step1 raw10114step1Labels raw10114step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

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

theorem canonical1095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1095 raw1095Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw1095 raw1095Labels = mixedMoment B raw1095step0 raw1095step0Labels := by
      have ha : raw1095step0 = (fun i j => raw1095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1095step0 raw1095; decide +kernel
      have hl : raw1095step0Labels = raw1095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1095 raw1095Labels permutation152 permutation4
    mixedMoment B raw1095step0 raw1095step0Labels = mixedMoment B raw1095step1 raw1095step1Labels := by
      have ha : raw1095step1 = raw1095step0 := by apply Matrix.ext; unfold raw1095step1 raw1095step0; decide +kernel
      have hl : raw1095step0Labels = labelEmbedding7 ∘ raw1095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1095step0 raw1095step0Labels raw1095step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4320 node4320Labels := by rfl

theorem canonical1096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1096 raw1096Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw1096 raw1096Labels = mixedMoment B raw1096step0 raw1096step0Labels := by
      have ha : raw1096step0 = (fun i j => raw1096 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1096step0 raw1096; decide +kernel
      have hl : raw1096step0Labels = raw1096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1096 raw1096Labels permutation152 permutation4
    _ = mixedMoment B node898 node898Labels := by rfl

theorem canonical1097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1097 raw1097Labels = mixedMoment B node1586 node1586Labels := by
  calc
    mixedMoment B raw1097 raw1097Labels = mixedMoment B raw1097step0 raw1097step0Labels := by
      have ha : raw1097step0 = (fun i j => raw1097 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1097step0 raw1097; decide +kernel
      have hl : raw1097step0Labels = raw1097Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1097 raw1097Labels permutation176 permutation6
    mixedMoment B raw1097step0 raw1097step0Labels = mixedMoment B raw1097step1 raw1097step1Labels := by
      have ha : raw1097step1 = -raw1097step0 := by apply Matrix.ext; change ∀ i j, raw1097step1 i j = -(raw1097step0 i j); unfold raw1097step1 raw1097step0; decide +kernel
      have hl : raw1097step1Labels = raw1097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1097step1 raw1097step1Labels = mixedMoment B raw1097step2 raw1097step2Labels := by
      have ha : raw1097step2 = raw1097step1 := by apply Matrix.ext; unfold raw1097step2 raw1097step1; decide +kernel
      have hl : raw1097step1Labels = labelEmbedding1 ∘ raw1097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1097step1 raw1097step1Labels raw1097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1586 node1586Labels := by rfl

theorem canonical1107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1107 raw1107Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw1107 raw1107Labels = mixedMoment B raw1107step0 raw1107step0Labels := by
      have ha : raw1107step0 = (fun i j => raw1107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1107step0 raw1107; decide +kernel
      have hl : raw1107step0Labels = raw1107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1107 raw1107Labels permutation32 permutation4
    mixedMoment B raw1107step0 raw1107step0Labels = mixedMoment B raw1107step1 raw1107step1Labels := by
      have ha : raw1107step1 = raw1107step0 := by apply Matrix.ext; unfold raw1107step1 raw1107step0; decide +kernel
      have hl : raw1107step0Labels = labelEmbedding7 ∘ raw1107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1107step0 raw1107step0Labels raw1107step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4324 node4324Labels := by rfl

theorem canonical1108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1108 raw1108Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw1108 raw1108Labels = mixedMoment B raw1108step0 raw1108step0Labels := by
      have ha : raw1108step0 = (fun i j => raw1108 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1108step0 raw1108; decide +kernel
      have hl : raw1108step0Labels = raw1108Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1108 raw1108Labels permutation32 permutation4
    _ = mixedMoment B node902 node902Labels := by rfl

theorem canonical1109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1109 raw1109Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw1109 raw1109Labels = mixedMoment B raw1109step0 raw1109step0Labels := by
      have ha : raw1109step0 = (fun i j => raw1109 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1109step0 raw1109; decide +kernel
      have hl : raw1109step0Labels = raw1109Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1109 raw1109Labels permutation38 permutation6
    mixedMoment B raw1109step0 raw1109step0Labels = mixedMoment B raw1109step1 raw1109step1Labels := by
      have ha : raw1109step1 = -raw1109step0 := by apply Matrix.ext; change ∀ i j, raw1109step1 i j = -(raw1109step0 i j); unfold raw1109step1 raw1109step0; decide +kernel
      have hl : raw1109step1Labels = raw1109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1109step1 raw1109step1Labels = mixedMoment B raw1109step2 raw1109step2Labels := by
      have ha : raw1109step2 = raw1109step1 := by apply Matrix.ext; unfold raw1109step2 raw1109step1; decide +kernel
      have hl : raw1109step1Labels = labelEmbedding1 ∘ raw1109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1109step1 raw1109step1Labels raw1109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

theorem canonical1125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1125 raw1125Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw1125 raw1125Labels = mixedMoment B raw1125step0 raw1125step0Labels := by
      have ha : raw1125step0 = (fun i j => raw1125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1125step0 raw1125; decide +kernel
      have hl : raw1125step0Labels = raw1125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1125 raw1125Labels permutation32 permutation4
    mixedMoment B raw1125step0 raw1125step0Labels = mixedMoment B raw1125step1 raw1125step1Labels := by
      have ha : raw1125step1 = raw1125step0 := by apply Matrix.ext; unfold raw1125step1 raw1125step0; decide +kernel
      have hl : raw1125step0Labels = labelEmbedding7 ∘ raw1125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1125step0 raw1125step0Labels raw1125step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1126 raw1126Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw1126 raw1126Labels = mixedMoment B raw1126step0 raw1126step0Labels := by
      have ha : raw1126step0 = (fun i j => raw1126 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1126step0 raw1126; decide +kernel
      have hl : raw1126step0Labels = raw1126Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1126 raw1126Labels permutation32 permutation4
    _ = mixedMoment B node921 node921Labels := by rfl

theorem canonical1127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1127 raw1127Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw1127 raw1127Labels = mixedMoment B raw1127step0 raw1127step0Labels := by
      have ha : raw1127step0 = (fun i j => raw1127 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1127step0 raw1127; decide +kernel
      have hl : raw1127step0Labels = raw1127Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1127 raw1127Labels permutation32 permutation6
    mixedMoment B raw1127step0 raw1127step0Labels = mixedMoment B raw1127step1 raw1127step1Labels := by
      have ha : raw1127step1 = -raw1127step0 := by apply Matrix.ext; change ∀ i j, raw1127step1 i j = -(raw1127step0 i j); unfold raw1127step1 raw1127step0; decide +kernel
      have hl : raw1127step1Labels = raw1127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1127step1 raw1127step1Labels = mixedMoment B raw1127step2 raw1127step2Labels := by
      have ha : raw1127step2 = raw1127step1 := by apply Matrix.ext; unfold raw1127step2 raw1127step1; decide +kernel
      have hl : raw1127step1Labels = labelEmbedding1 ∘ raw1127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1127step1 raw1127step1Labels raw1127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

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

theorem canonical1209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1209 raw1209Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw1209 raw1209Labels = mixedMoment B raw1209step0 raw1209step0Labels := by
      have ha : raw1209step0 = (fun i j => raw1209 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1209step0 raw1209; decide +kernel
      have hl : raw1209step0Labels = raw1209Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1209 raw1209Labels permutation32 permutation4
    mixedMoment B raw1209step0 raw1209step0Labels = mixedMoment B raw1209step1 raw1209step1Labels := by
      have ha : raw1209step1 = raw1209step0 := by apply Matrix.ext; unfold raw1209step1 raw1209step0; decide +kernel
      have hl : raw1209step0Labels = labelEmbedding7 ∘ raw1209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1209step0 raw1209step0Labels raw1209step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

theorem canonical1210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1210 raw1210Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw1210 raw1210Labels = mixedMoment B raw1210step0 raw1210step0Labels := by
      have ha : raw1210step0 = (fun i j => raw1210 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1210step0 raw1210; decide +kernel
      have hl : raw1210step0Labels = raw1210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1210 raw1210Labels permutation32 permutation4
    _ = mixedMoment B node979 node979Labels := by rfl

theorem canonical1211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1211 raw1211Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw1211 raw1211Labels = mixedMoment B raw1211step0 raw1211step0Labels := by
      have ha : raw1211step0 = (fun i j => raw1211 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1211step0 raw1211; decide +kernel
      have hl : raw1211step0Labels = raw1211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1211 raw1211Labels permutation34 permutation6
    mixedMoment B raw1211step0 raw1211step0Labels = mixedMoment B raw1211step1 raw1211step1Labels := by
      have ha : raw1211step1 = -raw1211step0 := by apply Matrix.ext; change ∀ i j, raw1211step1 i j = -(raw1211step0 i j); unfold raw1211step1 raw1211step0; decide +kernel
      have hl : raw1211step1Labels = raw1211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1211step1 raw1211step1Labels = mixedMoment B raw1211step2 raw1211step2Labels := by
      have ha : raw1211step2 = raw1211step1 := by apply Matrix.ext; unfold raw1211step2 raw1211step1; decide +kernel
      have hl : raw1211step1Labels = labelEmbedding1 ∘ raw1211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1211step1 raw1211step1Labels raw1211step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

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

theorem singleton4196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4196 node4196Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node699 node699Labels + mixedMoment B node748 node748Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw852 singletonSmall4196
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4196) = raw852Labels := by decide +kernel
  rw [hl, canonical852 B hB] at h
  have hc0 : mixedMoment B raw852 (Fin.cases (0 : Fin 2) singletonSmall4196) =
      mixedMoment B node699 node699Labels := by
    have ha : raw852 = raw853 := by apply Matrix.ext; unfold raw852 raw853; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4196 = raw853Labels := by decide +kernel
    rw [ha, hj, canonical853 B hB]
  have hc1 : mixedMoment B raw852 (Fin.cases (1 : Fin 2) singletonSmall4196) =
      mixedMoment B node748 node748Labels := by
    have ha : raw852 = raw854 := by apply Matrix.ext; unfold raw852 raw854; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4196 = raw854Labels := by decide +kernel
    rw [ha, hj, canonical854 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4198 node4198Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node701 node701Labels + mixedMoment B node750 node750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw858 singletonSmall4198
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4198) = raw858Labels := by decide +kernel
  rw [hl, canonical858 B hB] at h
  have hc0 : mixedMoment B raw858 (Fin.cases (0 : Fin 2) singletonSmall4198) =
      mixedMoment B node701 node701Labels := by
    have ha : raw858 = raw859 := by apply Matrix.ext; unfold raw858 raw859; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4198 = raw859Labels := by decide +kernel
    rw [ha, hj, canonical859 B hB]
  have hc1 : mixedMoment B raw858 (Fin.cases (1 : Fin 2) singletonSmall4198) =
      mixedMoment B node750 node750Labels := by
    have ha : raw858 = raw860 := by apply Matrix.ext; unfold raw858 raw860; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4198 = raw860Labels := by decide +kernel
    rw [ha, hj, canonical860 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4204 node4204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node707 node707Labels + mixedMoment B node763 node763Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw876 singletonSmall4204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4204) = raw876Labels := by decide +kernel
  rw [hl, canonical876 B hB] at h
  have hc0 : mixedMoment B raw876 (Fin.cases (0 : Fin 2) singletonSmall4204) =
      mixedMoment B node707 node707Labels := by
    have ha : raw876 = raw877 := by apply Matrix.ext; unfold raw876 raw877; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4204 = raw877Labels := by decide +kernel
    rw [ha, hj, canonical877 B hB]
  have hc1 : mixedMoment B raw876 (Fin.cases (1 : Fin 2) singletonSmall4204) =
      mixedMoment B node763 node763Labels := by
    have ha : raw876 = raw878 := by apply Matrix.ext; unfold raw876 raw878; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4204 = raw878Labels := by decide +kernel
    rw [ha, hj, canonical878 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4212 node4212Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node715 node715Labels + mixedMoment B node753 node753Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw894 singletonSmall4212
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4212) = raw894Labels := by decide +kernel
  rw [hl, canonical894 B hB] at h
  have hc0 : mixedMoment B raw894 (Fin.cases (0 : Fin 2) singletonSmall4212) =
      mixedMoment B node715 node715Labels := by
    have ha : raw894 = raw895 := by apply Matrix.ext; unfold raw894 raw895; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4212 = raw895Labels := by decide +kernel
    rw [ha, hj, canonical895 B hB]
  have hc1 : mixedMoment B raw894 (Fin.cases (1 : Fin 2) singletonSmall4212) =
      mixedMoment B node753 node753Labels := by
    have ha : raw894 = raw896 := by apply Matrix.ext; unfold raw894 raw896; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4212 = raw896Labels := by decide +kernel
    rw [ha, hj, canonical896 B hB]
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

theorem singleton4251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4251 node4251Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node785 node785Labels + mixedMoment B node804 node804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw972 singletonSmall4251
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4251) = raw972Labels := by decide +kernel
  rw [hl, canonical972 B hB] at h
  have hc0 : mixedMoment B raw972 (Fin.cases (0 : Fin 2) singletonSmall4251) =
      mixedMoment B node785 node785Labels := by
    have ha : raw972 = raw973 := by apply Matrix.ext; unfold raw972 raw973; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4251 = raw973Labels := by decide +kernel
    rw [ha, hj, canonical973 B hB]
  have hc1 : mixedMoment B raw972 (Fin.cases (1 : Fin 2) singletonSmall4251) =
      mixedMoment B node804 node804Labels := by
    have ha : raw972 = raw974 := by apply Matrix.ext; unfold raw972 raw974; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4251 = raw974Labels := by decide +kernel
    rw [ha, hj, canonical974 B hB]
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

theorem singleton4320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4320 node4320Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node898 node898Labels + mixedMoment B node1586 node1586Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1095 singletonSmall4320
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4320) = raw1095Labels := by decide +kernel
  rw [hl, canonical1095 B hB] at h
  have hc0 : mixedMoment B raw1095 (Fin.cases (0 : Fin 2) singletonSmall4320) =
      mixedMoment B node898 node898Labels := by
    have ha : raw1095 = raw1096 := by apply Matrix.ext; unfold raw1095 raw1096; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4320 = raw1096Labels := by decide +kernel
    rw [ha, hj, canonical1096 B hB]
  have hc1 : mixedMoment B raw1095 (Fin.cases (1 : Fin 2) singletonSmall4320) =
      mixedMoment B node1586 node1586Labels := by
    have ha : raw1095 = raw1097 := by apply Matrix.ext; unfold raw1095 raw1097; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4320 = raw1097Labels := by decide +kernel
    rw [ha, hj, canonical1097 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4324 node4324Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node902 node902Labels + mixedMoment B node1590 node1590Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1107 singletonSmall4324
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4324) = raw1107Labels := by decide +kernel
  rw [hl, canonical1107 B hB] at h
  have hc0 : mixedMoment B raw1107 (Fin.cases (0 : Fin 2) singletonSmall4324) =
      mixedMoment B node902 node902Labels := by
    have ha : raw1107 = raw1108 := by apply Matrix.ext; unfold raw1107 raw1108; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4324 = raw1108Labels := by decide +kernel
    rw [ha, hj, canonical1108 B hB]
  have hc1 : mixedMoment B raw1107 (Fin.cases (1 : Fin 2) singletonSmall4324) =
      mixedMoment B node1590 node1590Labels := by
    have ha : raw1107 = raw1109 := by apply Matrix.ext; unfold raw1107 raw1109; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4324 = raw1109Labels := by decide +kernel
    rw [ha, hj, canonical1109 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4343 node4343Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node921 node921Labels + mixedMoment B node1666 node1666Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1125 singletonSmall4343
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4343) = raw1125Labels := by decide +kernel
  rw [hl, canonical1125 B hB] at h
  have hc0 : mixedMoment B raw1125 (Fin.cases (0 : Fin 2) singletonSmall4343) =
      mixedMoment B node921 node921Labels := by
    have ha : raw1125 = raw1126 := by apply Matrix.ext; unfold raw1125 raw1126; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4343 = raw1126Labels := by decide +kernel
    rw [ha, hj, canonical1126 B hB]
  have hc1 : mixedMoment B raw1125 (Fin.cases (1 : Fin 2) singletonSmall4343) =
      mixedMoment B node1666 node1666Labels := by
    have ha : raw1125 = raw1127 := by apply Matrix.ext; unfold raw1125 raw1127; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4343 = raw1127Labels := by decide +kernel
    rw [ha, hj, canonical1127 B hB]
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

theorem singleton4398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4398 node4398Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node979 node979Labels + mixedMoment B node1599 node1599Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1209 singletonSmall4398
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4398) = raw1209Labels := by decide +kernel
  rw [hl, canonical1209 B hB] at h
  have hc0 : mixedMoment B raw1209 (Fin.cases (0 : Fin 2) singletonSmall4398) =
      mixedMoment B node979 node979Labels := by
    have ha : raw1209 = raw1210 := by apply Matrix.ext; unfold raw1209 raw1210; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4398 = raw1210Labels := by decide +kernel
    rw [ha, hj, canonical1210 B hB]
  have hc1 : mixedMoment B raw1209 (Fin.cases (1 : Fin 2) singletonSmall4398) =
      mixedMoment B node1599 node1599Labels := by
    have ha : raw1209 = raw1211 := by apply Matrix.ext; unfold raw1209 raw1211; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4398 = raw1211Labels := by decide +kernel
    rw [ha, hj, canonical1211 B hB]
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

theorem singleton4631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4631 node4631Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1760 node1760Labels + mixedMoment B node1836 node1836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1473 singletonSmall4631
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4631) = raw1473Labels := by decide +kernel
  rw [hl, canonical1473 B hB] at h
  have hc0 : mixedMoment B raw1473 (Fin.cases (0 : Fin 2) singletonSmall4631) =
      mixedMoment B node1760 node1760Labels := by
    have ha : raw1473 = raw1474 := by apply Matrix.ext; unfold raw1473 raw1474; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4631 = raw1474Labels := by decide +kernel
    rw [ha, hj, canonical1474 B hB]
  have hc1 : mixedMoment B raw1473 (Fin.cases (1 : Fin 2) singletonSmall4631) =
      mixedMoment B node1836 node1836Labels := by
    have ha : raw1473 = raw1475 := by apply Matrix.ext; unfold raw1473 raw1475; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4631 = raw1475Labels := by decide +kernel
    rw [ha, hj, canonical1475 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4637 node4637Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1766 node1766Labels + mixedMoment B node1850 node1850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1491 singletonSmall4637
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4637) = raw1491Labels := by decide +kernel
  rw [hl, canonical1491 B hB] at h
  have hc0 : mixedMoment B raw1491 (Fin.cases (0 : Fin 2) singletonSmall4637) =
      mixedMoment B node1766 node1766Labels := by
    have ha : raw1491 = raw1492 := by apply Matrix.ext; unfold raw1491 raw1492; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4637 = raw1492Labels := by decide +kernel
    rw [ha, hj, canonical1492 B hB]
  have hc1 : mixedMoment B raw1491 (Fin.cases (1 : Fin 2) singletonSmall4637) =
      mixedMoment B node1850 node1850Labels := by
    have ha : raw1491 = raw1493 := by apply Matrix.ext; unfold raw1491 raw1493; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4637 = raw1493Labels := by decide +kernel
    rw [ha, hj, canonical1493 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4644 node4644Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1773 node1773Labels + mixedMoment B node1841 node1841Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1506 singletonSmall4644
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4644) = raw1506Labels := by decide +kernel
  rw [hl, canonical1506 B hB] at h
  have hc0 : mixedMoment B raw1506 (Fin.cases (0 : Fin 2) singletonSmall4644) =
      mixedMoment B node1773 node1773Labels := by
    have ha : raw1506 = raw1507 := by apply Matrix.ext; unfold raw1506 raw1507; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4644 = raw1507Labels := by decide +kernel
    rw [ha, hj, canonical1507 B hB]
  have hc1 : mixedMoment B raw1506 (Fin.cases (1 : Fin 2) singletonSmall4644) =
      mixedMoment B node1841 node1841Labels := by
    have ha : raw1506 = raw1508 := by apply Matrix.ext; unfold raw1506 raw1508; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4644 = raw1508Labels := by decide +kernel
    rw [ha, hj, canonical1508 B hB]
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

theorem singleton4706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4706 node4706Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1860 node1860Labels + mixedMoment B node1888 node1888Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1590 singletonSmall4706
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4706) = raw1590Labels := by decide +kernel
  rw [hl, canonical1590 B hB] at h
  have hc0 : mixedMoment B raw1590 (Fin.cases (0 : Fin 2) singletonSmall4706) =
      mixedMoment B node1860 node1860Labels := by
    have ha : raw1590 = raw1591 := by apply Matrix.ext; unfold raw1590 raw1591; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4706 = raw1591Labels := by decide +kernel
    rw [ha, hj, canonical1591 B hB]
  have hc1 : mixedMoment B raw1590 (Fin.cases (1 : Fin 2) singletonSmall4706) =
      mixedMoment B node1888 node1888Labels := by
    have ha : raw1590 = raw1592 := by apply Matrix.ext; unfold raw1590 raw1592; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4706 = raw1592Labels := by decide +kernel
    rw [ha, hj, canonical1592 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4709 node4709Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1863 node1863Labels + mixedMoment B node1883 node1883Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1596 singletonSmall4709
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4709) = raw1596Labels := by decide +kernel
  rw [hl, canonical1596 B hB] at h
  have hc0 : mixedMoment B raw1596 (Fin.cases (0 : Fin 2) singletonSmall4709) =
      mixedMoment B node1863 node1863Labels := by
    have ha : raw1596 = raw1597 := by apply Matrix.ext; unfold raw1596 raw1597; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4709 = raw1597Labels := by decide +kernel
    rw [ha, hj, canonical1597 B hB]
  have hc1 : mixedMoment B raw1596 (Fin.cases (1 : Fin 2) singletonSmall4709) =
      mixedMoment B node1883 node1883Labels := by
    have ha : raw1596 = raw1598 := by apply Matrix.ext; unfold raw1596 raw1598; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4709 = raw1598Labels := by decide +kernel
    rw [ha, hj, canonical1598 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4728 node4728Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1897 node1897Labels + mixedMoment B node1907 node1907Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1641 singletonSmall4728
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4728) = raw1641Labels := by decide +kernel
  rw [hl, canonical1641 B hB] at h
  have hc0 : mixedMoment B raw1641 (Fin.cases (0 : Fin 2) singletonSmall4728) =
      mixedMoment B node1897 node1897Labels := by
    have ha : raw1641 = raw1642 := by apply Matrix.ext; unfold raw1641 raw1642; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4728 = raw1642Labels := by decide +kernel
    rw [ha, hj, canonical1642 B hB]
  have hc1 : mixedMoment B raw1641 (Fin.cases (1 : Fin 2) singletonSmall4728) =
      mixedMoment B node1907 node1907Labels := by
    have ha : raw1641 = raw1643 := by apply Matrix.ext; unfold raw1641 raw1643; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4728 = raw1643Labels := by decide +kernel
    rw [ha, hj, canonical1643 B hB]
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

theorem singleton4760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4760 node4760Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1960 node1960Labels + mixedMoment B node2173 node2173Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1689 singletonSmall4760
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4760) = raw1689Labels := by decide +kernel
  rw [hl, canonical1689 B hB] at h
  have hc0 : mixedMoment B raw1689 (Fin.cases (0 : Fin 2) singletonSmall4760) =
      mixedMoment B node1960 node1960Labels := by
    have ha : raw1689 = raw1690 := by apply Matrix.ext; unfold raw1689 raw1690; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4760 = raw1690Labels := by decide +kernel
    rw [ha, hj, canonical1690 B hB]
  have hc1 : mixedMoment B raw1689 (Fin.cases (1 : Fin 2) singletonSmall4760) =
      mixedMoment B node2173 node2173Labels := by
    have ha : raw1689 = raw1691 := by apply Matrix.ext; unfold raw1689 raw1691; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4760 = raw1691Labels := by decide +kernel
    rw [ha, hj, canonical1691 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4769 node4769Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1969 node1969Labels + mixedMoment B node2185 node2185Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1704 singletonSmall4769
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4769) = raw1704Labels := by decide +kernel
  rw [hl, canonical1704 B hB] at h
  have hc0 : mixedMoment B raw1704 (Fin.cases (0 : Fin 2) singletonSmall4769) =
      mixedMoment B node1969 node1969Labels := by
    have ha : raw1704 = raw1705 := by apply Matrix.ext; unfold raw1704 raw1705; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4769 = raw1705Labels := by decide +kernel
    rw [ha, hj, canonical1705 B hB]
  have hc1 : mixedMoment B raw1704 (Fin.cases (1 : Fin 2) singletonSmall4769) =
      mixedMoment B node2185 node2185Labels := by
    have ha : raw1704 = raw1706 := by apply Matrix.ext; unfold raw1704 raw1706; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4769 = raw1706Labels := by decide +kernel
    rw [ha, hj, canonical1706 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4779 node4779Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1987 node1987Labels + mixedMoment B node1996 node1996Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1713 singletonSmall4779
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4779) = raw1713Labels := by decide +kernel
  rw [hl, canonical1713 B hB] at h
  have hc0 : mixedMoment B raw1713 (Fin.cases (0 : Fin 2) singletonSmall4779) =
      mixedMoment B node1987 node1987Labels := by
    have ha : raw1713 = raw1714 := by apply Matrix.ext; unfold raw1713 raw1714; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4779 = raw1714Labels := by decide +kernel
    rw [ha, hj, canonical1714 B hB]
  have hc1 : mixedMoment B raw1713 (Fin.cases (1 : Fin 2) singletonSmall4779) =
      mixedMoment B node1996 node1996Labels := by
    have ha : raw1713 = raw1715 := by apply Matrix.ext; unfold raw1713 raw1715; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4779 = raw1715Labels := by decide +kernel
    rw [ha, hj, canonical1715 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4788 node4788Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2003 node2003Labels + mixedMoment B node2006 node2006Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1722 singletonSmall4788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4788) = raw1722Labels := by decide +kernel
  rw [hl, canonical1722 B hB] at h
  have hc0 : mixedMoment B raw1722 (Fin.cases (0 : Fin 2) singletonSmall4788) =
      mixedMoment B node2003 node2003Labels := by
    have ha : raw1722 = raw1723 := by apply Matrix.ext; unfold raw1722 raw1723; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4788 = raw1723Labels := by decide +kernel
    rw [ha, hj, canonical1723 B hB]
  have hc1 : mixedMoment B raw1722 (Fin.cases (1 : Fin 2) singletonSmall4788) =
      mixedMoment B node2006 node2006Labels := by
    have ha : raw1722 = raw1724 := by apply Matrix.ext; unfold raw1722 raw1724; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4788 = raw1724Labels := by decide +kernel
    rw [ha, hj, canonical1724 B hB]
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

theorem singleton4804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4804 node4804Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2022 node2022Labels + mixedMoment B node2203 node2203Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1737 singletonSmall4804
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4804) = raw1737Labels := by decide +kernel
  rw [hl, canonical1737 B hB] at h
  have hc0 : mixedMoment B raw1737 (Fin.cases (0 : Fin 2) singletonSmall4804) =
      mixedMoment B node2022 node2022Labels := by
    have ha : raw1737 = raw1738 := by apply Matrix.ext; unfold raw1737 raw1738; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4804 = raw1738Labels := by decide +kernel
    rw [ha, hj, canonical1738 B hB]
  have hc1 : mixedMoment B raw1737 (Fin.cases (1 : Fin 2) singletonSmall4804) =
      mixedMoment B node2203 node2203Labels := by
    have ha : raw1737 = raw1739 := by apply Matrix.ext; unfold raw1737 raw1739; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4804 = raw1739Labels := by decide +kernel
    rw [ha, hj, canonical1739 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4811 node4811Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2029 node2029Labels + mixedMoment B node2225 node2225Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1749 singletonSmall4811
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4811) = raw1749Labels := by decide +kernel
  rw [hl, canonical1749 B hB] at h
  have hc0 : mixedMoment B raw1749 (Fin.cases (0 : Fin 2) singletonSmall4811) =
      mixedMoment B node2029 node2029Labels := by
    have ha : raw1749 = raw1750 := by apply Matrix.ext; unfold raw1749 raw1750; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4811 = raw1750Labels := by decide +kernel
    rw [ha, hj, canonical1750 B hB]
  have hc1 : mixedMoment B raw1749 (Fin.cases (1 : Fin 2) singletonSmall4811) =
      mixedMoment B node2225 node2225Labels := by
    have ha : raw1749 = raw1751 := by apply Matrix.ext; unfold raw1749 raw1751; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4811 = raw1751Labels := by decide +kernel
    rw [ha, hj, canonical1751 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4832 node4832Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2052 node2052Labels + mixedMoment B node2193 node2193Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1764 singletonSmall4832
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4832) = raw1764Labels := by decide +kernel
  rw [hl, canonical1764 B hB] at h
  have hc0 : mixedMoment B raw1764 (Fin.cases (0 : Fin 2) singletonSmall4832) =
      mixedMoment B node2052 node2052Labels := by
    have ha : raw1764 = raw1765 := by apply Matrix.ext; unfold raw1764 raw1765; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4832 = raw1765Labels := by decide +kernel
    rw [ha, hj, canonical1765 B hB]
  have hc1 : mixedMoment B raw1764 (Fin.cases (1 : Fin 2) singletonSmall4832) =
      mixedMoment B node2193 node2193Labels := by
    have ha : raw1764 = raw1766 := by apply Matrix.ext; unfold raw1764 raw1766; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4832 = raw1766Labels := by decide +kernel
    rw [ha, hj, canonical1766 B hB]
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

theorem singleton4888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4888 node4888Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2244 node2244Labels + mixedMoment B node2262 node2262Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1815 singletonSmall4888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4888) = raw1815Labels := by decide +kernel
  rw [hl, canonical1815 B hB] at h
  have hc0 : mixedMoment B raw1815 (Fin.cases (0 : Fin 2) singletonSmall4888) =
      mixedMoment B node2244 node2244Labels := by
    have ha : raw1815 = raw1816 := by apply Matrix.ext; unfold raw1815 raw1816; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4888 = raw1816Labels := by decide +kernel
    rw [ha, hj, canonical1816 B hB]
  have hc1 : mixedMoment B raw1815 (Fin.cases (1 : Fin 2) singletonSmall4888) =
      mixedMoment B node2262 node2262Labels := by
    have ha : raw1815 = raw1817 := by apply Matrix.ext; unfold raw1815 raw1817; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4888 = raw1817Labels := by decide +kernel
    rw [ha, hj, canonical1817 B hB]
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

theorem singleton5134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5134 node5134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2553 node2553Labels + mixedMoment B node3514 node3514Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2163 singletonSmall5134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5134) = raw2163Labels := by decide +kernel
  rw [hl, canonical2163 B hB] at h
  have hc0 : mixedMoment B raw2163 (Fin.cases (0 : Fin 2) singletonSmall5134) =
      mixedMoment B node2553 node2553Labels := by
    have ha : raw2163 = raw2164 := by apply Matrix.ext; unfold raw2163 raw2164; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5134 = raw2164Labels := by decide +kernel
    rw [ha, hj, canonical2164 B hB]
  have hc1 : mixedMoment B raw2163 (Fin.cases (1 : Fin 2) singletonSmall5134) =
      mixedMoment B node3514 node3514Labels := by
    have ha : raw2163 = raw2165 := by apply Matrix.ext; unfold raw2163 raw2165; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5134 = raw2165Labels := by decide +kernel
    rw [ha, hj, canonical2165 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
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

theorem singleton5258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5258 node5258Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2722 node2722Labels + mixedMoment B node3533 node3533Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2271 singletonSmall5258
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5258) = raw2271Labels := by decide +kernel
  rw [hl, canonical2271 B hB] at h
  have hc0 : mixedMoment B raw2271 (Fin.cases (0 : Fin 2) singletonSmall5258) =
      mixedMoment B node2722 node2722Labels := by
    have ha : raw2271 = raw2272 := by apply Matrix.ext; unfold raw2271 raw2272; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5258 = raw2272Labels := by decide +kernel
    rw [ha, hj, canonical2272 B hB]
  have hc1 : mixedMoment B raw2271 (Fin.cases (1 : Fin 2) singletonSmall5258) =
      mixedMoment B node3533 node3533Labels := by
    have ha : raw2271 = raw2273 := by apply Matrix.ext; unfold raw2271 raw2273; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5258 = raw2273Labels := by decide +kernel
    rw [ha, hj, canonical2273 B hB]
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

theorem sound699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node699 node699Labels = Sparse.eval nodeValue699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 699) = mixedMoment B node699 node699Labels := rfl
  simpa [nodeValue699, Sparse.eval] using hc.symm

theorem sound701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node701 node701Labels = Sparse.eval nodeValue701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 701) = mixedMoment B node701 node701Labels := rfl
  simpa [nodeValue701, Sparse.eval] using hc.symm

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

theorem sound707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node707 node707Labels = Sparse.eval nodeValue707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 707) = mixedMoment B node707 node707Labels := rfl
  simpa [nodeValue707, Sparse.eval] using hc.symm

theorem sound715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node715 node715Labels = Sparse.eval nodeValue715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 715) = mixedMoment B node715 node715Labels := rfl
  simpa [nodeValue715, Sparse.eval] using hc.symm

theorem sound748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node748 node748Labels = Sparse.eval nodeValue748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 748) = mixedMoment B node748 node748Labels := rfl
  simpa [nodeValue748, Sparse.eval] using hc.symm

theorem sound750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node750 node750Labels = Sparse.eval nodeValue750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 750) = mixedMoment B node750 node750Labels := rfl
  simpa [nodeValue750, Sparse.eval] using hc.symm

theorem sound753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node753 node753Labels = Sparse.eval nodeValue753 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 753) = mixedMoment B node753 node753Labels := rfl
  simpa [nodeValue753, Sparse.eval] using hc.symm

theorem sound763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node763 node763Labels = Sparse.eval nodeValue763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 763) = mixedMoment B node763 node763Labels := rfl
  simpa [nodeValue763, Sparse.eval] using hc.symm

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

theorem sound785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node785 node785Labels = Sparse.eval nodeValue785 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 785) = mixedMoment B node785 node785Labels := rfl
  simpa [nodeValue785, Sparse.eval] using hc.symm

theorem sound804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node804 node804Labels = Sparse.eval nodeValue804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 804) = mixedMoment B node804 node804Labels := rfl
  simpa [nodeValue804, Sparse.eval] using hc.symm

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

theorem sound898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node898 node898Labels = Sparse.eval nodeValue898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 898) = mixedMoment B node898 node898Labels := rfl
  simpa [nodeValue898, Sparse.eval] using hc.symm

theorem sound902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node902 node902Labels = Sparse.eval nodeValue902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 902) = mixedMoment B node902 node902Labels := rfl
  simpa [nodeValue902, Sparse.eval] using hc.symm

theorem sound921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node921 node921Labels = Sparse.eval nodeValue921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 921) = mixedMoment B node921 node921Labels := rfl
  simpa [nodeValue921, Sparse.eval] using hc.symm

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

theorem sound979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node979 node979Labels = Sparse.eval nodeValue979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 979) = mixedMoment B node979 node979Labels := rfl
  simpa [nodeValue979, Sparse.eval] using hc.symm

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

theorem sound1586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1586 node1586Labels = Sparse.eval nodeValue1586 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1586) = mixedMoment B node1586 node1586Labels := rfl
  simpa [nodeValue1586, Sparse.eval] using hc.symm

theorem sound1590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1590 node1590Labels = Sparse.eval nodeValue1590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1590) = mixedMoment B node1590 node1590Labels := rfl
  simpa [nodeValue1590, Sparse.eval] using hc.symm

theorem sound1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1599 node1599Labels = Sparse.eval nodeValue1599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1599) = mixedMoment B node1599 node1599Labels := rfl
  simpa [nodeValue1599, Sparse.eval] using hc.symm

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

theorem sound1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1666 node1666Labels = Sparse.eval nodeValue1666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1666) = mixedMoment B node1666 node1666Labels := rfl
  simpa [nodeValue1666, Sparse.eval] using hc.symm

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

theorem sound1760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1760 node1760Labels = Sparse.eval nodeValue1760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1760) = mixedMoment B node1760 node1760Labels := rfl
  simpa [nodeValue1760, Sparse.eval] using hc.symm

theorem sound1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1766 node1766Labels = Sparse.eval nodeValue1766 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1766) = mixedMoment B node1766 node1766Labels := rfl
  simpa [nodeValue1766, Sparse.eval] using hc.symm

theorem sound1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1773 node1773Labels = Sparse.eval nodeValue1773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1773) = mixedMoment B node1773 node1773Labels := rfl
  simpa [nodeValue1773, Sparse.eval] using hc.symm

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

theorem sound1836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1836 node1836Labels = Sparse.eval nodeValue1836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1836) = mixedMoment B node1836 node1836Labels := rfl
  simpa [nodeValue1836, Sparse.eval] using hc.symm

theorem sound1841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1841 node1841Labels = Sparse.eval nodeValue1841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1841) = mixedMoment B node1841 node1841Labels := rfl
  simpa [nodeValue1841, Sparse.eval] using hc.symm

theorem sound1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1850 node1850Labels = Sparse.eval nodeValue1850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1850) = mixedMoment B node1850 node1850Labels := rfl
  simpa [nodeValue1850, Sparse.eval] using hc.symm

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

theorem sound1860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1860 node1860Labels = Sparse.eval nodeValue1860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1860) = mixedMoment B node1860 node1860Labels := rfl
  simpa [nodeValue1860, Sparse.eval] using hc.symm

theorem sound1863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1863 node1863Labels = Sparse.eval nodeValue1863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1863) = mixedMoment B node1863 node1863Labels := rfl
  simpa [nodeValue1863, Sparse.eval] using hc.symm

theorem sound1883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1883 node1883Labels = Sparse.eval nodeValue1883 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1883) = mixedMoment B node1883 node1883Labels := rfl
  simpa [nodeValue1883, Sparse.eval] using hc.symm

theorem sound1888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1888 node1888Labels = Sparse.eval nodeValue1888 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1888) = mixedMoment B node1888 node1888Labels := rfl
  simpa [nodeValue1888, Sparse.eval] using hc.symm

theorem sound1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1897 node1897Labels = Sparse.eval nodeValue1897 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1897) = mixedMoment B node1897 node1897Labels := rfl
  simpa [nodeValue1897, Sparse.eval] using hc.symm

theorem sound1907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1907 node1907Labels = Sparse.eval nodeValue1907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1907) = mixedMoment B node1907 node1907Labels := rfl
  simpa [nodeValue1907, Sparse.eval] using hc.symm

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

theorem sound1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1960 node1960Labels = Sparse.eval nodeValue1960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1960) = mixedMoment B node1960 node1960Labels := rfl
  simpa [nodeValue1960, Sparse.eval] using hc.symm

theorem sound1969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1969 node1969Labels = Sparse.eval nodeValue1969 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1969) = mixedMoment B node1969 node1969Labels := rfl
  simpa [nodeValue1969, Sparse.eval] using hc.symm

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

theorem sound1987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1987 node1987Labels = Sparse.eval nodeValue1987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1987) = mixedMoment B node1987 node1987Labels := rfl
  simpa [nodeValue1987, Sparse.eval] using hc.symm

theorem sound1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1996 node1996Labels = Sparse.eval nodeValue1996 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1996) = mixedMoment B node1996 node1996Labels := rfl
  simpa [nodeValue1996, Sparse.eval] using hc.symm

theorem sound2003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2003 node2003Labels = Sparse.eval nodeValue2003 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2003) = mixedMoment B node2003 node2003Labels := rfl
  simpa [nodeValue2003, Sparse.eval] using hc.symm

theorem sound2006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2006 node2006Labels = Sparse.eval nodeValue2006 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2006) = mixedMoment B node2006 node2006Labels := rfl
  simpa [nodeValue2006, Sparse.eval] using hc.symm

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

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

theorem sound2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2052 node2052Labels = Sparse.eval nodeValue2052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2052) = mixedMoment B node2052 node2052Labels := rfl
  simpa [nodeValue2052, Sparse.eval] using hc.symm

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

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

theorem sound2173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2173 node2173Labels = Sparse.eval nodeValue2173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2173) = mixedMoment B node2173 node2173Labels := rfl
  simpa [nodeValue2173, Sparse.eval] using hc.symm

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

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

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

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

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

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

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

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

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

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

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

theorem sound4196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4196 node4196Labels = Sparse.eval nodeValue4196 (mixedVector B) := by
  have h := singleton4196 B _hB
  rw [sound699 B _hB _hF, sound748 B _hB _hF] at h
  norm_num [nodeValue4196, nodeValue699, nodeValue748, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4198 node4198Labels = Sparse.eval nodeValue4198 (mixedVector B) := by
  have h := singleton4198 B _hB
  rw [sound701 B _hB _hF, sound750 B _hB _hF] at h
  norm_num [nodeValue4198, nodeValue701, nodeValue750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4204 node4204Labels = Sparse.eval nodeValue4204 (mixedVector B) := by
  have h := singleton4204 B _hB
  rw [sound707 B _hB _hF, sound763 B _hB _hF] at h
  norm_num [nodeValue4204, nodeValue707, nodeValue763, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4212 node4212Labels = Sparse.eval nodeValue4212 (mixedVector B) := by
  have h := singleton4212 B _hB
  rw [sound715 B _hB _hF, sound753 B _hB _hF] at h
  norm_num [nodeValue4212, nodeValue715, nodeValue753, Sparse.eval] at h ⊢
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

theorem sound4251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4251 node4251Labels = Sparse.eval nodeValue4251 (mixedVector B) := by
  have h := singleton4251 B _hB
  rw [sound785 B _hB _hF, sound804 B _hB _hF] at h
  norm_num [nodeValue4251, nodeValue785, nodeValue804, Sparse.eval] at h ⊢
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

theorem sound4320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4320 node4320Labels = Sparse.eval nodeValue4320 (mixedVector B) := by
  have h := singleton4320 B _hB
  rw [sound898 B _hB _hF, sound1586 B _hB _hF] at h
  norm_num [nodeValue4320, nodeValue898, nodeValue1586, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4324 node4324Labels = Sparse.eval nodeValue4324 (mixedVector B) := by
  have h := singleton4324 B _hB
  rw [sound902 B _hB _hF, sound1590 B _hB _hF] at h
  norm_num [nodeValue4324, nodeValue902, nodeValue1590, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4343 node4343Labels = Sparse.eval nodeValue4343 (mixedVector B) := by
  have h := singleton4343 B _hB
  rw [sound921 B _hB _hF, sound1666 B _hB _hF] at h
  norm_num [nodeValue4343, nodeValue921, nodeValue1666, Sparse.eval] at h ⊢
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

theorem sound4398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4398 node4398Labels = Sparse.eval nodeValue4398 (mixedVector B) := by
  have h := singleton4398 B _hB
  rw [sound979 B _hB _hF, sound1599 B _hB _hF] at h
  norm_num [nodeValue4398, nodeValue979, nodeValue1599, Sparse.eval] at h ⊢
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

theorem sound4631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4631 node4631Labels = Sparse.eval nodeValue4631 (mixedVector B) := by
  have h := singleton4631 B _hB
  rw [sound1760 B _hB _hF, sound1836 B _hB _hF] at h
  norm_num [nodeValue4631, nodeValue1760, nodeValue1836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4637 node4637Labels = Sparse.eval nodeValue4637 (mixedVector B) := by
  have h := singleton4637 B _hB
  rw [sound1766 B _hB _hF, sound1850 B _hB _hF] at h
  norm_num [nodeValue4637, nodeValue1766, nodeValue1850, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4644 node4644Labels = Sparse.eval nodeValue4644 (mixedVector B) := by
  have h := singleton4644 B _hB
  rw [sound1773 B _hB _hF, sound1841 B _hB _hF] at h
  norm_num [nodeValue4644, nodeValue1773, nodeValue1841, Sparse.eval] at h ⊢
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

theorem sound4706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4706 node4706Labels = Sparse.eval nodeValue4706 (mixedVector B) := by
  have h := singleton4706 B _hB
  rw [sound1860 B _hB _hF, sound1888 B _hB _hF] at h
  norm_num [nodeValue4706, nodeValue1860, nodeValue1888, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4709 node4709Labels = Sparse.eval nodeValue4709 (mixedVector B) := by
  have h := singleton4709 B _hB
  rw [sound1863 B _hB _hF, sound1883 B _hB _hF] at h
  norm_num [nodeValue4709, nodeValue1863, nodeValue1883, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4728 node4728Labels = Sparse.eval nodeValue4728 (mixedVector B) := by
  have h := singleton4728 B _hB
  rw [sound1897 B _hB _hF, sound1907 B _hB _hF] at h
  norm_num [nodeValue4728, nodeValue1897, nodeValue1907, Sparse.eval] at h ⊢
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

theorem sound4760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4760 node4760Labels = Sparse.eval nodeValue4760 (mixedVector B) := by
  have h := singleton4760 B _hB
  rw [sound1960 B _hB _hF, sound2173 B _hB _hF] at h
  norm_num [nodeValue4760, nodeValue1960, nodeValue2173, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4769 node4769Labels = Sparse.eval nodeValue4769 (mixedVector B) := by
  have h := singleton4769 B _hB
  rw [sound1969 B _hB _hF, sound2185 B _hB _hF] at h
  norm_num [nodeValue4769, nodeValue1969, nodeValue2185, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4779 node4779Labels = Sparse.eval nodeValue4779 (mixedVector B) := by
  have h := singleton4779 B _hB
  rw [sound1987 B _hB _hF, sound1996 B _hB _hF] at h
  norm_num [nodeValue4779, nodeValue1987, nodeValue1996, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4788 node4788Labels = Sparse.eval nodeValue4788 (mixedVector B) := by
  have h := singleton4788 B _hB
  rw [sound2003 B _hB _hF, sound2006 B _hB _hF] at h
  norm_num [nodeValue4788, nodeValue2003, nodeValue2006, Sparse.eval] at h ⊢
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

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4832 node4832Labels = Sparse.eval nodeValue4832 (mixedVector B) := by
  have h := singleton4832 B _hB
  rw [sound2052 B _hB _hF, sound2193 B _hB _hF] at h
  norm_num [nodeValue4832, nodeValue2052, nodeValue2193, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
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

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
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

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
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

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources63
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2046 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2046 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 1) (sourceB2046 + difference 1 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 1) (sourceB2046 + difference 1 0) sourceC2046) = raw28885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28885; decide +kernel
    rw [ha]
    exact (canonical28885 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 2) (sourceB2046 + difference 2 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 2) (sourceB2046 + difference 2 0) sourceC2046) = raw28886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28886; decide +kernel
    rw [ha]
    exact (canonical28886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 3) (sourceB2046 + difference 3 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 3) (sourceB2046 + difference 3 0) sourceC2046) = raw28887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28887; decide +kernel
    rw [ha]
    exact (canonical28887 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 4) (sourceB2046 + difference 4 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 4) (sourceB2046 + difference 4 0) sourceC2046) = raw28888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28888; decide +kernel
    rw [ha]
    exact (canonical28888 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 5) (sourceB2046 + difference 5 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 5) (sourceB2046 + difference 5 0) sourceC2046) = raw10085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10085; decide +kernel
    rw [ha]
    exact (canonical10085 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 0) (sourceB2046 + difference 0 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 0) (sourceB2046 + difference 0 1) sourceC2046) = raw10110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10110; decide +kernel
    rw [ha]
    exact (canonical10110 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 2) (sourceB2046 + difference 2 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 2) (sourceB2046 + difference 2 1) sourceC2046) = raw10112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10112; decide +kernel
    rw [ha]
    exact (canonical10112 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 3) (sourceB2046 + difference 3 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 3) (sourceB2046 + difference 3 1) sourceC2046) = raw10113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10113; decide +kernel
    rw [ha]
    exact (canonical10113 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 4) (sourceB2046 + difference 4 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 4) (sourceB2046 + difference 4 1) sourceC2046) = raw10114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10114; decide +kernel
    rw [ha]
    exact (canonical10114 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 5) (sourceB2046 + difference 5 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 5) (sourceB2046 + difference 5 1) sourceC2046) = raw25427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw25427; decide +kernel
    rw [ha]
    exact (canonical25427 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 0) (sourceB2046 + difference 0 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 0) (sourceB2046 + difference 0 2) sourceC2046) = raw28889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28889; decide +kernel
    rw [ha]
    exact (canonical28889 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 1) (sourceB2046 + difference 1 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 1) (sourceB2046 + difference 1 2) sourceC2046) = raw28890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28890; decide +kernel
    rw [ha]
    exact (canonical28890 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 3) (sourceB2046 + difference 3 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4709) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 3) (sourceB2046 + difference 3 2) sourceC2046) = raw28891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28891; decide +kernel
    rw [ha]
    exact (canonical28891 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 4) (sourceB2046 + difference 4 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 4) (sourceB2046 + difference 4 2) sourceC2046) = raw28892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28892; decide +kernel
    rw [ha]
    exact (canonical28892 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 5) (sourceB2046 + difference 5 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 5) (sourceB2046 + difference 5 2) sourceC2046) = raw10096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10096; decide +kernel
    rw [ha]
    exact (canonical10096 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 0) (sourceB2046 + difference 0 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 0) (sourceB2046 + difference 0 3) sourceC2046) = raw25446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw25446; decide +kernel
    rw [ha]
    exact (canonical25446 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 1) (sourceB2046 + difference 1 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 1) (sourceB2046 + difference 1 3) sourceC2046) = raw28893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28893; decide +kernel
    rw [ha]
    exact (canonical28893 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 2) (sourceB2046 + difference 2 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 2) (sourceB2046 + difference 2 3) sourceC2046) = raw28894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28894; decide +kernel
    rw [ha]
    exact (canonical28894 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 4) (sourceB2046 + difference 4 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 4) (sourceB2046 + difference 4 3) sourceC2046) = raw28895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28895; decide +kernel
    rw [ha]
    exact (canonical28895 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 5) (sourceB2046 + difference 5 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 5) (sourceB2046 + difference 5 3) sourceC2046) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 0) (sourceB2046 + difference 0 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 0) (sourceB2046 + difference 0 4) sourceC2046) = raw28896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28896; decide +kernel
    rw [ha]
    exact (canonical28896 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 1) (sourceB2046 + difference 1 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 1) (sourceB2046 + difference 1 4) sourceC2046) = raw28897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28897; decide +kernel
    rw [ha]
    exact (canonical28897 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 2) (sourceB2046 + difference 2 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 2) (sourceB2046 + difference 2 4) sourceC2046) = raw28898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28898; decide +kernel
    rw [ha]
    exact (canonical28898 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 3) (sourceB2046 + difference 3 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 3) (sourceB2046 + difference 3 4) sourceC2046) = raw28899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28899; decide +kernel
    rw [ha]
    exact (canonical28899 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 5) (sourceB2046 + difference 5 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 5) (sourceB2046 + difference 5 4) sourceC2046) = raw10106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10106; decide +kernel
    rw [ha]
    exact (canonical10106 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 0) (sourceB2046 + difference 0 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 0) (sourceB2046 + difference 0 5) sourceC2046) = raw28900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28900; decide +kernel
    rw [ha]
    exact (canonical28900 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 1) (sourceB2046 + difference 1 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 1) (sourceB2046 + difference 1 5) sourceC2046) = raw28901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28901; decide +kernel
    rw [ha]
    exact (canonical28901 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 2) (sourceB2046 + difference 2 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 2) (sourceB2046 + difference 2 5) sourceC2046) = raw28902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28902; decide +kernel
    rw [ha]
    exact (canonical28902 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 3) (sourceB2046 + difference 3 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 3) (sourceB2046 + difference 3 5) sourceC2046) = raw28903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28903; decide +kernel
    rw [ha]
    exact (canonical28903 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 4) (sourceB2046 + difference 4 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 4) (sourceB2046 + difference 4 5) sourceC2046) = raw28904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28904; decide +kernel
    rw [ha]
    exact (canonical28904 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2046 sourceB2046 sourceC2046
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2046, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1723 : Integer.Sparse.reindex keyMap MixedData.row1723 = numericRow1723 := by decide +kernel

theorem numericCheck1723 (x : Master → ℝ) : Integer.Sparse.eval numericRow1723 x =
    (17280 : ℝ) * reducedSource1723 x := by
  norm_num [numericRow1723, reducedSource1723, Integer.Sparse.eval, Sparse.eval, nodeValue4196, nodeValue4198, nodeValue4204, nodeValue4212, nodeValue4251, nodeValue4320, nodeValue4324, nodeValue4343, nodeValue4398, nodeValue4631, nodeValue4637, nodeValue4644, nodeValue4706, nodeValue4709, nodeValue4728, nodeValue4760, nodeValue4769, nodeValue4779, nodeValue4788, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4832, nodeValue4835, nodeValue4888, nodeValue5134, nodeValue5141, nodeValue5168, nodeValue5258, nodeValue5434] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1723 (mixedVector B) = 0 := by
  have h4196 : mixedVector B (Sum.inr 4196) = Sparse.eval nodeValue4196 (mixedVector B) := by
    change mixedMoment B node4196 node4196Labels = _
    exact sound4196 B hB hF
  have h4198 : mixedVector B (Sum.inr 4198) = Sparse.eval nodeValue4198 (mixedVector B) := by
    change mixedMoment B node4198 node4198Labels = _
    exact sound4198 B hB hF
  have h4204 : mixedVector B (Sum.inr 4204) = Sparse.eval nodeValue4204 (mixedVector B) := by
    change mixedMoment B node4204 node4204Labels = _
    exact sound4204 B hB hF
  have h4212 : mixedVector B (Sum.inr 4212) = Sparse.eval nodeValue4212 (mixedVector B) := by
    change mixedMoment B node4212 node4212Labels = _
    exact sound4212 B hB hF
  have h4251 : mixedVector B (Sum.inr 4251) = Sparse.eval nodeValue4251 (mixedVector B) := by
    change mixedMoment B node4251 node4251Labels = _
    exact sound4251 B hB hF
  have h4320 : mixedVector B (Sum.inr 4320) = Sparse.eval nodeValue4320 (mixedVector B) := by
    change mixedMoment B node4320 node4320Labels = _
    exact sound4320 B hB hF
  have h4324 : mixedVector B (Sum.inr 4324) = Sparse.eval nodeValue4324 (mixedVector B) := by
    change mixedMoment B node4324 node4324Labels = _
    exact sound4324 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4631 : mixedVector B (Sum.inr 4631) = Sparse.eval nodeValue4631 (mixedVector B) := by
    change mixedMoment B node4631 node4631Labels = _
    exact sound4631 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4644 : mixedVector B (Sum.inr 4644) = Sparse.eval nodeValue4644 (mixedVector B) := by
    change mixedMoment B node4644 node4644Labels = _
    exact sound4644 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4709 : mixedVector B (Sum.inr 4709) = Sparse.eval nodeValue4709 (mixedVector B) := by
    change mixedMoment B node4709 node4709Labels = _
    exact sound4709 B hB hF
  have h4728 : mixedVector B (Sum.inr 4728) = Sparse.eval nodeValue4728 (mixedVector B) := by
    change mixedMoment B node4728 node4728Labels = _
    exact sound4728 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  simpa only [sourceForm2046, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4196, h4198, h4204, h4212, h4251, h4320, h4324, h4343, h4398, h4631, h4637, h4644, h4706, h4709, h4728, h4760, h4769, h4779, h4788, h4802, h4804, h4811, h4832, h4835, h4888, h5134, h5141, h5168, h5258, h5434, reducedSource1723] using sourceEq2046 B hB

theorem rowSound1723_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1723 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1723, numericCheck1723, reducedZero1723 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e_oai
