-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:00:16.702836+00:00
-- url     : https://prove2.me/submissions/fdfe6539-dc54-415c-8653-ec35e5d61912

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5167_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e

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

theorem canonical1887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1887 raw1887Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw1887 raw1887Labels = mixedMoment B raw1887step0 raw1887step0Labels := by
      have ha : raw1887step0 = (fun i j => raw1887 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1887step0 raw1887; decide +kernel
      have hl : raw1887step0Labels = raw1887Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1887 raw1887Labels permutation152 permutation4
    mixedMoment B raw1887step0 raw1887step0Labels = mixedMoment B raw1887step1 raw1887step1Labels := by
      have ha : raw1887step1 = raw1887step0 := by apply Matrix.ext; unfold raw1887step1 raw1887step0; decide +kernel
      have hl : raw1887step0Labels = labelEmbedding7 ∘ raw1887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1887step0 raw1887step0Labels raw1887step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4926 node4926Labels := by rfl

theorem canonical1888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1888 raw1888Labels = mixedMoment B node2316 node2316Labels := by
  calc
    mixedMoment B raw1888 raw1888Labels = mixedMoment B raw1888step0 raw1888step0Labels := by
      have ha : raw1888step0 = (fun i j => raw1888 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1888step0 raw1888; decide +kernel
      have hl : raw1888step0Labels = raw1888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1888 raw1888Labels permutation152 permutation4
    _ = mixedMoment B node2316 node2316Labels := by rfl

theorem canonical1889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1889 raw1889Labels = mixedMoment B node3398 node3398Labels := by
  calc
    mixedMoment B raw1889 raw1889Labels = mixedMoment B raw1889step0 raw1889step0Labels := by
      have ha : raw1889step0 = (fun i j => raw1889 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1889step0 raw1889; decide +kernel
      have hl : raw1889step0Labels = raw1889Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1889 raw1889Labels permutation152 permutation6
    mixedMoment B raw1889step0 raw1889step0Labels = mixedMoment B raw1889step1 raw1889step1Labels := by
      have ha : raw1889step1 = -raw1889step0 := by apply Matrix.ext; change ∀ i j, raw1889step1 i j = -(raw1889step0 i j); unfold raw1889step1 raw1889step0; decide +kernel
      have hl : raw1889step1Labels = raw1889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1889step1 raw1889step1Labels = mixedMoment B raw1889step2 raw1889step2Labels := by
      have ha : raw1889step2 = raw1889step1 := by apply Matrix.ext; unfold raw1889step2 raw1889step1; decide +kernel
      have hl : raw1889step1Labels = labelEmbedding1 ∘ raw1889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1889step1 raw1889step1Labels raw1889step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3398 node3398Labels := by rfl

theorem canonical1893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1893 raw1893Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw1893 raw1893Labels = mixedMoment B raw1893step0 raw1893step0Labels := by
      have ha : raw1893step0 = (fun i j => raw1893 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1893step0 raw1893; decide +kernel
      have hl : raw1893step0Labels = raw1893Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1893 raw1893Labels permutation152 permutation4
    mixedMoment B raw1893step0 raw1893step0Labels = mixedMoment B raw1893step1 raw1893step1Labels := by
      have ha : raw1893step1 = raw1893step0 := by apply Matrix.ext; unfold raw1893step1 raw1893step0; decide +kernel
      have hl : raw1893step0Labels = labelEmbedding7 ∘ raw1893step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1893step0 raw1893step0Labels raw1893step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical1894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1894 raw1894Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw1894 raw1894Labels = mixedMoment B raw1894step0 raw1894step0Labels := by
      have ha : raw1894step0 = (fun i j => raw1894 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1894step0 raw1894; decide +kernel
      have hl : raw1894step0Labels = raw1894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1894 raw1894Labels permutation152 permutation4
    _ = mixedMoment B node2318 node2318Labels := by rfl

theorem canonical1895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1895 raw1895Labels = mixedMoment B node3400 node3400Labels := by
  calc
    mixedMoment B raw1895 raw1895Labels = mixedMoment B raw1895step0 raw1895step0Labels := by
      have ha : raw1895step0 = (fun i j => raw1895 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1895step0 raw1895; decide +kernel
      have hl : raw1895step0Labels = raw1895Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1895 raw1895Labels permutation152 permutation6
    mixedMoment B raw1895step0 raw1895step0Labels = mixedMoment B raw1895step1 raw1895step1Labels := by
      have ha : raw1895step1 = -raw1895step0 := by apply Matrix.ext; change ∀ i j, raw1895step1 i j = -(raw1895step0 i j); unfold raw1895step1 raw1895step0; decide +kernel
      have hl : raw1895step1Labels = raw1895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1895step1 raw1895step1Labels = mixedMoment B raw1895step2 raw1895step2Labels := by
      have ha : raw1895step2 = raw1895step1 := by apply Matrix.ext; unfold raw1895step2 raw1895step1; decide +kernel
      have hl : raw1895step1Labels = labelEmbedding1 ∘ raw1895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1895step1 raw1895step1Labels raw1895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3400 node3400Labels := by rfl

theorem canonical1902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1902 raw1902Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw1902 raw1902Labels = mixedMoment B raw1902step0 raw1902step0Labels := by
      have ha : raw1902step0 = (fun i j => raw1902 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1902step0 raw1902; decide +kernel
      have hl : raw1902step0Labels = raw1902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1902 raw1902Labels permutation152 permutation4
    mixedMoment B raw1902step0 raw1902step0Labels = mixedMoment B raw1902step1 raw1902step1Labels := by
      have ha : raw1902step1 = raw1902step0 := by apply Matrix.ext; unfold raw1902step1 raw1902step0; decide +kernel
      have hl : raw1902step0Labels = labelEmbedding7 ∘ raw1902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1902step0 raw1902step0Labels raw1902step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical1903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1903 raw1903Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw1903 raw1903Labels = mixedMoment B raw1903step0 raw1903step0Labels := by
      have ha : raw1903step0 = (fun i j => raw1903 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1903step0 raw1903; decide +kernel
      have hl : raw1903step0Labels = raw1903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1903 raw1903Labels permutation152 permutation4
    _ = mixedMoment B node2330 node2330Labels := by rfl

theorem canonical1904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1904 raw1904Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw1904 raw1904Labels = mixedMoment B raw1904step0 raw1904step0Labels := by
      have ha : raw1904step0 = (fun i j => raw1904 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1904step0 raw1904; decide +kernel
      have hl : raw1904step0Labels = raw1904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1904 raw1904Labels permutation152 permutation6
    mixedMoment B raw1904step0 raw1904step0Labels = mixedMoment B raw1904step1 raw1904step1Labels := by
      have ha : raw1904step1 = -raw1904step0 := by apply Matrix.ext; change ∀ i j, raw1904step1 i j = -(raw1904step0 i j); unfold raw1904step1 raw1904step0; decide +kernel
      have hl : raw1904step1Labels = raw1904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1904step1 raw1904step1Labels = mixedMoment B raw1904step2 raw1904step2Labels := by
      have ha : raw1904step2 = raw1904step1 := by apply Matrix.ext; unfold raw1904step2 raw1904step1; decide +kernel
      have hl : raw1904step1Labels = labelEmbedding1 ∘ raw1904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1904step1 raw1904step1Labels raw1904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

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

theorem canonical1989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1989 raw1989Labels = mixedMoment B node4985 node4985Labels := by
  calc
    mixedMoment B raw1989 raw1989Labels = mixedMoment B raw1989step0 raw1989step0Labels := by
      have ha : raw1989step0 = (fun i j => raw1989 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1989step0 raw1989; decide +kernel
      have hl : raw1989step0Labels = raw1989Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1989 raw1989Labels permutation152 permutation4
    mixedMoment B raw1989step0 raw1989step0Labels = mixedMoment B raw1989step1 raw1989step1Labels := by
      have ha : raw1989step1 = raw1989step0 := by apply Matrix.ext; unfold raw1989step1 raw1989step0; decide +kernel
      have hl : raw1989step0Labels = labelEmbedding7 ∘ raw1989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1989step0 raw1989step0Labels raw1989step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4985 node4985Labels := by rfl

theorem canonical1990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1990 raw1990Labels = mixedMoment B node2370 node2370Labels := by
  calc
    mixedMoment B raw1990 raw1990Labels = mixedMoment B raw1990step0 raw1990step0Labels := by
      have ha : raw1990step0 = (fun i j => raw1990 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1990step0 raw1990; decide +kernel
      have hl : raw1990step0Labels = raw1990Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1990 raw1990Labels permutation152 permutation4
    _ = mixedMoment B node2370 node2370Labels := by rfl

theorem canonical1991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1991 raw1991Labels = mixedMoment B node3334 node3334Labels := by
  calc
    mixedMoment B raw1991 raw1991Labels = mixedMoment B raw1991step0 raw1991step0Labels := by
      have ha : raw1991step0 = (fun i j => raw1991 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1991step0 raw1991; decide +kernel
      have hl : raw1991step0Labels = raw1991Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1991 raw1991Labels permutation152 permutation6
    mixedMoment B raw1991step0 raw1991step0Labels = mixedMoment B raw1991step1 raw1991step1Labels := by
      have ha : raw1991step1 = -raw1991step0 := by apply Matrix.ext; change ∀ i j, raw1991step1 i j = -(raw1991step0 i j); unfold raw1991step1 raw1991step0; decide +kernel
      have hl : raw1991step1Labels = raw1991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1991step1 raw1991step1Labels = mixedMoment B raw1991step2 raw1991step2Labels := by
      have ha : raw1991step2 = raw1991step1 := by apply Matrix.ext; unfold raw1991step2 raw1991step1; decide +kernel
      have hl : raw1991step1Labels = labelEmbedding1 ∘ raw1991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1991step1 raw1991step1Labels raw1991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3334 node3334Labels := by rfl

theorem canonical1995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1995 raw1995Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw1995 raw1995Labels = mixedMoment B raw1995step0 raw1995step0Labels := by
      have ha : raw1995step0 = (fun i j => raw1995 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1995step0 raw1995; decide +kernel
      have hl : raw1995step0Labels = raw1995Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1995 raw1995Labels permutation152 permutation4
    mixedMoment B raw1995step0 raw1995step0Labels = mixedMoment B raw1995step1 raw1995step1Labels := by
      have ha : raw1995step1 = raw1995step0 := by apply Matrix.ext; unfold raw1995step1 raw1995step0; decide +kernel
      have hl : raw1995step0Labels = labelEmbedding7 ∘ raw1995step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1995step0 raw1995step0Labels raw1995step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1996 raw1996Labels = mixedMoment B node2372 node2372Labels := by
  calc
    mixedMoment B raw1996 raw1996Labels = mixedMoment B raw1996step0 raw1996step0Labels := by
      have ha : raw1996step0 = (fun i j => raw1996 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1996step0 raw1996; decide +kernel
      have hl : raw1996step0Labels = raw1996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1996 raw1996Labels permutation152 permutation4
    _ = mixedMoment B node2372 node2372Labels := by rfl

theorem canonical1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1997 raw1997Labels = mixedMoment B node3336 node3336Labels := by
  calc
    mixedMoment B raw1997 raw1997Labels = mixedMoment B raw1997step0 raw1997step0Labels := by
      have ha : raw1997step0 = (fun i j => raw1997 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1997step0 raw1997; decide +kernel
      have hl : raw1997step0Labels = raw1997Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1997 raw1997Labels permutation152 permutation6
    mixedMoment B raw1997step0 raw1997step0Labels = mixedMoment B raw1997step1 raw1997step1Labels := by
      have ha : raw1997step1 = -raw1997step0 := by apply Matrix.ext; change ∀ i j, raw1997step1 i j = -(raw1997step0 i j); unfold raw1997step1 raw1997step0; decide +kernel
      have hl : raw1997step1Labels = raw1997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1997step1 raw1997step1Labels = mixedMoment B raw1997step2 raw1997step2Labels := by
      have ha : raw1997step2 = raw1997step1 := by apply Matrix.ext; unfold raw1997step2 raw1997step1; decide +kernel
      have hl : raw1997step1Labels = labelEmbedding1 ∘ raw1997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1997step1 raw1997step1Labels raw1997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3336 node3336Labels := by rfl

theorem canonical2007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2007 raw2007Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw2007 raw2007Labels = mixedMoment B raw2007step0 raw2007step0Labels := by
      have ha : raw2007step0 = (fun i j => raw2007 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2007step0 raw2007; decide +kernel
      have hl : raw2007step0Labels = raw2007Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2007 raw2007Labels permutation152 permutation4
    mixedMoment B raw2007step0 raw2007step0Labels = mixedMoment B raw2007step1 raw2007step1Labels := by
      have ha : raw2007step1 = raw2007step0 := by apply Matrix.ext; unfold raw2007step1 raw2007step0; decide +kernel
      have hl : raw2007step0Labels = labelEmbedding7 ∘ raw2007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2007step0 raw2007step0Labels raw2007step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical2008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2008 raw2008Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw2008 raw2008Labels = mixedMoment B raw2008step0 raw2008step0Labels := by
      have ha : raw2008step0 = (fun i j => raw2008 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2008step0 raw2008; decide +kernel
      have hl : raw2008step0Labels = raw2008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2008 raw2008Labels permutation152 permutation4
    _ = mixedMoment B node2382 node2382Labels := by rfl

theorem canonical2009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2009 raw2009Labels = mixedMoment B node3340 node3340Labels := by
  calc
    mixedMoment B raw2009 raw2009Labels = mixedMoment B raw2009step0 raw2009step0Labels := by
      have ha : raw2009step0 = (fun i j => raw2009 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2009step0 raw2009; decide +kernel
      have hl : raw2009step0Labels = raw2009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2009 raw2009Labels permutation158 permutation6
    mixedMoment B raw2009step0 raw2009step0Labels = mixedMoment B raw2009step1 raw2009step1Labels := by
      have ha : raw2009step1 = -raw2009step0 := by apply Matrix.ext; change ∀ i j, raw2009step1 i j = -(raw2009step0 i j); unfold raw2009step1 raw2009step0; decide +kernel
      have hl : raw2009step1Labels = raw2009step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2009step1 raw2009step1Labels = mixedMoment B raw2009step2 raw2009step2Labels := by
      have ha : raw2009step2 = raw2009step1 := by apply Matrix.ext; unfold raw2009step2 raw2009step1; decide +kernel
      have hl : raw2009step1Labels = labelEmbedding1 ∘ raw2009step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2009step1 raw2009step1Labels raw2009step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3340 node3340Labels := by rfl

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

theorem canonical2160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2160 raw2160Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw2160 raw2160Labels = mixedMoment B raw2160step0 raw2160step0Labels := by
      have ha : raw2160step0 = (fun i j => raw2160 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2160step0 raw2160; decide +kernel
      have hl : raw2160step0Labels = raw2160Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2160 raw2160Labels permutation152 permutation4
    mixedMoment B raw2160step0 raw2160step0Labels = mixedMoment B raw2160step1 raw2160step1Labels := by
      have ha : raw2160step1 = raw2160step0 := by apply Matrix.ext; unfold raw2160step1 raw2160step0; decide +kernel
      have hl : raw2160step0Labels = labelEmbedding7 ∘ raw2160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2160step0 raw2160step0Labels raw2160step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5126 node5126Labels := by rfl

theorem canonical2161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2161 raw2161Labels = mixedMoment B node2541 node2541Labels := by
  calc
    mixedMoment B raw2161 raw2161Labels = mixedMoment B raw2161step0 raw2161step0Labels := by
      have ha : raw2161step0 = (fun i j => raw2161 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2161step0 raw2161; decide +kernel
      have hl : raw2161step0Labels = raw2161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2161 raw2161Labels permutation152 permutation4
    _ = mixedMoment B node2541 node2541Labels := by rfl

theorem canonical2162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2162 raw2162Labels = mixedMoment B node3487 node3487Labels := by
  calc
    mixedMoment B raw2162 raw2162Labels = mixedMoment B raw2162step0 raw2162step0Labels := by
      have ha : raw2162step0 = (fun i j => raw2162 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2162step0 raw2162; decide +kernel
      have hl : raw2162step0Labels = raw2162Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2162 raw2162Labels permutation182 permutation6
    mixedMoment B raw2162step0 raw2162step0Labels = mixedMoment B raw2162step1 raw2162step1Labels := by
      have ha : raw2162step1 = -raw2162step0 := by apply Matrix.ext; change ∀ i j, raw2162step1 i j = -(raw2162step0 i j); unfold raw2162step1 raw2162step0; decide +kernel
      have hl : raw2162step1Labels = raw2162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2162step1 raw2162step1Labels = mixedMoment B raw2162step2 raw2162step2Labels := by
      have ha : raw2162step2 = raw2162step1 := by apply Matrix.ext; unfold raw2162step2 raw2162step1; decide +kernel
      have hl : raw2162step1Labels = labelEmbedding1 ∘ raw2162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2162step1 raw2162step1Labels raw2162step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3487 node3487Labels := by rfl

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

theorem canonical2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2166 raw2166Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw2166 raw2166Labels = mixedMoment B raw2166step0 raw2166step0Labels := by
      have ha : raw2166step0 = (fun i j => raw2166 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2166step0 raw2166; decide +kernel
      have hl : raw2166step0Labels = raw2166Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2166 raw2166Labels permutation152 permutation4
    mixedMoment B raw2166step0 raw2166step0Labels = mixedMoment B raw2166step1 raw2166step1Labels := by
      have ha : raw2166step1 = raw2166step0 := by apply Matrix.ext; unfold raw2166step1 raw2166step0; decide +kernel
      have hl : raw2166step0Labels = labelEmbedding7 ∘ raw2166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2166step0 raw2166step0Labels raw2166step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2167 raw2167Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw2167 raw2167Labels = mixedMoment B raw2167step0 raw2167step0Labels := by
      have ha : raw2167step0 = (fun i j => raw2167 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2167step0 raw2167; decide +kernel
      have hl : raw2167step0Labels = raw2167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2167 raw2167Labels permutation152 permutation4
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2168 raw2168Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw2168 raw2168Labels = mixedMoment B raw2168step0 raw2168step0Labels := by
      have ha : raw2168step0 = (fun i j => raw2168 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2168step0 raw2168; decide +kernel
      have hl : raw2168step0Labels = raw2168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2168 raw2168Labels permutation176 permutation6
    mixedMoment B raw2168step0 raw2168step0Labels = mixedMoment B raw2168step1 raw2168step1Labels := by
      have ha : raw2168step1 = -raw2168step0 := by apply Matrix.ext; change ∀ i j, raw2168step1 i j = -(raw2168step0 i j); unfold raw2168step1 raw2168step0; decide +kernel
      have hl : raw2168step1Labels = raw2168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2168step1 raw2168step1Labels = mixedMoment B raw2168step2 raw2168step2Labels := by
      have ha : raw2168step2 = raw2168step1 := by apply Matrix.ext; unfold raw2168step2 raw2168step1; decide +kernel
      have hl : raw2168step1Labels = labelEmbedding1 ∘ raw2168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2168step1 raw2168step1Labels raw2168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

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

theorem canonical2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2259 raw2259Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw2259 raw2259Labels = mixedMoment B raw2259step0 raw2259step0Labels := by
      have ha : raw2259step0 = (fun i j => raw2259 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2259step0 raw2259; decide +kernel
      have hl : raw2259step0Labels = raw2259Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2259 raw2259Labels permutation152 permutation4
    mixedMoment B raw2259step0 raw2259step0Labels = mixedMoment B raw2259step1 raw2259step1Labels := by
      have ha : raw2259step1 = raw2259step0 := by apply Matrix.ext; unfold raw2259step1 raw2259step0; decide +kernel
      have hl : raw2259step0Labels = labelEmbedding7 ∘ raw2259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2259step0 raw2259step0Labels raw2259step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2260 raw2260Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw2260 raw2260Labels = mixedMoment B raw2260step0 raw2260step0Labels := by
      have ha : raw2260step0 = (fun i j => raw2260 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2260step0 raw2260; decide +kernel
      have hl : raw2260step0Labels = raw2260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2260 raw2260Labels permutation152 permutation4
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2261 raw2261Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw2261 raw2261Labels = mixedMoment B raw2261step0 raw2261step0Labels := by
      have ha : raw2261step0 = (fun i j => raw2261 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2261step0 raw2261; decide +kernel
      have hl : raw2261step0Labels = raw2261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2261 raw2261Labels permutation152 permutation6
    mixedMoment B raw2261step0 raw2261step0Labels = mixedMoment B raw2261step1 raw2261step1Labels := by
      have ha : raw2261step1 = -raw2261step0 := by apply Matrix.ext; change ∀ i j, raw2261step1 i j = -(raw2261step0 i j); unfold raw2261step1 raw2261step0; decide +kernel
      have hl : raw2261step1Labels = raw2261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2261step1 raw2261step1Labels = mixedMoment B raw2261step2 raw2261step2Labels := by
      have ha : raw2261step2 = raw2261step1 := by apply Matrix.ext; unfold raw2261step2 raw2261step1; decide +kernel
      have hl : raw2261step1Labels = labelEmbedding1 ∘ raw2261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2261step1 raw2261step1Labels raw2261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3493 node3493Labels := by rfl

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2460 raw2460Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw2460 raw2460Labels = mixedMoment B raw2460step0 raw2460step0Labels := by
      have ha : raw2460step0 = (fun i j => raw2460 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2460step0 raw2460; decide +kernel
      have hl : raw2460step0Labels = raw2460Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2460 raw2460Labels permutation152 permutation4
    mixedMoment B raw2460step0 raw2460step0Labels = mixedMoment B raw2460step1 raw2460step1Labels := by
      have ha : raw2460step1 = raw2460step0 := by apply Matrix.ext; unfold raw2460step1 raw2460step0; decide +kernel
      have hl : raw2460step0Labels = labelEmbedding7 ∘ raw2460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2460step0 raw2460step0Labels raw2460step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2461 raw2461Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw2461 raw2461Labels = mixedMoment B raw2461step0 raw2461step0Labels := by
      have ha : raw2461step0 = (fun i j => raw2461 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2461step0 raw2461; decide +kernel
      have hl : raw2461step0Labels = raw2461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2461 raw2461Labels permutation152 permutation4
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2462 raw2462Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw2462 raw2462Labels = mixedMoment B raw2462step0 raw2462step0Labels := by
      have ha : raw2462step0 = (fun i j => raw2462 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2462step0 raw2462; decide +kernel
      have hl : raw2462step0Labels = raw2462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2462 raw2462Labels permutation152 permutation6
    mixedMoment B raw2462step0 raw2462step0Labels = mixedMoment B raw2462step1 raw2462step1Labels := by
      have ha : raw2462step1 = -raw2462step0 := by apply Matrix.ext; change ∀ i j, raw2462step1 i j = -(raw2462step0 i j); unfold raw2462step1 raw2462step0; decide +kernel
      have hl : raw2462step1Labels = raw2462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2462step1 raw2462step1Labels = mixedMoment B raw2462step2 raw2462step2Labels := by
      have ha : raw2462step2 = raw2462step1 := by apply Matrix.ext; unfold raw2462step2 raw2462step1; decide +kernel
      have hl : raw2462step1Labels = labelEmbedding1 ∘ raw2462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2462step1 raw2462step1Labels raw2462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

theorem canonical2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2463 raw2463Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw2463 raw2463Labels = mixedMoment B raw2463step0 raw2463step0Labels := by
      have ha : raw2463step0 = (fun i j => raw2463 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2463step0 raw2463; decide +kernel
      have hl : raw2463step0Labels = raw2463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2463 raw2463Labels permutation152 permutation4
    mixedMoment B raw2463step0 raw2463step0Labels = mixedMoment B raw2463step1 raw2463step1Labels := by
      have ha : raw2463step1 = raw2463step0 := by apply Matrix.ext; unfold raw2463step1 raw2463step0; decide +kernel
      have hl : raw2463step0Labels = labelEmbedding7 ∘ raw2463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2463step0 raw2463step0Labels raw2463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical2464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2464 raw2464Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw2464 raw2464Labels = mixedMoment B raw2464step0 raw2464step0Labels := by
      have ha : raw2464step0 = (fun i j => raw2464 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2464step0 raw2464; decide +kernel
      have hl : raw2464step0Labels = raw2464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2464 raw2464Labels permutation152 permutation4
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2465 raw2465Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw2465 raw2465Labels = mixedMoment B raw2465step0 raw2465step0Labels := by
      have ha : raw2465step0 = (fun i j => raw2465 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2465step0 raw2465; decide +kernel
      have hl : raw2465step0Labels = raw2465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2465 raw2465Labels permutation153 permutation6
    mixedMoment B raw2465step0 raw2465step0Labels = mixedMoment B raw2465step1 raw2465step1Labels := by
      have ha : raw2465step1 = -raw2465step0 := by apply Matrix.ext; change ∀ i j, raw2465step1 i j = -(raw2465step0 i j); unfold raw2465step1 raw2465step0; decide +kernel
      have hl : raw2465step1Labels = raw2465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2465step1 raw2465step1Labels = mixedMoment B raw2465step2 raw2465step2Labels := by
      have ha : raw2465step2 = raw2465step1 := by apply Matrix.ext; unfold raw2465step2 raw2465step1; decide +kernel
      have hl : raw2465step1Labels = labelEmbedding1 ∘ raw2465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2465step1 raw2465step1Labels raw2465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical2484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2484 raw2484Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw2484 raw2484Labels = mixedMoment B raw2484step0 raw2484step0Labels := by
      have ha : raw2484step0 = (fun i j => raw2484 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2484step0 raw2484; decide +kernel
      have hl : raw2484step0Labels = raw2484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2484 raw2484Labels permutation152 permutation4
    mixedMoment B raw2484step0 raw2484step0Labels = mixedMoment B raw2484step1 raw2484step1Labels := by
      have ha : raw2484step1 = raw2484step0 := by apply Matrix.ext; unfold raw2484step1 raw2484step0; decide +kernel
      have hl : raw2484step0Labels = labelEmbedding7 ∘ raw2484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2484step0 raw2484step0Labels raw2484step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2485 raw2485Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw2485 raw2485Labels = mixedMoment B raw2485step0 raw2485step0Labels := by
      have ha : raw2485step0 = (fun i j => raw2485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2485step0 raw2485; decide +kernel
      have hl : raw2485step0Labels = raw2485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2485 raw2485Labels permutation152 permutation4
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2486 raw2486Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw2486 raw2486Labels = mixedMoment B raw2486step0 raw2486step0Labels := by
      have ha : raw2486step0 = (fun i j => raw2486 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2486step0 raw2486; decide +kernel
      have hl : raw2486step0Labels = raw2486Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2486 raw2486Labels permutation164 permutation6
    mixedMoment B raw2486step0 raw2486step0Labels = mixedMoment B raw2486step1 raw2486step1Labels := by
      have ha : raw2486step1 = -raw2486step0 := by apply Matrix.ext; change ∀ i j, raw2486step1 i j = -(raw2486step0 i j); unfold raw2486step1 raw2486step0; decide +kernel
      have hl : raw2486step1Labels = raw2486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2486step1 raw2486step1Labels = mixedMoment B raw2486step2 raw2486step2Labels := by
      have ha : raw2486step2 = raw2486step1 := by apply Matrix.ext; unfold raw2486step2 raw2486step1; decide +kernel
      have hl : raw2486step1Labels = labelEmbedding1 ∘ raw2486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2486step1 raw2486step1Labels raw2486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

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

theorem canonical32966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32966 raw32966Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw32966 raw32966Labels = mixedMoment B raw32966step0 raw32966step0Labels := by
      have ha : raw32966step0 = (fun i j => raw32966 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32966step0 raw32966; decide +kernel
      have hl : raw32966step0Labels = raw32966Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32966 raw32966Labels permutation663 permutation3
    mixedMoment B raw32966step0 raw32966step0Labels = mixedMoment B raw32966step1 raw32966step1Labels := by
      have ha : raw32966step1 = -raw32966step0 := by apply Matrix.ext; change ∀ i j, raw32966step1 i j = -(raw32966step0 i j); unfold raw32966step1 raw32966step0; decide +kernel
      have hl : raw32966step1Labels = raw32966step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32966step1 raw32966step1Labels = mixedMoment B raw32966step2 raw32966step2Labels := by
      have ha : raw32966step2 = raw32966step1 := by apply Matrix.ext; unfold raw32966step2 raw32966step1; decide +kernel
      have hl : raw32966step1Labels = labelEmbedding6 ∘ raw32966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32966step1 raw32966step1Labels raw32966step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical32967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32967 raw32967Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw32967 raw32967Labels = mixedMoment B raw32967step0 raw32967step0Labels := by
      have ha : raw32967step0 = (fun i j => raw32967 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32967step0 raw32967; decide +kernel
      have hl : raw32967step0Labels = raw32967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32967 raw32967Labels permutation662 permutation3
    mixedMoment B raw32967step0 raw32967step0Labels = mixedMoment B raw32967step1 raw32967step1Labels := by
      have ha : raw32967step1 = -raw32967step0 := by apply Matrix.ext; change ∀ i j, raw32967step1 i j = -(raw32967step0 i j); unfold raw32967step1 raw32967step0; decide +kernel
      have hl : raw32967step1Labels = raw32967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32967step1 raw32967step1Labels = mixedMoment B raw32967step2 raw32967step2Labels := by
      have ha : raw32967step2 = raw32967step1 := by apply Matrix.ext; unfold raw32967step2 raw32967step1; decide +kernel
      have hl : raw32967step1Labels = labelEmbedding6 ∘ raw32967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32967step1 raw32967step1Labels raw32967step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical32968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32968 raw32968Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw32968 raw32968Labels = mixedMoment B raw32968step0 raw32968step0Labels := by
      have hz : ∀ j, raw32968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32968step0 = (fun i j => raw32968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32968step0 raw32968; decide +kernel
      have hl : raw32968step0Labels = raw32968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32968 raw32968Labels permutation434 hz
    mixedMoment B raw32968step0 raw32968step0Labels = mixedMoment B raw32968step1 raw32968step1Labels := by
      have ha : raw32968step1 = (fun i j => raw32968step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32968step1 raw32968step0; decide +kernel
      have hl : raw32968step1Labels = raw32968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32968step0 raw32968step0Labels permutation151 permutation3
    mixedMoment B raw32968step1 raw32968step1Labels = mixedMoment B raw32968step2 raw32968step2Labels := by
      have ha : raw32968step2 = -raw32968step1 := by apply Matrix.ext; change ∀ i j, raw32968step2 i j = -(raw32968step1 i j); unfold raw32968step2 raw32968step1; decide +kernel
      have hl : raw32968step2Labels = raw32968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32968step2 raw32968step2Labels = mixedMoment B raw32968step3 raw32968step3Labels := by
      have ha : raw32968step3 = raw32968step2 := by apply Matrix.ext; unfold raw32968step3 raw32968step2; decide +kernel
      have hl : raw32968step2Labels = labelEmbedding6 ∘ raw32968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32968step2 raw32968step2Labels raw32968step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical32969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32969 raw32969Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw32969 raw32969Labels = mixedMoment B raw32969step0 raw32969step0Labels := by
      have ha : raw32969step0 = (fun i j => raw32969 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32969step0 raw32969; decide +kernel
      have hl : raw32969step0Labels = raw32969Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32969 raw32969Labels permutation658 permutation3
    mixedMoment B raw32969step0 raw32969step0Labels = mixedMoment B raw32969step1 raw32969step1Labels := by
      have ha : raw32969step1 = -raw32969step0 := by apply Matrix.ext; change ∀ i j, raw32969step1 i j = -(raw32969step0 i j); unfold raw32969step1 raw32969step0; decide +kernel
      have hl : raw32969step1Labels = raw32969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32969step1 raw32969step1Labels = mixedMoment B raw32969step2 raw32969step2Labels := by
      have ha : raw32969step2 = raw32969step1 := by apply Matrix.ext; unfold raw32969step2 raw32969step1; decide +kernel
      have hl : raw32969step1Labels = labelEmbedding6 ∘ raw32969step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32969step1 raw32969step1Labels raw32969step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical32970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32970 raw32970Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw32970 raw32970Labels = mixedMoment B raw32970step0 raw32970step0Labels := by
      have ha : raw32970step0 = (fun i j => raw32970 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32970step0 raw32970; decide +kernel
      have hl : raw32970step0Labels = raw32970Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32970 raw32970Labels permutation153 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical32971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32971 raw32971Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw32971 raw32971Labels = mixedMoment B raw32971step0 raw32971step0Labels := by
      have ha : raw32971step0 = (fun i j => raw32971 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32971step0 raw32971; decide +kernel
      have hl : raw32971step0Labels = raw32971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32971 raw32971Labels permutation178 permutation3
    mixedMoment B raw32971step0 raw32971step0Labels = mixedMoment B raw32971step1 raw32971step1Labels := by
      have ha : raw32971step1 = raw32971step0 := by apply Matrix.ext; unfold raw32971step1 raw32971step0; decide +kernel
      have hl : raw32971step0Labels = labelEmbedding6 ∘ raw32971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32971step0 raw32971step0Labels raw32971step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

theorem canonical32972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32972 raw32972Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw32972 raw32972Labels = mixedMoment B raw32972step0 raw32972step0Labels := by
      have ha : raw32972step0 = (fun i j => raw32972 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32972step0 raw32972; decide +kernel
      have hl : raw32972step0Labels = raw32972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32972 raw32972Labels permutation178 permutation3
    mixedMoment B raw32972step0 raw32972step0Labels = mixedMoment B raw32972step1 raw32972step1Labels := by
      have ha : raw32972step1 = raw32972step0 := by apply Matrix.ext; unfold raw32972step1 raw32972step0; decide +kernel
      have hl : raw32972step0Labels = labelEmbedding6 ∘ raw32972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32972step0 raw32972step0Labels raw32972step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical32973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32973 raw32973Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw32973 raw32973Labels = mixedMoment B raw32973step0 raw32973step0Labels := by
      have hz : ∀ j, raw32973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32973step0 = (fun i j => raw32973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32973step0 raw32973; decide +kernel
      have hl : raw32973step0Labels = raw32973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32973 raw32973Labels permutation434 hz
    mixedMoment B raw32973step0 raw32973step0Labels = mixedMoment B raw32973step1 raw32973step1Labels := by
      have ha : raw32973step1 = (fun i j => raw32973step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32973step1 raw32973step0; decide +kernel
      have hl : raw32973step1Labels = raw32973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32973step0 raw32973step0Labels permutation38 permutation3
    mixedMoment B raw32973step1 raw32973step1Labels = mixedMoment B raw32973step2 raw32973step2Labels := by
      have ha : raw32973step2 = raw32973step1 := by apply Matrix.ext; unfold raw32973step2 raw32973step1; decide +kernel
      have hl : raw32973step1Labels = labelEmbedding6 ∘ raw32973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32973step1 raw32973step1Labels raw32973step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical32974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32974 raw32974Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw32974 raw32974Labels = mixedMoment B raw32974step0 raw32974step0Labels := by
      have ha : raw32974step0 = (fun i j => raw32974 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32974step0 raw32974; decide +kernel
      have hl : raw32974step0Labels = raw32974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32974 raw32974Labels permutation188 permutation3
    mixedMoment B raw32974step0 raw32974step0Labels = mixedMoment B raw32974step1 raw32974step1Labels := by
      have ha : raw32974step1 = raw32974step0 := by apply Matrix.ext; unfold raw32974step1 raw32974step0; decide +kernel
      have hl : raw32974step0Labels = labelEmbedding6 ∘ raw32974step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32974step0 raw32974step0Labels raw32974step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical32975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32975 raw32975Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw32975 raw32975Labels = mixedMoment B raw32975step0 raw32975step0Labels := by
      have ha : raw32975step0 = (fun i j => raw32975 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32975step0 raw32975; decide +kernel
      have hl : raw32975step0Labels = raw32975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32975 raw32975Labels permutation178 permutation3
    mixedMoment B raw32975step0 raw32975step0Labels = mixedMoment B raw32975step1 raw32975step1Labels := by
      have ha : raw32975step1 = raw32975step0 := by apply Matrix.ext; unfold raw32975step1 raw32975step0; decide +kernel
      have hl : raw32975step0Labels = labelEmbedding6 ∘ raw32975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32975step0 raw32975step0Labels raw32975step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical32976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32976 raw32976Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw32976 raw32976Labels = mixedMoment B raw32976step0 raw32976step0Labels := by
      have ha : raw32976step0 = (fun i j => raw32976 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32976step0 raw32976; decide +kernel
      have hl : raw32976step0Labels = raw32976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32976 raw32976Labels permutation154 permutation3
    mixedMoment B raw32976step0 raw32976step0Labels = mixedMoment B raw32976step1 raw32976step1Labels := by
      have ha : raw32976step1 = raw32976step0 := by apply Matrix.ext; unfold raw32976step1 raw32976step0; decide +kernel
      have hl : raw32976step0Labels = labelEmbedding6 ∘ raw32976step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32976step0 raw32976step0Labels raw32976step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical32977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32977 raw32977Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw32977 raw32977Labels = mixedMoment B raw32977step0 raw32977step0Labels := by
      have ha : raw32977step0 = (fun i j => raw32977 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32977step0 raw32977; decide +kernel
      have hl : raw32977step0Labels = raw32977Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32977 raw32977Labels permutation154 permutation3
    mixedMoment B raw32977step0 raw32977step0Labels = mixedMoment B raw32977step1 raw32977step1Labels := by
      have ha : raw32977step1 = raw32977step0 := by apply Matrix.ext; unfold raw32977step1 raw32977step0; decide +kernel
      have hl : raw32977step0Labels = labelEmbedding6 ∘ raw32977step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32977step0 raw32977step0Labels raw32977step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical32978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32978 raw32978Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32978 raw32978Labels = mixedMoment B raw32978step0 raw32978step0Labels := by
      have hz : ∀ j, raw32978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32978step0 = (fun i j => raw32978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32978step0 raw32978; decide +kernel
      have hl : raw32978step0Labels = raw32978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32978 raw32978Labels permutation434 hz
    mixedMoment B raw32978step0 raw32978step0Labels = mixedMoment B raw32978step1 raw32978step1Labels := by
      have ha : raw32978step1 = (fun i j => raw32978step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32978step1 raw32978step0; decide +kernel
      have hl : raw32978step1Labels = raw32978step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32978step0 raw32978step0Labels permutation32 permutation3
    mixedMoment B raw32978step1 raw32978step1Labels = mixedMoment B raw32978step2 raw32978step2Labels := by
      have ha : raw32978step2 = raw32978step1 := by apply Matrix.ext; unfold raw32978step2 raw32978step1; decide +kernel
      have hl : raw32978step1Labels = labelEmbedding6 ∘ raw32978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32978step1 raw32978step1Labels raw32978step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

theorem canonical32979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32979 raw32979Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32979 raw32979Labels = mixedMoment B raw32979step0 raw32979step0Labels := by
      have ha : raw32979step0 = (fun i j => raw32979 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32979step0 raw32979; decide +kernel
      have hl : raw32979step0Labels = raw32979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32979 raw32979Labels permutation164 permutation3
    mixedMoment B raw32979step0 raw32979step0Labels = mixedMoment B raw32979step1 raw32979step1Labels := by
      have ha : raw32979step1 = raw32979step0 := by apply Matrix.ext; unfold raw32979step1 raw32979step0; decide +kernel
      have hl : raw32979step0Labels = labelEmbedding6 ∘ raw32979step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32979step0 raw32979step0Labels raw32979step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical32980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32980 raw32980Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw32980 raw32980Labels = mixedMoment B raw32980step0 raw32980step0Labels := by
      have ha : raw32980step0 = (fun i j => raw32980 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32980step0 raw32980; decide +kernel
      have hl : raw32980step0Labels = raw32980Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32980 raw32980Labels permutation154 permutation3
    mixedMoment B raw32980step0 raw32980step0Labels = mixedMoment B raw32980step1 raw32980step1Labels := by
      have ha : raw32980step1 = raw32980step0 := by apply Matrix.ext; unfold raw32980step1 raw32980step0; decide +kernel
      have hl : raw32980step0Labels = labelEmbedding6 ∘ raw32980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32980step0 raw32980step0Labels raw32980step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

theorem canonical32981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32981 raw32981Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw32981 raw32981Labels = mixedMoment B raw32981step0 raw32981step0Labels := by
      have ha : raw32981step0 = (fun i j => raw32981 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32981step0 raw32981; decide +kernel
      have hl : raw32981step0Labels = raw32981Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32981 raw32981Labels permutation154 permutation3
    mixedMoment B raw32981step0 raw32981step0Labels = mixedMoment B raw32981step1 raw32981step1Labels := by
      have ha : raw32981step1 = raw32981step0 := by apply Matrix.ext; unfold raw32981step1 raw32981step0; decide +kernel
      have hl : raw32981step0Labels = labelEmbedding6 ∘ raw32981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32981step0 raw32981step0Labels raw32981step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4321 node4321Labels := by rfl

theorem canonical32982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32982 raw32982Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw32982 raw32982Labels = mixedMoment B raw32982step0 raw32982step0Labels := by
      have ha : raw32982step0 = (fun i j => raw32982 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32982step0 raw32982; decide +kernel
      have hl : raw32982step0Labels = raw32982Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32982 raw32982Labels permutation154 permutation3
    mixedMoment B raw32982step0 raw32982step0Labels = mixedMoment B raw32982step1 raw32982step1Labels := by
      have ha : raw32982step1 = raw32982step0 := by apply Matrix.ext; unfold raw32982step1 raw32982step0; decide +kernel
      have hl : raw32982step0Labels = labelEmbedding6 ∘ raw32982step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32982step0 raw32982step0Labels raw32982step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4926 node4926Labels := by rfl

theorem canonical32983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32983 raw32983Labels = mixedMoment B node4985 node4985Labels := by
  calc
    mixedMoment B raw32983 raw32983Labels = mixedMoment B raw32983step0 raw32983step0Labels := by
      have ha : raw32983step0 = (fun i j => raw32983 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32983step0 raw32983; decide +kernel
      have hl : raw32983step0Labels = raw32983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32983 raw32983Labels permutation178 permutation3
    mixedMoment B raw32983step0 raw32983step0Labels = mixedMoment B raw32983step1 raw32983step1Labels := by
      have ha : raw32983step1 = raw32983step0 := by apply Matrix.ext; unfold raw32983step1 raw32983step0; decide +kernel
      have hl : raw32983step0Labels = labelEmbedding6 ∘ raw32983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32983step0 raw32983step0Labels raw32983step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4985 node4985Labels := by rfl

theorem canonical32984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32984 raw32984Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw32984 raw32984Labels = mixedMoment B raw32984step0 raw32984step0Labels := by
      have ha : raw32984step0 = (fun i j => raw32984 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32984step0 raw32984; decide +kernel
      have hl : raw32984step0Labels = raw32984Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32984 raw32984Labels permutation154 permutation3
    mixedMoment B raw32984step0 raw32984step0Labels = mixedMoment B raw32984step1 raw32984step1Labels := by
      have ha : raw32984step1 = raw32984step0 := by apply Matrix.ext; unfold raw32984step1 raw32984step0; decide +kernel
      have hl : raw32984step0Labels = labelEmbedding6 ∘ raw32984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32984step0 raw32984step0Labels raw32984step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5126 node5126Labels := by rfl

theorem canonical32985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32985 raw32985Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32985 raw32985Labels = mixedMoment B raw32985step0 raw32985step0Labels := by
      have ha : raw32985step0 = (fun i j => raw32985 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32985step0 raw32985; decide +kernel
      have hl : raw32985step0Labels = raw32985Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32985 raw32985Labels permutation155 permutation3
    mixedMoment B raw32985step0 raw32985step0Labels = mixedMoment B raw32985step1 raw32985step1Labels := by
      have ha : raw32985step1 = raw32985step0 := by apply Matrix.ext; unfold raw32985step1 raw32985step0; decide +kernel
      have hl : raw32985step0Labels = labelEmbedding6 ∘ raw32985step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32985step0 raw32985step0Labels raw32985step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical32986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32986 raw32986Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw32986 raw32986Labels = mixedMoment B raw32986step0 raw32986step0Labels := by
      have ha : raw32986step0 = (fun i j => raw32986 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32986step0 raw32986; decide +kernel
      have hl : raw32986step0Labels = raw32986Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32986 raw32986Labels permutation152 permutation3
    mixedMoment B raw32986step0 raw32986step0Labels = mixedMoment B raw32986step1 raw32986step1Labels := by
      have ha : raw32986step1 = raw32986step0 := by apply Matrix.ext; unfold raw32986step1 raw32986step0; decide +kernel
      have hl : raw32986step0Labels = labelEmbedding6 ∘ raw32986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32986step0 raw32986step0Labels raw32986step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical32987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32987 raw32987Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw32987 raw32987Labels = mixedMoment B raw32987step0 raw32987step0Labels := by
      have ha : raw32987step0 = (fun i j => raw32987 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32987step0 raw32987; decide +kernel
      have hl : raw32987step0Labels = raw32987Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32987 raw32987Labels permutation152 permutation3
    mixedMoment B raw32987step0 raw32987step0Labels = mixedMoment B raw32987step1 raw32987step1Labels := by
      have ha : raw32987step1 = raw32987step0 := by apply Matrix.ext; unfold raw32987step1 raw32987step0; decide +kernel
      have hl : raw32987step0Labels = labelEmbedding6 ∘ raw32987step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32987step0 raw32987step0Labels raw32987step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical32988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32988 raw32988Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw32988 raw32988Labels = mixedMoment B raw32988step0 raw32988step0Labels := by
      have ha : raw32988step0 = (fun i j => raw32988 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32988step0 raw32988; decide +kernel
      have hl : raw32988step0Labels = raw32988Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32988 raw32988Labels permutation176 permutation3
    mixedMoment B raw32988step0 raw32988step0Labels = mixedMoment B raw32988step1 raw32988step1Labels := by
      have ha : raw32988step1 = raw32988step0 := by apply Matrix.ext; unfold raw32988step1 raw32988step0; decide +kernel
      have hl : raw32988step0Labels = labelEmbedding6 ∘ raw32988step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32988step0 raw32988step0Labels raw32988step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical32989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32989 raw32989Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32989 raw32989Labels = mixedMoment B raw32989step0 raw32989step0Labels := by
      have hz : ∀ j, raw32989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32989step0 = (fun i j => raw32989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32989step0 raw32989; decide +kernel
      have hl : raw32989step0Labels = raw32989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32989 raw32989Labels permutation434 hz
    mixedMoment B raw32989step0 raw32989step0Labels = mixedMoment B raw32989step1 raw32989step1Labels := by
      have ha : raw32989step1 = (fun i j => raw32989step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32989step1 raw32989step0; decide +kernel
      have hl : raw32989step1Labels = raw32989step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32989step0 raw32989step0Labels permutation32 permutation3
    mixedMoment B raw32989step1 raw32989step1Labels = mixedMoment B raw32989step2 raw32989step2Labels := by
      have ha : raw32989step2 = raw32989step1 := by apply Matrix.ext; unfold raw32989step2 raw32989step1; decide +kernel
      have hl : raw32989step1Labels = labelEmbedding6 ∘ raw32989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32989step1 raw32989step1Labels raw32989step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical32990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32990 raw32990Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw32990 raw32990Labels = mixedMoment B raw32990step0 raw32990step0Labels := by
      have ha : raw32990step0 = (fun i j => raw32990 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32990step0 raw32990; decide +kernel
      have hl : raw32990step0Labels = raw32990Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32990 raw32990Labels permutation153 permutation3
    mixedMoment B raw32990step0 raw32990step0Labels = mixedMoment B raw32990step1 raw32990step1Labels := by
      have ha : raw32990step1 = raw32990step0 := by apply Matrix.ext; unfold raw32990step1 raw32990step0; decide +kernel
      have hl : raw32990step0Labels = labelEmbedding6 ∘ raw32990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32990step0 raw32990step0Labels raw32990step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical32991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32991 raw32991Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw32991 raw32991Labels = mixedMoment B raw32991step0 raw32991step0Labels := by
      have ha : raw32991step0 = (fun i j => raw32991 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32991step0 raw32991; decide +kernel
      have hl : raw32991step0Labels = raw32991Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32991 raw32991Labels permutation154 permutation3
    mixedMoment B raw32991step0 raw32991step0Labels = mixedMoment B raw32991step1 raw32991step1Labels := by
      have ha : raw32991step1 = raw32991step0 := by apply Matrix.ext; unfold raw32991step1 raw32991step0; decide +kernel
      have hl : raw32991step0Labels = labelEmbedding6 ∘ raw32991step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32991step0 raw32991step0Labels raw32991step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4320 node4320Labels := by rfl

theorem canonical32992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32992 raw32992Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw32992 raw32992Labels = mixedMoment B raw32992step0 raw32992step0Labels := by
      have ha : raw32992step0 = (fun i j => raw32992 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32992step0 raw32992; decide +kernel
      have hl : raw32992step0Labels = raw32992Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32992 raw32992Labels permutation664 permutation3
    mixedMoment B raw32992step0 raw32992step0Labels = mixedMoment B raw32992step1 raw32992step1Labels := by
      have ha : raw32992step1 = -raw32992step0 := by apply Matrix.ext; change ∀ i j, raw32992step1 i j = -(raw32992step0 i j); unfold raw32992step1 raw32992step0; decide +kernel
      have hl : raw32992step1Labels = raw32992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32992step1 raw32992step1Labels = mixedMoment B raw32992step2 raw32992step2Labels := by
      have ha : raw32992step2 = raw32992step1 := by apply Matrix.ext; unfold raw32992step2 raw32992step1; decide +kernel
      have hl : raw32992step1Labels = labelEmbedding6 ∘ raw32992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32992step1 raw32992step1Labels raw32992step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

theorem canonical32993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32993 raw32993Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw32993 raw32993Labels = mixedMoment B raw32993step0 raw32993step0Labels := by
      have ha : raw32993step0 = (fun i j => raw32993 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32993step0 raw32993; decide +kernel
      have hl : raw32993step0Labels = raw32993Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32993 raw32993Labels permutation662 permutation3
    mixedMoment B raw32993step0 raw32993step0Labels = mixedMoment B raw32993step1 raw32993step1Labels := by
      have ha : raw32993step1 = -raw32993step0 := by apply Matrix.ext; change ∀ i j, raw32993step1 i j = -(raw32993step0 i j); unfold raw32993step1 raw32993step0; decide +kernel
      have hl : raw32993step1Labels = raw32993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32993step1 raw32993step1Labels = mixedMoment B raw32993step2 raw32993step2Labels := by
      have ha : raw32993step2 = raw32993step1 := by apply Matrix.ext; unfold raw32993step2 raw32993step1; decide +kernel
      have hl : raw32993step1Labels = labelEmbedding6 ∘ raw32993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32993step1 raw32993step1Labels raw32993step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

theorem canonical32994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32994 raw32994Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw32994 raw32994Labels = mixedMoment B raw32994step0 raw32994step0Labels := by
      have hz : ∀ j, raw32994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32994step0 = (fun i j => raw32994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32994step0 raw32994; decide +kernel
      have hl : raw32994step0Labels = raw32994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32994 raw32994Labels permutation434 hz
    mixedMoment B raw32994step0 raw32994step0Labels = mixedMoment B raw32994step1 raw32994step1Labels := by
      have ha : raw32994step1 = (fun i j => raw32994step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32994step1 raw32994step0; decide +kernel
      have hl : raw32994step1Labels = raw32994step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32994step0 raw32994step0Labels permutation151 permutation3
    mixedMoment B raw32994step1 raw32994step1Labels = mixedMoment B raw32994step2 raw32994step2Labels := by
      have ha : raw32994step2 = -raw32994step1 := by apply Matrix.ext; change ∀ i j, raw32994step2 i j = -(raw32994step1 i j); unfold raw32994step2 raw32994step1; decide +kernel
      have hl : raw32994step2Labels = raw32994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32994step2 raw32994step2Labels = mixedMoment B raw32994step3 raw32994step3Labels := by
      have ha : raw32994step3 = raw32994step2 := by apply Matrix.ext; unfold raw32994step3 raw32994step2; decide +kernel
      have hl : raw32994step2Labels = labelEmbedding6 ∘ raw32994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32994step2 raw32994step2Labels raw32994step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical32995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32995 raw32995Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw32995 raw32995Labels = mixedMoment B raw32995step0 raw32995step0Labels := by
      have ha : raw32995step0 = (fun i j => raw32995 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32995step0 raw32995; decide +kernel
      have hl : raw32995step0Labels = raw32995Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32995 raw32995Labels permutation658 permutation3
    mixedMoment B raw32995step0 raw32995step0Labels = mixedMoment B raw32995step1 raw32995step1Labels := by
      have ha : raw32995step1 = -raw32995step0 := by apply Matrix.ext; change ∀ i j, raw32995step1 i j = -(raw32995step0 i j); unfold raw32995step1 raw32995step0; decide +kernel
      have hl : raw32995step1Labels = raw32995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32995step1 raw32995step1Labels = mixedMoment B raw32995step2 raw32995step2Labels := by
      have ha : raw32995step2 = raw32995step1 := by apply Matrix.ext; unfold raw32995step2 raw32995step1; decide +kernel
      have hl : raw32995step1Labels = labelEmbedding6 ∘ raw32995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32995step1 raw32995step1Labels raw32995step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

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

theorem canonical1098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1098 raw1098Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw1098 raw1098Labels = mixedMoment B raw1098step0 raw1098step0Labels := by
      have ha : raw1098step0 = (fun i j => raw1098 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1098step0 raw1098; decide +kernel
      have hl : raw1098step0Labels = raw1098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1098 raw1098Labels permutation152 permutation4
    mixedMoment B raw1098step0 raw1098step0Labels = mixedMoment B raw1098step1 raw1098step1Labels := by
      have ha : raw1098step1 = raw1098step0 := by apply Matrix.ext; unfold raw1098step1 raw1098step0; decide +kernel
      have hl : raw1098step0Labels = labelEmbedding7 ∘ raw1098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1098step0 raw1098step0Labels raw1098step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4321 node4321Labels := by rfl

theorem canonical1099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1099 raw1099Labels = mixedMoment B node899 node899Labels := by
  calc
    mixedMoment B raw1099 raw1099Labels = mixedMoment B raw1099step0 raw1099step0Labels := by
      have ha : raw1099step0 = (fun i j => raw1099 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1099step0 raw1099; decide +kernel
      have hl : raw1099step0Labels = raw1099Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1099 raw1099Labels permutation152 permutation4
    _ = mixedMoment B node899 node899Labels := by rfl

theorem canonical1100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1100 raw1100Labels = mixedMoment B node1587 node1587Labels := by
  calc
    mixedMoment B raw1100 raw1100Labels = mixedMoment B raw1100step0 raw1100step0Labels := by
      have ha : raw1100step0 = (fun i j => raw1100 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1100step0 raw1100; decide +kernel
      have hl : raw1100step0Labels = raw1100Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1100 raw1100Labels permutation176 permutation6
    mixedMoment B raw1100step0 raw1100step0Labels = mixedMoment B raw1100step1 raw1100step1Labels := by
      have ha : raw1100step1 = -raw1100step0 := by apply Matrix.ext; change ∀ i j, raw1100step1 i j = -(raw1100step0 i j); unfold raw1100step1 raw1100step0; decide +kernel
      have hl : raw1100step1Labels = raw1100step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1100step1 raw1100step1Labels = mixedMoment B raw1100step2 raw1100step2Labels := by
      have ha : raw1100step2 = raw1100step1 := by apply Matrix.ext; unfold raw1100step2 raw1100step1; decide +kernel
      have hl : raw1100step1Labels = labelEmbedding1 ∘ raw1100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1100step1 raw1100step1Labels raw1100step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1587 node1587Labels := by rfl

theorem canonical1104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1104 raw1104Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw1104 raw1104Labels = mixedMoment B raw1104step0 raw1104step0Labels := by
      have ha : raw1104step0 = (fun i j => raw1104 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1104step0 raw1104; decide +kernel
      have hl : raw1104step0Labels = raw1104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1104 raw1104Labels permutation152 permutation4
    mixedMoment B raw1104step0 raw1104step0Labels = mixedMoment B raw1104step1 raw1104step1Labels := by
      have ha : raw1104step1 = raw1104step0 := by apply Matrix.ext; unfold raw1104step1 raw1104step0; decide +kernel
      have hl : raw1104step0Labels = labelEmbedding7 ∘ raw1104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1104step0 raw1104step0Labels raw1104step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical1105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1105 raw1105Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw1105 raw1105Labels = mixedMoment B raw1105step0 raw1105step0Labels := by
      have ha : raw1105step0 = (fun i j => raw1105 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1105step0 raw1105; decide +kernel
      have hl : raw1105step0Labels = raw1105Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1105 raw1105Labels permutation152 permutation4
    _ = mixedMoment B node901 node901Labels := by rfl

theorem canonical1106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1106 raw1106Labels = mixedMoment B node1589 node1589Labels := by
  calc
    mixedMoment B raw1106 raw1106Labels = mixedMoment B raw1106step0 raw1106step0Labels := by
      have ha : raw1106step0 = (fun i j => raw1106 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1106step0 raw1106; decide +kernel
      have hl : raw1106step0Labels = raw1106Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1106 raw1106Labels permutation176 permutation6
    mixedMoment B raw1106step0 raw1106step0Labels = mixedMoment B raw1106step1 raw1106step1Labels := by
      have ha : raw1106step1 = -raw1106step0 := by apply Matrix.ext; change ∀ i j, raw1106step1 i j = -(raw1106step0 i j); unfold raw1106step1 raw1106step0; decide +kernel
      have hl : raw1106step1Labels = raw1106step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1106step1 raw1106step1Labels = mixedMoment B raw1106step2 raw1106step2Labels := by
      have ha : raw1106step2 = raw1106step1 := by apply Matrix.ext; unfold raw1106step2 raw1106step1; decide +kernel
      have hl : raw1106step1Labels = labelEmbedding1 ∘ raw1106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1106step1 raw1106step1Labels raw1106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1589 node1589Labels := by rfl

theorem canonical1122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1122 raw1122Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw1122 raw1122Labels = mixedMoment B raw1122step0 raw1122step0Labels := by
      have ha : raw1122step0 = (fun i j => raw1122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1122step0 raw1122; decide +kernel
      have hl : raw1122step0Labels = raw1122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1122 raw1122Labels permutation152 permutation4
    mixedMoment B raw1122step0 raw1122step0Labels = mixedMoment B raw1122step1 raw1122step1Labels := by
      have ha : raw1122step1 = raw1122step0 := by apply Matrix.ext; unfold raw1122step1 raw1122step0; decide +kernel
      have hl : raw1122step0Labels = labelEmbedding7 ∘ raw1122step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1122step0 raw1122step0Labels raw1122step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical1123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1123 raw1123Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw1123 raw1123Labels = mixedMoment B raw1123step0 raw1123step0Labels := by
      have ha : raw1123step0 = (fun i j => raw1123 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1123step0 raw1123; decide +kernel
      have hl : raw1123step0Labels = raw1123Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1123 raw1123Labels permutation152 permutation4
    _ = mixedMoment B node919 node919Labels := by rfl

theorem canonical1124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1124 raw1124Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw1124 raw1124Labels = mixedMoment B raw1124step0 raw1124step0Labels := by
      have ha : raw1124step0 = (fun i j => raw1124 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1124step0 raw1124; decide +kernel
      have hl : raw1124step0Labels = raw1124Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1124 raw1124Labels permutation152 permutation6
    mixedMoment B raw1124step0 raw1124step0Labels = mixedMoment B raw1124step1 raw1124step1Labels := by
      have ha : raw1124step1 = -raw1124step0 := by apply Matrix.ext; change ∀ i j, raw1124step1 i j = -(raw1124step0 i j); unfold raw1124step1 raw1124step0; decide +kernel
      have hl : raw1124step1Labels = raw1124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1124step1 raw1124step1Labels = mixedMoment B raw1124step2 raw1124step2Labels := by
      have ha : raw1124step2 = raw1124step1 := by apply Matrix.ext; unfold raw1124step2 raw1124step1; decide +kernel
      have hl : raw1124step1Labels = labelEmbedding1 ∘ raw1124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1124step1 raw1124step1Labels raw1124step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

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

theorem canonical1206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1206 raw1206Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw1206 raw1206Labels = mixedMoment B raw1206step0 raw1206step0Labels := by
      have ha : raw1206step0 = (fun i j => raw1206 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1206step0 raw1206; decide +kernel
      have hl : raw1206step0Labels = raw1206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1206 raw1206Labels permutation152 permutation4
    mixedMoment B raw1206step0 raw1206step0Labels = mixedMoment B raw1206step1 raw1206step1Labels := by
      have ha : raw1206step1 = raw1206step0 := by apply Matrix.ext; unfold raw1206step1 raw1206step0; decide +kernel
      have hl : raw1206step0Labels = labelEmbedding7 ∘ raw1206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1206step0 raw1206step0Labels raw1206step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

theorem canonical1207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1207 raw1207Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw1207 raw1207Labels = mixedMoment B raw1207step0 raw1207step0Labels := by
      have ha : raw1207step0 = (fun i j => raw1207 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1207step0 raw1207; decide +kernel
      have hl : raw1207step0Labels = raw1207Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1207 raw1207Labels permutation152 permutation4
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical1208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1208 raw1208Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw1208 raw1208Labels = mixedMoment B raw1208step0 raw1208step0Labels := by
      have ha : raw1208step0 = (fun i j => raw1208 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1208step0 raw1208; decide +kernel
      have hl : raw1208step0Labels = raw1208Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1208 raw1208Labels permutation158 permutation6
    mixedMoment B raw1208step0 raw1208step0Labels = mixedMoment B raw1208step1 raw1208step1Labels := by
      have ha : raw1208step1 = -raw1208step0 := by apply Matrix.ext; change ∀ i j, raw1208step1 i j = -(raw1208step0 i j); unfold raw1208step1 raw1208step0; decide +kernel
      have hl : raw1208step1Labels = raw1208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1208step1 raw1208step1Labels = mixedMoment B raw1208step2 raw1208step2Labels := by
      have ha : raw1208step2 = raw1208step1 := by apply Matrix.ext; unfold raw1208step2 raw1208step1; decide +kernel
      have hl : raw1208step1Labels = labelEmbedding1 ∘ raw1208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1208step1 raw1208step1Labels raw1208step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1597 node1597Labels := by rfl

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

theorem singleton4321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4321 node4321Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node899 node899Labels + mixedMoment B node1587 node1587Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1098 singletonSmall4321
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4321) = raw1098Labels := by decide +kernel
  rw [hl, canonical1098 B hB] at h
  have hc0 : mixedMoment B raw1098 (Fin.cases (0 : Fin 2) singletonSmall4321) =
      mixedMoment B node899 node899Labels := by
    have ha : raw1098 = raw1099 := by apply Matrix.ext; unfold raw1098 raw1099; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4321 = raw1099Labels := by decide +kernel
    rw [ha, hj, canonical1099 B hB]
  have hc1 : mixedMoment B raw1098 (Fin.cases (1 : Fin 2) singletonSmall4321) =
      mixedMoment B node1587 node1587Labels := by
    have ha : raw1098 = raw1100 := by apply Matrix.ext; unfold raw1098 raw1100; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4321 = raw1100Labels := by decide +kernel
    rw [ha, hj, canonical1100 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4323 node4323Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node901 node901Labels + mixedMoment B node1589 node1589Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1104 singletonSmall4323
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4323) = raw1104Labels := by decide +kernel
  rw [hl, canonical1104 B hB] at h
  have hc0 : mixedMoment B raw1104 (Fin.cases (0 : Fin 2) singletonSmall4323) =
      mixedMoment B node901 node901Labels := by
    have ha : raw1104 = raw1105 := by apply Matrix.ext; unfold raw1104 raw1105; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4323 = raw1105Labels := by decide +kernel
    rw [ha, hj, canonical1105 B hB]
  have hc1 : mixedMoment B raw1104 (Fin.cases (1 : Fin 2) singletonSmall4323) =
      mixedMoment B node1589 node1589Labels := by
    have ha : raw1104 = raw1106 := by apply Matrix.ext; unfold raw1104 raw1106; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4323 = raw1106Labels := by decide +kernel
    rw [ha, hj, canonical1106 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4341 node4341Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node919 node919Labels + mixedMoment B node1664 node1664Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1122 singletonSmall4341
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4341) = raw1122Labels := by decide +kernel
  rw [hl, canonical1122 B hB] at h
  have hc0 : mixedMoment B raw1122 (Fin.cases (0 : Fin 2) singletonSmall4341) =
      mixedMoment B node919 node919Labels := by
    have ha : raw1122 = raw1123 := by apply Matrix.ext; unfold raw1122 raw1123; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4341 = raw1123Labels := by decide +kernel
    rw [ha, hj, canonical1123 B hB]
  have hc1 : mixedMoment B raw1122 (Fin.cases (1 : Fin 2) singletonSmall4341) =
      mixedMoment B node1664 node1664Labels := by
    have ha : raw1122 = raw1124 := by apply Matrix.ext; unfold raw1122 raw1124; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4341 = raw1124Labels := by decide +kernel
    rw [ha, hj, canonical1124 B hB]
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

theorem singleton4396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4396 node4396Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node977 node977Labels + mixedMoment B node1597 node1597Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1206 singletonSmall4396
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4396) = raw1206Labels := by decide +kernel
  rw [hl, canonical1206 B hB] at h
  have hc0 : mixedMoment B raw1206 (Fin.cases (0 : Fin 2) singletonSmall4396) =
      mixedMoment B node977 node977Labels := by
    have ha : raw1206 = raw1207 := by apply Matrix.ext; unfold raw1206 raw1207; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4396 = raw1207Labels := by decide +kernel
    rw [ha, hj, canonical1207 B hB]
  have hc1 : mixedMoment B raw1206 (Fin.cases (1 : Fin 2) singletonSmall4396) =
      mixedMoment B node1597 node1597Labels := by
    have ha : raw1206 = raw1208 := by apply Matrix.ext; unfold raw1206 raw1208; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4396 = raw1208Labels := by decide +kernel
    rw [ha, hj, canonical1208 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4926 node4926Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2316 node2316Labels + mixedMoment B node3398 node3398Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1887 singletonSmall4926
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4926) = raw1887Labels := by decide +kernel
  rw [hl, canonical1887 B hB] at h
  have hc0 : mixedMoment B raw1887 (Fin.cases (0 : Fin 2) singletonSmall4926) =
      mixedMoment B node2316 node2316Labels := by
    have ha : raw1887 = raw1888 := by apply Matrix.ext; unfold raw1887 raw1888; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4926 = raw1888Labels := by decide +kernel
    rw [ha, hj, canonical1888 B hB]
  have hc1 : mixedMoment B raw1887 (Fin.cases (1 : Fin 2) singletonSmall4926) =
      mixedMoment B node3398 node3398Labels := by
    have ha : raw1887 = raw1889 := by apply Matrix.ext; unfold raw1887 raw1889; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4926 = raw1889Labels := by decide +kernel
    rw [ha, hj, canonical1889 B hB]
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

theorem singleton4928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4928 node4928Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2318 node2318Labels + mixedMoment B node3400 node3400Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1893 singletonSmall4928
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4928) = raw1893Labels := by decide +kernel
  rw [hl, canonical1893 B hB] at h
  have hc0 : mixedMoment B raw1893 (Fin.cases (0 : Fin 2) singletonSmall4928) =
      mixedMoment B node2318 node2318Labels := by
    have ha : raw1893 = raw1894 := by apply Matrix.ext; unfold raw1893 raw1894; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4928 = raw1894Labels := by decide +kernel
    rw [ha, hj, canonical1894 B hB]
  have hc1 : mixedMoment B raw1893 (Fin.cases (1 : Fin 2) singletonSmall4928) =
      mixedMoment B node3400 node3400Labels := by
    have ha : raw1893 = raw1895 := by apply Matrix.ext; unfold raw1893 raw1895; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4928 = raw1895Labels := by decide +kernel
    rw [ha, hj, canonical1895 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4939 node4939Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2330 node2330Labels + mixedMoment B node3404 node3404Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1902 singletonSmall4939
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4939) = raw1902Labels := by decide +kernel
  rw [hl, canonical1902 B hB] at h
  have hc0 : mixedMoment B raw1902 (Fin.cases (0 : Fin 2) singletonSmall4939) =
      mixedMoment B node2330 node2330Labels := by
    have ha : raw1902 = raw1903 := by apply Matrix.ext; unfold raw1902 raw1903; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4939 = raw1903Labels := by decide +kernel
    rw [ha, hj, canonical1903 B hB]
  have hc1 : mixedMoment B raw1902 (Fin.cases (1 : Fin 2) singletonSmall4939) =
      mixedMoment B node3404 node3404Labels := by
    have ha : raw1902 = raw1904 := by apply Matrix.ext; unfold raw1902 raw1904; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4939 = raw1904Labels := by decide +kernel
    rw [ha, hj, canonical1904 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4985 node4985Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2370 node2370Labels + mixedMoment B node3334 node3334Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1989 singletonSmall4985
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4985) = raw1989Labels := by decide +kernel
  rw [hl, canonical1989 B hB] at h
  have hc0 : mixedMoment B raw1989 (Fin.cases (0 : Fin 2) singletonSmall4985) =
      mixedMoment B node2370 node2370Labels := by
    have ha : raw1989 = raw1990 := by apply Matrix.ext; unfold raw1989 raw1990; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4985 = raw1990Labels := by decide +kernel
    rw [ha, hj, canonical1990 B hB]
  have hc1 : mixedMoment B raw1989 (Fin.cases (1 : Fin 2) singletonSmall4985) =
      mixedMoment B node3334 node3334Labels := by
    have ha : raw1989 = raw1991 := by apply Matrix.ext; unfold raw1989 raw1991; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4985 = raw1991Labels := by decide +kernel
    rw [ha, hj, canonical1991 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4987 node4987Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2372 node2372Labels + mixedMoment B node3336 node3336Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1995 singletonSmall4987
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4987) = raw1995Labels := by decide +kernel
  rw [hl, canonical1995 B hB] at h
  have hc0 : mixedMoment B raw1995 (Fin.cases (0 : Fin 2) singletonSmall4987) =
      mixedMoment B node2372 node2372Labels := by
    have ha : raw1995 = raw1996 := by apply Matrix.ext; unfold raw1995 raw1996; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4987 = raw1996Labels := by decide +kernel
    rw [ha, hj, canonical1996 B hB]
  have hc1 : mixedMoment B raw1995 (Fin.cases (1 : Fin 2) singletonSmall4987) =
      mixedMoment B node3336 node3336Labels := by
    have ha : raw1995 = raw1997 := by apply Matrix.ext; unfold raw1995 raw1997; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4987 = raw1997Labels := by decide +kernel
    rw [ha, hj, canonical1997 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4996 node4996Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2382 node2382Labels + mixedMoment B node3340 node3340Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2007 singletonSmall4996
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4996) = raw2007Labels := by decide +kernel
  rw [hl, canonical2007 B hB] at h
  have hc0 : mixedMoment B raw2007 (Fin.cases (0 : Fin 2) singletonSmall4996) =
      mixedMoment B node2382 node2382Labels := by
    have ha : raw2007 = raw2008 := by apply Matrix.ext; unfold raw2007 raw2008; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4996 = raw2008Labels := by decide +kernel
    rw [ha, hj, canonical2008 B hB]
  have hc1 : mixedMoment B raw2007 (Fin.cases (1 : Fin 2) singletonSmall4996) =
      mixedMoment B node3340 node3340Labels := by
    have ha : raw2007 = raw2009 := by apply Matrix.ext; unfold raw2007 raw2009; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4996 = raw2009Labels := by decide +kernel
    rw [ha, hj, canonical2009 B hB]
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

theorem singleton5126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5126 node5126Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2541 node2541Labels + mixedMoment B node3487 node3487Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2160 singletonSmall5126
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5126) = raw2160Labels := by decide +kernel
  rw [hl, canonical2160 B hB] at h
  have hc0 : mixedMoment B raw2160 (Fin.cases (0 : Fin 2) singletonSmall5126) =
      mixedMoment B node2541 node2541Labels := by
    have ha : raw2160 = raw2161 := by apply Matrix.ext; unfold raw2160 raw2161; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5126 = raw2161Labels := by decide +kernel
    rw [ha, hj, canonical2161 B hB]
  have hc1 : mixedMoment B raw2160 (Fin.cases (1 : Fin 2) singletonSmall5126) =
      mixedMoment B node3487 node3487Labels := by
    have ha : raw2160 = raw2162 := by apply Matrix.ext; unfold raw2160 raw2162; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5126 = raw2162Labels := by decide +kernel
    rw [ha, hj, canonical2162 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5137 node5137Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2556 node2556Labels + mixedMoment B node3521 node3521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2166 singletonSmall5137
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5137) = raw2166Labels := by decide +kernel
  rw [hl, canonical2166 B hB] at h
  have hc0 : mixedMoment B raw2166 (Fin.cases (0 : Fin 2) singletonSmall5137) =
      mixedMoment B node2556 node2556Labels := by
    have ha : raw2166 = raw2167 := by apply Matrix.ext; unfold raw2166 raw2167; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5137 = raw2167Labels := by decide +kernel
    rw [ha, hj, canonical2167 B hB]
  have hc1 : mixedMoment B raw2166 (Fin.cases (1 : Fin 2) singletonSmall5137) =
      mixedMoment B node3521 node3521Labels := by
    have ha : raw2166 = raw2168 := by apply Matrix.ext; unfold raw2166 raw2168; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5137 = raw2168Labels := by decide +kernel
    rw [ha, hj, canonical2168 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5241 node5241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2694 node2694Labels + mixedMoment B node3493 node3493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2259 singletonSmall5241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5241) = raw2259Labels := by decide +kernel
  rw [hl, canonical2259 B hB] at h
  have hc0 : mixedMoment B raw2259 (Fin.cases (0 : Fin 2) singletonSmall5241) =
      mixedMoment B node2694 node2694Labels := by
    have ha : raw2259 = raw2260 := by apply Matrix.ext; unfold raw2259 raw2260; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5241 = raw2260Labels := by decide +kernel
    rw [ha, hj, canonical2260 B hB]
  have hc1 : mixedMoment B raw2259 (Fin.cases (1 : Fin 2) singletonSmall5241) =
      mixedMoment B node3493 node3493Labels := by
    have ha : raw2259 = raw2261 := by apply Matrix.ext; unfold raw2259 raw2261; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5241 = raw2261Labels := by decide +kernel
    rw [ha, hj, canonical2261 B hB]
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

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5393 node5393Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3779 node3779Labels + mixedMoment B node3797 node3797Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2460 singletonSmall5393
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5393) = raw2460Labels := by decide +kernel
  rw [hl, canonical2460 B hB] at h
  have hc0 : mixedMoment B raw2460 (Fin.cases (0 : Fin 2) singletonSmall5393) =
      mixedMoment B node3779 node3779Labels := by
    have ha : raw2460 = raw2461 := by apply Matrix.ext; unfold raw2460 raw2461; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5393 = raw2461Labels := by decide +kernel
    rw [ha, hj, canonical2461 B hB]
  have hc1 : mixedMoment B raw2460 (Fin.cases (1 : Fin 2) singletonSmall5393) =
      mixedMoment B node3797 node3797Labels := by
    have ha : raw2460 = raw2462 := by apply Matrix.ext; unfold raw2460 raw2462; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5393 = raw2462Labels := by decide +kernel
    rw [ha, hj, canonical2462 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5395 node5395Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3781 node3781Labels + mixedMoment B node3794 node3794Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2463 singletonSmall5395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5395) = raw2463Labels := by decide +kernel
  rw [hl, canonical2463 B hB] at h
  have hc0 : mixedMoment B raw2463 (Fin.cases (0 : Fin 2) singletonSmall5395) =
      mixedMoment B node3781 node3781Labels := by
    have ha : raw2463 = raw2464 := by apply Matrix.ext; unfold raw2463 raw2464; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5395 = raw2464Labels := by decide +kernel
    rw [ha, hj, canonical2464 B hB]
  have hc1 : mixedMoment B raw2463 (Fin.cases (1 : Fin 2) singletonSmall5395) =
      mixedMoment B node3794 node3794Labels := by
    have ha : raw2463 = raw2465 := by apply Matrix.ext; unfold raw2463 raw2465; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5395 = raw2465Labels := by decide +kernel
    rw [ha, hj, canonical2465 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5405 node5405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3800 node3800Labels + mixedMoment B node3805 node3805Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2484 singletonSmall5405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5405) = raw2484Labels := by decide +kernel
  rw [hl, canonical2484 B hB] at h
  have hc0 : mixedMoment B raw2484 (Fin.cases (0 : Fin 2) singletonSmall5405) =
      mixedMoment B node3800 node3800Labels := by
    have ha : raw2484 = raw2485 := by apply Matrix.ext; unfold raw2484 raw2485; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5405 = raw2485Labels := by decide +kernel
    rw [ha, hj, canonical2485 B hB]
  have hc1 : mixedMoment B raw2484 (Fin.cases (1 : Fin 2) singletonSmall5405) =
      mixedMoment B node3805 node3805Labels := by
    have ha : raw2484 = raw2486 := by apply Matrix.ext; unfold raw2484 raw2486; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5405 = raw2486Labels := by decide +kernel
    rw [ha, hj, canonical2486 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node899 node899Labels = Sparse.eval nodeValue899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 899) = mixedMoment B node899 node899Labels := rfl
  simpa [nodeValue899, Sparse.eval] using hc.symm

theorem sound901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node901 node901Labels = Sparse.eval nodeValue901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 901) = mixedMoment B node901 node901Labels := rfl
  simpa [nodeValue901, Sparse.eval] using hc.symm

theorem sound919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node919 node919Labels = Sparse.eval nodeValue919 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 919) = mixedMoment B node919 node919Labels := rfl
  simpa [nodeValue919, Sparse.eval] using hc.symm

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

theorem sound977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node977 node977Labels = Sparse.eval nodeValue977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 977) = mixedMoment B node977 node977Labels := rfl
  simpa [nodeValue977, Sparse.eval] using hc.symm

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

theorem sound1587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1587 node1587Labels = Sparse.eval nodeValue1587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1587) = mixedMoment B node1587 node1587Labels := rfl
  simpa [nodeValue1587, Sparse.eval] using hc.symm

theorem sound1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1589 node1589Labels = Sparse.eval nodeValue1589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1589) = mixedMoment B node1589 node1589Labels := rfl
  simpa [nodeValue1589, Sparse.eval] using hc.symm

theorem sound1597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1597 node1597Labels = Sparse.eval nodeValue1597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1597) = mixedMoment B node1597 node1597Labels := rfl
  simpa [nodeValue1597, Sparse.eval] using hc.symm

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

theorem sound1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1664 node1664Labels = Sparse.eval nodeValue1664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1664) = mixedMoment B node1664 node1664Labels := rfl
  simpa [nodeValue1664, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

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

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

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

theorem sound2316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2316 node2316Labels = Sparse.eval nodeValue2316 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2316) = mixedMoment B node2316 node2316Labels := rfl
  simpa [nodeValue2316, Sparse.eval] using hc.symm

theorem sound2318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2318 node2318Labels = Sparse.eval nodeValue2318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2318) = mixedMoment B node2318 node2318Labels := rfl
  simpa [nodeValue2318, Sparse.eval] using hc.symm

theorem sound2330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2330 node2330Labels = Sparse.eval nodeValue2330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2330) = mixedMoment B node2330 node2330Labels := rfl
  simpa [nodeValue2330, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2370 node2370Labels = Sparse.eval nodeValue2370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2370) = mixedMoment B node2370 node2370Labels := rfl
  simpa [nodeValue2370, Sparse.eval] using hc.symm

theorem sound2372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2372 node2372Labels = Sparse.eval nodeValue2372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2372) = mixedMoment B node2372 node2372Labels := rfl
  simpa [nodeValue2372, Sparse.eval] using hc.symm

theorem sound2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2382 node2382Labels = Sparse.eval nodeValue2382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2382) = mixedMoment B node2382 node2382Labels := rfl
  simpa [nodeValue2382, Sparse.eval] using hc.symm

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

theorem sound2541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2541 node2541Labels = Sparse.eval nodeValue2541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2541) = mixedMoment B node2541 node2541Labels := rfl
  simpa [nodeValue2541, Sparse.eval] using hc.symm

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3334 node3334Labels = Sparse.eval nodeValue3334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3334) = mixedMoment B node3334 node3334Labels := rfl
  simpa [nodeValue3334, Sparse.eval] using hc.symm

theorem sound3336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3336 node3336Labels = Sparse.eval nodeValue3336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3336) = mixedMoment B node3336 node3336Labels := rfl
  simpa [nodeValue3336, Sparse.eval] using hc.symm

theorem sound3340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3340 node3340Labels = Sparse.eval nodeValue3340 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3340) = mixedMoment B node3340 node3340Labels := rfl
  simpa [nodeValue3340, Sparse.eval] using hc.symm

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

theorem sound3398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3398 node3398Labels = Sparse.eval nodeValue3398 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3398) = mixedMoment B node3398 node3398Labels := rfl
  simpa [nodeValue3398, Sparse.eval] using hc.symm

theorem sound3400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3400 node3400Labels = Sparse.eval nodeValue3400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3400) = mixedMoment B node3400 node3400Labels := rfl
  simpa [nodeValue3400, Sparse.eval] using hc.symm

theorem sound3404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3404 node3404Labels = Sparse.eval nodeValue3404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3404) = mixedMoment B node3404 node3404Labels := rfl
  simpa [nodeValue3404, Sparse.eval] using hc.symm

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

theorem sound3487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3487 node3487Labels = Sparse.eval nodeValue3487 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3487) = mixedMoment B node3487 node3487Labels := rfl
  simpa [nodeValue3487, Sparse.eval] using hc.symm

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

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

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

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

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

theorem sound3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3797 node3797Labels = Sparse.eval nodeValue3797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3797) = mixedMoment B node3797 node3797Labels := rfl
  simpa [nodeValue3797, Sparse.eval] using hc.symm

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

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

theorem sound4321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4321 node4321Labels = Sparse.eval nodeValue4321 (mixedVector B) := by
  have h := singleton4321 B _hB
  rw [sound899 B _hB _hF, sound1587 B _hB _hF] at h
  norm_num [nodeValue4321, nodeValue899, nodeValue1587, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4323 node4323Labels = Sparse.eval nodeValue4323 (mixedVector B) := by
  have h := singleton4323 B _hB
  rw [sound901 B _hB _hF, sound1589 B _hB _hF] at h
  norm_num [nodeValue4323, nodeValue901, nodeValue1589, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4341 node4341Labels = Sparse.eval nodeValue4341 (mixedVector B) := by
  have h := singleton4341 B _hB
  rw [sound919 B _hB _hF, sound1664 B _hB _hF] at h
  norm_num [nodeValue4341, nodeValue919, nodeValue1664, Sparse.eval] at h ⊢
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

theorem sound4396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4396 node4396Labels = Sparse.eval nodeValue4396 (mixedVector B) := by
  have h := singleton4396 B _hB
  rw [sound977 B _hB _hF, sound1597 B _hB _hF] at h
  norm_num [nodeValue4396, nodeValue977, nodeValue1597, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
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

theorem sound4926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4926 node4926Labels = Sparse.eval nodeValue4926 (mixedVector B) := by
  have h := singleton4926 B _hB
  rw [sound2316 B _hB _hF, sound3398 B _hB _hF] at h
  norm_num [nodeValue4926, nodeValue2316, nodeValue3398, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4928 node4928Labels = Sparse.eval nodeValue4928 (mixedVector B) := by
  have h := singleton4928 B _hB
  rw [sound2318 B _hB _hF, sound3400 B _hB _hF] at h
  norm_num [nodeValue4928, nodeValue2318, nodeValue3400, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4939 node4939Labels = Sparse.eval nodeValue4939 (mixedVector B) := by
  have h := singleton4939 B _hB
  rw [sound2330 B _hB _hF, sound3404 B _hB _hF] at h
  norm_num [nodeValue4939, nodeValue2330, nodeValue3404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4985 node4985Labels = Sparse.eval nodeValue4985 (mixedVector B) := by
  have h := singleton4985 B _hB
  rw [sound2370 B _hB _hF, sound3334 B _hB _hF] at h
  norm_num [nodeValue4985, nodeValue2370, nodeValue3334, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4987 node4987Labels = Sparse.eval nodeValue4987 (mixedVector B) := by
  have h := singleton4987 B _hB
  rw [sound2372 B _hB _hF, sound3336 B _hB _hF] at h
  norm_num [nodeValue4987, nodeValue2372, nodeValue3336, Sparse.eval] at h ⊢
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

theorem sound4996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4996 node4996Labels = Sparse.eval nodeValue4996 (mixedVector B) := by
  have h := singleton4996 B _hB
  rw [sound2382 B _hB _hF, sound3340 B _hB _hF] at h
  norm_num [nodeValue4996, nodeValue2382, nodeValue3340, Sparse.eval] at h ⊢
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

theorem sound5126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5126 node5126Labels = Sparse.eval nodeValue5126 (mixedVector B) := by
  have h := singleton5126 B _hB
  rw [sound2541 B _hB _hF, sound3487 B _hB _hF] at h
  norm_num [nodeValue5126, nodeValue2541, nodeValue3487, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5137 node5137Labels = Sparse.eval nodeValue5137 (mixedVector B) := by
  have h := singleton5137 B _hB
  rw [sound2556 B _hB _hF, sound3521 B _hB _hF] at h
  norm_num [nodeValue5137, nodeValue2556, nodeValue3521, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5241 node5241Labels = Sparse.eval nodeValue5241 (mixedVector B) := by
  have h := singleton5241 B _hB
  rw [sound2694 B _hB _hF, sound3493 B _hB _hF] at h
  norm_num [nodeValue5241, nodeValue2694, nodeValue3493, Sparse.eval] at h ⊢
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

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5393 node5393Labels = Sparse.eval nodeValue5393 (mixedVector B) := by
  have h := singleton5393 B _hB
  rw [sound3779 B _hB _hF, sound3797 B _hB _hF] at h
  norm_num [nodeValue5393, nodeValue3779, nodeValue3797, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5405 node5405Labels = Sparse.eval nodeValue5405 (mixedVector B) := by
  have h := singleton5405 B _hB
  rw [sound3800 B _hB _hF, sound3805 B _hB _hF] at h
  norm_num [nodeValue5405, nodeValue3800, nodeValue3805, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources75
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2405 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 1) (sourceB2405 + difference 1 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 1) (sourceB2405 + difference 1 0) sourceC2405) = raw32966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32966; decide +kernel
    rw [ha]
    exact (canonical32966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 2) (sourceB2405 + difference 2 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 2) (sourceB2405 + difference 2 0) sourceC2405) = raw32967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32967; decide +kernel
    rw [ha]
    exact (canonical32967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 3) (sourceB2405 + difference 3 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 3) (sourceB2405 + difference 3 0) sourceC2405) = raw32968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32968; decide +kernel
    rw [ha]
    exact (canonical32968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 4) (sourceB2405 + difference 4 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 4) (sourceB2405 + difference 4 0) sourceC2405) = raw32969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32969; decide +kernel
    rw [ha]
    exact (canonical32969 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2405 + difference 0 5) (sourceB2405 + difference 5 0) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2405 + difference 0 5) (sourceB2405 + difference 5 0) sourceC2405) = raw32970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32970; decide +kernel
    rw [ha]
    exact (canonical32970 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 0) (sourceB2405 + difference 0 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 0) (sourceB2405 + difference 0 1) sourceC2405) = raw32971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32971; decide +kernel
    rw [ha]
    exact (canonical32971 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 2) (sourceB2405 + difference 2 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 2) (sourceB2405 + difference 2 1) sourceC2405) = raw32972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32972; decide +kernel
    rw [ha]
    exact (canonical32972 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 3) (sourceB2405 + difference 3 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 3) (sourceB2405 + difference 3 1) sourceC2405) = raw32973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32973; decide +kernel
    rw [ha]
    exact (canonical32973 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 4) (sourceB2405 + difference 4 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 4) (sourceB2405 + difference 4 1) sourceC2405) = raw32974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32974; decide +kernel
    rw [ha]
    exact (canonical32974 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2405 + difference 1 5) (sourceB2405 + difference 5 1) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2405 + difference 1 5) (sourceB2405 + difference 5 1) sourceC2405) = raw32975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32975; decide +kernel
    rw [ha]
    exact (canonical32975 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 0) (sourceB2405 + difference 0 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 0) (sourceB2405 + difference 0 2) sourceC2405) = raw32976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32976; decide +kernel
    rw [ha]
    exact (canonical32976 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 1) (sourceB2405 + difference 1 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 1) (sourceB2405 + difference 1 2) sourceC2405) = raw32977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32977; decide +kernel
    rw [ha]
    exact (canonical32977 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 3) (sourceB2405 + difference 3 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 3) (sourceB2405 + difference 3 2) sourceC2405) = raw32978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32978; decide +kernel
    rw [ha]
    exact (canonical32978 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 4) (sourceB2405 + difference 4 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 4) (sourceB2405 + difference 4 2) sourceC2405) = raw32979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32979; decide +kernel
    rw [ha]
    exact (canonical32979 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2405 + difference 2 5) (sourceB2405 + difference 5 2) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2405 + difference 2 5) (sourceB2405 + difference 5 2) sourceC2405) = raw32980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32980; decide +kernel
    rw [ha]
    exact (canonical32980 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 0) (sourceB2405 + difference 0 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4321) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 0) (sourceB2405 + difference 0 3) sourceC2405) = raw32981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32981; decide +kernel
    rw [ha]
    exact (canonical32981 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 1) (sourceB2405 + difference 1 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4926) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 1) (sourceB2405 + difference 1 3) sourceC2405) = raw32982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32982; decide +kernel
    rw [ha]
    exact (canonical32982 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 2) (sourceB2405 + difference 2 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4985) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 2) (sourceB2405 + difference 2 3) sourceC2405) = raw32983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32983; decide +kernel
    rw [ha]
    exact (canonical32983 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 4) (sourceB2405 + difference 4 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 4) (sourceB2405 + difference 4 3) sourceC2405) = raw32984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32984; decide +kernel
    rw [ha]
    exact (canonical32984 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2405 + difference 3 5) (sourceB2405 + difference 5 3) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2405 + difference 3 5) (sourceB2405 + difference 5 3) sourceC2405) = raw32985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32985; decide +kernel
    rw [ha]
    exact (canonical32985 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 0) (sourceB2405 + difference 0 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 0) (sourceB2405 + difference 0 4) sourceC2405) = raw32986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32986; decide +kernel
    rw [ha]
    exact (canonical32986 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 1) (sourceB2405 + difference 1 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 1) (sourceB2405 + difference 1 4) sourceC2405) = raw32987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32987; decide +kernel
    rw [ha]
    exact (canonical32987 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 2) (sourceB2405 + difference 2 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 2) (sourceB2405 + difference 2 4) sourceC2405) = raw32988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32988; decide +kernel
    rw [ha]
    exact (canonical32988 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 3) (sourceB2405 + difference 3 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 3) (sourceB2405 + difference 3 4) sourceC2405) = raw32989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32989; decide +kernel
    rw [ha]
    exact (canonical32989 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2405 + difference 4 5) (sourceB2405 + difference 5 4) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2405 + difference 4 5) (sourceB2405 + difference 5 4) sourceC2405) = raw32990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32990; decide +kernel
    rw [ha]
    exact (canonical32990 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 0) (sourceB2405 + difference 0 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 0) (sourceB2405 + difference 0 5) sourceC2405) = raw32991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32991; decide +kernel
    rw [ha]
    exact (canonical32991 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 1) (sourceB2405 + difference 1 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 1) (sourceB2405 + difference 1 5) sourceC2405) = raw32992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32992; decide +kernel
    rw [ha]
    exact (canonical32992 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 2) (sourceB2405 + difference 2 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4709) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 2) (sourceB2405 + difference 2 5) sourceC2405) = raw32993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32993; decide +kernel
    rw [ha]
    exact (canonical32993 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 3) (sourceB2405 + difference 3 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 3) (sourceB2405 + difference 3 5) sourceC2405) = raw32994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32994; decide +kernel
    rw [ha]
    exact (canonical32994 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2405 + difference 5 4) (sourceB2405 + difference 4 5) sourceC2405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2405 + difference 5 4) (sourceB2405 + difference 4 5) sourceC2405) = raw32995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2405 sourceB2405 sourceC2405 difference raw32995; decide +kernel
    rw [ha]
    exact (canonical32995 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2405 sourceB2405 sourceC2405
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2405, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1952 : Integer.Sparse.reindex keyMap MixedData.row1952 = numericRow1952 := by decide +kernel

theorem numericCheck1952 (x : Master → ℝ) : Integer.Sparse.eval numericRow1952 x =
    (17280 : ℝ) * reducedSource1952 x := by
  norm_num [numericRow1952, reducedSource1952, Integer.Sparse.eval, Sparse.eval, nodeValue4320, nodeValue4321, nodeValue4323, nodeValue4341, nodeValue4396, nodeValue4706, nodeValue4709, nodeValue4728, nodeValue4804, nodeValue4926, nodeValue4928, nodeValue4939, nodeValue4985, nodeValue4987, nodeValue4996, nodeValue5126, nodeValue5134, nodeValue5137, nodeValue5141, nodeValue5167, nodeValue5168, nodeValue5241, nodeValue5257, nodeValue5258, nodeValue5393, nodeValue5395, nodeValue5405, nodeValue5434, nodeValue5482]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1952 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1952 (mixedVector B) = 0 := by
  have h4320 : mixedVector B (Sum.inr 4320) = Sparse.eval nodeValue4320 (mixedVector B) := by
    change mixedMoment B node4320 node4320Labels = _
    exact sound4320 B hB hF
  have h4321 : mixedVector B (Sum.inr 4321) = Sparse.eval nodeValue4321 (mixedVector B) := by
    change mixedMoment B node4321 node4321Labels = _
    exact sound4321 B hB hF
  have h4323 : mixedVector B (Sum.inr 4323) = Sparse.eval nodeValue4323 (mixedVector B) := by
    change mixedMoment B node4323 node4323Labels = _
    exact sound4323 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4709 : mixedVector B (Sum.inr 4709) = Sparse.eval nodeValue4709 (mixedVector B) := by
    change mixedMoment B node4709 node4709Labels = _
    exact sound4709 B hB hF
  have h4728 : mixedVector B (Sum.inr 4728) = Sparse.eval nodeValue4728 (mixedVector B) := by
    change mixedMoment B node4728 node4728Labels = _
    exact sound4728 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4926 : mixedVector B (Sum.inr 4926) = Sparse.eval nodeValue4926 (mixedVector B) := by
    change mixedMoment B node4926 node4926Labels = _
    exact sound4926 B hB hF
  have h4928 : mixedVector B (Sum.inr 4928) = Sparse.eval nodeValue4928 (mixedVector B) := by
    change mixedMoment B node4928 node4928Labels = _
    exact sound4928 B hB hF
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4985 : mixedVector B (Sum.inr 4985) = Sparse.eval nodeValue4985 (mixedVector B) := by
    change mixedMoment B node4985 node4985Labels = _
    exact sound4985 B hB hF
  have h4987 : mixedVector B (Sum.inr 4987) = Sparse.eval nodeValue4987 (mixedVector B) := by
    change mixedMoment B node4987 node4987Labels = _
    exact sound4987 B hB hF
  have h4996 : mixedVector B (Sum.inr 4996) = Sparse.eval nodeValue4996 (mixedVector B) := by
    change mixedMoment B node4996 node4996Labels = _
    exact sound4996 B hB hF
  have h5126 : mixedVector B (Sum.inr 5126) = Sparse.eval nodeValue5126 (mixedVector B) := by
    change mixedMoment B node5126 node5126Labels = _
    exact sound5126 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167_e B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  simpa only [sourceForm2405, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4320, h4321, h4323, h4341, h4396, h4706, h4709, h4728, h4804, h4926, h4928, h4939, h4985, h4987, h4996, h5126, h5134, h5137, h5141, h5167, h5168, h5241, h5257, h5258, h5393, h5395, h5405, h5434, h5482, reducedSource1952] using sourceEq2405 B hB

theorem rowSound1952_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1952 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1952, numericCheck1952, reducedZero1952 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e_oai
