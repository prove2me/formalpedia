-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:43:48.301534+00:00
-- url     : https://prove2.me/submissions/bd4da548-c900-4a33-8238-80938137da18

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2016 raw2016Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw2016 raw2016Labels = mixedMoment B raw2016step0 raw2016step0Labels := by
      have ha : raw2016step0 = (fun i j => raw2016 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2016step0 raw2016; decide +kernel
      have hl : raw2016step0Labels = raw2016Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2016 raw2016Labels permutation32 permutation4
    mixedMoment B raw2016step0 raw2016step0Labels = mixedMoment B raw2016step1 raw2016step1Labels := by
      have ha : raw2016step1 = raw2016step0 := by apply Matrix.ext; unfold raw2016step1 raw2016step0; decide +kernel
      have hl : raw2016step0Labels = labelEmbedding7 ∘ raw2016step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2016step0 raw2016step0Labels raw2016step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical2017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2017 raw2017Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw2017 raw2017Labels = mixedMoment B raw2017step0 raw2017step0Labels := by
      have ha : raw2017step0 = (fun i j => raw2017 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2017step0 raw2017; decide +kernel
      have hl : raw2017step0Labels = raw2017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2017 raw2017Labels permutation32 permutation4
    _ = mixedMoment B node2388 node2388Labels := by rfl

theorem canonical2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2018 raw2018Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw2018 raw2018Labels = mixedMoment B raw2018step0 raw2018step0Labels := by
      have ha : raw2018step0 = (fun i j => raw2018 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2018step0 raw2018; decide +kernel
      have hl : raw2018step0Labels = raw2018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2018 raw2018Labels permutation32 permutation6
    mixedMoment B raw2018step0 raw2018step0Labels = mixedMoment B raw2018step1 raw2018step1Labels := by
      have ha : raw2018step1 = -raw2018step0 := by apply Matrix.ext; change ∀ i j, raw2018step1 i j = -(raw2018step0 i j); unfold raw2018step1 raw2018step0; decide +kernel
      have hl : raw2018step1Labels = raw2018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2018step1 raw2018step1Labels = mixedMoment B raw2018step2 raw2018step2Labels := by
      have ha : raw2018step2 = raw2018step1 := by apply Matrix.ext; unfold raw2018step2 raw2018step1; decide +kernel
      have hl : raw2018step1Labels = labelEmbedding1 ∘ raw2018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2018step1 raw2018step1Labels raw2018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3354 node3354Labels := by rfl

theorem canonical2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2025 raw2025Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw2025 raw2025Labels = mixedMoment B raw2025step0 raw2025step0Labels := by
      have ha : raw2025step0 = (fun i j => raw2025 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2025step0 raw2025; decide +kernel
      have hl : raw2025step0Labels = raw2025Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2025 raw2025Labels permutation32 permutation4
    mixedMoment B raw2025step0 raw2025step0Labels = mixedMoment B raw2025step1 raw2025step1Labels := by
      have ha : raw2025step1 = raw2025step0 := by apply Matrix.ext; unfold raw2025step1 raw2025step0; decide +kernel
      have hl : raw2025step0Labels = labelEmbedding7 ∘ raw2025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2025step0 raw2025step0Labels raw2025step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2026 raw2026Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw2026 raw2026Labels = mixedMoment B raw2026step0 raw2026step0Labels := by
      have ha : raw2026step0 = (fun i j => raw2026 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2026step0 raw2026; decide +kernel
      have hl : raw2026step0Labels = raw2026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2026 raw2026Labels permutation32 permutation4
    _ = mixedMoment B node2400 node2400Labels := by rfl

theorem canonical2027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2027 raw2027Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw2027 raw2027Labels = mixedMoment B raw2027step0 raw2027step0Labels := by
      have ha : raw2027step0 = (fun i j => raw2027 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2027step0 raw2027; decide +kernel
      have hl : raw2027step0Labels = raw2027Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2027 raw2027Labels permutation32 permutation6
    mixedMoment B raw2027step0 raw2027step0Labels = mixedMoment B raw2027step1 raw2027step1Labels := by
      have ha : raw2027step1 = -raw2027step0 := by apply Matrix.ext; change ∀ i j, raw2027step1 i j = -(raw2027step0 i j); unfold raw2027step1 raw2027step0; decide +kernel
      have hl : raw2027step1Labels = raw2027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2027step1 raw2027step1Labels = mixedMoment B raw2027step2 raw2027step2Labels := by
      have ha : raw2027step2 = raw2027step1 := by apply Matrix.ext; unfold raw2027step2 raw2027step1; decide +kernel
      have hl : raw2027step1Labels = labelEmbedding1 ∘ raw2027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2027step1 raw2027step1Labels raw2027step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3344 node3344Labels := by rfl

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

theorem canonical2076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2076 raw2076Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw2076 raw2076Labels = mixedMoment B raw2076step0 raw2076step0Labels := by
      have ha : raw2076step0 = (fun i j => raw2076 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2076step0 raw2076; decide +kernel
      have hl : raw2076step0Labels = raw2076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2076 raw2076Labels permutation152 permutation4
    mixedMoment B raw2076step0 raw2076step0Labels = mixedMoment B raw2076step1 raw2076step1Labels := by
      have ha : raw2076step1 = raw2076step0 := by apply Matrix.ext; unfold raw2076step1 raw2076step0; decide +kernel
      have hl : raw2076step0Labels = labelEmbedding7 ∘ raw2076step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2076step0 raw2076step0Labels raw2076step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

theorem canonical2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2077 raw2077Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw2077 raw2077Labels = mixedMoment B raw2077step0 raw2077step0Labels := by
      have ha : raw2077step0 = (fun i j => raw2077 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2077step0 raw2077; decide +kernel
      have hl : raw2077step0Labels = raw2077Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2077 raw2077Labels permutation152 permutation4
    _ = mixedMoment B node2452 node2452Labels := by rfl

theorem canonical2078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2078 raw2078Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw2078 raw2078Labels = mixedMoment B raw2078step0 raw2078step0Labels := by
      have ha : raw2078step0 = (fun i j => raw2078 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2078step0 raw2078; decide +kernel
      have hl : raw2078step0Labels = raw2078Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2078 raw2078Labels permutation152 permutation6
    mixedMoment B raw2078step0 raw2078step0Labels = mixedMoment B raw2078step1 raw2078step1Labels := by
      have ha : raw2078step1 = -raw2078step0 := by apply Matrix.ext; change ∀ i j, raw2078step1 i j = -(raw2078step0 i j); unfold raw2078step1 raw2078step0; decide +kernel
      have hl : raw2078step1Labels = raw2078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2078step1 raw2078step1Labels = mixedMoment B raw2078step2 raw2078step2Labels := by
      have ha : raw2078step2 = raw2078step1 := by apply Matrix.ext; unfold raw2078step2 raw2078step1; decide +kernel
      have hl : raw2078step1Labels = labelEmbedding1 ∘ raw2078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2078step1 raw2078step1Labels raw2078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3433 node3433Labels := by rfl

theorem canonical2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2082 raw2082Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw2082 raw2082Labels = mixedMoment B raw2082step0 raw2082step0Labels := by
      have ha : raw2082step0 = (fun i j => raw2082 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2082step0 raw2082; decide +kernel
      have hl : raw2082step0Labels = raw2082Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2082 raw2082Labels permutation152 permutation4
    mixedMoment B raw2082step0 raw2082step0Labels = mixedMoment B raw2082step1 raw2082step1Labels := by
      have ha : raw2082step1 = raw2082step0 := by apply Matrix.ext; unfold raw2082step1 raw2082step0; decide +kernel
      have hl : raw2082step0Labels = labelEmbedding7 ∘ raw2082step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2082step0 raw2082step0Labels raw2082step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

theorem canonical2083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2083 raw2083Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw2083 raw2083Labels = mixedMoment B raw2083step0 raw2083step0Labels := by
      have ha : raw2083step0 = (fun i j => raw2083 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2083step0 raw2083; decide +kernel
      have hl : raw2083step0Labels = raw2083Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2083 raw2083Labels permutation152 permutation4
    _ = mixedMoment B node2459 node2459Labels := by rfl

theorem canonical2084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2084 raw2084Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw2084 raw2084Labels = mixedMoment B raw2084step0 raw2084step0Labels := by
      have ha : raw2084step0 = (fun i j => raw2084 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2084step0 raw2084; decide +kernel
      have hl : raw2084step0Labels = raw2084Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2084 raw2084Labels permutation152 permutation6
    mixedMoment B raw2084step0 raw2084step0Labels = mixedMoment B raw2084step1 raw2084step1Labels := by
      have ha : raw2084step1 = -raw2084step0 := by apply Matrix.ext; change ∀ i j, raw2084step1 i j = -(raw2084step0 i j); unfold raw2084step1 raw2084step0; decide +kernel
      have hl : raw2084step1Labels = raw2084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2084step1 raw2084step1Labels = mixedMoment B raw2084step2 raw2084step2Labels := by
      have ha : raw2084step2 = raw2084step1 := by apply Matrix.ext; unfold raw2084step2 raw2084step1; decide +kernel
      have hl : raw2084step1Labels = labelEmbedding1 ∘ raw2084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2084step1 raw2084step1Labels raw2084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3429 node3429Labels := by rfl

theorem canonical2091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2091 raw2091Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw2091 raw2091Labels = mixedMoment B raw2091step0 raw2091step0Labels := by
      have ha : raw2091step0 = (fun i j => raw2091 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2091step0 raw2091; decide +kernel
      have hl : raw2091step0Labels = raw2091Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2091 raw2091Labels permutation152 permutation4
    mixedMoment B raw2091step0 raw2091step0Labels = mixedMoment B raw2091step1 raw2091step1Labels := by
      have ha : raw2091step1 = raw2091step0 := by apply Matrix.ext; unfold raw2091step1 raw2091step0; decide +kernel
      have hl : raw2091step0Labels = labelEmbedding7 ∘ raw2091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2091step0 raw2091step0Labels raw2091step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

theorem canonical2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2092 raw2092Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw2092 raw2092Labels = mixedMoment B raw2092step0 raw2092step0Labels := by
      have ha : raw2092step0 = (fun i j => raw2092 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2092step0 raw2092; decide +kernel
      have hl : raw2092step0Labels = raw2092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2092 raw2092Labels permutation152 permutation4
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical2093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2093 raw2093Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw2093 raw2093Labels = mixedMoment B raw2093step0 raw2093step0Labels := by
      have ha : raw2093step0 = (fun i j => raw2093 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2093step0 raw2093; decide +kernel
      have hl : raw2093step0Labels = raw2093Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2093 raw2093Labels permutation160 permutation6
    mixedMoment B raw2093step0 raw2093step0Labels = mixedMoment B raw2093step1 raw2093step1Labels := by
      have ha : raw2093step1 = -raw2093step0 := by apply Matrix.ext; change ∀ i j, raw2093step1 i j = -(raw2093step0 i j); unfold raw2093step1 raw2093step0; decide +kernel
      have hl : raw2093step1Labels = raw2093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2093step1 raw2093step1Labels = mixedMoment B raw2093step2 raw2093step2Labels := by
      have ha : raw2093step2 = raw2093step1 := by apply Matrix.ext; unfold raw2093step2 raw2093step1; decide +kernel
      have hl : raw2093step1Labels = labelEmbedding1 ∘ raw2093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2093step1 raw2093step1Labels raw2093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

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

theorem canonical2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2265 raw2265Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw2265 raw2265Labels = mixedMoment B raw2265step0 raw2265step0Labels := by
      have ha : raw2265step0 = (fun i j => raw2265 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2265step0 raw2265; decide +kernel
      have hl : raw2265step0Labels = raw2265Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2265 raw2265Labels permutation32 permutation4
    mixedMoment B raw2265step0 raw2265step0Labels = mixedMoment B raw2265step1 raw2265step1Labels := by
      have ha : raw2265step1 = raw2265step0 := by apply Matrix.ext; unfold raw2265step1 raw2265step0; decide +kernel
      have hl : raw2265step0Labels = labelEmbedding7 ∘ raw2265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2265step0 raw2265step0Labels raw2265step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2266 raw2266Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw2266 raw2266Labels = mixedMoment B raw2266step0 raw2266step0Labels := by
      have ha : raw2266step0 = (fun i j => raw2266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2266step0 raw2266; decide +kernel
      have hl : raw2266step0Labels = raw2266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2266 raw2266Labels permutation32 permutation4
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2267 raw2267Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw2267 raw2267Labels = mixedMoment B raw2267step0 raw2267step0Labels := by
      have ha : raw2267step0 = (fun i j => raw2267 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2267step0 raw2267; decide +kernel
      have hl : raw2267step0Labels = raw2267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2267 raw2267Labels permutation32 permutation6
    mixedMoment B raw2267step0 raw2267step0Labels = mixedMoment B raw2267step1 raw2267step1Labels := by
      have ha : raw2267step1 = -raw2267step0 := by apply Matrix.ext; change ∀ i j, raw2267step1 i j = -(raw2267step0 i j); unfold raw2267step1 raw2267step0; decide +kernel
      have hl : raw2267step1Labels = raw2267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2267step1 raw2267step1Labels = mixedMoment B raw2267step2 raw2267step2Labels := by
      have ha : raw2267step2 = raw2267step1 := by apply Matrix.ext; unfold raw2267step2 raw2267step1; decide +kernel
      have hl : raw2267step1Labels = labelEmbedding1 ∘ raw2267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2267step1 raw2267step1Labels raw2267step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

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

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

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

theorem canonical2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2514 raw2514Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw2514 raw2514Labels = mixedMoment B raw2514step0 raw2514step0Labels := by
      have ha : raw2514step0 = (fun i j => raw2514 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2514step0 raw2514; decide +kernel
      have hl : raw2514step0Labels = raw2514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2514 raw2514Labels permutation152 permutation4
    mixedMoment B raw2514step0 raw2514step0Labels = mixedMoment B raw2514step1 raw2514step1Labels := by
      have ha : raw2514step1 = raw2514step0 := by apply Matrix.ext; unfold raw2514step1 raw2514step0; decide +kernel
      have hl : raw2514step0Labels = labelEmbedding7 ∘ raw2514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2514step0 raw2514step0Labels raw2514step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2515 raw2515Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw2515 raw2515Labels = mixedMoment B raw2515step0 raw2515step0Labels := by
      have ha : raw2515step0 = (fun i j => raw2515 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2515step0 raw2515; decide +kernel
      have hl : raw2515step0Labels = raw2515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2515 raw2515Labels permutation152 permutation4
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2516 raw2516Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw2516 raw2516Labels = mixedMoment B raw2516step0 raw2516step0Labels := by
      have ha : raw2516step0 = (fun i j => raw2516 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2516step0 raw2516; decide +kernel
      have hl : raw2516step0Labels = raw2516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2516 raw2516Labels permutation176 permutation6
    mixedMoment B raw2516step0 raw2516step0Labels = mixedMoment B raw2516step1 raw2516step1Labels := by
      have ha : raw2516step1 = -raw2516step0 := by apply Matrix.ext; change ∀ i j, raw2516step1 i j = -(raw2516step0 i j); unfold raw2516step1 raw2516step0; decide +kernel
      have hl : raw2516step1Labels = raw2516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2516step1 raw2516step1Labels = mixedMoment B raw2516step2 raw2516step2Labels := by
      have ha : raw2516step2 = raw2516step1 := by apply Matrix.ext; unfold raw2516step2 raw2516step1; decide +kernel
      have hl : raw2516step1Labels = labelEmbedding1 ∘ raw2516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2516step1 raw2516step1Labels raw2516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2517 raw2517Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw2517 raw2517Labels = mixedMoment B raw2517step0 raw2517step0Labels := by
      have ha : raw2517step0 = (fun i j => raw2517 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2517step0 raw2517; decide +kernel
      have hl : raw2517step0Labels = raw2517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2517 raw2517Labels permutation32 permutation4
    mixedMoment B raw2517step0 raw2517step0Labels = mixedMoment B raw2517step1 raw2517step1Labels := by
      have ha : raw2517step1 = raw2517step0 := by apply Matrix.ext; unfold raw2517step1 raw2517step0; decide +kernel
      have hl : raw2517step0Labels = labelEmbedding7 ∘ raw2517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2517step0 raw2517step0Labels raw2517step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical2518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2518 raw2518Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2518 raw2518Labels = mixedMoment B raw2518step0 raw2518step0Labels := by
      have ha : raw2518step0 = (fun i j => raw2518 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2518step0 raw2518; decide +kernel
      have hl : raw2518step0Labels = raw2518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2518 raw2518Labels permutation32 permutation4
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2519 raw2519Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2519 raw2519Labels = mixedMoment B raw2519step0 raw2519step0Labels := by
      have ha : raw2519step0 = (fun i j => raw2519 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2519step0 raw2519; decide +kernel
      have hl : raw2519step0Labels = raw2519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2519 raw2519Labels permutation39 permutation6
    mixedMoment B raw2519step0 raw2519step0Labels = mixedMoment B raw2519step1 raw2519step1Labels := by
      have ha : raw2519step1 = -raw2519step0 := by apply Matrix.ext; change ∀ i j, raw2519step1 i j = -(raw2519step0 i j); unfold raw2519step1 raw2519step0; decide +kernel
      have hl : raw2519step1Labels = raw2519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2519step1 raw2519step1Labels = mixedMoment B raw2519step2 raw2519step2Labels := by
      have ha : raw2519step2 = raw2519step1 := by apply Matrix.ext; unfold raw2519step2 raw2519step1; decide +kernel
      have hl : raw2519step1Labels = labelEmbedding1 ∘ raw2519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2519step1 raw2519step1Labels raw2519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

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

theorem canonical10086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10086 raw10086Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw10086 raw10086Labels = mixedMoment B raw10086step0 raw10086step0Labels := by
      have ha : raw10086step0 = (fun i j => raw10086 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10086step0 raw10086; decide +kernel
      have hl : raw10086step0Labels = raw10086Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10086 raw10086Labels permutation676 permutation3
    mixedMoment B raw10086step0 raw10086step0Labels = mixedMoment B raw10086step1 raw10086step1Labels := by
      have ha : raw10086step1 = -raw10086step0 := by apply Matrix.ext; change ∀ i j, raw10086step1 i j = -(raw10086step0 i j); unfold raw10086step1 raw10086step0; decide +kernel
      have hl : raw10086step1Labels = raw10086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10086step1 raw10086step1Labels = mixedMoment B raw10086step2 raw10086step2Labels := by
      have ha : raw10086step2 = raw10086step1 := by apply Matrix.ext; unfold raw10086step2 raw10086step1; decide +kernel
      have hl : raw10086step1Labels = labelEmbedding6 ∘ raw10086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10086step1 raw10086step1Labels raw10086step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical10087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10087 raw10087Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw10087 raw10087Labels = mixedMoment B raw10087step0 raw10087step0Labels := by
      have hz : ∀ j, raw10087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10087step0 = (fun i j => raw10087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10087step0 raw10087; decide +kernel
      have hl : raw10087step0Labels = raw10087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10087 raw10087Labels permutation346 hz
    mixedMoment B raw10087step0 raw10087step0Labels = mixedMoment B raw10087step1 raw10087step1Labels := by
      have ha : raw10087step1 = (fun i j => raw10087step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10087step1 raw10087step0; decide +kernel
      have hl : raw10087step1Labels = raw10087step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10087step0 raw10087step0Labels permutation149 permutation3
    mixedMoment B raw10087step1 raw10087step1Labels = mixedMoment B raw10087step2 raw10087step2Labels := by
      have ha : raw10087step2 = -raw10087step1 := by apply Matrix.ext; change ∀ i j, raw10087step2 i j = -(raw10087step1 i j); unfold raw10087step2 raw10087step1; decide +kernel
      have hl : raw10087step2Labels = raw10087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10087step2 raw10087step2Labels = mixedMoment B raw10087step3 raw10087step3Labels := by
      have ha : raw10087step3 = raw10087step2 := by apply Matrix.ext; unfold raw10087step3 raw10087step2; decide +kernel
      have hl : raw10087step2Labels = labelEmbedding6 ∘ raw10087step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10087step2 raw10087step2Labels raw10087step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical10088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10088 raw10088Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw10088 raw10088Labels = mixedMoment B raw10088step0 raw10088step0Labels := by
      have hz : ∀ j, raw10088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10088step0 = (fun i j => raw10088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10088step0 raw10088; decide +kernel
      have hl : raw10088step0Labels = raw10088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10088 raw10088Labels permutation346 hz
    mixedMoment B raw10088step0 raw10088step0Labels = mixedMoment B raw10088step1 raw10088step1Labels := by
      have ha : raw10088step1 = (fun i j => raw10088step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10088step1 raw10088step0; decide +kernel
      have hl : raw10088step1Labels = raw10088step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10088step0 raw10088step0Labels permutation137 permutation5
    mixedMoment B raw10088step1 raw10088step1Labels = mixedMoment B raw10088step2 raw10088step2Labels := by
      have ha : raw10088step2 = raw10088step1 := by apply Matrix.ext; unfold raw10088step2 raw10088step1; decide +kernel
      have hl : raw10088step1Labels = labelEmbedding8 ∘ raw10088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10088step1 raw10088step1Labels raw10088step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical10089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10089 raw10089Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw10089 raw10089Labels = mixedMoment B raw10089step0 raw10089step0Labels := by
      have hz : ∀ j, raw10089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10089step0 = (fun i j => raw10089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10089step0 raw10089; decide +kernel
      have hl : raw10089step0Labels = raw10089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10089 raw10089Labels permutation346 hz
    mixedMoment B raw10089step0 raw10089step0Labels = mixedMoment B raw10089step1 raw10089step1Labels := by
      have ha : raw10089step1 = (fun i j => raw10089step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10089step1 raw10089step0; decide +kernel
      have hl : raw10089step1Labels = raw10089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10089step0 raw10089step0Labels permutation33 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical10090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10090 raw10090Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw10090 raw10090Labels = mixedMoment B raw10090step0 raw10090step0Labels := by
      have hz : ∀ j, raw10090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10090step0 = (fun i j => raw10090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10090step0 raw10090; decide +kernel
      have hl : raw10090step0Labels = raw10090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10090 raw10090Labels permutation346 hz
    mixedMoment B raw10090step0 raw10090step0Labels = mixedMoment B raw10090step1 raw10090step1Labels := by
      have ha : raw10090step1 = (fun i j => raw10090step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10090step1 raw10090step0; decide +kernel
      have hl : raw10090step1Labels = raw10090step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10090step0 raw10090step0Labels permutation40 permutation3
    mixedMoment B raw10090step1 raw10090step1Labels = mixedMoment B raw10090step2 raw10090step2Labels := by
      have ha : raw10090step2 = raw10090step1 := by apply Matrix.ext; unfold raw10090step2 raw10090step1; decide +kernel
      have hl : raw10090step1Labels = labelEmbedding6 ∘ raw10090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10090step1 raw10090step1Labels raw10090step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical10091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10091 raw10091Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw10091 raw10091Labels = mixedMoment B raw10091step0 raw10091step0Labels := by
      have ha : raw10091step0 = (fun i j => raw10091 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10091step0 raw10091; decide +kernel
      have hl : raw10091step0Labels = raw10091Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10091 raw10091Labels permutation184 permutation3
    mixedMoment B raw10091step0 raw10091step0Labels = mixedMoment B raw10091step1 raw10091step1Labels := by
      have ha : raw10091step1 = raw10091step0 := by apply Matrix.ext; unfold raw10091step1 raw10091step0; decide +kernel
      have hl : raw10091step0Labels = labelEmbedding6 ∘ raw10091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10091step0 raw10091step0Labels raw10091step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

theorem canonical10092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10092 raw10092Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw10092 raw10092Labels = mixedMoment B raw10092step0 raw10092step0Labels := by
      have hz : ∀ j, raw10092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10092step0 = (fun i j => raw10092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10092step0 raw10092; decide +kernel
      have hl : raw10092step0Labels = raw10092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10092 raw10092Labels permutation346 hz
    mixedMoment B raw10092step0 raw10092step0Labels = mixedMoment B raw10092step1 raw10092step1Labels := by
      have ha : raw10092step1 = (fun i j => raw10092step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10092step1 raw10092step0; decide +kernel
      have hl : raw10092step1Labels = raw10092step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10092step0 raw10092step0Labels permutation40 permutation3
    mixedMoment B raw10092step1 raw10092step1Labels = mixedMoment B raw10092step2 raw10092step2Labels := by
      have ha : raw10092step2 = raw10092step1 := by apply Matrix.ext; unfold raw10092step2 raw10092step1; decide +kernel
      have hl : raw10092step1Labels = labelEmbedding6 ∘ raw10092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10092step1 raw10092step1Labels raw10092step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical10093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10093 raw10093Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw10093 raw10093Labels = mixedMoment B raw10093step0 raw10093step0Labels := by
      have hz : ∀ j, raw10093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10093step0 = (fun i j => raw10093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10093step0 raw10093; decide +kernel
      have hl : raw10093step0Labels = raw10093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10093 raw10093Labels permutation346 hz
    mixedMoment B raw10093step0 raw10093step0Labels = mixedMoment B raw10093step1 raw10093step1Labels := by
      have ha : raw10093step1 = (fun i j => raw10093step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10093step1 raw10093step0; decide +kernel
      have hl : raw10093step1Labels = raw10093step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10093step0 raw10093step0Labels permutation40 permutation3
    mixedMoment B raw10093step1 raw10093step1Labels = mixedMoment B raw10093step2 raw10093step2Labels := by
      have ha : raw10093step2 = raw10093step1 := by apply Matrix.ext; unfold raw10093step2 raw10093step1; decide +kernel
      have hl : raw10093step1Labels = labelEmbedding6 ∘ raw10093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10093step1 raw10093step1Labels raw10093step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical10094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10094 raw10094Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10094 raw10094Labels = mixedMoment B raw10094step0 raw10094step0Labels := by
      have hz : ∀ j, raw10094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10094step0 = (fun i j => raw10094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10094step0 raw10094; decide +kernel
      have hl : raw10094step0Labels = raw10094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10094 raw10094Labels permutation346 hz
    mixedMoment B raw10094step0 raw10094step0Labels = mixedMoment B raw10094step1 raw10094step1Labels := by
      have ha : raw10094step1 = (fun i j => raw10094step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10094step1 raw10094step0; decide +kernel
      have hl : raw10094step1Labels = raw10094step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10094step0 raw10094step0Labels permutation41 permutation3
    mixedMoment B raw10094step1 raw10094step1Labels = mixedMoment B raw10094step2 raw10094step2Labels := by
      have ha : raw10094step2 = raw10094step1 := by apply Matrix.ext; unfold raw10094step2 raw10094step1; decide +kernel
      have hl : raw10094step1Labels = labelEmbedding6 ∘ raw10094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10094step1 raw10094step1Labels raw10094step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical10095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10095 raw10095Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw10095 raw10095Labels = mixedMoment B raw10095step0 raw10095step0Labels := by
      have ha : raw10095step0 = (fun i j => raw10095 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10095step0 raw10095; decide +kernel
      have hl : raw10095step0Labels = raw10095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10095 raw10095Labels permutation202 permutation3
    mixedMoment B raw10095step0 raw10095step0Labels = mixedMoment B raw10095step1 raw10095step1Labels := by
      have ha : raw10095step1 = raw10095step0 := by apply Matrix.ext; unfold raw10095step1 raw10095step0; decide +kernel
      have hl : raw10095step0Labels = labelEmbedding6 ∘ raw10095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10095step0 raw10095step0Labels raw10095step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

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

theorem canonical10097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10097 raw10097Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw10097 raw10097Labels = mixedMoment B raw10097step0 raw10097step0Labels := by
      have ha : raw10097step0 = (fun i j => raw10097 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10097step0 raw10097; decide +kernel
      have hl : raw10097step0Labels = raw10097Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10097 raw10097Labels permutation202 permutation3
    mixedMoment B raw10097step0 raw10097step0Labels = mixedMoment B raw10097step1 raw10097step1Labels := by
      have ha : raw10097step1 = raw10097step0 := by apply Matrix.ext; unfold raw10097step1 raw10097step0; decide +kernel
      have hl : raw10097step0Labels = labelEmbedding6 ∘ raw10097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10097step0 raw10097step0Labels raw10097step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical10098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10098 raw10098Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw10098 raw10098Labels = mixedMoment B raw10098step0 raw10098step0Labels := by
      have ha : raw10098step0 = (fun i j => raw10098 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10098step0 raw10098; decide +kernel
      have hl : raw10098step0Labels = raw10098Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10098 raw10098Labels permutation212 permutation3
    mixedMoment B raw10098step0 raw10098step0Labels = mixedMoment B raw10098step1 raw10098step1Labels := by
      have ha : raw10098step1 = raw10098step0 := by apply Matrix.ext; unfold raw10098step1 raw10098step0; decide +kernel
      have hl : raw10098step0Labels = labelEmbedding6 ∘ raw10098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10098step0 raw10098step0Labels raw10098step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical10099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10099 raw10099Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw10099 raw10099Labels = mixedMoment B raw10099step0 raw10099step0Labels := by
      have ha : raw10099step0 = (fun i j => raw10099 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10099step0 raw10099; decide +kernel
      have hl : raw10099step0Labels = raw10099Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10099 raw10099Labels permutation202 permutation3
    mixedMoment B raw10099step0 raw10099step0Labels = mixedMoment B raw10099step1 raw10099step1Labels := by
      have ha : raw10099step1 = raw10099step0 := by apply Matrix.ext; unfold raw10099step1 raw10099step0; decide +kernel
      have hl : raw10099step0Labels = labelEmbedding6 ∘ raw10099step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10099step0 raw10099step0Labels raw10099step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical10100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10100 raw10100Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw10100 raw10100Labels = mixedMoment B raw10100step0 raw10100step0Labels := by
      have hz : ∀ j, raw10100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10100step0 = (fun i j => raw10100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10100step0 raw10100; decide +kernel
      have hl : raw10100step0Labels = raw10100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10100 raw10100Labels permutation346 hz
    mixedMoment B raw10100step0 raw10100step0Labels = mixedMoment B raw10100step1 raw10100step1Labels := by
      have ha : raw10100step1 = (fun i j => raw10100step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10100step1 raw10100step0; decide +kernel
      have hl : raw10100step1Labels = raw10100step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10100step0 raw10100step0Labels permutation32 permutation3
    mixedMoment B raw10100step1 raw10100step1Labels = mixedMoment B raw10100step2 raw10100step2Labels := by
      have ha : raw10100step2 = raw10100step1 := by apply Matrix.ext; unfold raw10100step2 raw10100step1; decide +kernel
      have hl : raw10100step1Labels = labelEmbedding6 ∘ raw10100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10100step1 raw10100step1Labels raw10100step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

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

theorem canonical10102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10102 raw10102Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw10102 raw10102Labels = mixedMoment B raw10102step0 raw10102step0Labels := by
      have ha : raw10102step0 = (fun i j => raw10102 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10102step0 raw10102; decide +kernel
      have hl : raw10102step0Labels = raw10102Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10102 raw10102Labels permutation176 permutation3
    mixedMoment B raw10102step0 raw10102step0Labels = mixedMoment B raw10102step1 raw10102step1Labels := by
      have ha : raw10102step1 = raw10102step0 := by apply Matrix.ext; unfold raw10102step1 raw10102step0; decide +kernel
      have hl : raw10102step0Labels = labelEmbedding6 ∘ raw10102step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10102step0 raw10102step0Labels raw10102step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

theorem canonical10103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10103 raw10103Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10103 raw10103Labels = mixedMoment B raw10103step0 raw10103step0Labels := by
      have hz : ∀ j, raw10103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10103step0 = (fun i j => raw10103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10103step0 raw10103; decide +kernel
      have hl : raw10103step0Labels = raw10103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10103 raw10103Labels permutation346 hz
    mixedMoment B raw10103step0 raw10103step0Labels = mixedMoment B raw10103step1 raw10103step1Labels := by
      have ha : raw10103step1 = (fun i j => raw10103step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10103step1 raw10103step0; decide +kernel
      have hl : raw10103step1Labels = raw10103step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10103step0 raw10103step0Labels permutation44 permutation3
    mixedMoment B raw10103step1 raw10103step1Labels = mixedMoment B raw10103step2 raw10103step2Labels := by
      have ha : raw10103step2 = raw10103step1 := by apply Matrix.ext; unfold raw10103step2 raw10103step1; decide +kernel
      have hl : raw10103step1Labels = labelEmbedding6 ∘ raw10103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10103step1 raw10103step1Labels raw10103step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical10104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10104 raw10104Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw10104 raw10104Labels = mixedMoment B raw10104step0 raw10104step0Labels := by
      have hz : ∀ j, raw10104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10104step0 = (fun i j => raw10104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10104step0 raw10104; decide +kernel
      have hl : raw10104step0Labels = raw10104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10104 raw10104Labels permutation346 hz
    mixedMoment B raw10104step0 raw10104step0Labels = mixedMoment B raw10104step1 raw10104step1Labels := by
      have ha : raw10104step1 = (fun i j => raw10104step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10104step1 raw10104step0; decide +kernel
      have hl : raw10104step1Labels = raw10104step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10104step0 raw10104step0Labels permutation32 permutation3
    mixedMoment B raw10104step1 raw10104step1Labels = mixedMoment B raw10104step2 raw10104step2Labels := by
      have ha : raw10104step2 = raw10104step1 := by apply Matrix.ext; unfold raw10104step2 raw10104step1; decide +kernel
      have hl : raw10104step1Labels = labelEmbedding6 ∘ raw10104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10104step1 raw10104step1Labels raw10104step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical10105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10105 raw10105Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw10105 raw10105Labels = mixedMoment B raw10105step0 raw10105step0Labels := by
      have hz : ∀ j, raw10105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10105step0 = (fun i j => raw10105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10105step0 raw10105; decide +kernel
      have hl : raw10105step0Labels = raw10105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10105 raw10105Labels permutation346 hz
    mixedMoment B raw10105step0 raw10105step0Labels = mixedMoment B raw10105step1 raw10105step1Labels := by
      have ha : raw10105step1 = (fun i j => raw10105step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10105step1 raw10105step0; decide +kernel
      have hl : raw10105step1Labels = raw10105step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10105step0 raw10105step0Labels permutation38 permutation3
    mixedMoment B raw10105step1 raw10105step1Labels = mixedMoment B raw10105step2 raw10105step2Labels := by
      have ha : raw10105step2 = raw10105step1 := by apply Matrix.ext; unfold raw10105step2 raw10105step1; decide +kernel
      have hl : raw10105step1Labels = labelEmbedding6 ∘ raw10105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10105step1 raw10105step1Labels raw10105step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

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

theorem canonical10107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10107 raw10107Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw10107 raw10107Labels = mixedMoment B raw10107step0 raw10107step0Labels := by
      have ha : raw10107step0 = (fun i j => raw10107 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10107step0 raw10107; decide +kernel
      have hl : raw10107step0Labels = raw10107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10107 raw10107Labels permutation182 permutation3
    mixedMoment B raw10107step0 raw10107step0Labels = mixedMoment B raw10107step1 raw10107step1Labels := by
      have ha : raw10107step1 = raw10107step0 := by apply Matrix.ext; unfold raw10107step1 raw10107step0; decide +kernel
      have hl : raw10107step0Labels = labelEmbedding6 ∘ raw10107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10107step0 raw10107step0Labels raw10107step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

theorem canonical10108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10108 raw10108Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw10108 raw10108Labels = mixedMoment B raw10108step0 raw10108step0Labels := by
      have hz : ∀ j, raw10108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10108step0 = (fun i j => raw10108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10108step0 raw10108; decide +kernel
      have hl : raw10108step0Labels = raw10108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10108 raw10108Labels permutation346 hz
    mixedMoment B raw10108step0 raw10108step0Labels = mixedMoment B raw10108step1 raw10108step1Labels := by
      have ha : raw10108step1 = (fun i j => raw10108step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10108step1 raw10108step0; decide +kernel
      have hl : raw10108step1Labels = raw10108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10108step0 raw10108step0Labels permutation38 permutation3
    mixedMoment B raw10108step1 raw10108step1Labels = mixedMoment B raw10108step2 raw10108step2Labels := by
      have ha : raw10108step2 = raw10108step1 := by apply Matrix.ext; unfold raw10108step2 raw10108step1; decide +kernel
      have hl : raw10108step1Labels = labelEmbedding6 ∘ raw10108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10108step1 raw10108step1Labels raw10108step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical10109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10109 raw10109Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw10109 raw10109Labels = mixedMoment B raw10109step0 raw10109step0Labels := by
      have hz : ∀ j, raw10109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10109step0 = (fun i j => raw10109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10109step0 raw10109; decide +kernel
      have hl : raw10109step0Labels = raw10109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10109 raw10109Labels permutation346 hz
    mixedMoment B raw10109step0 raw10109step0Labels = mixedMoment B raw10109step1 raw10109step1Labels := by
      have ha : raw10109step1 = (fun i j => raw10109step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10109step1 raw10109step0; decide +kernel
      have hl : raw10109step1Labels = raw10109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10109step0 raw10109step0Labels permutation39 permutation3
    mixedMoment B raw10109step1 raw10109step1Labels = mixedMoment B raw10109step2 raw10109step2Labels := by
      have ha : raw10109step2 = raw10109step1 := by apply Matrix.ext; unfold raw10109step2 raw10109step1; decide +kernel
      have hl : raw10109step1Labels = labelEmbedding6 ∘ raw10109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10109step1 raw10109step1Labels raw10109step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

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

theorem canonical10111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10111 raw10111Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw10111 raw10111Labels = mixedMoment B raw10111step0 raw10111step0Labels := by
      have hz : ∀ j, raw10111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10111step0 = (fun i j => raw10111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10111step0 raw10111; decide +kernel
      have hl : raw10111step0Labels = raw10111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10111 raw10111Labels permutation346 hz
    mixedMoment B raw10111step0 raw10111step0Labels = mixedMoment B raw10111step1 raw10111step1Labels := by
      have ha : raw10111step1 = (fun i j => raw10111step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10111step1 raw10111step0; decide +kernel
      have hl : raw10111step1Labels = raw10111step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10111step0 raw10111step0Labels permutation151 permutation3
    mixedMoment B raw10111step1 raw10111step1Labels = mixedMoment B raw10111step2 raw10111step2Labels := by
      have ha : raw10111step2 = -raw10111step1 := by apply Matrix.ext; change ∀ i j, raw10111step2 i j = -(raw10111step1 i j); unfold raw10111step2 raw10111step1; decide +kernel
      have hl : raw10111step2Labels = raw10111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10111step2 raw10111step2Labels = mixedMoment B raw10111step3 raw10111step3Labels := by
      have ha : raw10111step3 = raw10111step2 := by apply Matrix.ext; unfold raw10111step3 raw10111step2; decide +kernel
      have hl : raw10111step2Labels = labelEmbedding6 ∘ raw10111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10111step2 raw10111step2Labels raw10111step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

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

theorem canonical1218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1218 raw1218Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw1218 raw1218Labels = mixedMoment B raw1218step0 raw1218step0Labels := by
      have ha : raw1218step0 = (fun i j => raw1218 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1218step0 raw1218; decide +kernel
      have hl : raw1218step0Labels = raw1218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1218 raw1218Labels permutation32 permutation4
    mixedMoment B raw1218step0 raw1218step0Labels = mixedMoment B raw1218step1 raw1218step1Labels := by
      have ha : raw1218step1 = raw1218step0 := by apply Matrix.ext; unfold raw1218step1 raw1218step0; decide +kernel
      have hl : raw1218step0Labels = labelEmbedding7 ∘ raw1218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1218step0 raw1218step0Labels raw1218step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

theorem canonical1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1219 raw1219Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw1219 raw1219Labels = mixedMoment B raw1219step0 raw1219step0Labels := by
      have ha : raw1219step0 = (fun i j => raw1219 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1219step0 raw1219; decide +kernel
      have hl : raw1219step0Labels = raw1219Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1219 raw1219Labels permutation32 permutation4
    _ = mixedMoment B node985 node985Labels := by rfl

theorem canonical1220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1220 raw1220Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw1220 raw1220Labels = mixedMoment B raw1220step0 raw1220step0Labels := by
      have ha : raw1220step0 = (fun i j => raw1220 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1220step0 raw1220; decide +kernel
      have hl : raw1220step0Labels = raw1220Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1220 raw1220Labels permutation32 permutation6
    mixedMoment B raw1220step0 raw1220step0Labels = mixedMoment B raw1220step1 raw1220step1Labels := by
      have ha : raw1220step1 = -raw1220step0 := by apply Matrix.ext; change ∀ i j, raw1220step1 i j = -(raw1220step0 i j); unfold raw1220step1 raw1220step0; decide +kernel
      have hl : raw1220step1Labels = raw1220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1220step1 raw1220step1Labels = mixedMoment B raw1220step2 raw1220step2Labels := by
      have ha : raw1220step2 = raw1220step1 := by apply Matrix.ext; unfold raw1220step2 raw1220step1; decide +kernel
      have hl : raw1220step1Labels = labelEmbedding1 ∘ raw1220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1220step1 raw1220step1Labels raw1220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1618 node1618Labels := by rfl

theorem canonical1230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1230 raw1230Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw1230 raw1230Labels = mixedMoment B raw1230step0 raw1230step0Labels := by
      have ha : raw1230step0 = (fun i j => raw1230 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1230step0 raw1230; decide +kernel
      have hl : raw1230step0Labels = raw1230Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1230 raw1230Labels permutation32 permutation4
    mixedMoment B raw1230step0 raw1230step0Labels = mixedMoment B raw1230step1 raw1230step1Labels := by
      have ha : raw1230step1 = raw1230step0 := by apply Matrix.ext; unfold raw1230step1 raw1230step0; decide +kernel
      have hl : raw1230step0Labels = labelEmbedding7 ∘ raw1230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1230step0 raw1230step0Labels raw1230step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical1231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1231 raw1231Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw1231 raw1231Labels = mixedMoment B raw1231step0 raw1231step0Labels := by
      have ha : raw1231step0 = (fun i j => raw1231 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1231step0 raw1231; decide +kernel
      have hl : raw1231step0Labels = raw1231Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1231 raw1231Labels permutation32 permutation4
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical1232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1232 raw1232Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw1232 raw1232Labels = mixedMoment B raw1232step0 raw1232step0Labels := by
      have ha : raw1232step0 = (fun i j => raw1232 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1232step0 raw1232; decide +kernel
      have hl : raw1232step0Labels = raw1232Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1232 raw1232Labels permutation32 permutation6
    mixedMoment B raw1232step0 raw1232step0Labels = mixedMoment B raw1232step1 raw1232step1Labels := by
      have ha : raw1232step1 = -raw1232step0 := by apply Matrix.ext; change ∀ i j, raw1232step1 i j = -(raw1232step0 i j); unfold raw1232step1 raw1232step0; decide +kernel
      have hl : raw1232step1Labels = raw1232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1232step1 raw1232step1Labels = mixedMoment B raw1232step2 raw1232step2Labels := by
      have ha : raw1232step2 = raw1232step1 := by apply Matrix.ext; unfold raw1232step2 raw1232step1; decide +kernel
      have hl : raw1232step1Labels = labelEmbedding1 ∘ raw1232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1232step1 raw1232step1Labels raw1232step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

theorem canonical1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1257 raw1257Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw1257 raw1257Labels = mixedMoment B raw1257step0 raw1257step0Labels := by
      have ha : raw1257step0 = (fun i j => raw1257 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1257step0 raw1257; decide +kernel
      have hl : raw1257step0Labels = raw1257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1257 raw1257Labels permutation32 permutation4
    mixedMoment B raw1257step0 raw1257step0Labels = mixedMoment B raw1257step1 raw1257step1Labels := by
      have ha : raw1257step1 = raw1257step0 := by apply Matrix.ext; unfold raw1257step1 raw1257step0; decide +kernel
      have hl : raw1257step0Labels = labelEmbedding7 ∘ raw1257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1257step0 raw1257step0Labels raw1257step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1258 raw1258Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw1258 raw1258Labels = mixedMoment B raw1258step0 raw1258step0Labels := by
      have ha : raw1258step0 = (fun i j => raw1258 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1258step0 raw1258; decide +kernel
      have hl : raw1258step0Labels = raw1258Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1258 raw1258Labels permutation32 permutation4
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1259 raw1259Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw1259 raw1259Labels = mixedMoment B raw1259step0 raw1259step0Labels := by
      have ha : raw1259step0 = (fun i j => raw1259 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1259step0 raw1259; decide +kernel
      have hl : raw1259step0Labels = raw1259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1259 raw1259Labels permutation40 permutation6
    mixedMoment B raw1259step0 raw1259step0Labels = mixedMoment B raw1259step1 raw1259step1Labels := by
      have ha : raw1259step1 = -raw1259step0 := by apply Matrix.ext; change ∀ i j, raw1259step1 i j = -(raw1259step0 i j); unfold raw1259step1 raw1259step0; decide +kernel
      have hl : raw1259step1Labels = raw1259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1259step1 raw1259step1Labels = mixedMoment B raw1259step2 raw1259step2Labels := by
      have ha : raw1259step2 = raw1259step1 := by apply Matrix.ext; unfold raw1259step2 raw1259step1; decide +kernel
      have hl : raw1259step1Labels = labelEmbedding1 ∘ raw1259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1259step1 raw1259step1Labels raw1259step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

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

theorem singleton4404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4404 node4404Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node985 node985Labels + mixedMoment B node1618 node1618Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1218 singletonSmall4404
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4404) = raw1218Labels := by decide +kernel
  rw [hl, canonical1218 B hB] at h
  have hc0 : mixedMoment B raw1218 (Fin.cases (0 : Fin 2) singletonSmall4404) =
      mixedMoment B node985 node985Labels := by
    have ha : raw1218 = raw1219 := by apply Matrix.ext; unfold raw1218 raw1219; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4404 = raw1219Labels := by decide +kernel
    rw [ha, hj, canonical1219 B hB]
  have hc1 : mixedMoment B raw1218 (Fin.cases (1 : Fin 2) singletonSmall4404) =
      mixedMoment B node1618 node1618Labels := by
    have ha : raw1218 = raw1220 := by apply Matrix.ext; unfold raw1218 raw1220; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4404 = raw1220Labels := by decide +kernel
    rw [ha, hj, canonical1220 B hB]
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

theorem singleton4419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4419 node4419Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1000 node1000Labels + mixedMoment B node1605 node1605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1230 singletonSmall4419
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4419) = raw1230Labels := by decide +kernel
  rw [hl, canonical1230 B hB] at h
  have hc0 : mixedMoment B raw1230 (Fin.cases (0 : Fin 2) singletonSmall4419) =
      mixedMoment B node1000 node1000Labels := by
    have ha : raw1230 = raw1231 := by apply Matrix.ext; unfold raw1230 raw1231; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4419 = raw1231Labels := by decide +kernel
    rw [ha, hj, canonical1231 B hB]
  have hc1 : mixedMoment B raw1230 (Fin.cases (1 : Fin 2) singletonSmall4419) =
      mixedMoment B node1605 node1605Labels := by
    have ha : raw1230 = raw1232 := by apply Matrix.ext; unfold raw1230 raw1232; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4419 = raw1232Labels := by decide +kernel
    rw [ha, hj, canonical1232 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4457 node4457Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1040 node1040Labels + mixedMoment B node1707 node1707Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1257 singletonSmall4457
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4457) = raw1257Labels := by decide +kernel
  rw [hl, canonical1257 B hB] at h
  have hc0 : mixedMoment B raw1257 (Fin.cases (0 : Fin 2) singletonSmall4457) =
      mixedMoment B node1040 node1040Labels := by
    have ha : raw1257 = raw1258 := by apply Matrix.ext; unfold raw1257 raw1258; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4457 = raw1258Labels := by decide +kernel
    rw [ha, hj, canonical1258 B hB]
  have hc1 : mixedMoment B raw1257 (Fin.cases (1 : Fin 2) singletonSmall4457) =
      mixedMoment B node1707 node1707Labels := by
    have ha : raw1257 = raw1259 := by apply Matrix.ext; unfold raw1257 raw1259; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4457 = raw1259Labels := by decide +kernel
    rw [ha, hj, canonical1259 B hB]
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

theorem singleton5003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5003 node5003Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2388 node2388Labels + mixedMoment B node3354 node3354Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2016 singletonSmall5003
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5003) = raw2016Labels := by decide +kernel
  rw [hl, canonical2016 B hB] at h
  have hc0 : mixedMoment B raw2016 (Fin.cases (0 : Fin 2) singletonSmall5003) =
      mixedMoment B node2388 node2388Labels := by
    have ha : raw2016 = raw2017 := by apply Matrix.ext; unfold raw2016 raw2017; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5003 = raw2017Labels := by decide +kernel
    rw [ha, hj, canonical2017 B hB]
  have hc1 : mixedMoment B raw2016 (Fin.cases (1 : Fin 2) singletonSmall5003) =
      mixedMoment B node3354 node3354Labels := by
    have ha : raw2016 = raw2018 := by apply Matrix.ext; unfold raw2016 raw2018; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5003 = raw2018Labels := by decide +kernel
    rw [ha, hj, canonical2018 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5015 node5015Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2400 node2400Labels + mixedMoment B node3344 node3344Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2025 singletonSmall5015
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5015) = raw2025Labels := by decide +kernel
  rw [hl, canonical2025 B hB] at h
  have hc0 : mixedMoment B raw2025 (Fin.cases (0 : Fin 2) singletonSmall5015) =
      mixedMoment B node2400 node2400Labels := by
    have ha : raw2025 = raw2026 := by apply Matrix.ext; unfold raw2025 raw2026; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5015 = raw2026Labels := by decide +kernel
    rw [ha, hj, canonical2026 B hB]
  have hc1 : mixedMoment B raw2025 (Fin.cases (1 : Fin 2) singletonSmall5015) =
      mixedMoment B node3344 node3344Labels := by
    have ha : raw2025 = raw2027 := by apply Matrix.ext; unfold raw2025 raw2027; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5015 = raw2027Labels := by decide +kernel
    rw [ha, hj, canonical2027 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5050 node5050Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2452 node2452Labels + mixedMoment B node3433 node3433Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2076 singletonSmall5050
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5050) = raw2076Labels := by decide +kernel
  rw [hl, canonical2076 B hB] at h
  have hc0 : mixedMoment B raw2076 (Fin.cases (0 : Fin 2) singletonSmall5050) =
      mixedMoment B node2452 node2452Labels := by
    have ha : raw2076 = raw2077 := by apply Matrix.ext; unfold raw2076 raw2077; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5050 = raw2077Labels := by decide +kernel
    rw [ha, hj, canonical2077 B hB]
  have hc1 : mixedMoment B raw2076 (Fin.cases (1 : Fin 2) singletonSmall5050) =
      mixedMoment B node3433 node3433Labels := by
    have ha : raw2076 = raw2078 := by apply Matrix.ext; unfold raw2076 raw2078; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5050 = raw2078Labels := by decide +kernel
    rw [ha, hj, canonical2078 B hB]
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

theorem singleton5056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5056 node5056Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2459 node2459Labels + mixedMoment B node3429 node3429Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2082 singletonSmall5056
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5056) = raw2082Labels := by decide +kernel
  rw [hl, canonical2082 B hB] at h
  have hc0 : mixedMoment B raw2082 (Fin.cases (0 : Fin 2) singletonSmall5056) =
      mixedMoment B node2459 node2459Labels := by
    have ha : raw2082 = raw2083 := by apply Matrix.ext; unfold raw2082 raw2083; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5056 = raw2083Labels := by decide +kernel
    rw [ha, hj, canonical2083 B hB]
  have hc1 : mixedMoment B raw2082 (Fin.cases (1 : Fin 2) singletonSmall5056) =
      mixedMoment B node3429 node3429Labels := by
    have ha : raw2082 = raw2084 := by apply Matrix.ext; unfold raw2082 raw2084; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5056 = raw2084Labels := by decide +kernel
    rw [ha, hj, canonical2084 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5072 node5072Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2479 node2479Labels + mixedMoment B node3459 node3459Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2091 singletonSmall5072
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5072) = raw2091Labels := by decide +kernel
  rw [hl, canonical2091 B hB] at h
  have hc0 : mixedMoment B raw2091 (Fin.cases (0 : Fin 2) singletonSmall5072) =
      mixedMoment B node2479 node2479Labels := by
    have ha : raw2091 = raw2092 := by apply Matrix.ext; unfold raw2091 raw2092; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5072 = raw2092Labels := by decide +kernel
    rw [ha, hj, canonical2092 B hB]
  have hc1 : mixedMoment B raw2091 (Fin.cases (1 : Fin 2) singletonSmall5072) =
      mixedMoment B node3459 node3459Labels := by
    have ha : raw2091 = raw2093 := by apply Matrix.ext; unfold raw2091 raw2093; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5072 = raw2093Labels := by decide +kernel
    rw [ha, hj, canonical2093 B hB]
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

theorem singleton5248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5248 node5248Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2705 node2705Labels + mixedMoment B node3498 node3498Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2265 singletonSmall5248
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5248) = raw2265Labels := by decide +kernel
  rw [hl, canonical2265 B hB] at h
  have hc0 : mixedMoment B raw2265 (Fin.cases (0 : Fin 2) singletonSmall5248) =
      mixedMoment B node2705 node2705Labels := by
    have ha : raw2265 = raw2266 := by apply Matrix.ext; unfold raw2265 raw2266; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5248 = raw2266Labels := by decide +kernel
    rw [ha, hj, canonical2266 B hB]
  have hc1 : mixedMoment B raw2265 (Fin.cases (1 : Fin 2) singletonSmall5248) =
      mixedMoment B node3498 node3498Labels := by
    have ha : raw2265 = raw2267 := by apply Matrix.ext; unfold raw2265 raw2267; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5248 = raw2267Labels := by decide +kernel
    rw [ha, hj, canonical2267 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
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

theorem singleton5424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5424 node5424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3838 node3838Labels + mixedMoment B node3843 node3843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2514 singletonSmall5424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5424) = raw2514Labels := by decide +kernel
  rw [hl, canonical2514 B hB] at h
  have hc0 : mixedMoment B raw2514 (Fin.cases (0 : Fin 2) singletonSmall5424) =
      mixedMoment B node3838 node3838Labels := by
    have ha : raw2514 = raw2515 := by apply Matrix.ext; unfold raw2514 raw2515; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5424 = raw2515Labels := by decide +kernel
    rw [ha, hj, canonical2515 B hB]
  have hc1 : mixedMoment B raw2514 (Fin.cases (1 : Fin 2) singletonSmall5424) =
      mixedMoment B node3843 node3843Labels := by
    have ha : raw2514 = raw2516 := by apply Matrix.ext; unfold raw2514 raw2516; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5424 = raw2516Labels := by decide +kernel
    rw [ha, hj, canonical2516 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5428 node5428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3845 node3845Labels + mixedMoment B node3845 node3845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2517 singletonSmall5428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5428) = raw2517Labels := by decide +kernel
  rw [hl, canonical2517 B hB] at h
  have hc0 : mixedMoment B raw2517 (Fin.cases (0 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2518 := by apply Matrix.ext; unfold raw2517 raw2518; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5428 = raw2518Labels := by decide +kernel
    rw [ha, hj, canonical2518 B hB]
  have hc1 : mixedMoment B raw2517 (Fin.cases (1 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2519 := by apply Matrix.ext; unfold raw2517 raw2519; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5428 = raw2519Labels := by decide +kernel
    rw [ha, hj, canonical2519 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node979 node979Labels = Sparse.eval nodeValue979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 979) = mixedMoment B node979 node979Labels := rfl
  simpa [nodeValue979, Sparse.eval] using hc.symm

theorem sound985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node985 node985Labels = Sparse.eval nodeValue985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 985) = mixedMoment B node985 node985Labels := rfl
  simpa [nodeValue985, Sparse.eval] using hc.symm

theorem sound1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1000 node1000Labels = Sparse.eval nodeValue1000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1000) = mixedMoment B node1000 node1000Labels := rfl
  simpa [nodeValue1000, Sparse.eval] using hc.symm

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

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

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

theorem sound1597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1597 node1597Labels = Sparse.eval nodeValue1597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1597) = mixedMoment B node1597 node1597Labels := rfl
  simpa [nodeValue1597, Sparse.eval] using hc.symm

theorem sound1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1599 node1599Labels = Sparse.eval nodeValue1599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1599) = mixedMoment B node1599 node1599Labels := rfl
  simpa [nodeValue1599, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1605 node1605Labels = Sparse.eval nodeValue1605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1605) = mixedMoment B node1605 node1605Labels := rfl
  simpa [nodeValue1605, Sparse.eval] using hc.symm

theorem sound1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1618 node1618Labels = Sparse.eval nodeValue1618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1618) = mixedMoment B node1618 node1618Labels := rfl
  simpa [nodeValue1618, Sparse.eval] using hc.symm

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

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

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

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

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

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

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

theorem sound2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2382 node2382Labels = Sparse.eval nodeValue2382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2382) = mixedMoment B node2382 node2382Labels := rfl
  simpa [nodeValue2382, Sparse.eval] using hc.symm

theorem sound2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2388 node2388Labels = Sparse.eval nodeValue2388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2388) = mixedMoment B node2388 node2388Labels := rfl
  simpa [nodeValue2388, Sparse.eval] using hc.symm

theorem sound2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2400 node2400Labels = Sparse.eval nodeValue2400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2400) = mixedMoment B node2400 node2400Labels := rfl
  simpa [nodeValue2400, Sparse.eval] using hc.symm

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

theorem sound2452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2452 node2452Labels = Sparse.eval nodeValue2452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2452) = mixedMoment B node2452 node2452Labels := rfl
  simpa [nodeValue2452, Sparse.eval] using hc.symm

theorem sound2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2459 node2459Labels = Sparse.eval nodeValue2459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2459) = mixedMoment B node2459 node2459Labels := rfl
  simpa [nodeValue2459, Sparse.eval] using hc.symm

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

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

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound3340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3340 node3340Labels = Sparse.eval nodeValue3340 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3340) = mixedMoment B node3340 node3340Labels := rfl
  simpa [nodeValue3340, Sparse.eval] using hc.symm

theorem sound3344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3344 node3344Labels = Sparse.eval nodeValue3344 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3344) = mixedMoment B node3344 node3344Labels := rfl
  simpa [nodeValue3344, Sparse.eval] using hc.symm

theorem sound3354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3354 node3354Labels = Sparse.eval nodeValue3354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3354) = mixedMoment B node3354 node3354Labels := rfl
  simpa [nodeValue3354, Sparse.eval] using hc.symm

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

theorem sound3429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3429 node3429Labels = Sparse.eval nodeValue3429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3429) = mixedMoment B node3429 node3429Labels := rfl
  simpa [nodeValue3429, Sparse.eval] using hc.symm

theorem sound3433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3433 node3433Labels = Sparse.eval nodeValue3433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3433) = mixedMoment B node3433 node3433Labels := rfl
  simpa [nodeValue3433, Sparse.eval] using hc.symm

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

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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

theorem sound4398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4398 node4398Labels = Sparse.eval nodeValue4398 (mixedVector B) := by
  have h := singleton4398 B _hB
  rw [sound979 B _hB _hF, sound1599 B _hB _hF] at h
  norm_num [nodeValue4398, nodeValue979, nodeValue1599, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4404 node4404Labels = Sparse.eval nodeValue4404 (mixedVector B) := by
  have h := singleton4404 B _hB
  rw [sound985 B _hB _hF, sound1618 B _hB _hF] at h
  norm_num [nodeValue4404, nodeValue985, nodeValue1618, Sparse.eval] at h ⊢
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

theorem sound4419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4419 node4419Labels = Sparse.eval nodeValue4419 (mixedVector B) := by
  have h := singleton4419 B _hB
  rw [sound1000 B _hB _hF, sound1605 B _hB _hF] at h
  norm_num [nodeValue4419, nodeValue1000, nodeValue1605, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4457 node4457Labels = Sparse.eval nodeValue4457 (mixedVector B) := by
  have h := singleton4457 B _hB
  rw [sound1040 B _hB _hF, sound1707 B _hB _hF] at h
  norm_num [nodeValue4457, nodeValue1040, nodeValue1707, Sparse.eval] at h ⊢
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

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4832 node4832Labels = Sparse.eval nodeValue4832 (mixedVector B) := by
  have h := singleton4832 B _hB
  rw [sound2052 B _hB _hF, sound2193 B _hB _hF] at h
  norm_num [nodeValue4832, nodeValue2052, nodeValue2193, Sparse.eval] at h ⊢
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

theorem sound5003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5003 node5003Labels = Sparse.eval nodeValue5003 (mixedVector B) := by
  have h := singleton5003 B _hB
  rw [sound2388 B _hB _hF, sound3354 B _hB _hF] at h
  norm_num [nodeValue5003, nodeValue2388, nodeValue3354, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5015 node5015Labels = Sparse.eval nodeValue5015 (mixedVector B) := by
  have h := singleton5015 B _hB
  rw [sound2400 B _hB _hF, sound3344 B _hB _hF] at h
  norm_num [nodeValue5015, nodeValue2400, nodeValue3344, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5050 node5050Labels = Sparse.eval nodeValue5050 (mixedVector B) := by
  have h := singleton5050 B _hB
  rw [sound2452 B _hB _hF, sound3433 B _hB _hF] at h
  norm_num [nodeValue5050, nodeValue2452, nodeValue3433, Sparse.eval] at h ⊢
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

theorem sound5056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5056 node5056Labels = Sparse.eval nodeValue5056 (mixedVector B) := by
  have h := singleton5056 B _hB
  rw [sound2459 B _hB _hF, sound3429 B _hB _hF] at h
  norm_num [nodeValue5056, nodeValue2459, nodeValue3429, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5072 node5072Labels = Sparse.eval nodeValue5072 (mixedVector B) := by
  have h := singleton5072 B _hB
  rw [sound2479 B _hB _hF, sound3459 B _hB _hF] at h
  norm_num [nodeValue5072, nodeValue2479, nodeValue3459, Sparse.eval] at h ⊢
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

theorem sound5248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5248 node5248Labels = Sparse.eval nodeValue5248 (mixedVector B) := by
  have h := singleton5248 B _hB
  rw [sound2705 B _hB _hF, sound3498 B _hB _hF] at h
  norm_num [nodeValue5248, nodeValue2705, nodeValue3498, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
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

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources18
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm603 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA603 + difference 0 1) (sourceB603 + difference 1 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA603 + difference 0 1) (sourceB603 + difference 1 0) sourceC603) = raw10085 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10085; decide +kernel
    rw [ha]
    exact (canonical10085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA603 + difference 0 2) (sourceB603 + difference 2 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA603 + difference 0 2) (sourceB603 + difference 2 0) sourceC603) = raw10086 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10086; decide +kernel
    rw [ha]
    exact (canonical10086 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA603 + difference 0 3) (sourceB603 + difference 3 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA603 + difference 0 3) (sourceB603 + difference 3 0) sourceC603) = raw10087 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10087; decide +kernel
    rw [ha]
    exact (canonical10087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA603 + difference 0 4) (sourceB603 + difference 4 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA603 + difference 0 4) (sourceB603 + difference 4 0) sourceC603) = raw10088 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10088; decide +kernel
    rw [ha]
    exact (canonical10088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA603 + difference 0 5) (sourceB603 + difference 5 0) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA603 + difference 0 5) (sourceB603 + difference 5 0) sourceC603) = raw10089 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10089; decide +kernel
    rw [ha]
    exact (canonical10089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA603 + difference 1 0) (sourceB603 + difference 0 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA603 + difference 1 0) (sourceB603 + difference 0 1) sourceC603) = raw10090 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10090; decide +kernel
    rw [ha]
    exact (canonical10090 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA603 + difference 1 2) (sourceB603 + difference 2 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA603 + difference 1 2) (sourceB603 + difference 2 1) sourceC603) = raw10091 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10091; decide +kernel
    rw [ha]
    exact (canonical10091 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA603 + difference 1 3) (sourceB603 + difference 3 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA603 + difference 1 3) (sourceB603 + difference 3 1) sourceC603) = raw10092 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10092; decide +kernel
    rw [ha]
    exact (canonical10092 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA603 + difference 1 4) (sourceB603 + difference 4 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA603 + difference 1 4) (sourceB603 + difference 4 1) sourceC603) = raw10093 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10093; decide +kernel
    rw [ha]
    exact (canonical10093 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA603 + difference 1 5) (sourceB603 + difference 5 1) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA603 + difference 1 5) (sourceB603 + difference 5 1) sourceC603) = raw10094 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10094; decide +kernel
    rw [ha]
    exact (canonical10094 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA603 + difference 2 0) (sourceB603 + difference 0 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA603 + difference 2 0) (sourceB603 + difference 0 2) sourceC603) = raw10095 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10095; decide +kernel
    rw [ha]
    exact (canonical10095 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA603 + difference 2 1) (sourceB603 + difference 1 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA603 + difference 2 1) (sourceB603 + difference 1 2) sourceC603) = raw10096 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10096; decide +kernel
    rw [ha]
    exact (canonical10096 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA603 + difference 2 3) (sourceB603 + difference 3 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA603 + difference 2 3) (sourceB603 + difference 3 2) sourceC603) = raw10097 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10097; decide +kernel
    rw [ha]
    exact (canonical10097 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA603 + difference 2 4) (sourceB603 + difference 4 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA603 + difference 2 4) (sourceB603 + difference 4 2) sourceC603) = raw10098 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10098; decide +kernel
    rw [ha]
    exact (canonical10098 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA603 + difference 2 5) (sourceB603 + difference 5 2) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA603 + difference 2 5) (sourceB603 + difference 5 2) sourceC603) = raw10099 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10099; decide +kernel
    rw [ha]
    exact (canonical10099 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA603 + difference 3 0) (sourceB603 + difference 0 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA603 + difference 3 0) (sourceB603 + difference 0 3) sourceC603) = raw10100 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10100; decide +kernel
    rw [ha]
    exact (canonical10100 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA603 + difference 3 1) (sourceB603 + difference 1 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA603 + difference 3 1) (sourceB603 + difference 1 3) sourceC603) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA603 + difference 3 2) (sourceB603 + difference 2 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA603 + difference 3 2) (sourceB603 + difference 2 3) sourceC603) = raw10102 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10102; decide +kernel
    rw [ha]
    exact (canonical10102 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA603 + difference 3 4) (sourceB603 + difference 4 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA603 + difference 3 4) (sourceB603 + difference 4 3) sourceC603) = raw10103 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10103; decide +kernel
    rw [ha]
    exact (canonical10103 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA603 + difference 3 5) (sourceB603 + difference 5 3) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA603 + difference 3 5) (sourceB603 + difference 5 3) sourceC603) = raw10104 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10104; decide +kernel
    rw [ha]
    exact (canonical10104 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA603 + difference 4 0) (sourceB603 + difference 0 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA603 + difference 4 0) (sourceB603 + difference 0 4) sourceC603) = raw10105 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10105; decide +kernel
    rw [ha]
    exact (canonical10105 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA603 + difference 4 1) (sourceB603 + difference 1 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA603 + difference 4 1) (sourceB603 + difference 1 4) sourceC603) = raw10106 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10106; decide +kernel
    rw [ha]
    exact (canonical10106 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA603 + difference 4 2) (sourceB603 + difference 2 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA603 + difference 4 2) (sourceB603 + difference 2 4) sourceC603) = raw10107 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10107; decide +kernel
    rw [ha]
    exact (canonical10107 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA603 + difference 4 3) (sourceB603 + difference 3 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA603 + difference 4 3) (sourceB603 + difference 3 4) sourceC603) = raw10108 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10108; decide +kernel
    rw [ha]
    exact (canonical10108 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA603 + difference 4 5) (sourceB603 + difference 5 4) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA603 + difference 4 5) (sourceB603 + difference 5 4) sourceC603) = raw10109 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10109; decide +kernel
    rw [ha]
    exact (canonical10109 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA603 + difference 5 0) (sourceB603 + difference 0 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA603 + difference 5 0) (sourceB603 + difference 0 5) sourceC603) = raw10110 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10110; decide +kernel
    rw [ha]
    exact (canonical10110 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA603 + difference 5 1) (sourceB603 + difference 1 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA603 + difference 5 1) (sourceB603 + difference 1 5) sourceC603) = raw10111 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10111; decide +kernel
    rw [ha]
    exact (canonical10111 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA603 + difference 5 2) (sourceB603 + difference 2 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA603 + difference 5 2) (sourceB603 + difference 2 5) sourceC603) = raw10112 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10112; decide +kernel
    rw [ha]
    exact (canonical10112 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA603 + difference 5 3) (sourceB603 + difference 3 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA603 + difference 5 3) (sourceB603 + difference 3 5) sourceC603) = raw10113 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10113; decide +kernel
    rw [ha]
    exact (canonical10113 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA603 + difference 5 4) (sourceB603 + difference 4 5) sourceC603) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA603 + difference 5 4) (sourceB603 + difference 4 5) sourceC603) = raw10114 := by
      apply Matrix.ext; unfold tripleCharges sourceA603 sourceB603 sourceC603 difference raw10114; decide +kernel
    rw [ha]
    exact (canonical10114 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA603 sourceB603 sourceC603
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm603, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck512 : Integer.Sparse.reindex keyMap MixedData.row512 = numericRow512 := by decide +kernel

theorem numericCheck512 (x : Master → ℝ) : Integer.Sparse.eval numericRow512 x =
    (17280 : ℝ) * reducedSource512 x := by
  norm_num [numericRow512, reducedSource512, Integer.Sparse.eval, Sparse.eval, nodeValue4396, nodeValue4398, nodeValue4404, nodeValue4419, nodeValue4457, nodeValue4779, nodeValue4788, nodeValue4804, nodeValue4832, nodeValue4996, nodeValue5003, nodeValue5015, nodeValue5050, nodeValue5056, nodeValue5072, nodeValue5134, nodeValue5141, nodeValue5168, nodeValue5241, nodeValue5248, nodeValue5257, nodeValue5258, nodeValue5259, nodeValue5271, nodeValue5292, nodeValue5424, nodeValue5428, nodeValue5434, nodeValue5439, nodeValue5490]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero512 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource512 (mixedVector B) = 0 := by
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4996 : mixedVector B (Sum.inr 4996) = Sparse.eval nodeValue4996 (mixedVector B) := by
    change mixedMoment B node4996 node4996Labels = _
    exact sound4996 B hB hF
  have h5003 : mixedVector B (Sum.inr 5003) = Sparse.eval nodeValue5003 (mixedVector B) := by
    change mixedMoment B node5003 node5003Labels = _
    exact sound5003 B hB hF
  have h5015 : mixedVector B (Sum.inr 5015) = Sparse.eval nodeValue5015 (mixedVector B) := by
    change mixedMoment B node5015 node5015Labels = _
    exact sound5015 B hB hF
  have h5050 : mixedVector B (Sum.inr 5050) = Sparse.eval nodeValue5050 (mixedVector B) := by
    change mixedMoment B node5050 node5050Labels = _
    exact sound5050 B hB hF
  have h5056 : mixedVector B (Sum.inr 5056) = Sparse.eval nodeValue5056 (mixedVector B) := by
    change mixedMoment B node5056 node5056Labels = _
    exact sound5056 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  simpa only [sourceForm603, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4396, h4398, h4404, h4419, h4457, h4779, h4788, h4804, h4832, h4996, h5003, h5015, h5050, h5056, h5072, h5134, h5141, h5168, h5241, h5248, h5257, h5258, h5259, h5271, h5292, h5424, h5428, h5434, h5439, h5490, reducedSource512] using sourceEq603 B hB

theorem rowSound512_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row512 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck512, numericCheck512, reducedZero512 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound512_e_oai
