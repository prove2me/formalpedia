-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:10:12.134515+00:00
-- url     : https://prove2.me/submissions/cf0164bd-0566-4394-8deb-231ac3d33775

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18863 raw18863Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18863 raw18863Labels = mixedMoment B raw18863step0 raw18863step0Labels := by
      have ha : raw18863step0 = (fun i j => raw18863 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18863step0 raw18863; decide +kernel
      have hl : raw18863step0Labels = raw18863Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18863 raw18863Labels permutation184 permutation2
    mixedMoment B raw18863step0 raw18863step0Labels = mixedMoment B raw18863step1 raw18863step1Labels := by
      have ha : raw18863step1 = -raw18863step0 := by apply Matrix.ext; change ∀ i j, raw18863step1 i j = -(raw18863step0 i j); unfold raw18863step1 raw18863step0; decide +kernel
      have hl : raw18863step1Labels = raw18863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical18864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18864 raw18864Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18864 raw18864Labels = mixedMoment B raw18864step0 raw18864step0Labels := by
      have hz : ∀ j, raw18864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18864step0 = (fun i j => raw18864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18864step0 raw18864; decide +kernel
      have hl : raw18864step0Labels = raw18864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18864 raw18864Labels permutation346 hz
    mixedMoment B raw18864step0 raw18864step0Labels = mixedMoment B raw18864step1 raw18864step1Labels := by
      have ha : raw18864step1 = (fun i j => raw18864step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18864step1 raw18864step0; decide +kernel
      have hl : raw18864step1Labels = raw18864step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18864step0 raw18864step0Labels permutation32 permutation7
    mixedMoment B raw18864step1 raw18864step1Labels = mixedMoment B raw18864step2 raw18864step2Labels := by
      have ha : raw18864step2 = raw18864step1 := by apply Matrix.ext; unfold raw18864step2 raw18864step1; decide +kernel
      have hl : raw18864step1Labels = labelEmbedding10 ∘ raw18864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18864step1 raw18864step1Labels raw18864step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical18865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18865 raw18865Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18865 raw18865Labels = mixedMoment B raw18865step0 raw18865step0Labels := by
      have ha : raw18865step0 = (fun i j => raw18865 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18865step0 raw18865; decide +kernel
      have hl : raw18865step0Labels = raw18865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18865 raw18865Labels permutation178 permutation2
    mixedMoment B raw18865step0 raw18865step0Labels = mixedMoment B raw18865step1 raw18865step1Labels := by
      have ha : raw18865step1 = -raw18865step0 := by apply Matrix.ext; change ∀ i j, raw18865step1 i j = -(raw18865step0 i j); unfold raw18865step1 raw18865step0; decide +kernel
      have hl : raw18865step1Labels = raw18865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical18866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18866 raw18866Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18866 raw18866Labels = mixedMoment B raw18866step0 raw18866step0Labels := by
      have ha : raw18866step0 = (fun i j => raw18866 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18866step0 raw18866; decide +kernel
      have hl : raw18866step0Labels = raw18866Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18866 raw18866Labels permutation176 permutation2
    mixedMoment B raw18866step0 raw18866step0Labels = mixedMoment B raw18866step1 raw18866step1Labels := by
      have ha : raw18866step1 = -raw18866step0 := by apply Matrix.ext; change ∀ i j, raw18866step1 i j = -(raw18866step0 i j); unfold raw18866step1 raw18866step0; decide +kernel
      have hl : raw18866step1Labels = raw18866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical18867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18867 raw18867Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18867 raw18867Labels = mixedMoment B raw18867step0 raw18867step0Labels := by
      have ha : raw18867step0 = (fun i j => raw18867 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18867step0 raw18867; decide +kernel
      have hl : raw18867step0Labels = raw18867Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18867 raw18867Labels permutation616 permutation3
    mixedMoment B raw18867step0 raw18867step0Labels = mixedMoment B raw18867step1 raw18867step1Labels := by
      have ha : raw18867step1 = raw18867step0 := by apply Matrix.ext; unfold raw18867step1 raw18867step0; decide +kernel
      have hl : raw18867step0Labels = labelEmbedding6 ∘ raw18867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18867step0 raw18867step0Labels raw18867step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical18868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18868 raw18868Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18868 raw18868Labels = mixedMoment B raw18868step0 raw18868step0Labels := by
      have ha : raw18868step0 = (fun i j => raw18868 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18868step0 raw18868; decide +kernel
      have hl : raw18868step0Labels = raw18868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18868 raw18868Labels permutation156 permutation6
    mixedMoment B raw18868step0 raw18868step0Labels = mixedMoment B raw18868step1 raw18868step1Labels := by
      have ha : raw18868step1 = raw18868step0 := by apply Matrix.ext; unfold raw18868step1 raw18868step0; decide +kernel
      have hl : raw18868step0Labels = labelEmbedding9 ∘ raw18868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18868step0 raw18868step0Labels raw18868step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18869 raw18869Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18869 raw18869Labels = mixedMoment B raw18869step0 raw18869step0Labels := by
      have hz : ∀ j, raw18869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18869step0 = (fun i j => raw18869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18869step0 raw18869; decide +kernel
      have hl : raw18869step0Labels = raw18869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18869 raw18869Labels permutation346 hz
    mixedMoment B raw18869step0 raw18869step0Labels = mixedMoment B raw18869step1 raw18869step1Labels := by
      have ha : raw18869step1 = (fun i j => raw18869step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18869step1 raw18869step0; decide +kernel
      have hl : raw18869step1Labels = raw18869step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18869step0 raw18869step0Labels permutation32 permutation7
    mixedMoment B raw18869step1 raw18869step1Labels = mixedMoment B raw18869step2 raw18869step2Labels := by
      have ha : raw18869step2 = raw18869step1 := by apply Matrix.ext; unfold raw18869step2 raw18869step1; decide +kernel
      have hl : raw18869step1Labels = labelEmbedding10 ∘ raw18869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18869step1 raw18869step1Labels raw18869step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical18870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18870 raw18870Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18870 raw18870Labels = mixedMoment B raw18870step0 raw18870step0Labels := by
      have ha : raw18870step0 = (fun i j => raw18870 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18870step0 raw18870; decide +kernel
      have hl : raw18870step0Labels = raw18870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18870 raw18870Labels permutation664 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical18871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18871 raw18871Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18871 raw18871Labels = mixedMoment B raw18871step0 raw18871step0Labels := by
      have ha : raw18871step0 = (fun i j => raw18871 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18871step0 raw18871; decide +kernel
      have hl : raw18871step0Labels = raw18871Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18871 raw18871Labels permutation688 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical18872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18872 raw18872Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18872 raw18872Labels = mixedMoment B raw18872step0 raw18872step0Labels := by
      have ha : raw18872step0 = (fun i j => raw18872 (permutation659 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18872step0 raw18872; decide +kernel
      have hl : raw18872step0Labels = raw18872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18872 raw18872Labels permutation659 permutation3
    mixedMoment B raw18872step0 raw18872step0Labels = mixedMoment B raw18872step1 raw18872step1Labels := by
      have ha : raw18872step1 = raw18872step0 := by apply Matrix.ext; unfold raw18872step1 raw18872step0; decide +kernel
      have hl : raw18872step0Labels = labelEmbedding6 ∘ raw18872step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18872step0 raw18872step0Labels raw18872step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical18873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18873 raw18873Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw18873 raw18873Labels = mixedMoment B raw18873step0 raw18873step0Labels := by
      have ha : raw18873step0 = (fun i j => raw18873 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18873step0 raw18873; decide +kernel
      have hl : raw18873step0Labels = raw18873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18873 raw18873Labels permutation173 permutation4
    mixedMoment B raw18873step0 raw18873step0Labels = mixedMoment B raw18873step1 raw18873step1Labels := by
      have ha : raw18873step1 = -raw18873step0 := by apply Matrix.ext; change ∀ i j, raw18873step1 i j = -(raw18873step0 i j); unfold raw18873step1 raw18873step0; decide +kernel
      have hl : raw18873step1Labels = raw18873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18873step1 raw18873step1Labels = mixedMoment B raw18873step2 raw18873step2Labels := by
      have ha : raw18873step2 = raw18873step1 := by apply Matrix.ext; unfold raw18873step2 raw18873step1; decide +kernel
      have hl : raw18873step1Labels = labelEmbedding7 ∘ raw18873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18873step1 raw18873step1Labels raw18873step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

theorem canonical18874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18874 raw18874Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw18874 raw18874Labels = mixedMoment B raw18874step0 raw18874step0Labels := by
      have ha : raw18874step0 = (fun i j => raw18874 (permutation390 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18874step0 raw18874; decide +kernel
      have hl : raw18874step0Labels = raw18874Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18874 raw18874Labels permutation390 permutation5
    mixedMoment B raw18874step0 raw18874step0Labels = mixedMoment B raw18874step1 raw18874step1Labels := by
      have ha : raw18874step1 = raw18874step0 := by apply Matrix.ext; unfold raw18874step1 raw18874step0; decide +kernel
      have hl : raw18874step0Labels = labelEmbedding8 ∘ raw18874step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18874step0 raw18874step0Labels raw18874step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

theorem canonical18875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18875 raw18875Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18875 raw18875Labels = mixedMoment B raw18875step0 raw18875step0Labels := by
      have ha : raw18875step0 = (fun i j => raw18875 (permutation407 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18875step0 raw18875; decide +kernel
      have hl : raw18875step0Labels = raw18875Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18875 raw18875Labels permutation407 permutation5
    mixedMoment B raw18875step0 raw18875step0Labels = mixedMoment B raw18875step1 raw18875step1Labels := by
      have ha : raw18875step1 = raw18875step0 := by apply Matrix.ext; unfold raw18875step1 raw18875step0; decide +kernel
      have hl : raw18875step0Labels = labelEmbedding8 ∘ raw18875step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18875step0 raw18875step0Labels raw18875step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18876 raw18876Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18876 raw18876Labels = mixedMoment B raw18876step0 raw18876step0Labels := by
      have ha : raw18876step0 = (fun i j => raw18876 (permutation389 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18876step0 raw18876; decide +kernel
      have hl : raw18876step0Labels = raw18876Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18876 raw18876Labels permutation389 permutation5
    mixedMoment B raw18876step0 raw18876step0Labels = mixedMoment B raw18876step1 raw18876step1Labels := by
      have ha : raw18876step1 = raw18876step0 := by apply Matrix.ext; unfold raw18876step1 raw18876step0; decide +kernel
      have hl : raw18876step0Labels = labelEmbedding8 ∘ raw18876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18876step0 raw18876step0Labels raw18876step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical18877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18877 raw18877Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw18877 raw18877Labels = mixedMoment B raw18877step0 raw18877step0Labels := by
      have ha : raw18877step0 = (fun i j => raw18877 (permutation615 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18877step0 raw18877; decide +kernel
      have hl : raw18877step0Labels = raw18877Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18877 raw18877Labels permutation615 permutation3
    mixedMoment B raw18877step0 raw18877step0Labels = mixedMoment B raw18877step1 raw18877step1Labels := by
      have ha : raw18877step1 = raw18877step0 := by apply Matrix.ext; unfold raw18877step1 raw18877step0; decide +kernel
      have hl : raw18877step0Labels = labelEmbedding6 ∘ raw18877step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18877step0 raw18877step0Labels raw18877step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

theorem canonical18878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18878 raw18878Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18878 raw18878Labels = mixedMoment B raw18878step0 raw18878step0Labels := by
      have ha : raw18878step0 = (fun i j => raw18878 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18878step0 raw18878; decide +kernel
      have hl : raw18878step0Labels = raw18878Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18878 raw18878Labels permutation171 permutation4
    mixedMoment B raw18878step0 raw18878step0Labels = mixedMoment B raw18878step1 raw18878step1Labels := by
      have ha : raw18878step1 = -raw18878step0 := by apply Matrix.ext; change ∀ i j, raw18878step1 i j = -(raw18878step0 i j); unfold raw18878step1 raw18878step0; decide +kernel
      have hl : raw18878step1Labels = raw18878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18878step1 raw18878step1Labels = mixedMoment B raw18878step2 raw18878step2Labels := by
      have ha : raw18878step2 = raw18878step1 := by apply Matrix.ext; unfold raw18878step2 raw18878step1; decide +kernel
      have hl : raw18878step1Labels = labelEmbedding7 ∘ raw18878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18878step1 raw18878step1Labels raw18878step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical18879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18879 raw18879Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw18879 raw18879Labels = mixedMoment B raw18879step0 raw18879step0Labels := by
      have ha : raw18879step0 = (fun i j => raw18879 (permutation284 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18879step0 raw18879; decide +kernel
      have hl : raw18879step0Labels = raw18879Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18879 raw18879Labels permutation284 permutation4
    mixedMoment B raw18879step0 raw18879step0Labels = mixedMoment B raw18879step1 raw18879step1Labels := by
      have ha : raw18879step1 = -raw18879step0 := by apply Matrix.ext; change ∀ i j, raw18879step1 i j = -(raw18879step0 i j); unfold raw18879step1 raw18879step0; decide +kernel
      have hl : raw18879step1Labels = raw18879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18879step1 raw18879step1Labels = mixedMoment B raw18879step2 raw18879step2Labels := by
      have ha : raw18879step2 = raw18879step1 := by apply Matrix.ext; unfold raw18879step2 raw18879step1; decide +kernel
      have hl : raw18879step1Labels = labelEmbedding7 ∘ raw18879step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18879step1 raw18879step1Labels raw18879step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

theorem canonical18880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18880 raw18880Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18880 raw18880Labels = mixedMoment B raw18880step0 raw18880step0Labels := by
      have hz : ∀ j, raw18880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18880step0 = (fun i j => raw18880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18880step0 raw18880; decide +kernel
      have hl : raw18880step0Labels = raw18880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18880 raw18880Labels permutation346 hz
    mixedMoment B raw18880step0 raw18880step0Labels = mixedMoment B raw18880step1 raw18880step1Labels := by
      have ha : raw18880step1 = (fun i j => raw18880step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18880step1 raw18880step0; decide +kernel
      have hl : raw18880step1Labels = raw18880step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18880step0 raw18880step0Labels permutation97 permutation4
    mixedMoment B raw18880step1 raw18880step1Labels = mixedMoment B raw18880step2 raw18880step2Labels := by
      have ha : raw18880step2 = raw18880step1 := by apply Matrix.ext; unfold raw18880step2 raw18880step1; decide +kernel
      have hl : raw18880step1Labels = labelEmbedding7 ∘ raw18880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18880step1 raw18880step1Labels raw18880step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical18881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18881 raw18881Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw18881 raw18881Labels = mixedMoment B raw18881step0 raw18881step0Labels := by
      have ha : raw18881step0 = (fun i j => raw18881 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18881step0 raw18881; decide +kernel
      have hl : raw18881step0Labels = raw18881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18881 raw18881Labels permutation676 permutation2
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical18882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18882 raw18882Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw18882 raw18882Labels = mixedMoment B raw18882step0 raw18882step0Labels := by
      have ha : raw18882step0 = (fun i j => raw18882 (permutation617 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18882step0 raw18882; decide +kernel
      have hl : raw18882step0Labels = raw18882Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18882 raw18882Labels permutation617 permutation3
    mixedMoment B raw18882step0 raw18882step0Labels = mixedMoment B raw18882step1 raw18882step1Labels := by
      have ha : raw18882step1 = raw18882step0 := by apply Matrix.ext; unfold raw18882step1 raw18882step0; decide +kernel
      have hl : raw18882step0Labels = labelEmbedding6 ∘ raw18882step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18882step0 raw18882step0Labels raw18882step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical18883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18883 raw18883Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18883 raw18883Labels = mixedMoment B raw18883step0 raw18883step0Labels := by
      have ha : raw18883step0 = (fun i j => raw18883 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18883step0 raw18883; decide +kernel
      have hl : raw18883step0Labels = raw18883Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18883 raw18883Labels permutation170 permutation4
    mixedMoment B raw18883step0 raw18883step0Labels = mixedMoment B raw18883step1 raw18883step1Labels := by
      have ha : raw18883step1 = -raw18883step0 := by apply Matrix.ext; change ∀ i j, raw18883step1 i j = -(raw18883step0 i j); unfold raw18883step1 raw18883step0; decide +kernel
      have hl : raw18883step1Labels = raw18883step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18883step1 raw18883step1Labels = mixedMoment B raw18883step2 raw18883step2Labels := by
      have ha : raw18883step2 = raw18883step1 := by apply Matrix.ext; unfold raw18883step2 raw18883step1; decide +kernel
      have hl : raw18883step1Labels = labelEmbedding7 ∘ raw18883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18883step1 raw18883step1Labels raw18883step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical18884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18884 raw18884Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw18884 raw18884Labels = mixedMoment B raw18884step0 raw18884step0Labels := by
      have ha : raw18884step0 = (fun i j => raw18884 (permutation283 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18884step0 raw18884; decide +kernel
      have hl : raw18884step0Labels = raw18884Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18884 raw18884Labels permutation283 permutation4
    mixedMoment B raw18884step0 raw18884step0Labels = mixedMoment B raw18884step1 raw18884step1Labels := by
      have ha : raw18884step1 = -raw18884step0 := by apply Matrix.ext; change ∀ i j, raw18884step1 i j = -(raw18884step0 i j); unfold raw18884step1 raw18884step0; decide +kernel
      have hl : raw18884step1Labels = raw18884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18884step1 raw18884step1Labels = mixedMoment B raw18884step2 raw18884step2Labels := by
      have ha : raw18884step2 = raw18884step1 := by apply Matrix.ext; unfold raw18884step2 raw18884step1; decide +kernel
      have hl : raw18884step1Labels = labelEmbedding7 ∘ raw18884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18884step1 raw18884step1Labels raw18884step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

theorem canonical18885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18885 raw18885Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18885 raw18885Labels = mixedMoment B raw18885step0 raw18885step0Labels := by
      have hz : ∀ j, raw18885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18885step0 = (fun i j => raw18885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18885step0 raw18885; decide +kernel
      have hl : raw18885step0Labels = raw18885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18885 raw18885Labels permutation346 hz
    mixedMoment B raw18885step0 raw18885step0Labels = mixedMoment B raw18885step1 raw18885step1Labels := by
      have ha : raw18885step1 = (fun i j => raw18885step0 (permutation121 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18885step1 raw18885step0; decide +kernel
      have hl : raw18885step1Labels = raw18885step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18885step0 raw18885step0Labels permutation121 permutation4
    mixedMoment B raw18885step1 raw18885step1Labels = mixedMoment B raw18885step2 raw18885step2Labels := by
      have ha : raw18885step2 = raw18885step1 := by apply Matrix.ext; unfold raw18885step2 raw18885step1; decide +kernel
      have hl : raw18885step1Labels = labelEmbedding7 ∘ raw18885step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18885step1 raw18885step1Labels raw18885step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical18886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18886 raw18886Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw18886 raw18886Labels = mixedMoment B raw18886step0 raw18886step0Labels := by
      have ha : raw18886step0 = (fun i j => raw18886 (permutation654 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18886step0 raw18886; decide +kernel
      have hl : raw18886step0Labels = raw18886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18886 raw18886Labels permutation654 permutation2
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical18887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18887 raw18887Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw18887 raw18887Labels = mixedMoment B raw18887step0 raw18887step0Labels := by
      have ha : raw18887step0 = (fun i j => raw18887 (permutation612 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18887step0 raw18887; decide +kernel
      have hl : raw18887step0Labels = raw18887Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18887 raw18887Labels permutation612 permutation3
    mixedMoment B raw18887step0 raw18887step0Labels = mixedMoment B raw18887step1 raw18887step1Labels := by
      have ha : raw18887step1 = raw18887step0 := by apply Matrix.ext; unfold raw18887step1 raw18887step0; decide +kernel
      have hl : raw18887step0Labels = labelEmbedding6 ∘ raw18887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18887step0 raw18887step0Labels raw18887step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical18888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18888 raw18888Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw18888 raw18888Labels = mixedMoment B raw18888step0 raw18888step0Labels := by
      have ha : raw18888step0 = (fun i j => raw18888 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18888step0 raw18888; decide +kernel
      have hl : raw18888step0Labels = raw18888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18888 raw18888Labels permutation170 permutation4
    mixedMoment B raw18888step0 raw18888step0Labels = mixedMoment B raw18888step1 raw18888step1Labels := by
      have ha : raw18888step1 = -raw18888step0 := by apply Matrix.ext; change ∀ i j, raw18888step1 i j = -(raw18888step0 i j); unfold raw18888step1 raw18888step0; decide +kernel
      have hl : raw18888step1Labels = raw18888step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18888step1 raw18888step1Labels = mixedMoment B raw18888step2 raw18888step2Labels := by
      have ha : raw18888step2 = raw18888step1 := by apply Matrix.ext; unfold raw18888step2 raw18888step1; decide +kernel
      have hl : raw18888step1Labels = labelEmbedding7 ∘ raw18888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18888step1 raw18888step1Labels raw18888step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5408 node5408Labels := by rfl

theorem canonical18889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18889 raw18889Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw18889 raw18889Labels = mixedMoment B raw18889step0 raw18889step0Labels := by
      have ha : raw18889step0 = (fun i j => raw18889 (permutation283 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18889step0 raw18889; decide +kernel
      have hl : raw18889step0Labels = raw18889Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18889 raw18889Labels permutation283 permutation4
    mixedMoment B raw18889step0 raw18889step0Labels = mixedMoment B raw18889step1 raw18889step1Labels := by
      have ha : raw18889step1 = -raw18889step0 := by apply Matrix.ext; change ∀ i j, raw18889step1 i j = -(raw18889step0 i j); unfold raw18889step1 raw18889step0; decide +kernel
      have hl : raw18889step1Labels = raw18889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18889step1 raw18889step1Labels = mixedMoment B raw18889step2 raw18889step2Labels := by
      have ha : raw18889step2 = raw18889step1 := by apply Matrix.ext; unfold raw18889step2 raw18889step1; decide +kernel
      have hl : raw18889step1Labels = labelEmbedding7 ∘ raw18889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18889step1 raw18889step1Labels raw18889step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical18890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18890 raw18890Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw18890 raw18890Labels = mixedMoment B raw18890step0 raw18890step0Labels := by
      have hz : ∀ j, raw18890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18890step0 = (fun i j => raw18890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18890step0 raw18890; decide +kernel
      have hl : raw18890step0Labels = raw18890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18890 raw18890Labels permutation346 hz
    mixedMoment B raw18890step0 raw18890step0Labels = mixedMoment B raw18890step1 raw18890step1Labels := by
      have ha : raw18890step1 = (fun i j => raw18890step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18890step1 raw18890step0; decide +kernel
      have hl : raw18890step1Labels = raw18890step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18890step0 raw18890step0Labels permutation36 permutation6
    mixedMoment B raw18890step1 raw18890step1Labels = mixedMoment B raw18890step2 raw18890step2Labels := by
      have ha : raw18890step2 = raw18890step1 := by apply Matrix.ext; unfold raw18890step2 raw18890step1; decide +kernel
      have hl : raw18890step1Labels = labelEmbedding9 ∘ raw18890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18890step1 raw18890step1Labels raw18890step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical18891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18891 raw18891Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18891 raw18891Labels = mixedMoment B raw18891step0 raw18891step0Labels := by
      have ha : raw18891step0 = (fun i j => raw18891 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18891step0 raw18891; decide +kernel
      have hl : raw18891step0Labels = raw18891Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18891 raw18891Labels permutation153 permutation6
    mixedMoment B raw18891step0 raw18891step0Labels = mixedMoment B raw18891step1 raw18891step1Labels := by
      have ha : raw18891step1 = raw18891step0 := by apply Matrix.ext; unfold raw18891step1 raw18891step0; decide +kernel
      have hl : raw18891step0Labels = labelEmbedding9 ∘ raw18891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18891step0 raw18891step0Labels raw18891step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical18892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18892 raw18892Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18892 raw18892Labels = mixedMoment B raw18892step0 raw18892step0Labels := by
      have ha : raw18892step0 = (fun i j => raw18892 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18892step0 raw18892; decide +kernel
      have hl : raw18892step0Labels = raw18892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18892 raw18892Labels permutation155 permutation6
    mixedMoment B raw18892step0 raw18892step0Labels = mixedMoment B raw18892step1 raw18892step1Labels := by
      have ha : raw18892step1 = raw18892step0 := by apply Matrix.ext; unfold raw18892step1 raw18892step0; decide +kernel
      have hl : raw18892step0Labels = labelEmbedding9 ∘ raw18892step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18892step0 raw18892step0Labels raw18892step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

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

theorem canonical2475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2475 raw2475Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw2475 raw2475Labels = mixedMoment B raw2475step0 raw2475step0Labels := by
      have ha : raw2475step0 = (fun i j => raw2475 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2475step0 raw2475; decide +kernel
      have hl : raw2475step0Labels = raw2475Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2475 raw2475Labels permutation152 permutation4
    mixedMoment B raw2475step0 raw2475step0Labels = mixedMoment B raw2475step1 raw2475step1Labels := by
      have ha : raw2475step1 = raw2475step0 := by apply Matrix.ext; unfold raw2475step1 raw2475step0; decide +kernel
      have hl : raw2475step0Labels = labelEmbedding7 ∘ raw2475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2475step0 raw2475step0Labels raw2475step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical2476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2476 raw2476Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw2476 raw2476Labels = mixedMoment B raw2476step0 raw2476step0Labels := by
      have ha : raw2476step0 = (fun i j => raw2476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2476step0 raw2476; decide +kernel
      have hl : raw2476step0Labels = raw2476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2476 raw2476Labels permutation152 permutation4
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2477 raw2477Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw2477 raw2477Labels = mixedMoment B raw2477step0 raw2477step0Labels := by
      have ha : raw2477step0 = (fun i j => raw2477 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2477step0 raw2477; decide +kernel
      have hl : raw2477step0Labels = raw2477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2477 raw2477Labels permutation158 permutation6
    mixedMoment B raw2477step0 raw2477step0Labels = mixedMoment B raw2477step1 raw2477step1Labels := by
      have ha : raw2477step1 = -raw2477step0 := by apply Matrix.ext; change ∀ i j, raw2477step1 i j = -(raw2477step0 i j); unfold raw2477step1 raw2477step0; decide +kernel
      have hl : raw2477step1Labels = raw2477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2477step1 raw2477step1Labels = mixedMoment B raw2477step2 raw2477step2Labels := by
      have ha : raw2477step2 = raw2477step1 := by apply Matrix.ext; unfold raw2477step2 raw2477step1; decide +kernel
      have hl : raw2477step1Labels = labelEmbedding1 ∘ raw2477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2477step1 raw2477step1Labels raw2477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical2478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2478 raw2478Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw2478 raw2478Labels = mixedMoment B raw2478step0 raw2478step0Labels := by
      have ha : raw2478step0 = (fun i j => raw2478 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2478step0 raw2478; decide +kernel
      have hl : raw2478step0Labels = raw2478Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2478 raw2478Labels permutation152 permutation4
    mixedMoment B raw2478step0 raw2478step0Labels = mixedMoment B raw2478step1 raw2478step1Labels := by
      have ha : raw2478step1 = raw2478step0 := by apply Matrix.ext; unfold raw2478step1 raw2478step0; decide +kernel
      have hl : raw2478step0Labels = labelEmbedding7 ∘ raw2478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2478step0 raw2478step0Labels raw2478step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

theorem canonical2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2479 raw2479Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw2479 raw2479Labels = mixedMoment B raw2479step0 raw2479step0Labels := by
      have ha : raw2479step0 = (fun i j => raw2479 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2479step0 raw2479; decide +kernel
      have hl : raw2479step0Labels = raw2479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2479 raw2479Labels permutation152 permutation4
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2480 raw2480Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw2480 raw2480Labels = mixedMoment B raw2480step0 raw2480step0Labels := by
      have ha : raw2480step0 = (fun i j => raw2480 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2480step0 raw2480; decide +kernel
      have hl : raw2480step0Labels = raw2480Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2480 raw2480Labels permutation170 permutation6
    mixedMoment B raw2480step0 raw2480step0Labels = mixedMoment B raw2480step1 raw2480step1Labels := by
      have ha : raw2480step1 = -raw2480step0 := by apply Matrix.ext; change ∀ i j, raw2480step1 i j = -(raw2480step0 i j); unfold raw2480step1 raw2480step0; decide +kernel
      have hl : raw2480step1Labels = raw2480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2480step1 raw2480step1Labels = mixedMoment B raw2480step2 raw2480step2Labels := by
      have ha : raw2480step2 = raw2480step1 := by apply Matrix.ext; unfold raw2480step2 raw2480step1; decide +kernel
      have hl : raw2480step1Labels = labelEmbedding1 ∘ raw2480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2480step1 raw2480step1Labels raw2480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

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

theorem canonical2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2520 raw2520Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw2520 raw2520Labels = mixedMoment B raw2520step0 raw2520step0Labels := by
      have ha : raw2520step0 = (fun i j => raw2520 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2520step0 raw2520; decide +kernel
      have hl : raw2520step0Labels = raw2520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2520 raw2520Labels permutation152 permutation4
    mixedMoment B raw2520step0 raw2520step0Labels = mixedMoment B raw2520step1 raw2520step1Labels := by
      have ha : raw2520step1 = raw2520step0 := by apply Matrix.ext; unfold raw2520step1 raw2520step0; decide +kernel
      have hl : raw2520step0Labels = labelEmbedding7 ∘ raw2520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2520step0 raw2520step0Labels raw2520step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2521 raw2521Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw2521 raw2521Labels = mixedMoment B raw2521step0 raw2521step0Labels := by
      have ha : raw2521step0 = (fun i j => raw2521 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2521step0 raw2521; decide +kernel
      have hl : raw2521step0Labels = raw2521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2521 raw2521Labels permutation152 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2522 raw2522Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw2522 raw2522Labels = mixedMoment B raw2522step0 raw2522step0Labels := by
      have ha : raw2522step0 = (fun i j => raw2522 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2522step0 raw2522; decide +kernel
      have hl : raw2522step0Labels = raw2522Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2522 raw2522Labels permutation200 permutation6
    mixedMoment B raw2522step0 raw2522step0Labels = mixedMoment B raw2522step1 raw2522step1Labels := by
      have ha : raw2522step1 = -raw2522step0 := by apply Matrix.ext; change ∀ i j, raw2522step1 i j = -(raw2522step0 i j); unfold raw2522step1 raw2522step0; decide +kernel
      have hl : raw2522step1Labels = raw2522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2522step1 raw2522step1Labels = mixedMoment B raw2522step2 raw2522step2Labels := by
      have ha : raw2522step2 = raw2522step1 := by apply Matrix.ext; unfold raw2522step2 raw2522step1; decide +kernel
      have hl : raw2522step1Labels = labelEmbedding1 ∘ raw2522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2522step1 raw2522step1Labels raw2522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

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

theorem canonical2586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2586 raw2586Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw2586 raw2586Labels = mixedMoment B raw2586step0 raw2586step0Labels := by
      have ha : raw2586step0 = (fun i j => raw2586 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2586step0 raw2586; decide +kernel
      have hl : raw2586step0Labels = raw2586Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2586 raw2586Labels permutation152 permutation4
    mixedMoment B raw2586step0 raw2586step0Labels = mixedMoment B raw2586step1 raw2586step1Labels := by
      have ha : raw2586step1 = raw2586step0 := by apply Matrix.ext; unfold raw2586step1 raw2586step0; decide +kernel
      have hl : raw2586step0Labels = labelEmbedding7 ∘ raw2586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2586step0 raw2586step0Labels raw2586step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2587 raw2587Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw2587 raw2587Labels = mixedMoment B raw2587step0 raw2587step0Labels := by
      have ha : raw2587step0 = (fun i j => raw2587 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2587step0 raw2587; decide +kernel
      have hl : raw2587step0Labels = raw2587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2587 raw2587Labels permutation152 permutation4
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical2588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2588 raw2588Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw2588 raw2588Labels = mixedMoment B raw2588step0 raw2588step0Labels := by
      have ha : raw2588step0 = (fun i j => raw2588 (permutation271 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2588step0 raw2588; decide +kernel
      have hl : raw2588step0Labels = raw2588Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2588 raw2588Labels permutation271 permutation6
    mixedMoment B raw2588step0 raw2588step0Labels = mixedMoment B raw2588step1 raw2588step1Labels := by
      have ha : raw2588step1 = -raw2588step0 := by apply Matrix.ext; change ∀ i j, raw2588step1 i j = -(raw2588step0 i j); unfold raw2588step1 raw2588step0; decide +kernel
      have hl : raw2588step1Labels = raw2588step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2588step1 raw2588step1Labels = mixedMoment B raw2588step2 raw2588step2Labels := by
      have ha : raw2588step2 = raw2588step1 := by apply Matrix.ext; unfold raw2588step2 raw2588step1; decide +kernel
      have hl : raw2588step1Labels = labelEmbedding1 ∘ raw2588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2588step1 raw2588step1Labels raw2588step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2598 raw2598Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw2598 raw2598Labels = mixedMoment B raw2598step0 raw2598step0Labels := by
      have ha : raw2598step0 = (fun i j => raw2598 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2598step0 raw2598; decide +kernel
      have hl : raw2598step0Labels = raw2598Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2598 raw2598Labels permutation152 permutation4
    mixedMoment B raw2598step0 raw2598step0Labels = mixedMoment B raw2598step1 raw2598step1Labels := by
      have ha : raw2598step1 = raw2598step0 := by apply Matrix.ext; unfold raw2598step1 raw2598step0; decide +kernel
      have hl : raw2598step0Labels = labelEmbedding7 ∘ raw2598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2598step0 raw2598step0Labels raw2598step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical2599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2599 raw2599Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2599 raw2599Labels = mixedMoment B raw2599step0 raw2599step0Labels := by
      have ha : raw2599step0 = (fun i j => raw2599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2599step0 raw2599; decide +kernel
      have hl : raw2599step0Labels = raw2599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2599 raw2599Labels permutation152 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2600 raw2600Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2600 raw2600Labels = mixedMoment B raw2600step0 raw2600step0Labels := by
      have ha : raw2600step0 = (fun i j => raw2600 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2600step0 raw2600; decide +kernel
      have hl : raw2600step0Labels = raw2600Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2600 raw2600Labels permutation688 permutation6
    mixedMoment B raw2600step0 raw2600step0Labels = mixedMoment B raw2600step1 raw2600step1Labels := by
      have ha : raw2600step1 = raw2600step0 := by apply Matrix.ext; unfold raw2600step1 raw2600step0; decide +kernel
      have hl : raw2600step0Labels = labelEmbedding1 ∘ raw2600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2600step0 raw2600step0Labels raw2600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2607 raw2607Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw2607 raw2607Labels = mixedMoment B raw2607step0 raw2607step0Labels := by
      have ha : raw2607step0 = (fun i j => raw2607 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2607step0 raw2607; decide +kernel
      have hl : raw2607step0Labels = raw2607Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2607 raw2607Labels permutation32 permutation4
    mixedMoment B raw2607step0 raw2607step0Labels = mixedMoment B raw2607step1 raw2607step1Labels := by
      have ha : raw2607step1 = raw2607step0 := by apply Matrix.ext; unfold raw2607step1 raw2607step0; decide +kernel
      have hl : raw2607step0Labels = labelEmbedding7 ∘ raw2607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2607step0 raw2607step0Labels raw2607step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2608 raw2608Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2608 raw2608Labels = mixedMoment B raw2608step0 raw2608step0Labels := by
      have ha : raw2608step0 = (fun i j => raw2608 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2608step0 raw2608; decide +kernel
      have hl : raw2608step0Labels = raw2608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2608 raw2608Labels permutation32 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2609 raw2609Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2609 raw2609Labels = mixedMoment B raw2609step0 raw2609step0Labels := by
      have ha : raw2609step0 = (fun i j => raw2609 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2609step0 raw2609; decide +kernel
      have hl : raw2609step0Labels = raw2609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2609 raw2609Labels permutation151 permutation6
    mixedMoment B raw2609step0 raw2609step0Labels = mixedMoment B raw2609step1 raw2609step1Labels := by
      have ha : raw2609step1 = raw2609step0 := by apply Matrix.ext; unfold raw2609step1 raw2609step0; decide +kernel
      have hl : raw2609step0Labels = labelEmbedding1 ∘ raw2609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2609step0 raw2609step0Labels raw2609step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5401 node5401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3787 node3787Labels + mixedMoment B node3804 node3804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2475 singletonSmall5401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5401) = raw2475Labels := by decide +kernel
  rw [hl, canonical2475 B hB] at h
  have hc0 : mixedMoment B raw2475 (Fin.cases (0 : Fin 2) singletonSmall5401) =
      mixedMoment B node3787 node3787Labels := by
    have ha : raw2475 = raw2476 := by apply Matrix.ext; unfold raw2475 raw2476; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5401 = raw2476Labels := by decide +kernel
    rw [ha, hj, canonical2476 B hB]
  have hc1 : mixedMoment B raw2475 (Fin.cases (1 : Fin 2) singletonSmall5401) =
      mixedMoment B node3804 node3804Labels := by
    have ha : raw2475 = raw2477 := by apply Matrix.ext; unfold raw2475 raw2477; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5401 = raw2477Labels := by decide +kernel
    rw [ha, hj, canonical2477 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5403 node5403Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3789 node3789Labels + mixedMoment B node3810 node3810Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2478 singletonSmall5403
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5403) = raw2478Labels := by decide +kernel
  rw [hl, canonical2478 B hB] at h
  have hc0 : mixedMoment B raw2478 (Fin.cases (0 : Fin 2) singletonSmall5403) =
      mixedMoment B node3789 node3789Labels := by
    have ha : raw2478 = raw2479 := by apply Matrix.ext; unfold raw2478 raw2479; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5403 = raw2479Labels := by decide +kernel
    rw [ha, hj, canonical2479 B hB]
  have hc1 : mixedMoment B raw2478 (Fin.cases (1 : Fin 2) singletonSmall5403) =
      mixedMoment B node3810 node3810Labels := by
    have ha : raw2478 = raw2480 := by apply Matrix.ext; unfold raw2478 raw2480; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5403 = raw2480Labels := by decide +kernel
    rw [ha, hj, canonical2480 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5431 node5431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3849 node3849Labels + mixedMoment B node3875 node3875Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2520 singletonSmall5431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5431) = raw2520Labels := by decide +kernel
  rw [hl, canonical2520 B hB] at h
  have hc0 : mixedMoment B raw2520 (Fin.cases (0 : Fin 2) singletonSmall5431) =
      mixedMoment B node3849 node3849Labels := by
    have ha : raw2520 = raw2521 := by apply Matrix.ext; unfold raw2520 raw2521; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5431 = raw2521Labels := by decide +kernel
    rw [ha, hj, canonical2521 B hB]
  have hc1 : mixedMoment B raw2520 (Fin.cases (1 : Fin 2) singletonSmall5431) =
      mixedMoment B node3875 node3875Labels := by
    have ha : raw2520 = raw2522 := by apply Matrix.ext; unfold raw2520 raw2522; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5431 = raw2522Labels := by decide +kernel
    rw [ha, hj, canonical2522 B hB]
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

theorem singleton5472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5472 node5472Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3957 node3957Labels + mixedMoment B node3957 node3957Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2586 singletonSmall5472
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5472) = raw2586Labels := by decide +kernel
  rw [hl, canonical2586 B hB] at h
  have hc0 : mixedMoment B raw2586 (Fin.cases (0 : Fin 2) singletonSmall5472) =
      mixedMoment B node3957 node3957Labels := by
    have ha : raw2586 = raw2587 := by apply Matrix.ext; unfold raw2586 raw2587; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5472 = raw2587Labels := by decide +kernel
    rw [ha, hj, canonical2587 B hB]
  have hc1 : mixedMoment B raw2586 (Fin.cases (1 : Fin 2) singletonSmall5472) =
      mixedMoment B node3957 node3957Labels := by
    have ha : raw2586 = raw2588 := by apply Matrix.ext; unfold raw2586 raw2588; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5472 = raw2588Labels := by decide +kernel
    rw [ha, hj, canonical2588 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5478 node5478Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3974 node3974Labels + mixedMoment B node3974 node3974Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2598 singletonSmall5478
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5478) = raw2598Labels := by decide +kernel
  rw [hl, canonical2598 B hB] at h
  have hc0 : mixedMoment B raw2598 (Fin.cases (0 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2599 := by apply Matrix.ext; unfold raw2598 raw2599; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5478 = raw2599Labels := by decide +kernel
    rw [ha, hj, canonical2599 B hB]
  have hc1 : mixedMoment B raw2598 (Fin.cases (1 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2600 := by apply Matrix.ext; unfold raw2598 raw2600; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5478 = raw2600Labels := by decide +kernel
    rw [ha, hj, canonical2600 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5484 node5484Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3983 node3983Labels + mixedMoment B node3983 node3983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2607 singletonSmall5484
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5484) = raw2607Labels := by decide +kernel
  rw [hl, canonical2607 B hB] at h
  have hc0 : mixedMoment B raw2607 (Fin.cases (0 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2608 := by apply Matrix.ext; unfold raw2607 raw2608; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5484 = raw2608Labels := by decide +kernel
    rw [ha, hj, canonical2608 B hB]
  have hc1 : mixedMoment B raw2607 (Fin.cases (1 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2609 := by apply Matrix.ext; unfold raw2607 raw2609; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5484 = raw2609Labels := by decide +kernel
    rw [ha, hj, canonical2609 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = 0 := by
  exact mixedMoment_order_one B hB node5486 node5486Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3789 node3789Labels = Sparse.eval nodeValue3789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3789) = mixedMoment B node3789 node3789Labels := rfl
  simpa [nodeValue3789, Sparse.eval] using hc.symm

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3810 node3810Labels = Sparse.eval nodeValue3810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3810) = mixedMoment B node3810 node3810Labels := rfl
  simpa [nodeValue3810, Sparse.eval] using hc.symm

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

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

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

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

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

theorem sound5249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5249 node5249Labels = Sparse.eval nodeValue5249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5249) = mixedMoment B node5249 node5249Labels := rfl
  simpa [nodeValue5249, Sparse.eval] using hc.symm

theorem sound5251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5251 node5251Labels = Sparse.eval nodeValue5251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5251) = mixedMoment B node5251 node5251Labels := rfl
  simpa [nodeValue5251, Sparse.eval] using hc.symm

theorem sound5255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5255 node5255Labels = Sparse.eval nodeValue5255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5255) = mixedMoment B node5255 node5255Labels := rfl
  simpa [nodeValue5255, Sparse.eval] using hc.symm

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

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

theorem zero5408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5408 node5408Labels = 0 := by
  exact mixedMoment_order_one B hB node5408 node5408Labels 1
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

theorem sound5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5401 node5401Labels = Sparse.eval nodeValue5401 (mixedVector B) := by
  have h := singleton5401 B _hB
  rw [sound3787 B _hB _hF, sound3804 B _hB _hF] at h
  norm_num [nodeValue5401, nodeValue3787, nodeValue3804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5403 node5403Labels = Sparse.eval nodeValue5403 (mixedVector B) := by
  have h := singleton5403 B _hB
  rw [sound3789 B _hB _hF, sound3810 B _hB _hF] at h
  norm_num [nodeValue5403, nodeValue3789, nodeValue3810, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5408 node5408Labels = Sparse.eval nodeValue5408 (mixedVector B) := by
  simpa only [nodeValue5408, Sparse.eval_nil] using zero5408 B _hB _hF

theorem sound5414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5414 node5414Labels = Sparse.eval nodeValue5414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5414) = mixedMoment B node5414 node5414Labels := rfl
  simpa [nodeValue5414, Sparse.eval] using hc.symm

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
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

theorem sound5470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5470 node5470Labels = Sparse.eval nodeValue5470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5470) = mixedMoment B node5470 node5470Labels := rfl
  simpa [nodeValue5470, Sparse.eval] using hc.symm

theorem sound5472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5472 node5472Labels = Sparse.eval nodeValue5472 (mixedVector B) := by
  have h := singleton5472 B _hB
  rw [sound3957 B _hB _hF] at h
  norm_num [nodeValue5472, nodeValue3957, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5480 node5480Labels = Sparse.eval nodeValue5480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5480) = mixedMoment B node5480 node5480Labels := rfl
  simpa [nodeValue5480, Sparse.eval] using hc.symm

theorem sound5484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5484 node5484Labels = Sparse.eval nodeValue5484 (mixedVector B) := by
  have h := singleton5484 B _hB
  rw [sound3983 B _hB _hF] at h
  norm_num [nodeValue5484, nodeValue3983, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = Sparse.eval nodeValue5486 (mixedVector B) := by
  simpa only [nodeValue5486, Sparse.eval_nil] using zero5486 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1120 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 1) (sourceB1120 + difference 1 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 1) (sourceB1120 + difference 1 0) sourceC1120) = raw18863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18863; decide +kernel
    rw [ha]
    exact (canonical18863 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 2) (sourceB1120 + difference 2 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 2) (sourceB1120 + difference 2 0) sourceC1120) = raw18864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18864; decide +kernel
    rw [ha]
    exact (canonical18864 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 3) (sourceB1120 + difference 3 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 3) (sourceB1120 + difference 3 0) sourceC1120) = raw18865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18865; decide +kernel
    rw [ha]
    exact (canonical18865 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 4) (sourceB1120 + difference 4 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 4) (sourceB1120 + difference 4 0) sourceC1120) = raw18866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18866; decide +kernel
    rw [ha]
    exact (canonical18866 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1120 + difference 0 5) (sourceB1120 + difference 5 0) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA1120 + difference 0 5) (sourceB1120 + difference 5 0) sourceC1120) = raw18867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18867; decide +kernel
    rw [ha]
    exact (canonical18867 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 0) (sourceB1120 + difference 0 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 0) (sourceB1120 + difference 0 1) sourceC1120) = raw18868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18868; decide +kernel
    rw [ha]
    exact (canonical18868 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 2) (sourceB1120 + difference 2 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 2) (sourceB1120 + difference 2 1) sourceC1120) = raw18869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18869; decide +kernel
    rw [ha]
    exact (canonical18869 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 3) (sourceB1120 + difference 3 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 3) (sourceB1120 + difference 3 1) sourceC1120) = raw18870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18870; decide +kernel
    rw [ha]
    exact (canonical18870 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 4) (sourceB1120 + difference 4 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 4) (sourceB1120 + difference 4 1) sourceC1120) = raw18871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18871; decide +kernel
    rw [ha]
    exact (canonical18871 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1120 + difference 1 5) (sourceB1120 + difference 5 1) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1120 + difference 1 5) (sourceB1120 + difference 5 1) sourceC1120) = raw18872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18872; decide +kernel
    rw [ha]
    exact (canonical18872 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 0) (sourceB1120 + difference 0 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 0) (sourceB1120 + difference 0 2) sourceC1120) = raw18873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18873; decide +kernel
    rw [ha]
    exact (canonical18873 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 1) (sourceB1120 + difference 1 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 1) (sourceB1120 + difference 1 2) sourceC1120) = raw18874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18874; decide +kernel
    rw [ha]
    exact (canonical18874 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 3) (sourceB1120 + difference 3 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 3) (sourceB1120 + difference 3 2) sourceC1120) = raw18875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18875; decide +kernel
    rw [ha]
    exact (canonical18875 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 4) (sourceB1120 + difference 4 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 4) (sourceB1120 + difference 4 2) sourceC1120) = raw18876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18876; decide +kernel
    rw [ha]
    exact (canonical18876 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1120 + difference 2 5) (sourceB1120 + difference 5 2) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA1120 + difference 2 5) (sourceB1120 + difference 5 2) sourceC1120) = raw18877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18877; decide +kernel
    rw [ha]
    exact (canonical18877 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 0) (sourceB1120 + difference 0 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 0) (sourceB1120 + difference 0 3) sourceC1120) = raw18878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18878; decide +kernel
    rw [ha]
    exact (canonical18878 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 1) (sourceB1120 + difference 1 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 1) (sourceB1120 + difference 1 3) sourceC1120) = raw18879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18879; decide +kernel
    rw [ha]
    exact (canonical18879 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 2) (sourceB1120 + difference 2 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 2) (sourceB1120 + difference 2 3) sourceC1120) = raw18880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18880; decide +kernel
    rw [ha]
    exact (canonical18880 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 4) (sourceB1120 + difference 4 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 4) (sourceB1120 + difference 4 3) sourceC1120) = raw18881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18881; decide +kernel
    rw [ha]
    exact (canonical18881 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1120 + difference 3 5) (sourceB1120 + difference 5 3) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA1120 + difference 3 5) (sourceB1120 + difference 5 3) sourceC1120) = raw18882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18882; decide +kernel
    rw [ha]
    exact (canonical18882 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 0) (sourceB1120 + difference 0 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 0) (sourceB1120 + difference 0 4) sourceC1120) = raw18883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18883; decide +kernel
    rw [ha]
    exact (canonical18883 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 1) (sourceB1120 + difference 1 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 1) (sourceB1120 + difference 1 4) sourceC1120) = raw18884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18884; decide +kernel
    rw [ha]
    exact (canonical18884 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 2) (sourceB1120 + difference 2 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 2) (sourceB1120 + difference 2 4) sourceC1120) = raw18885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18885; decide +kernel
    rw [ha]
    exact (canonical18885 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 3) (sourceB1120 + difference 3 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 3) (sourceB1120 + difference 3 4) sourceC1120) = raw18886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18886; decide +kernel
    rw [ha]
    exact (canonical18886 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1120 + difference 4 5) (sourceB1120 + difference 5 4) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA1120 + difference 4 5) (sourceB1120 + difference 5 4) sourceC1120) = raw18887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18887; decide +kernel
    rw [ha]
    exact (canonical18887 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 0) (sourceB1120 + difference 0 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 0) (sourceB1120 + difference 0 5) sourceC1120) = raw18888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18888; decide +kernel
    rw [ha]
    exact (canonical18888 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 1) (sourceB1120 + difference 1 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 1) (sourceB1120 + difference 1 5) sourceC1120) = raw18889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18889; decide +kernel
    rw [ha]
    exact (canonical18889 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 2) (sourceB1120 + difference 2 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 2) (sourceB1120 + difference 2 5) sourceC1120) = raw18890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18890; decide +kernel
    rw [ha]
    exact (canonical18890 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 3) (sourceB1120 + difference 3 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 3) (sourceB1120 + difference 3 5) sourceC1120) = raw18891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18891; decide +kernel
    rw [ha]
    exact (canonical18891 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1120 + difference 5 4) (sourceB1120 + difference 4 5) sourceC1120) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1120 + difference 5 4) (sourceB1120 + difference 4 5) sourceC1120) = raw18892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1120 sourceB1120 sourceC1120 difference raw18892; decide +kernel
    rw [ha]
    exact (canonical18892 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1120 sourceB1120 sourceC1120
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1120, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck972 : Integer.Sparse.reindex keyMap MixedData.row972 = numericRow972 := by decide +kernel

theorem numericCheck972 (x : Master → ℝ) : Integer.Sparse.eval numericRow972 x =
    (8640 : ℝ) * reducedSource972 x := by
  norm_num [numericRow972, reducedSource972, Integer.Sparse.eval, Sparse.eval, nodeValue5249, nodeValue5251, nodeValue5255, nodeValue5281, nodeValue5401, nodeValue5403, nodeValue5408, nodeValue5414, nodeValue5424, nodeValue5429, nodeValue5430, nodeValue5431, nodeValue5439, nodeValue5470, nodeValue5472, nodeValue5478, nodeValue5480, nodeValue5482, nodeValue5484, nodeValue5485, nodeValue5486]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero972 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource972 (mixedVector B) = 0 := by
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5408 : mixedVector B (Sum.inr 5408) = Sparse.eval nodeValue5408 (mixedVector B) := by
    change mixedMoment B node5408 node5408Labels = _
    exact sound5408 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5470 : mixedVector B (Sum.inr 5470) = Sparse.eval nodeValue5470 (mixedVector B) := by
    change mixedMoment B node5470 node5470Labels = _
    exact sound5470 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5480 : mixedVector B (Sum.inr 5480) = Sparse.eval nodeValue5480 (mixedVector B) := by
    change mixedMoment B node5480 node5480Labels = _
    exact sound5480 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm1120, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5249, h5251, h5255, h5281, h5401, h5403, h5408, h5414, h5424, h5429, h5430, h5431, h5439, h5470, h5472, h5478, h5480, h5482, h5484, h5485, h5486, reducedSource972] using sourceEq1120 B hB

theorem rowSound972_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row972 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck972, numericCheck972, reducedZero972 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e_oai
