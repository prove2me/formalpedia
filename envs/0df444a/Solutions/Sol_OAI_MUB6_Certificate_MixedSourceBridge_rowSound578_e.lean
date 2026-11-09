-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:57:15.808059+00:00
-- url     : https://prove2.me/submissions/8745e304-0cbc-4ce5-85ea-41d4301276fc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5452_e

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

theorem canonical1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1650 raw1650Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw1650 raw1650Labels = mixedMoment B raw1650step0 raw1650step0Labels := by
      have ha : raw1650step0 = (fun i j => raw1650 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1650step0 raw1650; decide +kernel
      have hl : raw1650step0Labels = raw1650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1650 raw1650Labels permutation152 permutation4
    mixedMoment B raw1650step0 raw1650step0Labels = mixedMoment B raw1650step1 raw1650step1Labels := by
      have ha : raw1650step1 = raw1650step0 := by apply Matrix.ext; unfold raw1650step1 raw1650step0; decide +kernel
      have hl : raw1650step0Labels = labelEmbedding7 ∘ raw1650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1650step0 raw1650step0Labels raw1650step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

theorem canonical1651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1651 raw1651Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw1651 raw1651Labels = mixedMoment B raw1651step0 raw1651step0Labels := by
      have ha : raw1651step0 = (fun i j => raw1651 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1651step0 raw1651; decide +kernel
      have hl : raw1651step0Labels = raw1651Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1651 raw1651Labels permutation152 permutation4
    _ = mixedMoment B node1901 node1901Labels := by rfl

theorem canonical1652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1652 raw1652Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw1652 raw1652Labels = mixedMoment B raw1652step0 raw1652step0Labels := by
      have ha : raw1652step0 = (fun i j => raw1652 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1652step0 raw1652; decide +kernel
      have hl : raw1652step0Labels = raw1652Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1652 raw1652Labels permutation152 permutation6
    mixedMoment B raw1652step0 raw1652step0Labels = mixedMoment B raw1652step1 raw1652step1Labels := by
      have ha : raw1652step1 = -raw1652step0 := by apply Matrix.ext; change ∀ i j, raw1652step1 i j = -(raw1652step0 i j); unfold raw1652step1 raw1652step0; decide +kernel
      have hl : raw1652step1Labels = raw1652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1652step1 raw1652step1Labels = mixedMoment B raw1652step2 raw1652step2Labels := by
      have ha : raw1652step2 = raw1652step1 := by apply Matrix.ext; unfold raw1652step2 raw1652step1; decide +kernel
      have hl : raw1652step1Labels = labelEmbedding1 ∘ raw1652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1652step1 raw1652step1Labels raw1652step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1941 node1941Labels := by rfl

theorem canonical1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1653 raw1653Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw1653 raw1653Labels = mixedMoment B raw1653step0 raw1653step0Labels := by
      have ha : raw1653step0 = (fun i j => raw1653 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1653step0 raw1653; decide +kernel
      have hl : raw1653step0Labels = raw1653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1653 raw1653Labels permutation152 permutation4
    mixedMoment B raw1653step0 raw1653step0Labels = mixedMoment B raw1653step1 raw1653step1Labels := by
      have ha : raw1653step1 = raw1653step0 := by apply Matrix.ext; unfold raw1653step1 raw1653step0; decide +kernel
      have hl : raw1653step0Labels = labelEmbedding7 ∘ raw1653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1653step0 raw1653step0Labels raw1653step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical1654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1654 raw1654Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw1654 raw1654Labels = mixedMoment B raw1654step0 raw1654step0Labels := by
      have ha : raw1654step0 = (fun i j => raw1654 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1654step0 raw1654; decide +kernel
      have hl : raw1654step0Labels = raw1654Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1654 raw1654Labels permutation152 permutation4
    _ = mixedMoment B node1909 node1909Labels := by rfl

theorem canonical1655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1655 raw1655Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw1655 raw1655Labels = mixedMoment B raw1655step0 raw1655step0Labels := by
      have ha : raw1655step0 = (fun i j => raw1655 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1655step0 raw1655; decide +kernel
      have hl : raw1655step0Labels = raw1655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1655 raw1655Labels permutation159 permutation6
    mixedMoment B raw1655step0 raw1655step0Labels = mixedMoment B raw1655step1 raw1655step1Labels := by
      have ha : raw1655step1 = -raw1655step0 := by apply Matrix.ext; change ∀ i j, raw1655step1 i j = -(raw1655step0 i j); unfold raw1655step1 raw1655step0; decide +kernel
      have hl : raw1655step1Labels = raw1655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1655step1 raw1655step1Labels = mixedMoment B raw1655step2 raw1655step2Labels := by
      have ha : raw1655step2 = raw1655step1 := by apply Matrix.ext; unfold raw1655step2 raw1655step1; decide +kernel
      have hl : raw1655step1Labels = labelEmbedding1 ∘ raw1655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1655step1 raw1655step1Labels raw1655step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1909 node1909Labels := by rfl

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

theorem canonical1761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1761 raw1761Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw1761 raw1761Labels = mixedMoment B raw1761step0 raw1761step0Labels := by
      have ha : raw1761step0 = (fun i j => raw1761 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1761step0 raw1761; decide +kernel
      have hl : raw1761step0Labels = raw1761Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1761 raw1761Labels permutation152 permutation4
    mixedMoment B raw1761step0 raw1761step0Labels = mixedMoment B raw1761step1 raw1761step1Labels := by
      have ha : raw1761step1 = raw1761step0 := by apply Matrix.ext; unfold raw1761step1 raw1761step0; decide +kernel
      have hl : raw1761step0Labels = labelEmbedding7 ∘ raw1761step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1761step0 raw1761step0Labels raw1761step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical1762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1762 raw1762Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw1762 raw1762Labels = mixedMoment B raw1762step0 raw1762step0Labels := by
      have ha : raw1762step0 = (fun i j => raw1762 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1762step0 raw1762; decide +kernel
      have hl : raw1762step0Labels = raw1762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1762 raw1762Labels permutation152 permutation4
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical1763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1763 raw1763Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw1763 raw1763Labels = mixedMoment B raw1763step0 raw1763step0Labels := by
      have ha : raw1763step0 = (fun i j => raw1763 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1763step0 raw1763; decide +kernel
      have hl : raw1763step0Labels = raw1763Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1763 raw1763Labels permutation152 permutation6
    mixedMoment B raw1763step0 raw1763step0Labels = mixedMoment B raw1763step1 raw1763step1Labels := by
      have ha : raw1763step1 = -raw1763step0 := by apply Matrix.ext; change ∀ i j, raw1763step1 i j = -(raw1763step0 i j); unfold raw1763step1 raw1763step0; decide +kernel
      have hl : raw1763step1Labels = raw1763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1763step1 raw1763step1Labels = mixedMoment B raw1763step2 raw1763step2Labels := by
      have ha : raw1763step2 = raw1763step1 := by apply Matrix.ext; unfold raw1763step2 raw1763step1; decide +kernel
      have hl : raw1763step1Labels = labelEmbedding1 ∘ raw1763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1763step1 raw1763step1Labels raw1763step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

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

theorem canonical1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1812 raw1812Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw1812 raw1812Labels = mixedMoment B raw1812step0 raw1812step0Labels := by
      have ha : raw1812step0 = (fun i j => raw1812 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1812step0 raw1812; decide +kernel
      have hl : raw1812step0Labels = raw1812Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1812 raw1812Labels permutation152 permutation4
    mixedMoment B raw1812step0 raw1812step0Labels = mixedMoment B raw1812step1 raw1812step1Labels := by
      have ha : raw1812step1 = raw1812step0 := by apply Matrix.ext; unfold raw1812step1 raw1812step0; decide +kernel
      have hl : raw1812step0Labels = labelEmbedding7 ∘ raw1812step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1812step0 raw1812step0Labels raw1812step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical1813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1813 raw1813Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1813 raw1813Labels = mixedMoment B raw1813step0 raw1813step0Labels := by
      have ha : raw1813step0 = (fun i j => raw1813 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1813step0 raw1813; decide +kernel
      have hl : raw1813step0Labels = raw1813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1813 raw1813Labels permutation152 permutation4
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1814 raw1814Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1814 raw1814Labels = mixedMoment B raw1814step0 raw1814step0Labels := by
      have ha : raw1814step0 = (fun i j => raw1814 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1814step0 raw1814; decide +kernel
      have hl : raw1814step0Labels = raw1814Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1814 raw1814Labels permutation212 permutation6
    mixedMoment B raw1814step0 raw1814step0Labels = mixedMoment B raw1814step1 raw1814step1Labels := by
      have ha : raw1814step1 = -raw1814step0 := by apply Matrix.ext; change ∀ i j, raw1814step1 i j = -(raw1814step0 i j); unfold raw1814step1 raw1814step0; decide +kernel
      have hl : raw1814step1Labels = raw1814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1814step1 raw1814step1Labels = mixedMoment B raw1814step2 raw1814step2Labels := by
      have ha : raw1814step2 = raw1814step1 := by apply Matrix.ext; unfold raw1814step2 raw1814step1; decide +kernel
      have hl : raw1814step1Labels = labelEmbedding1 ∘ raw1814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1814step1 raw1814step1Labels raw1814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw969 raw969Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw969 raw969Labels = mixedMoment B raw969step0 raw969step0Labels := by
      have ha : raw969step0 = (fun i j => raw969 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw969step0 raw969; decide +kernel
      have hl : raw969step0Labels = raw969Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw969 raw969Labels permutation152 permutation4
    mixedMoment B raw969step0 raw969step0Labels = mixedMoment B raw969step1 raw969step1Labels := by
      have ha : raw969step1 = raw969step0 := by apply Matrix.ext; unfold raw969step1 raw969step0; decide +kernel
      have hl : raw969step0Labels = labelEmbedding7 ∘ raw969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw969step0 raw969step0Labels raw969step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw970 raw970Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw970 raw970Labels = mixedMoment B raw970step0 raw970step0Labels := by
      have ha : raw970step0 = (fun i j => raw970 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw970step0 raw970; decide +kernel
      have hl : raw970step0Labels = raw970Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw970 raw970Labels permutation152 permutation4
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw971 raw971Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw971 raw971Labels = mixedMoment B raw971step0 raw971step0Labels := by
      have ha : raw971step0 = (fun i j => raw971 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw971step0 raw971; decide +kernel
      have hl : raw971step0Labels = raw971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw971 raw971Labels permutation200 permutation6
    mixedMoment B raw971step0 raw971step0Labels = mixedMoment B raw971step1 raw971step1Labels := by
      have ha : raw971step1 = -raw971step0 := by apply Matrix.ext; change ∀ i j, raw971step1 i j = -(raw971step0 i j); unfold raw971step1 raw971step0; decide +kernel
      have hl : raw971step1Labels = raw971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw971step1 raw971step1Labels = mixedMoment B raw971step2 raw971step2Labels := by
      have ha : raw971step2 = raw971step1 := by apply Matrix.ext; unfold raw971step2 raw971step1; decide +kernel
      have hl : raw971step1Labels = labelEmbedding1 ∘ raw971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw971step1 raw971step1Labels raw971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

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

theorem canonical984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw984 raw984Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw984 raw984Labels = mixedMoment B raw984step0 raw984step0Labels := by
      have ha : raw984step0 = (fun i j => raw984 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw984step0 raw984; decide +kernel
      have hl : raw984step0Labels = raw984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw984 raw984Labels permutation32 permutation4
    mixedMoment B raw984step0 raw984step0Labels = mixedMoment B raw984step1 raw984step1Labels := by
      have ha : raw984step1 = raw984step0 := by apply Matrix.ext; unfold raw984step1 raw984step0; decide +kernel
      have hl : raw984step0Labels = labelEmbedding7 ∘ raw984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw984step0 raw984step0Labels raw984step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw985 raw985Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw985 raw985Labels = mixedMoment B raw985step0 raw985step0Labels := by
      have ha : raw985step0 = (fun i j => raw985 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw985step0 raw985; decide +kernel
      have hl : raw985step0Labels = raw985Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw985 raw985Labels permutation32 permutation4
    _ = mixedMoment B node790 node790Labels := by rfl

theorem canonical986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw986 raw986Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw986 raw986Labels = mixedMoment B raw986step0 raw986step0Labels := by
      have ha : raw986step0 = (fun i j => raw986 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw986step0 raw986; decide +kernel
      have hl : raw986step0Labels = raw986Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw986 raw986Labels permutation32 permutation6
    mixedMoment B raw986step0 raw986step0Labels = mixedMoment B raw986step1 raw986step1Labels := by
      have ha : raw986step1 = -raw986step0 := by apply Matrix.ext; change ∀ i j, raw986step1 i j = -(raw986step0 i j); unfold raw986step1 raw986step0; decide +kernel
      have hl : raw986step1Labels = raw986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw986step1 raw986step1Labels = mixedMoment B raw986step2 raw986step2Labels := by
      have ha : raw986step2 = raw986step1 := by apply Matrix.ext; unfold raw986step2 raw986step1; decide +kernel
      have hl : raw986step1Labels = labelEmbedding1 ∘ raw986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw986step1 raw986step1Labels raw986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

theorem canonical990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw990 raw990Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw990 raw990Labels = mixedMoment B raw990step0 raw990step0Labels := by
      have ha : raw990step0 = (fun i j => raw990 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw990step0 raw990; decide +kernel
      have hl : raw990step0Labels = raw990Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw990 raw990Labels permutation32 permutation4
    mixedMoment B raw990step0 raw990step0Labels = mixedMoment B raw990step1 raw990step1Labels := by
      have ha : raw990step1 = raw990step0 := by apply Matrix.ext; unfold raw990step1 raw990step0; decide +kernel
      have hl : raw990step0Labels = labelEmbedding7 ∘ raw990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw990step0 raw990step0Labels raw990step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw991 raw991Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw991 raw991Labels = mixedMoment B raw991step0 raw991step0Labels := by
      have ha : raw991step0 = (fun i j => raw991 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw991step0 raw991; decide +kernel
      have hl : raw991step0Labels = raw991Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw991 raw991Labels permutation32 permutation4
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw992 raw992Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw992 raw992Labels = mixedMoment B raw992step0 raw992step0Labels := by
      have ha : raw992step0 = (fun i j => raw992 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw992step0 raw992; decide +kernel
      have hl : raw992step0Labels = raw992Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw992 raw992Labels permutation39 permutation6
    mixedMoment B raw992step0 raw992step0Labels = mixedMoment B raw992step1 raw992step1Labels := by
      have ha : raw992step1 = -raw992step0 := by apply Matrix.ext; change ∀ i j, raw992step1 i j = -(raw992step0 i j); unfold raw992step1 raw992step0; decide +kernel
      have hl : raw992step1Labels = raw992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw992step1 raw992step1Labels = mixedMoment B raw992step2 raw992step2Labels := by
      have ha : raw992step2 = raw992step1 := by apply Matrix.ext; unfold raw992step2 raw992step1; decide +kernel
      have hl : raw992step1Labels = labelEmbedding1 ∘ raw992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw992step1 raw992step1Labels raw992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11315 raw11315Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw11315 raw11315Labels = mixedMoment B raw11315step0 raw11315step0Labels := by
      have hz : ∀ j, raw11315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11315step0 = (fun i j => raw11315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11315step0 raw11315; decide +kernel
      have hl : raw11315step0Labels = raw11315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11315 raw11315Labels permutation434 hz
    mixedMoment B raw11315step0 raw11315step0Labels = mixedMoment B raw11315step1 raw11315step1Labels := by
      have ha : raw11315step1 = (fun i j => raw11315step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11315step1 raw11315step0; decide +kernel
      have hl : raw11315step1Labels = raw11315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11315step0 raw11315step0Labels permutation32 permutation3
    mixedMoment B raw11315step1 raw11315step1Labels = mixedMoment B raw11315step2 raw11315step2Labels := by
      have ha : raw11315step2 = raw11315step1 := by apply Matrix.ext; unfold raw11315step2 raw11315step1; decide +kernel
      have hl : raw11315step1Labels = labelEmbedding6 ∘ raw11315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11315step1 raw11315step1Labels raw11315step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical11316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11316 raw11316Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw11316 raw11316Labels = mixedMoment B raw11316step0 raw11316step0Labels := by
      have hz : ∀ j, raw11316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11316step0 = (fun i j => raw11316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11316step0 raw11316; decide +kernel
      have hl : raw11316step0Labels = raw11316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11316 raw11316Labels permutation434 hz
    mixedMoment B raw11316step0 raw11316step0Labels = mixedMoment B raw11316step1 raw11316step1Labels := by
      have ha : raw11316step1 = (fun i j => raw11316step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11316step1 raw11316step0; decide +kernel
      have hl : raw11316step1Labels = raw11316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11316step0 raw11316step0Labels permutation38 permutation3
    mixedMoment B raw11316step1 raw11316step1Labels = mixedMoment B raw11316step2 raw11316step2Labels := by
      have ha : raw11316step2 = raw11316step1 := by apply Matrix.ext; unfold raw11316step2 raw11316step1; decide +kernel
      have hl : raw11316step1Labels = labelEmbedding6 ∘ raw11316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11316step1 raw11316step1Labels raw11316step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical11317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11317 raw11317Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw11317 raw11317Labels = mixedMoment B raw11317step0 raw11317step0Labels := by
      have ha : raw11317step0 = (fun i j => raw11317 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11317step0 raw11317; decide +kernel
      have hl : raw11317step0Labels = raw11317Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11317 raw11317Labels permutation200 permutation3
    mixedMoment B raw11317step0 raw11317step0Labels = mixedMoment B raw11317step1 raw11317step1Labels := by
      have ha : raw11317step1 = raw11317step0 := by apply Matrix.ext; unfold raw11317step1 raw11317step0; decide +kernel
      have hl : raw11317step0Labels = labelEmbedding6 ∘ raw11317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11317step0 raw11317step0Labels raw11317step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical11318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11318 raw11318Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw11318 raw11318Labels = mixedMoment B raw11318step0 raw11318step0Labels := by
      have hz : ∀ j, raw11318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11318step0 = (fun i j => raw11318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11318step0 raw11318; decide +kernel
      have hl : raw11318step0Labels = raw11318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11318 raw11318Labels permutation434 hz
    mixedMoment B raw11318step0 raw11318step0Labels = mixedMoment B raw11318step1 raw11318step1Labels := by
      have ha : raw11318step1 = (fun i j => raw11318step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11318step1 raw11318step0; decide +kernel
      have hl : raw11318step1Labels = raw11318step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11318step0 raw11318step0Labels permutation44 permutation5
    mixedMoment B raw11318step1 raw11318step1Labels = mixedMoment B raw11318step2 raw11318step2Labels := by
      have ha : raw11318step2 = -raw11318step1 := by apply Matrix.ext; change ∀ i j, raw11318step2 i j = -(raw11318step1 i j); unfold raw11318step2 raw11318step1; decide +kernel
      have hl : raw11318step2Labels = raw11318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11318step2 raw11318step2Labels = mixedMoment B raw11318step3 raw11318step3Labels := by
      have ha : raw11318step3 = raw11318step2 := by apply Matrix.ext; unfold raw11318step3 raw11318step2; decide +kernel
      have hl : raw11318step2Labels = labelEmbedding8 ∘ raw11318step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11318step2 raw11318step2Labels raw11318step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical11319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11319 raw11319Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw11319 raw11319Labels = mixedMoment B raw11319step0 raw11319step0Labels := by
      have hz : ∀ j, raw11319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11319step0 = (fun i j => raw11319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11319step0 raw11319; decide +kernel
      have hl : raw11319step0Labels = raw11319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11319 raw11319Labels permutation434 hz
    mixedMoment B raw11319step0 raw11319step0Labels = mixedMoment B raw11319step1 raw11319step1Labels := by
      have ha : raw11319step1 = (fun i j => raw11319step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11319step1 raw11319step0; decide +kernel
      have hl : raw11319step1Labels = raw11319step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11319step0 raw11319step0Labels permutation32 permutation3
    mixedMoment B raw11319step1 raw11319step1Labels = mixedMoment B raw11319step2 raw11319step2Labels := by
      have ha : raw11319step2 = raw11319step1 := by apply Matrix.ext; unfold raw11319step2 raw11319step1; decide +kernel
      have hl : raw11319step1Labels = labelEmbedding6 ∘ raw11319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11319step1 raw11319step1Labels raw11319step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical11320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11320 raw11320Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw11320 raw11320Labels = mixedMoment B raw11320step0 raw11320step0Labels := by
      have hz : ∀ j, raw11320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11320step0 = (fun i j => raw11320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11320step0 raw11320; decide +kernel
      have hl : raw11320step0Labels = raw11320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11320 raw11320Labels permutation434 hz
    mixedMoment B raw11320step0 raw11320step0Labels = mixedMoment B raw11320step1 raw11320step1Labels := by
      have ha : raw11320step1 = (fun i j => raw11320step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11320step1 raw11320step0; decide +kernel
      have hl : raw11320step1Labels = raw11320step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11320step0 raw11320step0Labels permutation40 permutation3
    mixedMoment B raw11320step1 raw11320step1Labels = mixedMoment B raw11320step2 raw11320step2Labels := by
      have ha : raw11320step2 = raw11320step1 := by apply Matrix.ext; unfold raw11320step2 raw11320step1; decide +kernel
      have hl : raw11320step1Labels = labelEmbedding6 ∘ raw11320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11320step1 raw11320step1Labels raw11320step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical11321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11321 raw11321Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11321 raw11321Labels = mixedMoment B raw11321step0 raw11321step0Labels := by
      have hz : ∀ j, raw11321 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11321step0 = (fun i j => raw11321 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11321step0 raw11321; decide +kernel
      have hl : raw11321step0Labels = raw11321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11321 raw11321Labels permutation434 hz
    mixedMoment B raw11321step0 raw11321step0Labels = mixedMoment B raw11321step1 raw11321step1Labels := by
      have ha : raw11321step1 = (fun i j => raw11321step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11321step1 raw11321step0; decide +kernel
      have hl : raw11321step1Labels = raw11321step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11321step0 raw11321step0Labels permutation40 permutation3
    mixedMoment B raw11321step1 raw11321step1Labels = mixedMoment B raw11321step2 raw11321step2Labels := by
      have ha : raw11321step2 = raw11321step1 := by apply Matrix.ext; unfold raw11321step2 raw11321step1; decide +kernel
      have hl : raw11321step1Labels = labelEmbedding6 ∘ raw11321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11321step1 raw11321step1Labels raw11321step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical11322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11322 raw11322Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw11322 raw11322Labels = mixedMoment B raw11322step0 raw11322step0Labels := by
      have ha : raw11322step0 = (fun i j => raw11322 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11322step0 raw11322; decide +kernel
      have hl : raw11322step0Labels = raw11322Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11322 raw11322Labels permutation208 permutation3
    mixedMoment B raw11322step0 raw11322step0Labels = mixedMoment B raw11322step1 raw11322step1Labels := by
      have ha : raw11322step1 = raw11322step0 := by apply Matrix.ext; unfold raw11322step1 raw11322step0; decide +kernel
      have hl : raw11322step0Labels = labelEmbedding6 ∘ raw11322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11322step0 raw11322step0Labels raw11322step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical11323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11323 raw11323Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11323 raw11323Labels = mixedMoment B raw11323step0 raw11323step0Labels := by
      have hz : ∀ j, raw11323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11323step0 = (fun i j => raw11323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11323step0 raw11323; decide +kernel
      have hl : raw11323step0Labels = raw11323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11323 raw11323Labels permutation434 hz
    mixedMoment B raw11323step0 raw11323step0Labels = mixedMoment B raw11323step1 raw11323step1Labels := by
      have ha : raw11323step1 = (fun i j => raw11323step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11323step1 raw11323step0; decide +kernel
      have hl : raw11323step1Labels = raw11323step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11323step0 raw11323step0Labels permutation47 permutation5
    mixedMoment B raw11323step1 raw11323step1Labels = mixedMoment B raw11323step2 raw11323step2Labels := by
      have ha : raw11323step2 = -raw11323step1 := by apply Matrix.ext; change ∀ i j, raw11323step2 i j = -(raw11323step1 i j); unfold raw11323step2 raw11323step1; decide +kernel
      have hl : raw11323step2Labels = raw11323step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11323step2 raw11323step2Labels = mixedMoment B raw11323step3 raw11323step3Labels := by
      have ha : raw11323step3 = raw11323step2 := by apply Matrix.ext; unfold raw11323step3 raw11323step2; decide +kernel
      have hl : raw11323step2Labels = labelEmbedding8 ∘ raw11323step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11323step2 raw11323step2Labels raw11323step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical11324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11324 raw11324Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11324 raw11324Labels = mixedMoment B raw11324step0 raw11324step0Labels := by
      have hz : ∀ j, raw11324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11324step0 = (fun i j => raw11324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11324step0 raw11324; decide +kernel
      have hl : raw11324step0Labels = raw11324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11324 raw11324Labels permutation434 hz
    mixedMoment B raw11324step0 raw11324step0Labels = mixedMoment B raw11324step1 raw11324step1Labels := by
      have ha : raw11324step1 = (fun i j => raw11324step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11324step1 raw11324step0; decide +kernel
      have hl : raw11324step1Labels = raw11324step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11324step0 raw11324step0Labels permutation49 permutation5
    mixedMoment B raw11324step1 raw11324step1Labels = mixedMoment B raw11324step2 raw11324step2Labels := by
      have ha : raw11324step2 = -raw11324step1 := by apply Matrix.ext; change ∀ i j, raw11324step2 i j = -(raw11324step1 i j); unfold raw11324step2 raw11324step1; decide +kernel
      have hl : raw11324step2Labels = raw11324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11324step2 raw11324step2Labels = mixedMoment B raw11324step3 raw11324step3Labels := by
      have ha : raw11324step3 = raw11324step2 := by apply Matrix.ext; unfold raw11324step3 raw11324step2; decide +kernel
      have hl : raw11324step2Labels = labelEmbedding8 ∘ raw11324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11324step2 raw11324step2Labels raw11324step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11325 raw11325Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw11325 raw11325Labels = mixedMoment B raw11325step0 raw11325step0Labels := by
      have hz : ∀ j, raw11325 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11325step0 = (fun i j => raw11325 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11325step0 raw11325; decide +kernel
      have hl : raw11325step0Labels = raw11325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11325 raw11325Labels permutation434 hz
    mixedMoment B raw11325step0 raw11325step0Labels = mixedMoment B raw11325step1 raw11325step1Labels := by
      have ha : raw11325step1 = (fun i j => raw11325step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11325step1 raw11325step0; decide +kernel
      have hl : raw11325step1Labels = raw11325step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11325step0 raw11325step0Labels permutation34 permutation3
    mixedMoment B raw11325step1 raw11325step1Labels = mixedMoment B raw11325step2 raw11325step2Labels := by
      have ha : raw11325step2 = raw11325step1 := by apply Matrix.ext; unfold raw11325step2 raw11325step1; decide +kernel
      have hl : raw11325step1Labels = labelEmbedding6 ∘ raw11325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11325step1 raw11325step1Labels raw11325step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical11326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11326 raw11326Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11326 raw11326Labels = mixedMoment B raw11326step0 raw11326step0Labels := by
      have hz : ∀ j, raw11326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11326step0 = (fun i j => raw11326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11326step0 raw11326; decide +kernel
      have hl : raw11326step0Labels = raw11326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11326 raw11326Labels permutation434 hz
    mixedMoment B raw11326step0 raw11326step0Labels = mixedMoment B raw11326step1 raw11326step1Labels := by
      have ha : raw11326step1 = (fun i j => raw11326step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11326step1 raw11326step0; decide +kernel
      have hl : raw11326step1Labels = raw11326step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11326step0 raw11326step0Labels permutation34 permutation3
    mixedMoment B raw11326step1 raw11326step1Labels = mixedMoment B raw11326step2 raw11326step2Labels := by
      have ha : raw11326step2 = raw11326step1 := by apply Matrix.ext; unfold raw11326step2 raw11326step1; decide +kernel
      have hl : raw11326step1Labels = labelEmbedding6 ∘ raw11326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11326step1 raw11326step1Labels raw11326step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical11327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11327 raw11327Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw11327 raw11327Labels = mixedMoment B raw11327step0 raw11327step0Labels := by
      have ha : raw11327step0 = (fun i j => raw11327 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11327step0 raw11327; decide +kernel
      have hl : raw11327step0Labels = raw11327Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11327 raw11327Labels permutation202 permutation3
    mixedMoment B raw11327step0 raw11327step0Labels = mixedMoment B raw11327step1 raw11327step1Labels := by
      have ha : raw11327step1 = raw11327step0 := by apply Matrix.ext; unfold raw11327step1 raw11327step0; decide +kernel
      have hl : raw11327step0Labels = labelEmbedding6 ∘ raw11327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11327step0 raw11327step0Labels raw11327step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical11328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11328 raw11328Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw11328 raw11328Labels = mixedMoment B raw11328step0 raw11328step0Labels := by
      have hz : ∀ j, raw11328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11328step0 = (fun i j => raw11328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11328step0 raw11328; decide +kernel
      have hl : raw11328step0Labels = raw11328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11328 raw11328Labels permutation434 hz
    mixedMoment B raw11328step0 raw11328step0Labels = mixedMoment B raw11328step1 raw11328step1Labels := by
      have ha : raw11328step1 = (fun i j => raw11328step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11328step1 raw11328step0; decide +kernel
      have hl : raw11328step1Labels = raw11328step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11328step0 raw11328step0Labels permutation45 permutation5
    mixedMoment B raw11328step1 raw11328step1Labels = mixedMoment B raw11328step2 raw11328step2Labels := by
      have ha : raw11328step2 = -raw11328step1 := by apply Matrix.ext; change ∀ i j, raw11328step2 i j = -(raw11328step1 i j); unfold raw11328step2 raw11328step1; decide +kernel
      have hl : raw11328step2Labels = raw11328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11328step2 raw11328step2Labels = mixedMoment B raw11328step3 raw11328step3Labels := by
      have ha : raw11328step3 = raw11328step2 := by apply Matrix.ext; unfold raw11328step3 raw11328step2; decide +kernel
      have hl : raw11328step2Labels = labelEmbedding8 ∘ raw11328step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11328step2 raw11328step2Labels raw11328step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical11329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11329 raw11329Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11329 raw11329Labels = mixedMoment B raw11329step0 raw11329step0Labels := by
      have hz : ∀ j, raw11329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11329step0 = (fun i j => raw11329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11329step0 raw11329; decide +kernel
      have hl : raw11329step0Labels = raw11329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11329 raw11329Labels permutation434 hz
    mixedMoment B raw11329step0 raw11329step0Labels = mixedMoment B raw11329step1 raw11329step1Labels := by
      have ha : raw11329step1 = (fun i j => raw11329step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11329step1 raw11329step0; decide +kernel
      have hl : raw11329step1Labels = raw11329step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11329step0 raw11329step0Labels permutation48 permutation5
    mixedMoment B raw11329step1 raw11329step1Labels = mixedMoment B raw11329step2 raw11329step2Labels := by
      have ha : raw11329step2 = -raw11329step1 := by apply Matrix.ext; change ∀ i j, raw11329step2 i j = -(raw11329step1 i j); unfold raw11329step2 raw11329step1; decide +kernel
      have hl : raw11329step2Labels = raw11329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11329step2 raw11329step2Labels = mixedMoment B raw11329step3 raw11329step3Labels := by
      have ha : raw11329step3 = raw11329step2 := by apply Matrix.ext; unfold raw11329step3 raw11329step2; decide +kernel
      have hl : raw11329step2Labels = labelEmbedding8 ∘ raw11329step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11329step2 raw11329step2Labels raw11329step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11330 raw11330Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw11330 raw11330Labels = mixedMoment B raw11330step0 raw11330step0Labels := by
      have ha : raw11330step0 = (fun i j => raw11330 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11330step0 raw11330; decide +kernel
      have hl : raw11330step0Labels = raw11330Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11330 raw11330Labels permutation154 permutation3
    mixedMoment B raw11330step0 raw11330step0Labels = mixedMoment B raw11330step1 raw11330step1Labels := by
      have ha : raw11330step1 = raw11330step0 := by apply Matrix.ext; unfold raw11330step1 raw11330step0; decide +kernel
      have hl : raw11330step0Labels = labelEmbedding6 ∘ raw11330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11330step0 raw11330step0Labels raw11330step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical11331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11331 raw11331Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11331 raw11331Labels = mixedMoment B raw11331step0 raw11331step0Labels := by
      have ha : raw11331step0 = (fun i j => raw11331 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11331step0 raw11331; decide +kernel
      have hl : raw11331step0Labels = raw11331Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11331 raw11331Labels permutation154 permutation3
    mixedMoment B raw11331step0 raw11331step0Labels = mixedMoment B raw11331step1 raw11331step1Labels := by
      have ha : raw11331step1 = raw11331step0 := by apply Matrix.ext; unfold raw11331step1 raw11331step0; decide +kernel
      have hl : raw11331step0Labels = labelEmbedding6 ∘ raw11331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11331step0 raw11331step0Labels raw11331step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical11332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11332 raw11332Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11332 raw11332Labels = mixedMoment B raw11332step0 raw11332step0Labels := by
      have ha : raw11332step0 = (fun i j => raw11332 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11332step0 raw11332; decide +kernel
      have hl : raw11332step0Labels = raw11332Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11332 raw11332Labels permutation178 permutation3
    mixedMoment B raw11332step0 raw11332step0Labels = mixedMoment B raw11332step1 raw11332step1Labels := by
      have ha : raw11332step1 = raw11332step0 := by apply Matrix.ext; unfold raw11332step1 raw11332step0; decide +kernel
      have hl : raw11332step0Labels = labelEmbedding6 ∘ raw11332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11332step0 raw11332step0Labels raw11332step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical11333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11333 raw11333Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw11333 raw11333Labels = mixedMoment B raw11333step0 raw11333step0Labels := by
      have ha : raw11333step0 = (fun i j => raw11333 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11333step0 raw11333; decide +kernel
      have hl : raw11333step0Labels = raw11333Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11333 raw11333Labels permutation224 permutation5
    mixedMoment B raw11333step0 raw11333step0Labels = mixedMoment B raw11333step1 raw11333step1Labels := by
      have ha : raw11333step1 = -raw11333step0 := by apply Matrix.ext; change ∀ i j, raw11333step1 i j = -(raw11333step0 i j); unfold raw11333step1 raw11333step0; decide +kernel
      have hl : raw11333step1Labels = raw11333step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11333step1 raw11333step1Labels = mixedMoment B raw11333step2 raw11333step2Labels := by
      have ha : raw11333step2 = raw11333step1 := by apply Matrix.ext; unfold raw11333step2 raw11333step1; decide +kernel
      have hl : raw11333step1Labels = labelEmbedding8 ∘ raw11333step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11333step1 raw11333step1Labels raw11333step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical11334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11334 raw11334Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw11334 raw11334Labels = mixedMoment B raw11334step0 raw11334step0Labels := by
      have ha : raw11334step0 = (fun i j => raw11334 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11334step0 raw11334; decide +kernel
      have hl : raw11334step0Labels = raw11334Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11334 raw11334Labels permutation155 permutation3
    mixedMoment B raw11334step0 raw11334step0Labels = mixedMoment B raw11334step1 raw11334step1Labels := by
      have ha : raw11334step1 = raw11334step0 := by apply Matrix.ext; unfold raw11334step1 raw11334step0; decide +kernel
      have hl : raw11334step0Labels = labelEmbedding6 ∘ raw11334step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11334step0 raw11334step0Labels raw11334step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical11335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11335 raw11335Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw11335 raw11335Labels = mixedMoment B raw11335step0 raw11335step0Labels := by
      have hz : ∀ j, raw11335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11335step0 = (fun i j => raw11335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11335step0 raw11335; decide +kernel
      have hl : raw11335step0Labels = raw11335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11335 raw11335Labels permutation434 hz
    mixedMoment B raw11335step0 raw11335step0Labels = mixedMoment B raw11335step1 raw11335step1Labels := by
      have ha : raw11335step1 = (fun i j => raw11335step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11335step1 raw11335step0; decide +kernel
      have hl : raw11335step1Labels = raw11335step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11335step0 raw11335step0Labels permutation32 permutation3
    mixedMoment B raw11335step1 raw11335step1Labels = mixedMoment B raw11335step2 raw11335step2Labels := by
      have ha : raw11335step2 = raw11335step1 := by apply Matrix.ext; unfold raw11335step2 raw11335step1; decide +kernel
      have hl : raw11335step1Labels = labelEmbedding6 ∘ raw11335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11335step1 raw11335step1Labels raw11335step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical11336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11336 raw11336Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11336 raw11336Labels = mixedMoment B raw11336step0 raw11336step0Labels := by
      have hz : ∀ j, raw11336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11336step0 = (fun i j => raw11336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11336step0 raw11336; decide +kernel
      have hl : raw11336step0Labels = raw11336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11336 raw11336Labels permutation434 hz
    mixedMoment B raw11336step0 raw11336step0Labels = mixedMoment B raw11336step1 raw11336step1Labels := by
      have ha : raw11336step1 = (fun i j => raw11336step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11336step1 raw11336step0; decide +kernel
      have hl : raw11336step1Labels = raw11336step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11336step0 raw11336step0Labels permutation32 permutation3
    mixedMoment B raw11336step1 raw11336step1Labels = mixedMoment B raw11336step2 raw11336step2Labels := by
      have ha : raw11336step2 = raw11336step1 := by apply Matrix.ext; unfold raw11336step2 raw11336step1; decide +kernel
      have hl : raw11336step1Labels = labelEmbedding6 ∘ raw11336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11336step1 raw11336step1Labels raw11336step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical11337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11337 raw11337Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11337 raw11337Labels = mixedMoment B raw11337step0 raw11337step0Labels := by
      have hz : ∀ j, raw11337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11337step0 = (fun i j => raw11337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11337step0 raw11337; decide +kernel
      have hl : raw11337step0Labels = raw11337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11337 raw11337Labels permutation434 hz
    mixedMoment B raw11337step0 raw11337step0Labels = mixedMoment B raw11337step1 raw11337step1Labels := by
      have ha : raw11337step1 = (fun i j => raw11337step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11337step1 raw11337step0; decide +kernel
      have hl : raw11337step1Labels = raw11337step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11337step0 raw11337step0Labels permutation38 permutation3
    mixedMoment B raw11337step1 raw11337step1Labels = mixedMoment B raw11337step2 raw11337step2Labels := by
      have ha : raw11337step2 = raw11337step1 := by apply Matrix.ext; unfold raw11337step2 raw11337step1; decide +kernel
      have hl : raw11337step1Labels = labelEmbedding6 ∘ raw11337step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11337step1 raw11337step1Labels raw11337step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical11338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11338 raw11338Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw11338 raw11338Labels = mixedMoment B raw11338step0 raw11338step0Labels := by
      have ha : raw11338step0 = (fun i j => raw11338 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11338step0 raw11338; decide +kernel
      have hl : raw11338step0Labels = raw11338Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11338 raw11338Labels permutation200 permutation3
    mixedMoment B raw11338step0 raw11338step0Labels = mixedMoment B raw11338step1 raw11338step1Labels := by
      have ha : raw11338step1 = raw11338step0 := by apply Matrix.ext; unfold raw11338step1 raw11338step0; decide +kernel
      have hl : raw11338step0Labels = labelEmbedding6 ∘ raw11338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11338step0 raw11338step0Labels raw11338step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

theorem canonical11339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11339 raw11339Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11339 raw11339Labels = mixedMoment B raw11339step0 raw11339step0Labels := by
      have hz : ∀ j, raw11339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11339step0 = (fun i j => raw11339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11339step0 raw11339; decide +kernel
      have hl : raw11339step0Labels = raw11339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11339 raw11339Labels permutation434 hz
    mixedMoment B raw11339step0 raw11339step0Labels = mixedMoment B raw11339step1 raw11339step1Labels := by
      have ha : raw11339step1 = (fun i j => raw11339step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11339step1 raw11339step0; decide +kernel
      have hl : raw11339step1Labels = raw11339step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11339step0 raw11339step0Labels permutation33 permutation3
    mixedMoment B raw11339step1 raw11339step1Labels = mixedMoment B raw11339step2 raw11339step2Labels := by
      have ha : raw11339step2 = raw11339step1 := by apply Matrix.ext; unfold raw11339step2 raw11339step1; decide +kernel
      have hl : raw11339step1Labels = labelEmbedding6 ∘ raw11339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11339step1 raw11339step1Labels raw11339step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11340 raw11340Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw11340 raw11340Labels = mixedMoment B raw11340step0 raw11340step0Labels := by
      have hz : ∀ j, raw11340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11340step0 = (fun i j => raw11340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11340step0 raw11340; decide +kernel
      have hl : raw11340step0Labels = raw11340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11340 raw11340Labels permutation434 hz
    mixedMoment B raw11340step0 raw11340step0Labels = mixedMoment B raw11340step1 raw11340step1Labels := by
      have ha : raw11340step1 = (fun i j => raw11340step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11340step1 raw11340step0; decide +kernel
      have hl : raw11340step1Labels = raw11340step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11340step0 raw11340step0Labels permutation32 permutation3
    mixedMoment B raw11340step1 raw11340step1Labels = mixedMoment B raw11340step2 raw11340step2Labels := by
      have ha : raw11340step2 = raw11340step1 := by apply Matrix.ext; unfold raw11340step2 raw11340step1; decide +kernel
      have hl : raw11340step1Labels = labelEmbedding6 ∘ raw11340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11340step1 raw11340step1Labels raw11340step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

theorem canonical11341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11341 raw11341Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11341 raw11341Labels = mixedMoment B raw11341step0 raw11341step0Labels := by
      have hz : ∀ j, raw11341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11341step0 = (fun i j => raw11341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11341step0 raw11341; decide +kernel
      have hl : raw11341step0Labels = raw11341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11341 raw11341Labels permutation434 hz
    mixedMoment B raw11341step0 raw11341step0Labels = mixedMoment B raw11341step1 raw11341step1Labels := by
      have ha : raw11341step1 = (fun i j => raw11341step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11341step1 raw11341step0; decide +kernel
      have hl : raw11341step1Labels = raw11341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11341step0 raw11341step0Labels permutation32 permutation3
    mixedMoment B raw11341step1 raw11341step1Labels = mixedMoment B raw11341step2 raw11341step2Labels := by
      have ha : raw11341step2 = raw11341step1 := by apply Matrix.ext; unfold raw11341step2 raw11341step1; decide +kernel
      have hl : raw11341step1Labels = labelEmbedding6 ∘ raw11341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11341step1 raw11341step1Labels raw11341step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical11342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11342 raw11342Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw11342 raw11342Labels = mixedMoment B raw11342step0 raw11342step0Labels := by
      have hz : ∀ j, raw11342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11342step0 = (fun i j => raw11342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11342step0 raw11342; decide +kernel
      have hl : raw11342step0Labels = raw11342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11342 raw11342Labels permutation434 hz
    mixedMoment B raw11342step0 raw11342step0Labels = mixedMoment B raw11342step1 raw11342step1Labels := by
      have ha : raw11342step1 = (fun i j => raw11342step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11342step1 raw11342step0; decide +kernel
      have hl : raw11342step1Labels = raw11342step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11342step0 raw11342step0Labels permutation38 permutation3
    mixedMoment B raw11342step1 raw11342step1Labels = mixedMoment B raw11342step2 raw11342step2Labels := by
      have ha : raw11342step2 = raw11342step1 := by apply Matrix.ext; unfold raw11342step2 raw11342step1; decide +kernel
      have hl : raw11342step1Labels = labelEmbedding6 ∘ raw11342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11342step1 raw11342step1Labels raw11342step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical11343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11343 raw11343Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw11343 raw11343Labels = mixedMoment B raw11343step0 raw11343step0Labels := by
      have ha : raw11343step0 = (fun i j => raw11343 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11343step0 raw11343; decide +kernel
      have hl : raw11343step0Labels = raw11343Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11343 raw11343Labels permutation200 permutation3
    mixedMoment B raw11343step0 raw11343step0Labels = mixedMoment B raw11343step1 raw11343step1Labels := by
      have ha : raw11343step1 = raw11343step0 := by apply Matrix.ext; unfold raw11343step1 raw11343step0; decide +kernel
      have hl : raw11343step0Labels = labelEmbedding6 ∘ raw11343step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11343step0 raw11343step0Labels raw11343step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

theorem canonical11344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11344 raw11344Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw11344 raw11344Labels = mixedMoment B raw11344step0 raw11344step0Labels := by
      have hz : ∀ j, raw11344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11344step0 = (fun i j => raw11344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11344step0 raw11344; decide +kernel
      have hl : raw11344step0Labels = raw11344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11344 raw11344Labels permutation434 hz
    mixedMoment B raw11344step0 raw11344step0Labels = mixedMoment B raw11344step1 raw11344step1Labels := by
      have ha : raw11344step1 = (fun i j => raw11344step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11344step1 raw11344step0; decide +kernel
      have hl : raw11344step1Labels = raw11344step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11344step0 raw11344step0Labels permutation44 permutation5
    mixedMoment B raw11344step1 raw11344step1Labels = mixedMoment B raw11344step2 raw11344step2Labels := by
      have ha : raw11344step2 = -raw11344step1 := by apply Matrix.ext; change ∀ i j, raw11344step2 i j = -(raw11344step1 i j); unfold raw11344step2 raw11344step1; decide +kernel
      have hl : raw11344step2Labels = raw11344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11344step2 raw11344step2Labels = mixedMoment B raw11344step3 raw11344step3Labels := by
      have ha : raw11344step3 = raw11344step2 := by apply Matrix.ext; unfold raw11344step3 raw11344step2; decide +kernel
      have hl : raw11344step2Labels = labelEmbedding8 ∘ raw11344step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11344step2 raw11344step2Labels raw11344step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4249 node4249Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node783 node783Labels + mixedMoment B node803 node803Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw969 singletonSmall4249
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4249) = raw969Labels := by decide +kernel
  rw [hl, canonical969 B hB] at h
  have hc0 : mixedMoment B raw969 (Fin.cases (0 : Fin 2) singletonSmall4249) =
      mixedMoment B node783 node783Labels := by
    have ha : raw969 = raw970 := by apply Matrix.ext; unfold raw969 raw970; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4249 = raw970Labels := by decide +kernel
    rw [ha, hj, canonical970 B hB]
  have hc1 : mixedMoment B raw969 (Fin.cases (1 : Fin 2) singletonSmall4249) =
      mixedMoment B node803 node803Labels := by
    have ha : raw969 = raw971 := by apply Matrix.ext; unfold raw969 raw971; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4249 = raw971Labels := by decide +kernel
    rw [ha, hj, canonical971 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4256 node4256Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node790 node790Labels + mixedMoment B node848 node848Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw984 singletonSmall4256
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4256) = raw984Labels := by decide +kernel
  rw [hl, canonical984 B hB] at h
  have hc0 : mixedMoment B raw984 (Fin.cases (0 : Fin 2) singletonSmall4256) =
      mixedMoment B node790 node790Labels := by
    have ha : raw984 = raw985 := by apply Matrix.ext; unfold raw984 raw985; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4256 = raw985Labels := by decide +kernel
    rw [ha, hj, canonical985 B hB]
  have hc1 : mixedMoment B raw984 (Fin.cases (1 : Fin 2) singletonSmall4256) =
      mixedMoment B node848 node848Labels := by
    have ha : raw984 = raw986 := by apply Matrix.ext; unfold raw984 raw986; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4256 = raw986Labels := by decide +kernel
    rw [ha, hj, canonical986 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4265 node4265Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node807 node807Labels + mixedMoment B node807 node807Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw990 singletonSmall4265
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4265) = raw990Labels := by decide +kernel
  rw [hl, canonical990 B hB] at h
  have hc0 : mixedMoment B raw990 (Fin.cases (0 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw991 := by apply Matrix.ext; unfold raw990 raw991; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4265 = raw991Labels := by decide +kernel
    rw [ha, hj, canonical991 B hB]
  have hc1 : mixedMoment B raw990 (Fin.cases (1 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw992 := by apply Matrix.ext; unfold raw990 raw992; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4265 = raw992Labels := by decide +kernel
    rw [ha, hj, canonical992 B hB]
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

theorem singleton4732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4732 node4732Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1901 node1901Labels + mixedMoment B node1941 node1941Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1650 singletonSmall4732
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4732) = raw1650Labels := by decide +kernel
  rw [hl, canonical1650 B hB] at h
  have hc0 : mixedMoment B raw1650 (Fin.cases (0 : Fin 2) singletonSmall4732) =
      mixedMoment B node1901 node1901Labels := by
    have ha : raw1650 = raw1651 := by apply Matrix.ext; unfold raw1650 raw1651; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4732 = raw1651Labels := by decide +kernel
    rw [ha, hj, canonical1651 B hB]
  have hc1 : mixedMoment B raw1650 (Fin.cases (1 : Fin 2) singletonSmall4732) =
      mixedMoment B node1941 node1941Labels := by
    have ha : raw1650 = raw1652 := by apply Matrix.ext; unfold raw1650 raw1652; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4732 = raw1652Labels := by decide +kernel
    rw [ha, hj, canonical1652 B hB]
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

theorem singleton4737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4737 node4737Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1909 node1909Labels + mixedMoment B node1909 node1909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1653 singletonSmall4737
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4737) = raw1653Labels := by decide +kernel
  rw [hl, canonical1653 B hB] at h
  have hc0 : mixedMoment B raw1653 (Fin.cases (0 : Fin 2) singletonSmall4737) =
      mixedMoment B node1909 node1909Labels := by
    have ha : raw1653 = raw1654 := by apply Matrix.ext; unfold raw1653 raw1654; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4737 = raw1654Labels := by decide +kernel
    rw [ha, hj, canonical1654 B hB]
  have hc1 : mixedMoment B raw1653 (Fin.cases (1 : Fin 2) singletonSmall4737) =
      mixedMoment B node1909 node1909Labels := by
    have ha : raw1653 = raw1655 := by apply Matrix.ext; unfold raw1653 raw1655; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4737 = raw1655Labels := by decide +kernel
    rw [ha, hj, canonical1655 B hB]
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

theorem singleton4831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4831 node4831Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2051 node2051Labels + mixedMoment B node2191 node2191Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1761 singletonSmall4831
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4831) = raw1761Labels := by decide +kernel
  rw [hl, canonical1761 B hB] at h
  have hc0 : mixedMoment B raw1761 (Fin.cases (0 : Fin 2) singletonSmall4831) =
      mixedMoment B node2051 node2051Labels := by
    have ha : raw1761 = raw1762 := by apply Matrix.ext; unfold raw1761 raw1762; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4831 = raw1762Labels := by decide +kernel
    rw [ha, hj, canonical1762 B hB]
  have hc1 : mixedMoment B raw1761 (Fin.cases (1 : Fin 2) singletonSmall4831) =
      mixedMoment B node2191 node2191Labels := by
    have ha : raw1761 = raw1763 := by apply Matrix.ext; unfold raw1761 raw1763; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4831 = raw1763Labels := by decide +kernel
    rw [ha, hj, canonical1763 B hB]
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

theorem singleton4887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4887 node4887Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2243 node2243Labels + mixedMoment B node2243 node2243Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1812 singletonSmall4887
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4887) = raw1812Labels := by decide +kernel
  rw [hl, canonical1812 B hB] at h
  have hc0 : mixedMoment B raw1812 (Fin.cases (0 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1813 := by apply Matrix.ext; unfold raw1812 raw1813; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4887 = raw1813Labels := by decide +kernel
    rw [ha, hj, canonical1813 B hB]
  have hc1 : mixedMoment B raw1812 (Fin.cases (1 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1814 := by apply Matrix.ext; unfold raw1812 raw1814; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4887 = raw1814Labels := by decide +kernel
    rw [ha, hj, canonical1814 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node783 node783Labels = Sparse.eval nodeValue783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 783) = mixedMoment B node783 node783Labels := rfl
  simpa [nodeValue783, Sparse.eval] using hc.symm

theorem sound785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node785 node785Labels = Sparse.eval nodeValue785 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 785) = mixedMoment B node785 node785Labels := rfl
  simpa [nodeValue785, Sparse.eval] using hc.symm

theorem sound790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node790 node790Labels = Sparse.eval nodeValue790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 790) = mixedMoment B node790 node790Labels := rfl
  simpa [nodeValue790, Sparse.eval] using hc.symm

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

theorem sound804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node804 node804Labels = Sparse.eval nodeValue804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 804) = mixedMoment B node804 node804Labels := rfl
  simpa [nodeValue804, Sparse.eval] using hc.symm

theorem sound807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node807 node807Labels = Sparse.eval nodeValue807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 807) = mixedMoment B node807 node807Labels := rfl
  simpa [nodeValue807, Sparse.eval] using hc.symm

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

theorem sound848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node848 node848Labels = Sparse.eval nodeValue848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 848) = mixedMoment B node848 node848Labels := rfl
  simpa [nodeValue848, Sparse.eval] using hc.symm

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

theorem sound1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1897 node1897Labels = Sparse.eval nodeValue1897 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1897) = mixedMoment B node1897 node1897Labels := rfl
  simpa [nodeValue1897, Sparse.eval] using hc.symm

theorem sound1901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1901 node1901Labels = Sparse.eval nodeValue1901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1901) = mixedMoment B node1901 node1901Labels := rfl
  simpa [nodeValue1901, Sparse.eval] using hc.symm

theorem sound1907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1907 node1907Labels = Sparse.eval nodeValue1907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1907) = mixedMoment B node1907 node1907Labels := rfl
  simpa [nodeValue1907, Sparse.eval] using hc.symm

theorem sound1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1909 node1909Labels = Sparse.eval nodeValue1909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1909) = mixedMoment B node1909 node1909Labels := rfl
  simpa [nodeValue1909, Sparse.eval] using hc.symm

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

theorem sound1941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1941 node1941Labels = Sparse.eval nodeValue1941 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1941) = mixedMoment B node1941 node1941Labels := rfl
  simpa [nodeValue1941, Sparse.eval] using hc.symm

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

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

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

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4249 node4249Labels = Sparse.eval nodeValue4249 (mixedVector B) := by
  have h := singleton4249 B _hB
  rw [sound783 B _hB _hF, sound803 B _hB _hF] at h
  norm_num [nodeValue4249, nodeValue783, nodeValue803, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4251 node4251Labels = Sparse.eval nodeValue4251 (mixedVector B) := by
  have h := singleton4251 B _hB
  rw [sound785 B _hB _hF, sound804 B _hB _hF] at h
  norm_num [nodeValue4251, nodeValue785, nodeValue804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4256 node4256Labels = Sparse.eval nodeValue4256 (mixedVector B) := by
  have h := singleton4256 B _hB
  rw [sound790 B _hB _hF, sound848 B _hB _hF] at h
  norm_num [nodeValue4256, nodeValue790, nodeValue848, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4265 node4265Labels = Sparse.eval nodeValue4265 (mixedVector B) := by
  have h := singleton4265 B _hB
  rw [sound807 B _hB _hF] at h
  norm_num [nodeValue4265, nodeValue807, Sparse.eval] at h ⊢
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

theorem sound4728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4728 node4728Labels = Sparse.eval nodeValue4728 (mixedVector B) := by
  have h := singleton4728 B _hB
  rw [sound1897 B _hB _hF, sound1907 B _hB _hF] at h
  norm_num [nodeValue4728, nodeValue1897, nodeValue1907, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4732 node4732Labels = Sparse.eval nodeValue4732 (mixedVector B) := by
  have h := singleton4732 B _hB
  rw [sound1901 B _hB _hF, sound1941 B _hB _hF] at h
  norm_num [nodeValue4732, nodeValue1901, nodeValue1941, Sparse.eval] at h ⊢
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

theorem sound4737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4737 node4737Labels = Sparse.eval nodeValue4737 (mixedVector B) := by
  have h := singleton4737 B _hB
  rw [sound1909 B _hB _hF] at h
  norm_num [nodeValue4737, nodeValue1909, Sparse.eval] at h ⊢
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

theorem sound4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4831 node4831Labels = Sparse.eval nodeValue4831 (mixedVector B) := by
  have h := singleton4831 B _hB
  rw [sound2051 B _hB _hF, sound2191 B _hB _hF] at h
  norm_num [nodeValue4831, nodeValue2051, nodeValue2191, Sparse.eval] at h ⊢
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

theorem sound4887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4887 node4887Labels = Sparse.eval nodeValue4887 (mixedVector B) := by
  have h := singleton4887 B _hB
  rw [sound2243 B _hB _hF] at h
  norm_num [nodeValue4887, nodeValue2243, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources20
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm669 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA669 + difference 0 1) (sourceB669 + difference 1 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA669 + difference 0 1) (sourceB669 + difference 1 0) sourceC669) = raw11315 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11315; decide +kernel
    rw [ha]
    exact (canonical11315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA669 + difference 0 2) (sourceB669 + difference 2 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA669 + difference 0 2) (sourceB669 + difference 2 0) sourceC669) = raw11316 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11316; decide +kernel
    rw [ha]
    exact (canonical11316 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA669 + difference 0 3) (sourceB669 + difference 3 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA669 + difference 0 3) (sourceB669 + difference 3 0) sourceC669) = raw11317 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11317; decide +kernel
    rw [ha]
    exact (canonical11317 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA669 + difference 0 4) (sourceB669 + difference 4 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA669 + difference 0 4) (sourceB669 + difference 4 0) sourceC669) = raw11318 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11318; decide +kernel
    rw [ha]
    exact (canonical11318 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA669 + difference 0 5) (sourceB669 + difference 5 0) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA669 + difference 0 5) (sourceB669 + difference 5 0) sourceC669) = raw11319 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11319; decide +kernel
    rw [ha]
    exact (canonical11319 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA669 + difference 1 0) (sourceB669 + difference 0 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA669 + difference 1 0) (sourceB669 + difference 0 1) sourceC669) = raw11320 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11320; decide +kernel
    rw [ha]
    exact (canonical11320 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA669 + difference 1 2) (sourceB669 + difference 2 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA669 + difference 1 2) (sourceB669 + difference 2 1) sourceC669) = raw11321 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11321; decide +kernel
    rw [ha]
    exact (canonical11321 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA669 + difference 1 3) (sourceB669 + difference 3 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA669 + difference 1 3) (sourceB669 + difference 3 1) sourceC669) = raw11322 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11322; decide +kernel
    rw [ha]
    exact (canonical11322 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA669 + difference 1 4) (sourceB669 + difference 4 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA669 + difference 1 4) (sourceB669 + difference 4 1) sourceC669) = raw11323 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11323; decide +kernel
    rw [ha]
    exact (canonical11323 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA669 + difference 1 5) (sourceB669 + difference 5 1) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA669 + difference 1 5) (sourceB669 + difference 5 1) sourceC669) = raw11324 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11324; decide +kernel
    rw [ha]
    exact (canonical11324 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA669 + difference 2 0) (sourceB669 + difference 0 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA669 + difference 2 0) (sourceB669 + difference 0 2) sourceC669) = raw11325 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11325; decide +kernel
    rw [ha]
    exact (canonical11325 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA669 + difference 2 1) (sourceB669 + difference 1 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA669 + difference 2 1) (sourceB669 + difference 1 2) sourceC669) = raw11326 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11326; decide +kernel
    rw [ha]
    exact (canonical11326 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA669 + difference 2 3) (sourceB669 + difference 3 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA669 + difference 2 3) (sourceB669 + difference 3 2) sourceC669) = raw11327 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11327; decide +kernel
    rw [ha]
    exact (canonical11327 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA669 + difference 2 4) (sourceB669 + difference 4 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA669 + difference 2 4) (sourceB669 + difference 4 2) sourceC669) = raw11328 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11328; decide +kernel
    rw [ha]
    exact (canonical11328 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA669 + difference 2 5) (sourceB669 + difference 5 2) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA669 + difference 2 5) (sourceB669 + difference 5 2) sourceC669) = raw11329 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11329; decide +kernel
    rw [ha]
    exact (canonical11329 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA669 + difference 3 0) (sourceB669 + difference 0 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA669 + difference 3 0) (sourceB669 + difference 0 3) sourceC669) = raw11330 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11330; decide +kernel
    rw [ha]
    exact (canonical11330 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA669 + difference 3 1) (sourceB669 + difference 1 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA669 + difference 3 1) (sourceB669 + difference 1 3) sourceC669) = raw11331 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11331; decide +kernel
    rw [ha]
    exact (canonical11331 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA669 + difference 3 2) (sourceB669 + difference 2 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA669 + difference 3 2) (sourceB669 + difference 2 3) sourceC669) = raw11332 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11332; decide +kernel
    rw [ha]
    exact (canonical11332 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA669 + difference 3 4) (sourceB669 + difference 4 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA669 + difference 3 4) (sourceB669 + difference 4 3) sourceC669) = raw11333 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11333; decide +kernel
    rw [ha]
    exact (canonical11333 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA669 + difference 3 5) (sourceB669 + difference 5 3) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA669 + difference 3 5) (sourceB669 + difference 5 3) sourceC669) = raw11334 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11334; decide +kernel
    rw [ha]
    exact (canonical11334 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA669 + difference 4 0) (sourceB669 + difference 0 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA669 + difference 4 0) (sourceB669 + difference 0 4) sourceC669) = raw11335 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11335; decide +kernel
    rw [ha]
    exact (canonical11335 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA669 + difference 4 1) (sourceB669 + difference 1 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA669 + difference 4 1) (sourceB669 + difference 1 4) sourceC669) = raw11336 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11336; decide +kernel
    rw [ha]
    exact (canonical11336 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA669 + difference 4 2) (sourceB669 + difference 2 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA669 + difference 4 2) (sourceB669 + difference 2 4) sourceC669) = raw11337 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11337; decide +kernel
    rw [ha]
    exact (canonical11337 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA669 + difference 4 3) (sourceB669 + difference 3 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA669 + difference 4 3) (sourceB669 + difference 3 4) sourceC669) = raw11338 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11338; decide +kernel
    rw [ha]
    exact (canonical11338 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA669 + difference 4 5) (sourceB669 + difference 5 4) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA669 + difference 4 5) (sourceB669 + difference 5 4) sourceC669) = raw11339 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11339; decide +kernel
    rw [ha]
    exact (canonical11339 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA669 + difference 5 0) (sourceB669 + difference 0 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA669 + difference 5 0) (sourceB669 + difference 0 5) sourceC669) = raw11340 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11340; decide +kernel
    rw [ha]
    exact (canonical11340 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA669 + difference 5 1) (sourceB669 + difference 1 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA669 + difference 5 1) (sourceB669 + difference 1 5) sourceC669) = raw11341 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11341; decide +kernel
    rw [ha]
    exact (canonical11341 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA669 + difference 5 2) (sourceB669 + difference 2 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA669 + difference 5 2) (sourceB669 + difference 2 5) sourceC669) = raw11342 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11342; decide +kernel
    rw [ha]
    exact (canonical11342 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA669 + difference 5 3) (sourceB669 + difference 3 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA669 + difference 5 3) (sourceB669 + difference 3 5) sourceC669) = raw11343 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11343; decide +kernel
    rw [ha]
    exact (canonical11343 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA669 + difference 5 4) (sourceB669 + difference 4 5) sourceC669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA669 + difference 5 4) (sourceB669 + difference 4 5) sourceC669) = raw11344 := by
      apply Matrix.ext; unfold tripleCharges sourceA669 sourceB669 sourceC669 difference raw11344; decide +kernel
    rw [ha]
    exact (canonical11344 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA669 sourceB669 sourceC669
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm669, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck578 : Integer.Sparse.reindex keyMap MixedData.row578 = numericRow578 := by decide +kernel

theorem numericCheck578 (x : Master → ℝ) : Integer.Sparse.eval numericRow578 x =
    (17280 : ℝ) * reducedSource578 x := by
  norm_num [numericRow578, reducedSource578, Integer.Sparse.eval, Sparse.eval, nodeValue4249, nodeValue4251, nodeValue4256, nodeValue4265, nodeValue4728, nodeValue4732, nodeValue4737, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4831, nodeValue4832, nodeValue4835, nodeValue4887, nodeValue4888, nodeValue5405, nodeValue5434, nodeValue5439, nodeValue5452] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero578 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource578 (mixedVector B) = 0 := by
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4251 : mixedVector B (Sum.inr 4251) = Sparse.eval nodeValue4251 (mixedVector B) := by
    change mixedMoment B node4251 node4251Labels = _
    exact sound4251 B hB hF
  have h4256 : mixedVector B (Sum.inr 4256) = Sparse.eval nodeValue4256 (mixedVector B) := by
    change mixedMoment B node4256 node4256Labels = _
    exact sound4256 B hB hF
  have h4265 : mixedVector B (Sum.inr 4265) = Sparse.eval nodeValue4265 (mixedVector B) := by
    change mixedMoment B node4265 node4265Labels = _
    exact sound4265 B hB hF
  have h4728 : mixedVector B (Sum.inr 4728) = Sparse.eval nodeValue4728 (mixedVector B) := by
    change mixedMoment B node4728 node4728Labels = _
    exact sound4728 B hB hF
  have h4732 : mixedVector B (Sum.inr 4732) = Sparse.eval nodeValue4732 (mixedVector B) := by
    change mixedMoment B node4732 node4732Labels = _
    exact sound4732 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452_e B hB hF
  simpa only [sourceForm669, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4249, h4251, h4256, h4265, h4728, h4732, h4737, h4802, h4804, h4811, h4831, h4832, h4835, h4887, h4888, h5405, h5434, h5439, h5452, reducedSource578] using sourceEq669 B hB

theorem rowSound578_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row578 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck578, numericCheck578, reducedZero578 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e_oai
