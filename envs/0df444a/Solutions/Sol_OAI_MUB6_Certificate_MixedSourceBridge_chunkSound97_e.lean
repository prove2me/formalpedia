-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:42:18.205795+00:00
-- url     : https://prove2.me/submissions/0c317269-f908-4039-a014-dfcb5a8596ff

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1299_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1441_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1559_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1560_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1562_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1567_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

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

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

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

theorem canonical1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1422 raw1422Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw1422 raw1422Labels = mixedMoment B raw1422step0 raw1422step0Labels := by
      have ha : raw1422step0 = (fun i j => raw1422 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1422step0 raw1422; decide +kernel
      have hl : raw1422step0Labels = raw1422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1422 raw1422Labels permutation152 permutation4
    mixedMoment B raw1422step0 raw1422step0Labels = mixedMoment B raw1422step1 raw1422step1Labels := by
      have ha : raw1422step1 = raw1422step0 := by apply Matrix.ext; unfold raw1422step1 raw1422step0; decide +kernel
      have hl : raw1422step0Labels = labelEmbedding7 ∘ raw1422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1422step0 raw1422step0Labels raw1422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1423 raw1423Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw1423 raw1423Labels = mixedMoment B raw1423step0 raw1423step0Labels := by
      have ha : raw1423step0 = (fun i j => raw1423 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1423step0 raw1423; decide +kernel
      have hl : raw1423step0Labels = raw1423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1423 raw1423Labels permutation152 permutation4
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1424 raw1424Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw1424 raw1424Labels = mixedMoment B raw1424step0 raw1424step0Labels := by
      have ha : raw1424step0 = (fun i j => raw1424 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1424step0 raw1424; decide +kernel
      have hl : raw1424step0Labels = raw1424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1424 raw1424Labels permutation152 permutation6
    mixedMoment B raw1424step0 raw1424step0Labels = mixedMoment B raw1424step1 raw1424step1Labels := by
      have ha : raw1424step1 = -raw1424step0 := by apply Matrix.ext; change ∀ i j, raw1424step1 i j = -(raw1424step0 i j); unfold raw1424step1 raw1424step0; decide +kernel
      have hl : raw1424step1Labels = raw1424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1424step1 raw1424step1Labels = mixedMoment B raw1424step2 raw1424step2Labels := by
      have ha : raw1424step2 = raw1424step1 := by apply Matrix.ext; unfold raw1424step2 raw1424step1; decide +kernel
      have hl : raw1424step1Labels = labelEmbedding1 ∘ raw1424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1424step1 raw1424step1Labels raw1424step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical1431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1431 raw1431Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw1431 raw1431Labels = mixedMoment B raw1431step0 raw1431step0Labels := by
      have ha : raw1431step0 = (fun i j => raw1431 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1431step0 raw1431; decide +kernel
      have hl : raw1431step0Labels = raw1431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1431 raw1431Labels permutation32 permutation4
    mixedMoment B raw1431step0 raw1431step0Labels = mixedMoment B raw1431step1 raw1431step1Labels := by
      have ha : raw1431step1 = raw1431step0 := by apply Matrix.ext; unfold raw1431step1 raw1431step0; decide +kernel
      have hl : raw1431step0Labels = labelEmbedding7 ∘ raw1431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1431step0 raw1431step0Labels raw1431step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical1432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1432 raw1432Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw1432 raw1432Labels = mixedMoment B raw1432step0 raw1432step0Labels := by
      have ha : raw1432step0 = (fun i j => raw1432 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1432step0 raw1432; decide +kernel
      have hl : raw1432step0Labels = raw1432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1432 raw1432Labels permutation32 permutation4
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1433 raw1433Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw1433 raw1433Labels = mixedMoment B raw1433step0 raw1433step0Labels := by
      have ha : raw1433step0 = (fun i j => raw1433 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1433step0 raw1433; decide +kernel
      have hl : raw1433step0Labels = raw1433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1433 raw1433Labels permutation32 permutation6
    mixedMoment B raw1433step0 raw1433step0Labels = mixedMoment B raw1433step1 raw1433step1Labels := by
      have ha : raw1433step1 = -raw1433step0 := by apply Matrix.ext; change ∀ i j, raw1433step1 i j = -(raw1433step0 i j); unfold raw1433step1 raw1433step0; decide +kernel
      have hl : raw1433step1Labels = raw1433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1433step1 raw1433step1Labels = mixedMoment B raw1433step2 raw1433step2Labels := by
      have ha : raw1433step2 = raw1433step1 := by apply Matrix.ext; unfold raw1433step2 raw1433step1; decide +kernel
      have hl : raw1433step1Labels = labelEmbedding1 ∘ raw1433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1433step1 raw1433step1Labels raw1433step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

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

theorem canonical2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2187 raw2187Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw2187 raw2187Labels = mixedMoment B raw2187step0 raw2187step0Labels := by
      have ha : raw2187step0 = (fun i j => raw2187 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2187step0 raw2187; decide +kernel
      have hl : raw2187step0Labels = raw2187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2187 raw2187Labels permutation152 permutation4
    mixedMoment B raw2187step0 raw2187step0Labels = mixedMoment B raw2187step1 raw2187step1Labels := by
      have ha : raw2187step1 = raw2187step0 := by apply Matrix.ext; unfold raw2187step1 raw2187step0; decide +kernel
      have hl : raw2187step0Labels = labelEmbedding7 ∘ raw2187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2187step0 raw2187step0Labels raw2187step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

theorem canonical2188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2188 raw2188Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw2188 raw2188Labels = mixedMoment B raw2188step0 raw2188step0Labels := by
      have ha : raw2188step0 = (fun i j => raw2188 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2188step0 raw2188; decide +kernel
      have hl : raw2188step0Labels = raw2188Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2188 raw2188Labels permutation152 permutation4
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2189 raw2189Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw2189 raw2189Labels = mixedMoment B raw2189step0 raw2189step0Labels := by
      have ha : raw2189step0 = (fun i j => raw2189 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2189step0 raw2189; decide +kernel
      have hl : raw2189step0Labels = raw2189Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2189 raw2189Labels permutation176 permutation6
    mixedMoment B raw2189step0 raw2189step0Labels = mixedMoment B raw2189step1 raw2189step1Labels := by
      have ha : raw2189step1 = -raw2189step0 := by apply Matrix.ext; change ∀ i j, raw2189step1 i j = -(raw2189step0 i j); unfold raw2189step1 raw2189step0; decide +kernel
      have hl : raw2189step1Labels = raw2189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2189step1 raw2189step1Labels = mixedMoment B raw2189step2 raw2189step2Labels := by
      have ha : raw2189step2 = raw2189step1 := by apply Matrix.ext; unfold raw2189step2 raw2189step1; decide +kernel
      have hl : raw2189step1Labels = labelEmbedding1 ∘ raw2189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2189step1 raw2189step1Labels raw2189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical205
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26366 raw26366Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw26366 raw26366Labels = mixedMoment B raw26366step0 raw26366step0Labels := by
      have hz : ∀ j, raw26366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26366step0 = (fun i j => raw26366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26366step0 raw26366; decide +kernel
      have hl : raw26366step0Labels = raw26366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26366 raw26366Labels permutation265 hz
    mixedMoment B raw26366step0 raw26366step0Labels = mixedMoment B raw26366step1 raw26366step1Labels := by
      have ha : raw26366step1 = (fun i j => raw26366step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26366step1 raw26366step0; decide +kernel
      have hl : raw26366step1Labels = raw26366step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26366step0 raw26366step0Labels permutation145 permutation4
    _ = mixedMoment B node3072 node3072Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical206
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26369 raw26369Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw26369 raw26369Labels = mixedMoment B raw26369step0 raw26369step0Labels := by
      have hz : ∀ j, raw26369 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26369step0 = (fun i j => raw26369 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26369step0 raw26369; decide +kernel
      have hl : raw26369step0Labels = raw26369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26369 raw26369Labels permutation265 hz
    mixedMoment B raw26369step0 raw26369step0Labels = mixedMoment B raw26369step1 raw26369step1Labels := by
      have ha : raw26369step1 = (fun i j => raw26369step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26369step1 raw26369step0; decide +kernel
      have hl : raw26369step1Labels = raw26369step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26369step0 raw26369step0Labels permutation50 permutation2
    mixedMoment B raw26369step1 raw26369step1Labels = mixedMoment B raw26369step2 raw26369step2Labels := by
      have ha : raw26369step2 = -raw26369step1 := by apply Matrix.ext; change ∀ i j, raw26369step2 i j = -(raw26369step1 i j); unfold raw26369step2 raw26369step1; decide +kernel
      have hl : raw26369step2Labels = raw26369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3304 node3304Labels := by rfl

theorem canonical26370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26370 raw26370Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26370 raw26370Labels = mixedMoment B raw26370step0 raw26370step0Labels := by
      have hz : ∀ j, raw26370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26370step0 = (fun i j => raw26370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26370step0 raw26370; decide +kernel
      have hl : raw26370step0Labels = raw26370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26370 raw26370Labels permutation265 hz
    mixedMoment B raw26370step0 raw26370step0Labels = mixedMoment B raw26370step1 raw26370step1Labels := by
      have ha : raw26370step1 = -raw26370step0 := by apply Matrix.ext; change ∀ i j, raw26370step1 i j = -(raw26370step0 i j); unfold raw26370step1 raw26370step0; decide +kernel
      have hl : raw26370step1Labels = raw26370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical26374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26374 raw26374Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26374 raw26374Labels = mixedMoment B raw26374step0 raw26374step0Labels := by
      have hz : ∀ j, raw26374 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26374step0 = (fun i j => raw26374 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26374step0 raw26374; decide +kernel
      have hl : raw26374step0Labels = raw26374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26374 raw26374Labels permutation265 hz
    mixedMoment B raw26374step0 raw26374step0Labels = mixedMoment B raw26374step1 raw26374step1Labels := by
      have ha : raw26374step1 = (fun i j => raw26374step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26374step1 raw26374step0; decide +kernel
      have hl : raw26374step1Labels = raw26374step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26374step0 raw26374step0Labels permutation32 permutation4
    mixedMoment B raw26374step1 raw26374step1Labels = mixedMoment B raw26374step2 raw26374step2Labels := by
      have ha : raw26374step2 = -raw26374step1 := by apply Matrix.ext; change ∀ i j, raw26374step2 i j = -(raw26374step1 i j); unfold raw26374step2 raw26374step1; decide +kernel
      have hl : raw26374step2Labels = raw26374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical26379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26379 raw26379Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26379 raw26379Labels = mixedMoment B raw26379step0 raw26379step0Labels := by
      have ha : raw26379step0 = (fun i j => raw26379 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26379step0 raw26379; decide +kernel
      have hl : raw26379step0Labels = raw26379Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26379 raw26379Labels permutation173 permutation2
    mixedMoment B raw26379step0 raw26379step0Labels = mixedMoment B raw26379step1 raw26379step1Labels := by
      have ha : raw26379step1 = -raw26379step0 := by apply Matrix.ext; change ∀ i j, raw26379step1 i j = -(raw26379step0 i j); unfold raw26379step1 raw26379step0; decide +kernel
      have hl : raw26379step1Labels = raw26379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

theorem canonical26416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26416 raw26416Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw26416 raw26416Labels = mixedMoment B raw26416step0 raw26416step0Labels := by
      have ha : raw26416step0 = (fun i j => raw26416 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26416step0 raw26416; decide +kernel
      have hl : raw26416step0Labels = raw26416Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26416 raw26416Labels permutation246 permutation2
    mixedMoment B raw26416step0 raw26416step0Labels = mixedMoment B raw26416step1 raw26416step1Labels := by
      have ha : raw26416step1 = -raw26416step0 := by apply Matrix.ext; change ∀ i j, raw26416step1 i j = -(raw26416step0 i j); unfold raw26416step1 raw26416step0; decide +kernel
      have hl : raw26416step1Labels = raw26416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1644 node1644Labels := by rfl

theorem canonical26417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26417 raw26417Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26417 raw26417Labels = mixedMoment B raw26417step0 raw26417step0Labels := by
      have ha : raw26417step0 = (fun i j => raw26417 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26417step0 raw26417; decide +kernel
      have hl : raw26417step0Labels = raw26417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26417 raw26417Labels permutation160 permutation4
    mixedMoment B raw26417step0 raw26417step0Labels = mixedMoment B raw26417step1 raw26417step1Labels := by
      have ha : raw26417step1 = -raw26417step0 := by apply Matrix.ext; change ∀ i j, raw26417step1 i j = -(raw26417step0 i j); unfold raw26417step1 raw26417step0; decide +kernel
      have hl : raw26417step1Labels = raw26417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26419 raw26419Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26419 raw26419Labels = mixedMoment B raw26419step0 raw26419step0Labels := by
      have ha : raw26419step0 = (fun i j => raw26419 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26419step0 raw26419; decide +kernel
      have hl : raw26419step0Labels = raw26419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26419 raw26419Labels permutation152 permutation4
    mixedMoment B raw26419step0 raw26419step0Labels = mixedMoment B raw26419step1 raw26419step1Labels := by
      have ha : raw26419step1 = -raw26419step0 := by apply Matrix.ext; change ∀ i j, raw26419step1 i j = -(raw26419step0 i j); unfold raw26419step1 raw26419step0; decide +kernel
      have hl : raw26419step1Labels = raw26419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26433 raw26433Labels = mixedMoment B node1638 node1638Labels := by
  calc
    mixedMoment B raw26433 raw26433Labels = mixedMoment B raw26433step0 raw26433step0Labels := by
      have ha : raw26433step0 = (fun i j => raw26433 (permutation263 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26433step0 raw26433; decide +kernel
      have hl : raw26433step0Labels = raw26433Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26433 raw26433Labels permutation263 permutation2
    mixedMoment B raw26433step0 raw26433step0Labels = mixedMoment B raw26433step1 raw26433step1Labels := by
      have ha : raw26433step1 = -raw26433step0 := by apply Matrix.ext; change ∀ i j, raw26433step1 i j = -(raw26433step0 i j); unfold raw26433step1 raw26433step0; decide +kernel
      have hl : raw26433step1Labels = raw26433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1638 node1638Labels := by rfl

theorem canonical26434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26434 raw26434Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw26434 raw26434Labels = mixedMoment B raw26434step0 raw26434step0Labels := by
      have ha : raw26434step0 = (fun i j => raw26434 (permutation261 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26434step0 raw26434; decide +kernel
      have hl : raw26434step0Labels = raw26434Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26434 raw26434Labels permutation261 permutation2
    mixedMoment B raw26434step0 raw26434step0Labels = mixedMoment B raw26434step1 raw26434step1Labels := by
      have ha : raw26434step1 = -raw26434step0 := by apply Matrix.ext; change ∀ i j, raw26434step1 i j = -(raw26434step0 i j); unfold raw26434step1 raw26434step0; decide +kernel
      have hl : raw26434step1Labels = raw26434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1636 node1636Labels := by rfl

theorem canonical26435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26435 raw26435Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw26435 raw26435Labels = mixedMoment B raw26435step0 raw26435step0Labels := by
      have ha : raw26435step0 = (fun i j => raw26435 (permutation260 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26435step0 raw26435; decide +kernel
      have hl : raw26435step0Labels = raw26435Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26435 raw26435Labels permutation260 permutation2
    mixedMoment B raw26435step0 raw26435step0Labels = mixedMoment B raw26435step1 raw26435step1Labels := by
      have ha : raw26435step1 = -raw26435step0 := by apply Matrix.ext; change ∀ i j, raw26435step1 i j = -(raw26435step0 i j); unfold raw26435step1 raw26435step0; decide +kernel
      have hl : raw26435step1Labels = raw26435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1636 node1636Labels := by rfl

theorem canonical26436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26436 raw26436Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26436 raw26436Labels = mixedMoment B raw26436step0 raw26436step0Labels := by
      have ha : raw26436step0 = (fun i j => raw26436 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26436step0 raw26436; decide +kernel
      have hl : raw26436step0Labels = raw26436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26436 raw26436Labels permutation240 permutation2
    mixedMoment B raw26436step0 raw26436step0Labels = mixedMoment B raw26436step1 raw26436step1Labels := by
      have ha : raw26436step1 = -raw26436step0 := by apply Matrix.ext; change ∀ i j, raw26436step1 i j = -(raw26436step0 i j); unfold raw26436step1 raw26436step0; decide +kernel
      have hl : raw26436step1Labels = raw26436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical26437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26437 raw26437Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw26437 raw26437Labels = mixedMoment B raw26437step0 raw26437step0Labels := by
      have ha : raw26437step0 = (fun i j => raw26437 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26437step0 raw26437; decide +kernel
      have hl : raw26437step0Labels = raw26437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26437 raw26437Labels permutation158 permutation4
    mixedMoment B raw26437step0 raw26437step0Labels = mixedMoment B raw26437step1 raw26437step1Labels := by
      have ha : raw26437step1 = -raw26437step0 := by apply Matrix.ext; change ∀ i j, raw26437step1 i j = -(raw26437step0 i j); unfold raw26437step1 raw26437step0; decide +kernel
      have hl : raw26437step1Labels = raw26437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1600 node1600Labels := by rfl

theorem canonical26438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26438 raw26438Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw26438 raw26438Labels = mixedMoment B raw26438step0 raw26438step0Labels := by
      have ha : raw26438step0 = (fun i j => raw26438 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26438step0 raw26438; decide +kernel
      have hl : raw26438step0Labels = raw26438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26438 raw26438Labels permutation152 permutation4
    mixedMoment B raw26438step0 raw26438step0Labels = mixedMoment B raw26438step1 raw26438step1Labels := by
      have ha : raw26438step1 = -raw26438step0 := by apply Matrix.ext; change ∀ i j, raw26438step1 i j = -(raw26438step0 i j); unfold raw26438step1 raw26438step0; decide +kernel
      have hl : raw26438step1Labels = raw26438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1600 node1600Labels := by rfl

theorem canonical26439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26439 raw26439Labels = mixedMoment B node1595 node1595Labels := by
  calc
    mixedMoment B raw26439 raw26439Labels = mixedMoment B raw26439step0 raw26439step0Labels := by
      have ha : raw26439step0 = (fun i j => raw26439 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26439step0 raw26439; decide +kernel
      have hl : raw26439step0Labels = raw26439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26439 raw26439Labels permutation152 permutation4
    mixedMoment B raw26439step0 raw26439step0Labels = mixedMoment B raw26439step1 raw26439step1Labels := by
      have ha : raw26439step1 = -raw26439step0 := by apply Matrix.ext; change ∀ i j, raw26439step1 i j = -(raw26439step0 i j); unfold raw26439step1 raw26439step0; decide +kernel
      have hl : raw26439step1Labels = raw26439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1595 node1595Labels := by rfl

theorem canonical26440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26440 raw26440Labels = mixedMoment B node1593 node1593Labels := by
  calc
    mixedMoment B raw26440 raw26440Labels = mixedMoment B raw26440step0 raw26440step0Labels := by
      have ha : raw26440step0 = (fun i j => raw26440 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26440step0 raw26440; decide +kernel
      have hl : raw26440step0Labels = raw26440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26440 raw26440Labels permutation152 permutation4
    mixedMoment B raw26440step0 raw26440step0Labels = mixedMoment B raw26440step1 raw26440step1Labels := by
      have ha : raw26440step1 = -raw26440step0 := by apply Matrix.ext; change ∀ i j, raw26440step1 i j = -(raw26440step0 i j); unfold raw26440step1 raw26440step0; decide +kernel
      have hl : raw26440step1Labels = raw26440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1593 node1593Labels := by rfl

theorem canonical26441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26441 raw26441Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw26441 raw26441Labels = mixedMoment B raw26441step0 raw26441step0Labels := by
      have hz : ∀ j, raw26441 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26441step0 = (fun i j => raw26441 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26441step0 raw26441; decide +kernel
      have hl : raw26441step0Labels = raw26441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26441 raw26441Labels permutation265 hz
    mixedMoment B raw26441step0 raw26441step0Labels = mixedMoment B raw26441step1 raw26441step1Labels := by
      have ha : raw26441step1 = (fun i j => raw26441step0 (permutation55 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26441step1 raw26441step0; decide +kernel
      have hl : raw26441step1Labels = raw26441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26441step0 raw26441step0Labels permutation55 permutation2
    mixedMoment B raw26441step1 raw26441step1Labels = mixedMoment B raw26441step2 raw26441step2Labels := by
      have ha : raw26441step2 = -raw26441step1 := by apply Matrix.ext; change ∀ i j, raw26441step2 i j = -(raw26441step1 i j); unfold raw26441step2 raw26441step1; decide +kernel
      have hl : raw26441step2Labels = raw26441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3303 node3303Labels := by rfl

theorem canonical26442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26442 raw26442Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw26442 raw26442Labels = mixedMoment B raw26442step0 raw26442step0Labels := by
      have hz : ∀ j, raw26442 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26442step0 = (fun i j => raw26442 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26442step0 raw26442; decide +kernel
      have hl : raw26442step0Labels = raw26442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26442 raw26442Labels permutation265 hz
    mixedMoment B raw26442step0 raw26442step0Labels = mixedMoment B raw26442step1 raw26442step1Labels := by
      have ha : raw26442step1 = (fun i j => raw26442step0 (permutation54 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26442step1 raw26442step0; decide +kernel
      have hl : raw26442step1Labels = raw26442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26442step0 raw26442step0Labels permutation54 permutation2
    mixedMoment B raw26442step1 raw26442step1Labels = mixedMoment B raw26442step2 raw26442step2Labels := by
      have ha : raw26442step2 = -raw26442step1 := by apply Matrix.ext; change ∀ i j, raw26442step2 i j = -(raw26442step1 i j); unfold raw26442step2 raw26442step1; decide +kernel
      have hl : raw26442step2Labels = raw26442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3303 node3303Labels := by rfl

theorem canonical26443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26443 raw26443Labels = mixedMoment B node3307 node3307Labels := by
  calc
    mixedMoment B raw26443 raw26443Labels = mixedMoment B raw26443step0 raw26443step0Labels := by
      have hz : ∀ j, raw26443 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26443step0 = (fun i j => raw26443 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26443step0 raw26443; decide +kernel
      have hl : raw26443step0Labels = raw26443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26443 raw26443Labels permutation265 hz
    mixedMoment B raw26443step0 raw26443step0Labels = mixedMoment B raw26443step1 raw26443step1Labels := by
      have ha : raw26443step1 = (fun i j => raw26443step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26443step1 raw26443step0; decide +kernel
      have hl : raw26443step1Labels = raw26443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26443step0 raw26443step0Labels permutation48 permutation2
    mixedMoment B raw26443step1 raw26443step1Labels = mixedMoment B raw26443step2 raw26443step2Labels := by
      have ha : raw26443step2 = -raw26443step1 := by apply Matrix.ext; change ∀ i j, raw26443step2 i j = -(raw26443step1 i j); unfold raw26443step2 raw26443step1; decide +kernel
      have hl : raw26443step2Labels = raw26443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3307 node3307Labels := by rfl

theorem canonical26444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26444 raw26444Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw26444 raw26444Labels = mixedMoment B raw26444step0 raw26444step0Labels := by
      have ha : raw26444step0 = (fun i j => raw26444 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26444step0 raw26444; decide +kernel
      have hl : raw26444step0Labels = raw26444Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26444 raw26444Labels permutation158 permutation4
    mixedMoment B raw26444step0 raw26444step0Labels = mixedMoment B raw26444step1 raw26444step1Labels := by
      have ha : raw26444step1 = -raw26444step0 := by apply Matrix.ext; change ∀ i j, raw26444step1 i j = -(raw26444step0 i j); unfold raw26444step1 raw26444step0; decide +kernel
      have hl : raw26444step1Labels = raw26444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3239 node3239Labels := by rfl

theorem canonical26445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26445 raw26445Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw26445 raw26445Labels = mixedMoment B raw26445step0 raw26445step0Labels := by
      have ha : raw26445step0 = (fun i j => raw26445 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26445step0 raw26445; decide +kernel
      have hl : raw26445step0Labels = raw26445Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26445 raw26445Labels permutation158 permutation4
    mixedMoment B raw26445step0 raw26445step0Labels = mixedMoment B raw26445step1 raw26445step1Labels := by
      have ha : raw26445step1 = -raw26445step0 := by apply Matrix.ext; change ∀ i j, raw26445step1 i j = -(raw26445step0 i j); unfold raw26445step1 raw26445step0; decide +kernel
      have hl : raw26445step1Labels = raw26445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3286 node3286Labels := by rfl

theorem canonical26446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26446 raw26446Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw26446 raw26446Labels = mixedMoment B raw26446step0 raw26446step0Labels := by
      have ha : raw26446step0 = (fun i j => raw26446 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26446step0 raw26446; decide +kernel
      have hl : raw26446step0Labels = raw26446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26446 raw26446Labels permutation158 permutation4
    mixedMoment B raw26446step0 raw26446step0Labels = mixedMoment B raw26446step1 raw26446step1Labels := by
      have ha : raw26446step1 = -raw26446step0 := by apply Matrix.ext; change ∀ i j, raw26446step1 i j = -(raw26446step0 i j); unfold raw26446step1 raw26446step0; decide +kernel
      have hl : raw26446step1Labels = raw26446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical26447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26447 raw26447Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw26447 raw26447Labels = mixedMoment B raw26447step0 raw26447step0Labels := by
      have ha : raw26447step0 = (fun i j => raw26447 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26447step0 raw26447; decide +kernel
      have hl : raw26447step0Labels = raw26447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26447 raw26447Labels permutation152 permutation4
    mixedMoment B raw26447step0 raw26447step0Labels = mixedMoment B raw26447step1 raw26447step1Labels := by
      have ha : raw26447step1 = -raw26447step0 := by apply Matrix.ext; change ∀ i j, raw26447step1 i j = -(raw26447step0 i j); unfold raw26447step1 raw26447step0; decide +kernel
      have hl : raw26447step1Labels = raw26447step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical26448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26448 raw26448Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26448 raw26448Labels = mixedMoment B raw26448step0 raw26448step0Labels := by
      have ha : raw26448step0 = (fun i j => raw26448 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26448step0 raw26448; decide +kernel
      have hl : raw26448step0Labels = raw26448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26448 raw26448Labels permutation153 permutation4
    mixedMoment B raw26448step0 raw26448step0Labels = mixedMoment B raw26448step1 raw26448step1Labels := by
      have ha : raw26448step1 = -raw26448step0 := by apply Matrix.ext; change ∀ i j, raw26448step1 i j = -(raw26448step0 i j); unfold raw26448step1 raw26448step0; decide +kernel
      have hl : raw26448step1Labels = raw26448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26456 raw26456Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw26456 raw26456Labels = mixedMoment B raw26456step0 raw26456step0Labels := by
      have hz : ∀ j, raw26456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26456step0 = (fun i j => raw26456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26456step0 raw26456; decide +kernel
      have hl : raw26456step0Labels = raw26456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26456 raw26456Labels permutation265 hz
    mixedMoment B raw26456step0 raw26456step0Labels = mixedMoment B raw26456step1 raw26456step1Labels := by
      have ha : raw26456step1 = (fun i j => raw26456step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26456step1 raw26456step0; decide +kernel
      have hl : raw26456step1Labels = raw26456step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26456step0 raw26456step0Labels permutation53 permutation2
    mixedMoment B raw26456step1 raw26456step1Labels = mixedMoment B raw26456step2 raw26456step2Labels := by
      have ha : raw26456step2 = -raw26456step1 := by apply Matrix.ext; change ∀ i j, raw26456step2 i j = -(raw26456step1 i j); unfold raw26456step2 raw26456step1; decide +kernel
      have hl : raw26456step2Labels = raw26456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1648 node1648Labels := by rfl

theorem canonical26457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26457 raw26457Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw26457 raw26457Labels = mixedMoment B raw26457step0 raw26457step0Labels := by
      have hz : ∀ j, raw26457 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26457step0 = (fun i j => raw26457 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26457step0 raw26457; decide +kernel
      have hl : raw26457step0Labels = raw26457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26457 raw26457Labels permutation265 hz
    mixedMoment B raw26457step0 raw26457step0Labels = mixedMoment B raw26457step1 raw26457step1Labels := by
      have ha : raw26457step1 = (fun i j => raw26457step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26457step1 raw26457step0; decide +kernel
      have hl : raw26457step1Labels = raw26457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26457step0 raw26457step0Labels permutation53 permutation2
    mixedMoment B raw26457step1 raw26457step1Labels = mixedMoment B raw26457step2 raw26457step2Labels := by
      have ha : raw26457step2 = -raw26457step1 := by apply Matrix.ext; change ∀ i j, raw26457step2 i j = -(raw26457step1 i j); unfold raw26457step2 raw26457step1; decide +kernel
      have hl : raw26457step2Labels = raw26457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3303 node3303Labels := by rfl

theorem canonical26458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26458 raw26458Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw26458 raw26458Labels = mixedMoment B raw26458step0 raw26458step0Labels := by
      have hz : ∀ j, raw26458 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26458step0 = (fun i j => raw26458 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26458step0 raw26458; decide +kernel
      have hl : raw26458step0Labels = raw26458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26458 raw26458Labels permutation265 hz
    mixedMoment B raw26458step0 raw26458step0Labels = mixedMoment B raw26458step1 raw26458step1Labels := by
      have ha : raw26458step1 = (fun i j => raw26458step0 (permutation55 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26458step1 raw26458step0; decide +kernel
      have hl : raw26458step1Labels = raw26458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26458step0 raw26458step0Labels permutation55 permutation2
    mixedMoment B raw26458step1 raw26458step1Labels = mixedMoment B raw26458step2 raw26458step2Labels := by
      have ha : raw26458step2 = -raw26458step1 := by apply Matrix.ext; change ∀ i j, raw26458step2 i j = -(raw26458step1 i j); unfold raw26458step2 raw26458step1; decide +kernel
      have hl : raw26458step2Labels = raw26458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1639 node1639Labels := by rfl

theorem canonical26459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26459 raw26459Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw26459 raw26459Labels = mixedMoment B raw26459step0 raw26459step0Labels := by
      have hz : ∀ j, raw26459 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26459step0 = (fun i j => raw26459 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26459step0 raw26459; decide +kernel
      have hl : raw26459step0Labels = raw26459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26459 raw26459Labels permutation265 hz
    mixedMoment B raw26459step0 raw26459step0Labels = mixedMoment B raw26459step1 raw26459step1Labels := by
      have ha : raw26459step1 = (fun i j => raw26459step0 (permutation54 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26459step1 raw26459step0; decide +kernel
      have hl : raw26459step1Labels = raw26459step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26459step0 raw26459step0Labels permutation54 permutation2
    mixedMoment B raw26459step1 raw26459step1Labels = mixedMoment B raw26459step2 raw26459step2Labels := by
      have ha : raw26459step2 = -raw26459step1 := by apply Matrix.ext; change ∀ i j, raw26459step2 i j = -(raw26459step1 i j); unfold raw26459step2 raw26459step1; decide +kernel
      have hl : raw26459step2Labels = raw26459step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1641 node1641Labels := by rfl

theorem canonical26460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26460 raw26460Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26460 raw26460Labels = mixedMoment B raw26460step0 raw26460step0Labels := by
      have hz : ∀ j, raw26460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26460step0 = (fun i j => raw26460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26460step0 raw26460; decide +kernel
      have hl : raw26460step0Labels = raw26460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26460 raw26460Labels permutation265 hz
    mixedMoment B raw26460step0 raw26460step0Labels = mixedMoment B raw26460step1 raw26460step1Labels := by
      have ha : raw26460step1 = (fun i j => raw26460step0 (permutation49 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26460step1 raw26460step0; decide +kernel
      have hl : raw26460step1Labels = raw26460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26460step0 raw26460step0Labels permutation49 permutation2
    mixedMoment B raw26460step1 raw26460step1Labels = mixedMoment B raw26460step2 raw26460step2Labels := by
      have ha : raw26460step2 = -raw26460step1 := by apply Matrix.ext; change ∀ i j, raw26460step2 i j = -(raw26460step1 i j); unfold raw26460step2 raw26460step1; decide +kernel
      have hl : raw26460step2Labels = raw26460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical26493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26493 raw26493Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw26493 raw26493Labels = mixedMoment B raw26493step0 raw26493step0Labels := by
      have ha : raw26493step0 = (fun i j => raw26493 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26493step0 raw26493; decide +kernel
      have hl : raw26493step0Labels = raw26493Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26493 raw26493Labels permutation170 permutation2
    _ = mixedMoment B node5162 node5162Labels := by rfl

theorem canonical26494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26494 raw26494Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw26494 raw26494Labels = mixedMoment B raw26494step0 raw26494step0Labels := by
      have hz : ∀ j, raw26494 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26494step0 = (fun i j => raw26494 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26494step0 raw26494; decide +kernel
      have hl : raw26494step0Labels = raw26494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26494 raw26494Labels permutation265 hz
    mixedMoment B raw26494step0 raw26494step0Labels = mixedMoment B raw26494step1 raw26494step1Labels := by
      have ha : raw26494step1 = (fun i j => raw26494step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26494step1 raw26494step0; decide +kernel
      have hl : raw26494step1Labels = raw26494step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26494step0 raw26494step0Labels permutation48 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical26495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26495 raw26495Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw26495 raw26495Labels = mixedMoment B raw26495step0 raw26495step0Labels := by
      have hz : ∀ j, raw26495 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26495step0 = (fun i j => raw26495 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26495step0 raw26495; decide +kernel
      have hl : raw26495step0Labels = raw26495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26495 raw26495Labels permutation265 hz
    mixedMoment B raw26495step0 raw26495step0Labels = mixedMoment B raw26495step1 raw26495step1Labels := by
      have ha : raw26495step1 = (fun i j => raw26495step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26495step1 raw26495step0; decide +kernel
      have hl : raw26495step1Labels = raw26495step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26495step0 raw26495step0Labels permutation50 permutation2
    _ = mixedMoment B node5273 node5273Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical207
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26496 raw26496Labels = mixedMoment B node4169 node4169Labels := by
  calc
    mixedMoment B raw26496 raw26496Labels = mixedMoment B raw26496step0 raw26496step0Labels := by
      have ha : raw26496step0 = (fun i j => raw26496 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26496step0 raw26496; decide +kernel
      have hl : raw26496step0Labels = raw26496Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26496 raw26496Labels permutation184 permutation3
    mixedMoment B raw26496step0 raw26496step0Labels = mixedMoment B raw26496step1 raw26496step1Labels := by
      have ha : raw26496step1 = raw26496step0 := by apply Matrix.ext; unfold raw26496step1 raw26496step0; decide +kernel
      have hl : raw26496step0Labels = labelEmbedding6 ∘ raw26496step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26496step0 raw26496step0Labels raw26496step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4169 node4169Labels := by rfl

theorem canonical26497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26497 raw26497Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26497 raw26497Labels = mixedMoment B raw26497step0 raw26497step0Labels := by
      have ha : raw26497step0 = (fun i j => raw26497 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26497step0 raw26497; decide +kernel
      have hl : raw26497step0Labels = raw26497Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26497 raw26497Labels permutation184 permutation3
    mixedMoment B raw26497step0 raw26497step0Labels = mixedMoment B raw26497step1 raw26497step1Labels := by
      have ha : raw26497step1 = raw26497step0 := by apply Matrix.ext; unfold raw26497step1 raw26497step0; decide +kernel
      have hl : raw26497step0Labels = labelEmbedding6 ∘ raw26497step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26497step0 raw26497step0Labels raw26497step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26498 raw26498Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26498 raw26498Labels = mixedMoment B raw26498step0 raw26498step0Labels := by
      have ha : raw26498step0 = (fun i j => raw26498 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26498step0 raw26498; decide +kernel
      have hl : raw26498step0Labels = raw26498Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26498 raw26498Labels permutation208 permutation3
    mixedMoment B raw26498step0 raw26498step0Labels = mixedMoment B raw26498step1 raw26498step1Labels := by
      have ha : raw26498step1 = raw26498step0 := by apply Matrix.ext; unfold raw26498step1 raw26498step0; decide +kernel
      have hl : raw26498step0Labels = labelEmbedding6 ∘ raw26498step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26498step0 raw26498step0Labels raw26498step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26499 raw26499Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw26499 raw26499Labels = mixedMoment B raw26499step0 raw26499step0Labels := by
      have ha : raw26499step0 = (fun i j => raw26499 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26499step0 raw26499; decide +kernel
      have hl : raw26499step0Labels = raw26499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26499 raw26499Labels permutation232 permutation3
    mixedMoment B raw26499step0 raw26499step0Labels = mixedMoment B raw26499step1 raw26499step1Labels := by
      have ha : raw26499step1 = raw26499step0 := by apply Matrix.ext; unfold raw26499step1 raw26499step0; decide +kernel
      have hl : raw26499step0Labels = labelEmbedding6 ∘ raw26499step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26499step0 raw26499step0Labels raw26499step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical26500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26500 raw26500Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26500 raw26500Labels = mixedMoment B raw26500step0 raw26500step0Labels := by
      have ha : raw26500step0 = (fun i j => raw26500 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26500step0 raw26500; decide +kernel
      have hl : raw26500step0Labels = raw26500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26500 raw26500Labels permutation246 permutation2
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical26501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26501 raw26501Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw26501 raw26501Labels = mixedMoment B raw26501step0 raw26501step0Labels := by
      have hz : ∀ j, raw26501 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26501step0 = (fun i j => raw26501 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26501step0 raw26501; decide +kernel
      have hl : raw26501step0Labels = raw26501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26501 raw26501Labels permutation265 hz
    mixedMoment B raw26501step0 raw26501step0Labels = mixedMoment B raw26501step1 raw26501step1Labels := by
      have ha : raw26501step1 = (fun i j => raw26501step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26501step1 raw26501step0; decide +kernel
      have hl : raw26501step1Labels = raw26501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26501step0 raw26501step0Labels permutation41 permutation3
    mixedMoment B raw26501step1 raw26501step1Labels = mixedMoment B raw26501step2 raw26501step2Labels := by
      have ha : raw26501step2 = raw26501step1 := by apply Matrix.ext; unfold raw26501step2 raw26501step1; decide +kernel
      have hl : raw26501step1Labels = labelEmbedding6 ∘ raw26501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26501step1 raw26501step1Labels raw26501step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4173 node4173Labels := by rfl

theorem canonical26502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26502 raw26502Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw26502 raw26502Labels = mixedMoment B raw26502step0 raw26502step0Labels := by
      have ha : raw26502step0 = (fun i j => raw26502 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26502step0 raw26502; decide +kernel
      have hl : raw26502step0Labels = raw26502Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26502 raw26502Labels permutation161 permutation3
    mixedMoment B raw26502step0 raw26502step0Labels = mixedMoment B raw26502step1 raw26502step1Labels := by
      have ha : raw26502step1 = raw26502step0 := by apply Matrix.ext; unfold raw26502step1 raw26502step0; decide +kernel
      have hl : raw26502step0Labels = labelEmbedding6 ∘ raw26502step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26502step0 raw26502step0Labels raw26502step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4542 node4542Labels := by rfl

theorem canonical26503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26503 raw26503Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26503 raw26503Labels = mixedMoment B raw26503step0 raw26503step0Labels := by
      have hz : ∀ j, raw26503 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26503step0 = (fun i j => raw26503 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26503step0 raw26503; decide +kernel
      have hl : raw26503step0Labels = raw26503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26503 raw26503Labels permutation265 hz
    mixedMoment B raw26503step0 raw26503step0Labels = mixedMoment B raw26503step1 raw26503step1Labels := by
      have ha : raw26503step1 = (fun i j => raw26503step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26503step1 raw26503step0; decide +kernel
      have hl : raw26503step1Labels = raw26503step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26503step0 raw26503step0Labels permutation41 permutation3
    mixedMoment B raw26503step1 raw26503step1Labels = mixedMoment B raw26503step2 raw26503step2Labels := by
      have ha : raw26503step2 = raw26503step1 := by apply Matrix.ext; unfold raw26503step2 raw26503step1; decide +kernel
      have hl : raw26503step1Labels = labelEmbedding6 ∘ raw26503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26503step1 raw26503step1Labels raw26503step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical26504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26504 raw26504Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26504 raw26504Labels = mixedMoment B raw26504step0 raw26504step0Labels := by
      have hz : ∀ j, raw26504 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26504step0 = (fun i j => raw26504 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26504step0 raw26504; decide +kernel
      have hl : raw26504step0Labels = raw26504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26504 raw26504Labels permutation265 hz
    mixedMoment B raw26504step0 raw26504step0Labels = mixedMoment B raw26504step1 raw26504step1Labels := by
      have ha : raw26504step1 = (fun i j => raw26504step0 (permutation47 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26504step1 raw26504step0; decide +kernel
      have hl : raw26504step1Labels = raw26504step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26504step0 raw26504step0Labels permutation47 permutation3
    mixedMoment B raw26504step1 raw26504step1Labels = mixedMoment B raw26504step2 raw26504step2Labels := by
      have ha : raw26504step2 = raw26504step1 := by apply Matrix.ext; unfold raw26504step2 raw26504step1; decide +kernel
      have hl : raw26504step1Labels = labelEmbedding6 ∘ raw26504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26504step1 raw26504step1Labels raw26504step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical26505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26505 raw26505Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26505 raw26505Labels = mixedMoment B raw26505step0 raw26505step0Labels := by
      have hz : ∀ j, raw26505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26505step0 = (fun i j => raw26505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26505step0 raw26505; decide +kernel
      have hl : raw26505step0Labels = raw26505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26505 raw26505Labels permutation265 hz
    mixedMoment B raw26505step0 raw26505step0Labels = mixedMoment B raw26505step1 raw26505step1Labels := by
      have ha : raw26505step1 = (fun i j => raw26505step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26505step1 raw26505step0; decide +kernel
      have hl : raw26505step1Labels = raw26505step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26505step0 raw26505step0Labels permutation53 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical26506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26506 raw26506Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw26506 raw26506Labels = mixedMoment B raw26506step0 raw26506step0Labels := by
      have hz : ∀ j, raw26506 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26506step0 = (fun i j => raw26506 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26506step0 raw26506; decide +kernel
      have hl : raw26506step0Labels = raw26506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26506 raw26506Labels permutation265 hz
    mixedMoment B raw26506step0 raw26506step0Labels = mixedMoment B raw26506step1 raw26506step1Labels := by
      have ha : raw26506step1 = (fun i j => raw26506step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26506step1 raw26506step0; decide +kernel
      have hl : raw26506step1Labels = raw26506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26506step0 raw26506step0Labels permutation35 permutation3
    mixedMoment B raw26506step1 raw26506step1Labels = mixedMoment B raw26506step2 raw26506step2Labels := by
      have ha : raw26506step2 = raw26506step1 := by apply Matrix.ext; unfold raw26506step2 raw26506step1; decide +kernel
      have hl : raw26506step1Labels = labelEmbedding6 ∘ raw26506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26506step1 raw26506step1Labels raw26506step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4173 node4173Labels := by rfl

theorem canonical26507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26507 raw26507Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw26507 raw26507Labels = mixedMoment B raw26507step0 raw26507step0Labels := by
      have ha : raw26507step0 = (fun i j => raw26507 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26507step0 raw26507; decide +kernel
      have hl : raw26507step0Labels = raw26507Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26507 raw26507Labels permutation155 permutation3
    mixedMoment B raw26507step0 raw26507step0Labels = mixedMoment B raw26507step1 raw26507step1Labels := by
      have ha : raw26507step1 = raw26507step0 := by apply Matrix.ext; unfold raw26507step1 raw26507step0; decide +kernel
      have hl : raw26507step0Labels = labelEmbedding6 ∘ raw26507step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26507step0 raw26507step0Labels raw26507step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4542 node4542Labels := by rfl

theorem canonical26508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26508 raw26508Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26508 raw26508Labels = mixedMoment B raw26508step0 raw26508step0Labels := by
      have hz : ∀ j, raw26508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26508step0 = (fun i j => raw26508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26508step0 raw26508; decide +kernel
      have hl : raw26508step0Labels = raw26508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26508 raw26508Labels permutation265 hz
    mixedMoment B raw26508step0 raw26508step0Labels = mixedMoment B raw26508step1 raw26508step1Labels := by
      have ha : raw26508step1 = (fun i j => raw26508step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26508step1 raw26508step0; decide +kernel
      have hl : raw26508step1Labels = raw26508step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26508step0 raw26508step0Labels permutation35 permutation3
    mixedMoment B raw26508step1 raw26508step1Labels = mixedMoment B raw26508step2 raw26508step2Labels := by
      have ha : raw26508step2 = raw26508step1 := by apply Matrix.ext; unfold raw26508step2 raw26508step1; decide +kernel
      have hl : raw26508step1Labels = labelEmbedding6 ∘ raw26508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26508step1 raw26508step1Labels raw26508step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical26509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26509 raw26509Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26509 raw26509Labels = mixedMoment B raw26509step0 raw26509step0Labels := by
      have hz : ∀ j, raw26509 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26509step0 = (fun i j => raw26509 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26509step0 raw26509; decide +kernel
      have hl : raw26509step0Labels = raw26509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26509 raw26509Labels permutation265 hz
    mixedMoment B raw26509step0 raw26509step0Labels = mixedMoment B raw26509step1 raw26509step1Labels := by
      have ha : raw26509step1 = (fun i j => raw26509step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26509step1 raw26509step0; decide +kernel
      have hl : raw26509step1Labels = raw26509step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26509step0 raw26509step0Labels permutation45 permutation3
    mixedMoment B raw26509step1 raw26509step1Labels = mixedMoment B raw26509step2 raw26509step2Labels := by
      have ha : raw26509step2 = raw26509step1 := by apply Matrix.ext; unfold raw26509step2 raw26509step1; decide +kernel
      have hl : raw26509step1Labels = labelEmbedding6 ∘ raw26509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26509step1 raw26509step1Labels raw26509step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical26510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26510 raw26510Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26510 raw26510Labels = mixedMoment B raw26510step0 raw26510step0Labels := by
      have hz : ∀ j, raw26510 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26510step0 = (fun i j => raw26510 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26510step0 raw26510; decide +kernel
      have hl : raw26510step0Labels = raw26510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26510 raw26510Labels permutation265 hz
    mixedMoment B raw26510step0 raw26510step0Labels = mixedMoment B raw26510step1 raw26510step1Labels := by
      have ha : raw26510step1 = (fun i j => raw26510step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26510step1 raw26510step0; decide +kernel
      have hl : raw26510step1Labels = raw26510step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26510step0 raw26510step0Labels permutation51 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical26511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26511 raw26511Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw26511 raw26511Labels = mixedMoment B raw26511step0 raw26511step0Labels := by
      have hz : ∀ j, raw26511 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26511step0 = (fun i j => raw26511 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26511step0 raw26511; decide +kernel
      have hl : raw26511step0Labels = raw26511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26511 raw26511Labels permutation265 hz
    mixedMoment B raw26511step0 raw26511step0Labels = mixedMoment B raw26511step1 raw26511step1Labels := by
      have ha : raw26511step1 = (fun i j => raw26511step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26511step1 raw26511step0; decide +kernel
      have hl : raw26511step1Labels = raw26511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26511step0 raw26511step0Labels permutation33 permutation3
    mixedMoment B raw26511step1 raw26511step1Labels = mixedMoment B raw26511step2 raw26511step2Labels := by
      have ha : raw26511step2 = raw26511step1 := by apply Matrix.ext; unfold raw26511step2 raw26511step1; decide +kernel
      have hl : raw26511step1Labels = labelEmbedding6 ∘ raw26511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26511step1 raw26511step1Labels raw26511step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4173 node4173Labels := by rfl

theorem canonical26512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26512 raw26512Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw26512 raw26512Labels = mixedMoment B raw26512step0 raw26512step0Labels := by
      have ha : raw26512step0 = (fun i j => raw26512 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26512step0 raw26512; decide +kernel
      have hl : raw26512step0Labels = raw26512Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26512 raw26512Labels permutation153 permutation3
    mixedMoment B raw26512step0 raw26512step0Labels = mixedMoment B raw26512step1 raw26512step1Labels := by
      have ha : raw26512step1 = raw26512step0 := by apply Matrix.ext; unfold raw26512step1 raw26512step0; decide +kernel
      have hl : raw26512step0Labels = labelEmbedding6 ∘ raw26512step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26512step0 raw26512step0Labels raw26512step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4542 node4542Labels := by rfl

theorem canonical26513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26513 raw26513Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26513 raw26513Labels = mixedMoment B raw26513step0 raw26513step0Labels := by
      have hz : ∀ j, raw26513 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26513step0 = (fun i j => raw26513 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26513step0 raw26513; decide +kernel
      have hl : raw26513step0Labels = raw26513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26513 raw26513Labels permutation265 hz
    mixedMoment B raw26513step0 raw26513step0Labels = mixedMoment B raw26513step1 raw26513step1Labels := by
      have ha : raw26513step1 = (fun i j => raw26513step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26513step1 raw26513step0; decide +kernel
      have hl : raw26513step1Labels = raw26513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26513step0 raw26513step0Labels permutation33 permutation3
    mixedMoment B raw26513step1 raw26513step1Labels = mixedMoment B raw26513step2 raw26513step2Labels := by
      have ha : raw26513step2 = raw26513step1 := by apply Matrix.ext; unfold raw26513step2 raw26513step1; decide +kernel
      have hl : raw26513step1Labels = labelEmbedding6 ∘ raw26513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26513step1 raw26513step1Labels raw26513step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical26514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26514 raw26514Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw26514 raw26514Labels = mixedMoment B raw26514step0 raw26514step0Labels := by
      have hz : ∀ j, raw26514 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26514step0 = (fun i j => raw26514 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26514step0 raw26514; decide +kernel
      have hl : raw26514step0Labels = raw26514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26514 raw26514Labels permutation265 hz
    mixedMoment B raw26514step0 raw26514step0Labels = mixedMoment B raw26514step1 raw26514step1Labels := by
      have ha : raw26514step1 = (fun i j => raw26514step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26514step1 raw26514step0; decide +kernel
      have hl : raw26514step1Labels = raw26514step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26514step0 raw26514step0Labels permutation39 permutation3
    mixedMoment B raw26514step1 raw26514step1Labels = mixedMoment B raw26514step2 raw26514step2Labels := by
      have ha : raw26514step2 = raw26514step1 := by apply Matrix.ext; unfold raw26514step2 raw26514step1; decide +kernel
      have hl : raw26514step1Labels = labelEmbedding6 ∘ raw26514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26514step1 raw26514step1Labels raw26514step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical26515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26515 raw26515Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26515 raw26515Labels = mixedMoment B raw26515step0 raw26515step0Labels := by
      have hz : ∀ j, raw26515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26515step0 = (fun i j => raw26515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26515step0 raw26515; decide +kernel
      have hl : raw26515step0Labels = raw26515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26515 raw26515Labels permutation265 hz
    mixedMoment B raw26515step0 raw26515step0Labels = mixedMoment B raw26515step1 raw26515step1Labels := by
      have ha : raw26515step1 = (fun i j => raw26515step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26515step1 raw26515step0; decide +kernel
      have hl : raw26515step1Labels = raw26515step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26515step0 raw26515step0Labels permutation50 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical26516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26516 raw26516Labels = mixedMoment B node4170 node4170Labels := by
  calc
    mixedMoment B raw26516 raw26516Labels = mixedMoment B raw26516step0 raw26516step0Labels := by
      have hz : ∀ j, raw26516 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26516step0 = (fun i j => raw26516 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26516step0 raw26516; decide +kernel
      have hl : raw26516step0Labels = raw26516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26516 raw26516Labels permutation265 hz
    mixedMoment B raw26516step0 raw26516step0Labels = mixedMoment B raw26516step1 raw26516step1Labels := by
      have ha : raw26516step1 = (fun i j => raw26516step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26516step1 raw26516step0; decide +kernel
      have hl : raw26516step1Labels = raw26516step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26516step0 raw26516step0Labels permutation32 permutation3
    mixedMoment B raw26516step1 raw26516step1Labels = mixedMoment B raw26516step2 raw26516step2Labels := by
      have ha : raw26516step2 = raw26516step1 := by apply Matrix.ext; unfold raw26516step2 raw26516step1; decide +kernel
      have hl : raw26516step1Labels = labelEmbedding6 ∘ raw26516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26516step1 raw26516step1Labels raw26516step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4170 node4170Labels := by rfl

theorem canonical26517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26517 raw26517Labels = mixedMoment B node4540 node4540Labels := by
  calc
    mixedMoment B raw26517 raw26517Labels = mixedMoment B raw26517step0 raw26517step0Labels := by
      have ha : raw26517step0 = (fun i j => raw26517 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26517step0 raw26517; decide +kernel
      have hl : raw26517step0Labels = raw26517Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26517 raw26517Labels permutation152 permutation3
    mixedMoment B raw26517step0 raw26517step0Labels = mixedMoment B raw26517step1 raw26517step1Labels := by
      have ha : raw26517step1 = raw26517step0 := by apply Matrix.ext; unfold raw26517step1 raw26517step0; decide +kernel
      have hl : raw26517step0Labels = labelEmbedding6 ∘ raw26517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26517step0 raw26517step0Labels raw26517step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4540 node4540Labels := by rfl

theorem canonical26518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26518 raw26518Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw26518 raw26518Labels = mixedMoment B raw26518step0 raw26518step0Labels := by
      have hz : ∀ j, raw26518 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26518step0 = (fun i j => raw26518 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26518step0 raw26518; decide +kernel
      have hl : raw26518step0Labels = raw26518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26518 raw26518Labels permutation265 hz
    mixedMoment B raw26518step0 raw26518step0Labels = mixedMoment B raw26518step1 raw26518step1Labels := by
      have ha : raw26518step1 = (fun i j => raw26518step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26518step1 raw26518step0; decide +kernel
      have hl : raw26518step1Labels = raw26518step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26518step0 raw26518step0Labels permutation44 permutation3
    mixedMoment B raw26518step1 raw26518step1Labels = mixedMoment B raw26518step2 raw26518step2Labels := by
      have ha : raw26518step2 = raw26518step1 := by apply Matrix.ext; unfold raw26518step2 raw26518step1; decide +kernel
      have hl : raw26518step1Labels = labelEmbedding6 ∘ raw26518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26518step1 raw26518step1Labels raw26518step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

theorem canonical26545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26545 raw26545Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw26545 raw26545Labels = mixedMoment B raw26545step0 raw26545step0Labels := by
      have ha : raw26545step0 = (fun i j => raw26545 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26545step0 raw26545; decide +kernel
      have hl : raw26545step0Labels = raw26545Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26545 raw26545Labels permutation246 permutation7
    mixedMoment B raw26545step0 raw26545step0Labels = mixedMoment B raw26545step1 raw26545step1Labels := by
      have ha : raw26545step1 = -raw26545step0 := by apply Matrix.ext; change ∀ i j, raw26545step1 i j = -(raw26545step0 i j); unfold raw26545step1 raw26545step0; decide +kernel
      have hl : raw26545step1Labels = raw26545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26545step1 raw26545step1Labels = mixedMoment B raw26545step2 raw26545step2Labels := by
      have ha : raw26545step2 = raw26545step1 := by apply Matrix.ext; unfold raw26545step2 raw26545step1; decide +kernel
      have hl : raw26545step1Labels = labelEmbedding1 ∘ raw26545step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26545step1 raw26545step1Labels raw26545step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

theorem canonical26546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26546 raw26546Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw26546 raw26546Labels = mixedMoment B raw26546step0 raw26546step0Labels := by
      have hz : ∀ j, raw26546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26546step0 = (fun i j => raw26546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26546step0 raw26546; decide +kernel
      have hl : raw26546step0Labels = raw26546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26546 raw26546Labels permutation265 hz
    mixedMoment B raw26546step0 raw26546step0Labels = mixedMoment B raw26546step1 raw26546step1Labels := by
      have ha : raw26546step1 = (fun i j => raw26546step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26546step1 raw26546step0; decide +kernel
      have hl : raw26546step1Labels = raw26546step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26546step0 raw26546step0Labels permutation54 permutation7
    mixedMoment B raw26546step1 raw26546step1Labels = mixedMoment B raw26546step2 raw26546step2Labels := by
      have ha : raw26546step2 = -raw26546step1 := by apply Matrix.ext; change ∀ i j, raw26546step2 i j = -(raw26546step1 i j); unfold raw26546step2 raw26546step1; decide +kernel
      have hl : raw26546step2Labels = raw26546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26546step2 raw26546step2Labels = mixedMoment B raw26546step3 raw26546step3Labels := by
      have ha : raw26546step3 = raw26546step2 := by apply Matrix.ext; unfold raw26546step3 raw26546step2; decide +kernel
      have hl : raw26546step2Labels = labelEmbedding1 ∘ raw26546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26546step2 raw26546step2Labels raw26546step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical26547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26547 raw26547Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw26547 raw26547Labels = mixedMoment B raw26547step0 raw26547step0Labels := by
      have hz : ∀ j, raw26547 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26547step0 = (fun i j => raw26547 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26547step0 raw26547; decide +kernel
      have hl : raw26547step0Labels = raw26547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26547 raw26547Labels permutation265 hz
    mixedMoment B raw26547step0 raw26547step0Labels = mixedMoment B raw26547step1 raw26547step1Labels := by
      have ha : raw26547step1 = (fun i j => raw26547step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26547step1 raw26547step0; decide +kernel
      have hl : raw26547step1Labels = raw26547step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26547step0 raw26547step0Labels permutation50 permutation7
    mixedMoment B raw26547step1 raw26547step1Labels = mixedMoment B raw26547step2 raw26547step2Labels := by
      have ha : raw26547step2 = -raw26547step1 := by apply Matrix.ext; change ∀ i j, raw26547step2 i j = -(raw26547step1 i j); unfold raw26547step2 raw26547step1; decide +kernel
      have hl : raw26547step2Labels = raw26547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26547step2 raw26547step2Labels = mixedMoment B raw26547step3 raw26547step3Labels := by
      have ha : raw26547step3 = raw26547step2 := by apply Matrix.ext; unfold raw26547step3 raw26547step2; decide +kernel
      have hl : raw26547step2Labels = labelEmbedding1 ∘ raw26547step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26547step2 raw26547step2Labels raw26547step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

theorem canonical26548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26548 raw26548Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw26548 raw26548Labels = mixedMoment B raw26548step0 raw26548step0Labels := by
      have ha : raw26548step0 = (fun i j => raw26548 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26548step0 raw26548; decide +kernel
      have hl : raw26548step0Labels = raw26548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26548 raw26548Labels permutation184 permutation5
    mixedMoment B raw26548step0 raw26548step0Labels = mixedMoment B raw26548step1 raw26548step1Labels := by
      have ha : raw26548step1 = -raw26548step0 := by apply Matrix.ext; change ∀ i j, raw26548step1 i j = -(raw26548step0 i j); unfold raw26548step1 raw26548step0; decide +kernel
      have hl : raw26548step1Labels = raw26548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26548step1 raw26548step1Labels = mixedMoment B raw26548step2 raw26548step2Labels := by
      have ha : raw26548step2 = raw26548step1 := by apply Matrix.ext; unfold raw26548step2 raw26548step1; decide +kernel
      have hl : raw26548step1Labels = labelEmbedding1 ∘ raw26548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26548step1 raw26548step1Labels raw26548step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1502 node1502Labels := by rfl

theorem canonical26549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26549 raw26549Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26549 raw26549Labels = mixedMoment B raw26549step0 raw26549step0Labels := by
      have ha : raw26549step0 = (fun i j => raw26549 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26549step0 raw26549; decide +kernel
      have hl : raw26549step0Labels = raw26549Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26549 raw26549Labels permutation184 permutation5
    mixedMoment B raw26549step0 raw26549step0Labels = mixedMoment B raw26549step1 raw26549step1Labels := by
      have ha : raw26549step1 = -raw26549step0 := by apply Matrix.ext; change ∀ i j, raw26549step1 i j = -(raw26549step0 i j); unfold raw26549step1 raw26549step0; decide +kernel
      have hl : raw26549step1Labels = raw26549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26549step1 raw26549step1Labels = mixedMoment B raw26549step2 raw26549step2Labels := by
      have ha : raw26549step2 = raw26549step1 := by apply Matrix.ext; unfold raw26549step2 raw26549step1; decide +kernel
      have hl : raw26549step1Labels = labelEmbedding1 ∘ raw26549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26549step1 raw26549step1Labels raw26549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26550 raw26550Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26550 raw26550Labels = mixedMoment B raw26550step0 raw26550step0Labels := by
      have ha : raw26550step0 = (fun i j => raw26550 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26550step0 raw26550; decide +kernel
      have hl : raw26550step0Labels = raw26550Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26550 raw26550Labels permutation208 permutation5
    mixedMoment B raw26550step0 raw26550step0Labels = mixedMoment B raw26550step1 raw26550step1Labels := by
      have ha : raw26550step1 = -raw26550step0 := by apply Matrix.ext; change ∀ i j, raw26550step1 i j = -(raw26550step0 i j); unfold raw26550step1 raw26550step0; decide +kernel
      have hl : raw26550step1Labels = raw26550step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26550step1 raw26550step1Labels = mixedMoment B raw26550step2 raw26550step2Labels := by
      have ha : raw26550step2 = raw26550step1 := by apply Matrix.ext; unfold raw26550step2 raw26550step1; decide +kernel
      have hl : raw26550step1Labels = labelEmbedding1 ∘ raw26550step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26550step1 raw26550step1Labels raw26550step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26551 raw26551Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw26551 raw26551Labels = mixedMoment B raw26551step0 raw26551step0Labels := by
      have ha : raw26551step0 = (fun i j => raw26551 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26551step0 raw26551; decide +kernel
      have hl : raw26551step0Labels = raw26551Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26551 raw26551Labels permutation232 permutation5
    mixedMoment B raw26551step0 raw26551step0Labels = mixedMoment B raw26551step1 raw26551step1Labels := by
      have ha : raw26551step1 = -raw26551step0 := by apply Matrix.ext; change ∀ i j, raw26551step1 i j = -(raw26551step0 i j); unfold raw26551step1 raw26551step0; decide +kernel
      have hl : raw26551step1Labels = raw26551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26551step1 raw26551step1Labels = mixedMoment B raw26551step2 raw26551step2Labels := by
      have ha : raw26551step2 = raw26551step1 := by apply Matrix.ext; unfold raw26551step2 raw26551step1; decide +kernel
      have hl : raw26551step1Labels = labelEmbedding1 ∘ raw26551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26551step1 raw26551step1Labels raw26551step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical26552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26552 raw26552Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw26552 raw26552Labels = mixedMoment B raw26552step0 raw26552step0Labels := by
      have ha : raw26552step0 = (fun i j => raw26552 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26552step0 raw26552; decide +kernel
      have hl : raw26552step0Labels = raw26552Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26552 raw26552Labels permutation246 permutation7
    mixedMoment B raw26552step0 raw26552step0Labels = mixedMoment B raw26552step1 raw26552step1Labels := by
      have ha : raw26552step1 = -raw26552step0 := by apply Matrix.ext; change ∀ i j, raw26552step1 i j = -(raw26552step0 i j); unfold raw26552step1 raw26552step0; decide +kernel
      have hl : raw26552step1Labels = raw26552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26552step1 raw26552step1Labels = mixedMoment B raw26552step2 raw26552step2Labels := by
      have ha : raw26552step2 = raw26552step1 := by apply Matrix.ext; unfold raw26552step2 raw26552step1; decide +kernel
      have hl : raw26552step1Labels = labelEmbedding1 ∘ raw26552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26552step1 raw26552step1Labels raw26552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical26553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26553 raw26553Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw26553 raw26553Labels = mixedMoment B raw26553step0 raw26553step0Labels := by
      have hz : ∀ j, raw26553 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26553step0 = (fun i j => raw26553 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26553step0 raw26553; decide +kernel
      have hl : raw26553step0Labels = raw26553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26553 raw26553Labels permutation265 hz
    mixedMoment B raw26553step0 raw26553step0Labels = mixedMoment B raw26553step1 raw26553step1Labels := by
      have ha : raw26553step1 = (fun i j => raw26553step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26553step1 raw26553step0; decide +kernel
      have hl : raw26553step1Labels = raw26553step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26553step0 raw26553step0Labels permutation40 permutation5
    mixedMoment B raw26553step1 raw26553step1Labels = mixedMoment B raw26553step2 raw26553step2Labels := by
      have ha : raw26553step2 = -raw26553step1 := by apply Matrix.ext; change ∀ i j, raw26553step2 i j = -(raw26553step1 i j); unfold raw26553step2 raw26553step1; decide +kernel
      have hl : raw26553step2Labels = raw26553step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26553step2 raw26553step2Labels = mixedMoment B raw26553step3 raw26553step3Labels := by
      have ha : raw26553step3 = raw26553step2 := by apply Matrix.ext; unfold raw26553step3 raw26553step2; decide +kernel
      have hl : raw26553step2Labels = labelEmbedding1 ∘ raw26553step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26553step2 raw26553step2Labels raw26553step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

theorem canonical26554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26554 raw26554Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26554 raw26554Labels = mixedMoment B raw26554step0 raw26554step0Labels := by
      have ha : raw26554step0 = (fun i j => raw26554 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26554step0 raw26554; decide +kernel
      have hl : raw26554step0Labels = raw26554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26554 raw26554Labels permutation160 permutation5
    mixedMoment B raw26554step0 raw26554step0Labels = mixedMoment B raw26554step1 raw26554step1Labels := by
      have ha : raw26554step1 = -raw26554step0 := by apply Matrix.ext; change ∀ i j, raw26554step1 i j = -(raw26554step0 i j); unfold raw26554step1 raw26554step0; decide +kernel
      have hl : raw26554step1Labels = raw26554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26554step1 raw26554step1Labels = mixedMoment B raw26554step2 raw26554step2Labels := by
      have ha : raw26554step2 = raw26554step1 := by apply Matrix.ext; unfold raw26554step2 raw26554step1; decide +kernel
      have hl : raw26554step1Labels = labelEmbedding1 ∘ raw26554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26554step1 raw26554step1Labels raw26554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical26555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26555 raw26555Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26555 raw26555Labels = mixedMoment B raw26555step0 raw26555step0Labels := by
      have hz : ∀ j, raw26555 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26555step0 = (fun i j => raw26555 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26555step0 raw26555; decide +kernel
      have hl : raw26555step0Labels = raw26555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26555 raw26555Labels permutation265 hz
    mixedMoment B raw26555step0 raw26555step0Labels = mixedMoment B raw26555step1 raw26555step1Labels := by
      have ha : raw26555step1 = (fun i j => raw26555step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26555step1 raw26555step0; decide +kernel
      have hl : raw26555step1Labels = raw26555step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26555step0 raw26555step0Labels permutation40 permutation5
    mixedMoment B raw26555step1 raw26555step1Labels = mixedMoment B raw26555step2 raw26555step2Labels := by
      have ha : raw26555step2 = -raw26555step1 := by apply Matrix.ext; change ∀ i j, raw26555step2 i j = -(raw26555step1 i j); unfold raw26555step2 raw26555step1; decide +kernel
      have hl : raw26555step2Labels = raw26555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26555step2 raw26555step2Labels = mixedMoment B raw26555step3 raw26555step3Labels := by
      have ha : raw26555step3 = raw26555step2 := by apply Matrix.ext; unfold raw26555step3 raw26555step2; decide +kernel
      have hl : raw26555step2Labels = labelEmbedding1 ∘ raw26555step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26555step2 raw26555step2Labels raw26555step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical26556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26556 raw26556Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26556 raw26556Labels = mixedMoment B raw26556step0 raw26556step0Labels := by
      have hz : ∀ j, raw26556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26556step0 = (fun i j => raw26556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26556step0 raw26556; decide +kernel
      have hl : raw26556step0Labels = raw26556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26556 raw26556Labels permutation265 hz
    mixedMoment B raw26556step0 raw26556step0Labels = mixedMoment B raw26556step1 raw26556step1Labels := by
      have ha : raw26556step1 = (fun i j => raw26556step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26556step1 raw26556step0; decide +kernel
      have hl : raw26556step1Labels = raw26556step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26556step0 raw26556step0Labels permutation46 permutation5
    mixedMoment B raw26556step1 raw26556step1Labels = mixedMoment B raw26556step2 raw26556step2Labels := by
      have ha : raw26556step2 = -raw26556step1 := by apply Matrix.ext; change ∀ i j, raw26556step2 i j = -(raw26556step1 i j); unfold raw26556step2 raw26556step1; decide +kernel
      have hl : raw26556step2Labels = raw26556step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26556step2 raw26556step2Labels = mixedMoment B raw26556step3 raw26556step3Labels := by
      have ha : raw26556step3 = raw26556step2 := by apply Matrix.ext; unfold raw26556step3 raw26556step2; decide +kernel
      have hl : raw26556step2Labels = labelEmbedding1 ∘ raw26556step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26556step2 raw26556step2Labels raw26556step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical26557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26557 raw26557Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26557 raw26557Labels = mixedMoment B raw26557step0 raw26557step0Labels := by
      have hz : ∀ j, raw26557 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26557step0 = (fun i j => raw26557 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26557step0 raw26557; decide +kernel
      have hl : raw26557step0Labels = raw26557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26557 raw26557Labels permutation265 hz
    mixedMoment B raw26557step0 raw26557step0Labels = mixedMoment B raw26557step1 raw26557step1Labels := by
      have ha : raw26557step1 = (fun i j => raw26557step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26557step1 raw26557step0; decide +kernel
      have hl : raw26557step1Labels = raw26557step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26557step0 raw26557step0Labels permutation53 permutation7
    mixedMoment B raw26557step1 raw26557step1Labels = mixedMoment B raw26557step2 raw26557step2Labels := by
      have ha : raw26557step2 = -raw26557step1 := by apply Matrix.ext; change ∀ i j, raw26557step2 i j = -(raw26557step1 i j); unfold raw26557step2 raw26557step1; decide +kernel
      have hl : raw26557step2Labels = raw26557step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26557step2 raw26557step2Labels = mixedMoment B raw26557step3 raw26557step3Labels := by
      have ha : raw26557step3 = raw26557step2 := by apply Matrix.ext; unfold raw26557step3 raw26557step2; decide +kernel
      have hl : raw26557step2Labels = labelEmbedding1 ∘ raw26557step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26557step2 raw26557step2Labels raw26557step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical26558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26558 raw26558Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw26558 raw26558Labels = mixedMoment B raw26558step0 raw26558step0Labels := by
      have hz : ∀ j, raw26558 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26558step0 = (fun i j => raw26558 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26558step0 raw26558; decide +kernel
      have hl : raw26558step0Labels = raw26558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26558 raw26558Labels permutation265 hz
    mixedMoment B raw26558step0 raw26558step0Labels = mixedMoment B raw26558step1 raw26558step1Labels := by
      have ha : raw26558step1 = (fun i j => raw26558step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26558step1 raw26558step0; decide +kernel
      have hl : raw26558step1Labels = raw26558step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26558step0 raw26558step0Labels permutation34 permutation5
    mixedMoment B raw26558step1 raw26558step1Labels = mixedMoment B raw26558step2 raw26558step2Labels := by
      have ha : raw26558step2 = -raw26558step1 := by apply Matrix.ext; change ∀ i j, raw26558step2 i j = -(raw26558step1 i j); unfold raw26558step2 raw26558step1; decide +kernel
      have hl : raw26558step2Labels = raw26558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26558step2 raw26558step2Labels = mixedMoment B raw26558step3 raw26558step3Labels := by
      have ha : raw26558step3 = raw26558step2 := by apply Matrix.ext; unfold raw26558step3 raw26558step2; decide +kernel
      have hl : raw26558step2Labels = labelEmbedding1 ∘ raw26558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26558step2 raw26558step2Labels raw26558step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

theorem canonical26559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26559 raw26559Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26559 raw26559Labels = mixedMoment B raw26559step0 raw26559step0Labels := by
      have ha : raw26559step0 = (fun i j => raw26559 (permutation154 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26559step0 raw26559; decide +kernel
      have hl : raw26559step0Labels = raw26559Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26559 raw26559Labels permutation154 permutation5
    mixedMoment B raw26559step0 raw26559step0Labels = mixedMoment B raw26559step1 raw26559step1Labels := by
      have ha : raw26559step1 = -raw26559step0 := by apply Matrix.ext; change ∀ i j, raw26559step1 i j = -(raw26559step0 i j); unfold raw26559step1 raw26559step0; decide +kernel
      have hl : raw26559step1Labels = raw26559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26559step1 raw26559step1Labels = mixedMoment B raw26559step2 raw26559step2Labels := by
      have ha : raw26559step2 = raw26559step1 := by apply Matrix.ext; unfold raw26559step2 raw26559step1; decide +kernel
      have hl : raw26559step1Labels = labelEmbedding1 ∘ raw26559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26559step1 raw26559step1Labels raw26559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical26560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26560 raw26560Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26560 raw26560Labels = mixedMoment B raw26560step0 raw26560step0Labels := by
      have hz : ∀ j, raw26560 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26560step0 = (fun i j => raw26560 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26560step0 raw26560; decide +kernel
      have hl : raw26560step0Labels = raw26560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26560 raw26560Labels permutation265 hz
    mixedMoment B raw26560step0 raw26560step0Labels = mixedMoment B raw26560step1 raw26560step1Labels := by
      have ha : raw26560step1 = (fun i j => raw26560step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26560step1 raw26560step0; decide +kernel
      have hl : raw26560step1Labels = raw26560step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26560step0 raw26560step0Labels permutation34 permutation5
    mixedMoment B raw26560step1 raw26560step1Labels = mixedMoment B raw26560step2 raw26560step2Labels := by
      have ha : raw26560step2 = -raw26560step1 := by apply Matrix.ext; change ∀ i j, raw26560step2 i j = -(raw26560step1 i j); unfold raw26560step2 raw26560step1; decide +kernel
      have hl : raw26560step2Labels = raw26560step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26560step2 raw26560step2Labels = mixedMoment B raw26560step3 raw26560step3Labels := by
      have ha : raw26560step3 = raw26560step2 := by apply Matrix.ext; unfold raw26560step3 raw26560step2; decide +kernel
      have hl : raw26560step2Labels = labelEmbedding1 ∘ raw26560step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26560step2 raw26560step2Labels raw26560step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical26561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26561 raw26561Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26561 raw26561Labels = mixedMoment B raw26561step0 raw26561step0Labels := by
      have hz : ∀ j, raw26561 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26561step0 = (fun i j => raw26561 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26561step0 raw26561; decide +kernel
      have hl : raw26561step0Labels = raw26561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26561 raw26561Labels permutation265 hz
    mixedMoment B raw26561step0 raw26561step0Labels = mixedMoment B raw26561step1 raw26561step1Labels := by
      have ha : raw26561step1 = (fun i j => raw26561step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26561step1 raw26561step0; decide +kernel
      have hl : raw26561step1Labels = raw26561step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26561step0 raw26561step0Labels permutation44 permutation5
    mixedMoment B raw26561step1 raw26561step1Labels = mixedMoment B raw26561step2 raw26561step2Labels := by
      have ha : raw26561step2 = -raw26561step1 := by apply Matrix.ext; change ∀ i j, raw26561step2 i j = -(raw26561step1 i j); unfold raw26561step2 raw26561step1; decide +kernel
      have hl : raw26561step2Labels = raw26561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26561step2 raw26561step2Labels = mixedMoment B raw26561step3 raw26561step3Labels := by
      have ha : raw26561step3 = raw26561step2 := by apply Matrix.ext; unfold raw26561step3 raw26561step2; decide +kernel
      have hl : raw26561step2Labels = labelEmbedding1 ∘ raw26561step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26561step2 raw26561step2Labels raw26561step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical26562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26562 raw26562Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26562 raw26562Labels = mixedMoment B raw26562step0 raw26562step0Labels := by
      have hz : ∀ j, raw26562 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26562step0 = (fun i j => raw26562 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26562step0 raw26562; decide +kernel
      have hl : raw26562step0Labels = raw26562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26562 raw26562Labels permutation265 hz
    mixedMoment B raw26562step0 raw26562step0Labels = mixedMoment B raw26562step1 raw26562step1Labels := by
      have ha : raw26562step1 = (fun i j => raw26562step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26562step1 raw26562step0; decide +kernel
      have hl : raw26562step1Labels = raw26562step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26562step0 raw26562step0Labels permutation51 permutation7
    mixedMoment B raw26562step1 raw26562step1Labels = mixedMoment B raw26562step2 raw26562step2Labels := by
      have ha : raw26562step2 = -raw26562step1 := by apply Matrix.ext; change ∀ i j, raw26562step2 i j = -(raw26562step1 i j); unfold raw26562step2 raw26562step1; decide +kernel
      have hl : raw26562step2Labels = raw26562step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26562step2 raw26562step2Labels = mixedMoment B raw26562step3 raw26562step3Labels := by
      have ha : raw26562step3 = raw26562step2 := by apply Matrix.ext; unfold raw26562step3 raw26562step2; decide +kernel
      have hl : raw26562step2Labels = labelEmbedding1 ∘ raw26562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26562step2 raw26562step2Labels raw26562step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical26563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26563 raw26563Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw26563 raw26563Labels = mixedMoment B raw26563step0 raw26563step0Labels := by
      have hz : ∀ j, raw26563 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26563step0 = (fun i j => raw26563 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26563step0 raw26563; decide +kernel
      have hl : raw26563step0Labels = raw26563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26563 raw26563Labels permutation265 hz
    mixedMoment B raw26563step0 raw26563step0Labels = mixedMoment B raw26563step1 raw26563step1Labels := by
      have ha : raw26563step1 = (fun i j => raw26563step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26563step1 raw26563step0; decide +kernel
      have hl : raw26563step1Labels = raw26563step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26563step0 raw26563step0Labels permutation32 permutation5
    mixedMoment B raw26563step1 raw26563step1Labels = mixedMoment B raw26563step2 raw26563step2Labels := by
      have ha : raw26563step2 = -raw26563step1 := by apply Matrix.ext; change ∀ i j, raw26563step2 i j = -(raw26563step1 i j); unfold raw26563step2 raw26563step1; decide +kernel
      have hl : raw26563step2Labels = raw26563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26563step2 raw26563step2Labels = mixedMoment B raw26563step3 raw26563step3Labels := by
      have ha : raw26563step3 = raw26563step2 := by apply Matrix.ext; unfold raw26563step3 raw26563step2; decide +kernel
      have hl : raw26563step2Labels = labelEmbedding1 ∘ raw26563step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26563step2 raw26563step2Labels raw26563step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

theorem canonical26564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26564 raw26564Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw26564 raw26564Labels = mixedMoment B raw26564step0 raw26564step0Labels := by
      have ha : raw26564step0 = (fun i j => raw26564 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26564step0 raw26564; decide +kernel
      have hl : raw26564step0Labels = raw26564Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26564 raw26564Labels permutation152 permutation5
    mixedMoment B raw26564step0 raw26564step0Labels = mixedMoment B raw26564step1 raw26564step1Labels := by
      have ha : raw26564step1 = -raw26564step0 := by apply Matrix.ext; change ∀ i j, raw26564step1 i j = -(raw26564step0 i j); unfold raw26564step1 raw26564step0; decide +kernel
      have hl : raw26564step1Labels = raw26564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26564step1 raw26564step1Labels = mixedMoment B raw26564step2 raw26564step2Labels := by
      have ha : raw26564step2 = raw26564step1 := by apply Matrix.ext; unfold raw26564step2 raw26564step1; decide +kernel
      have hl : raw26564step1Labels = labelEmbedding1 ∘ raw26564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26564step1 raw26564step1Labels raw26564step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

theorem canonical26565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26565 raw26565Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26565 raw26565Labels = mixedMoment B raw26565step0 raw26565step0Labels := by
      have hz : ∀ j, raw26565 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26565step0 = (fun i j => raw26565 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26565step0 raw26565; decide +kernel
      have hl : raw26565step0Labels = raw26565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26565 raw26565Labels permutation265 hz
    mixedMoment B raw26565step0 raw26565step0Labels = mixedMoment B raw26565step1 raw26565step1Labels := by
      have ha : raw26565step1 = (fun i j => raw26565step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26565step1 raw26565step0; decide +kernel
      have hl : raw26565step1Labels = raw26565step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26565step0 raw26565step0Labels permutation32 permutation5
    mixedMoment B raw26565step1 raw26565step1Labels = mixedMoment B raw26565step2 raw26565step2Labels := by
      have ha : raw26565step2 = -raw26565step1 := by apply Matrix.ext; change ∀ i j, raw26565step2 i j = -(raw26565step1 i j); unfold raw26565step2 raw26565step1; decide +kernel
      have hl : raw26565step2Labels = raw26565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26565step2 raw26565step2Labels = mixedMoment B raw26565step3 raw26565step3Labels := by
      have ha : raw26565step3 = raw26565step2 := by apply Matrix.ext; unfold raw26565step3 raw26565step2; decide +kernel
      have hl : raw26565step2Labels = labelEmbedding1 ∘ raw26565step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26565step2 raw26565step2Labels raw26565step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical26566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26566 raw26566Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw26566 raw26566Labels = mixedMoment B raw26566step0 raw26566step0Labels := by
      have hz : ∀ j, raw26566 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26566step0 = (fun i j => raw26566 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26566step0 raw26566; decide +kernel
      have hl : raw26566step0Labels = raw26566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26566 raw26566Labels permutation265 hz
    mixedMoment B raw26566step0 raw26566step0Labels = mixedMoment B raw26566step1 raw26566step1Labels := by
      have ha : raw26566step1 = (fun i j => raw26566step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26566step1 raw26566step0; decide +kernel
      have hl : raw26566step1Labels = raw26566step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26566step0 raw26566step0Labels permutation38 permutation5
    mixedMoment B raw26566step1 raw26566step1Labels = mixedMoment B raw26566step2 raw26566step2Labels := by
      have ha : raw26566step2 = -raw26566step1 := by apply Matrix.ext; change ∀ i j, raw26566step2 i j = -(raw26566step1 i j); unfold raw26566step2 raw26566step1; decide +kernel
      have hl : raw26566step2Labels = raw26566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26566step2 raw26566step2Labels = mixedMoment B raw26566step3 raw26566step3Labels := by
      have ha : raw26566step3 = raw26566step2 := by apply Matrix.ext; unfold raw26566step3 raw26566step2; decide +kernel
      have hl : raw26566step2Labels = labelEmbedding1 ∘ raw26566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26566step2 raw26566step2Labels raw26566step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical26567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26567 raw26567Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw26567 raw26567Labels = mixedMoment B raw26567step0 raw26567step0Labels := by
      have hz : ∀ j, raw26567 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26567step0 = (fun i j => raw26567 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26567step0 raw26567; decide +kernel
      have hl : raw26567step0Labels = raw26567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26567 raw26567Labels permutation265 hz
    mixedMoment B raw26567step0 raw26567step0Labels = mixedMoment B raw26567step1 raw26567step1Labels := by
      have ha : raw26567step1 = (fun i j => raw26567step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26567step1 raw26567step0; decide +kernel
      have hl : raw26567step1Labels = raw26567step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26567step0 raw26567step0Labels permutation50 permutation7
    mixedMoment B raw26567step1 raw26567step1Labels = mixedMoment B raw26567step2 raw26567step2Labels := by
      have ha : raw26567step2 = -raw26567step1 := by apply Matrix.ext; change ∀ i j, raw26567step2 i j = -(raw26567step1 i j); unfold raw26567step2 raw26567step1; decide +kernel
      have hl : raw26567step2Labels = raw26567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26567step2 raw26567step2Labels = mixedMoment B raw26567step3 raw26567step3Labels := by
      have ha : raw26567step3 = raw26567step2 := by apply Matrix.ext; unfold raw26567step3 raw26567step2; decide +kernel
      have hl : raw26567step2Labels = labelEmbedding1 ∘ raw26567step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26567step2 raw26567step2Labels raw26567step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical26568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26568 raw26568Labels = mixedMoment B node1503 node1503Labels := by
  calc
    mixedMoment B raw26568 raw26568Labels = mixedMoment B raw26568step0 raw26568step0Labels := by
      have hz : ∀ j, raw26568 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26568step0 = (fun i j => raw26568 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26568step0 raw26568; decide +kernel
      have hl : raw26568step0Labels = raw26568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26568 raw26568Labels permutation265 hz
    mixedMoment B raw26568step0 raw26568step0Labels = mixedMoment B raw26568step1 raw26568step1Labels := by
      have ha : raw26568step1 = (fun i j => raw26568step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26568step1 raw26568step0; decide +kernel
      have hl : raw26568step1Labels = raw26568step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26568step0 raw26568step0Labels permutation32 permutation5
    mixedMoment B raw26568step1 raw26568step1Labels = mixedMoment B raw26568step2 raw26568step2Labels := by
      have ha : raw26568step2 = -raw26568step1 := by apply Matrix.ext; change ∀ i j, raw26568step2 i j = -(raw26568step1 i j); unfold raw26568step2 raw26568step1; decide +kernel
      have hl : raw26568step2Labels = raw26568step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26568step2 raw26568step2Labels = mixedMoment B raw26568step3 raw26568step3Labels := by
      have ha : raw26568step3 = raw26568step2 := by apply Matrix.ext; unfold raw26568step3 raw26568step2; decide +kernel
      have hl : raw26568step2Labels = labelEmbedding1 ∘ raw26568step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26568step2 raw26568step2Labels raw26568step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1503 node1503Labels := by rfl

theorem canonical26569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26569 raw26569Labels = mixedMoment B node2688 node2688Labels := by
  calc
    mixedMoment B raw26569 raw26569Labels = mixedMoment B raw26569step0 raw26569step0Labels := by
      have ha : raw26569step0 = (fun i j => raw26569 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26569step0 raw26569; decide +kernel
      have hl : raw26569step0Labels = raw26569Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26569 raw26569Labels permutation640 permutation5
    mixedMoment B raw26569step0 raw26569step0Labels = mixedMoment B raw26569step1 raw26569step1Labels := by
      have ha : raw26569step1 = raw26569step0 := by apply Matrix.ext; unfold raw26569step1 raw26569step0; decide +kernel
      have hl : raw26569step0Labels = labelEmbedding1 ∘ raw26569step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26569step0 raw26569step0Labels raw26569step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2688 node2688Labels := by rfl

theorem canonical26570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26570 raw26570Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw26570 raw26570Labels = mixedMoment B raw26570step0 raw26570step0Labels := by
      have hz : ∀ j, raw26570 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26570step0 = (fun i j => raw26570 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26570step0 raw26570; decide +kernel
      have hl : raw26570step0Labels = raw26570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26570 raw26570Labels permutation265 hz
    mixedMoment B raw26570step0 raw26570step0Labels = mixedMoment B raw26570step1 raw26570step1Labels := by
      have ha : raw26570step1 = (fun i j => raw26570step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26570step1 raw26570step0; decide +kernel
      have hl : raw26570step1Labels = raw26570step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26570step0 raw26570step0Labels permutation137 permutation5
    mixedMoment B raw26570step1 raw26570step1Labels = mixedMoment B raw26570step2 raw26570step2Labels := by
      have ha : raw26570step2 = raw26570step1 := by apply Matrix.ext; unfold raw26570step2 raw26570step1; decide +kernel
      have hl : raw26570step1Labels = labelEmbedding1 ∘ raw26570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26570step1 raw26570step1Labels raw26570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical26571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26571 raw26571Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw26571 raw26571Labels = mixedMoment B raw26571step0 raw26571step0Labels := by
      have hz : ∀ j, raw26571 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26571step0 = (fun i j => raw26571 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26571step0 raw26571; decide +kernel
      have hl : raw26571step0Labels = raw26571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26571 raw26571Labels permutation265 hz
    mixedMoment B raw26571step0 raw26571step0Labels = mixedMoment B raw26571step1 raw26571step1Labels := by
      have ha : raw26571step1 = (fun i j => raw26571step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26571step1 raw26571step0; decide +kernel
      have hl : raw26571step1Labels = raw26571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26571step0 raw26571step0Labels permutation50 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

theorem canonical26572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26572 raw26572Labels = mixedMoment B node637 node637Labels := by
  calc
    mixedMoment B raw26572 raw26572Labels = mixedMoment B raw26572step0 raw26572step0Labels := by
      have ha : raw26572step0 = (fun i j => raw26572 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26572step0 raw26572; decide +kernel
      have hl : raw26572step0Labels = raw26572Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26572 raw26572Labels permutation246 permutation2
    _ = mixedMoment B node637 node637Labels := by rfl

theorem canonical26573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26573 raw26573Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw26573 raw26573Labels = mixedMoment B raw26573step0 raw26573step0Labels := by
      have hz : ∀ j, raw26573 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26573step0 = (fun i j => raw26573 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26573step0 raw26573; decide +kernel
      have hl : raw26573step0Labels = raw26573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26573 raw26573Labels permutation265 hz
    mixedMoment B raw26573step0 raw26573step0Labels = mixedMoment B raw26573step1 raw26573step1Labels := by
      have ha : raw26573step1 = (fun i j => raw26573step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26573step1 raw26573step0; decide +kernel
      have hl : raw26573step1Labels = raw26573step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26573step0 raw26573step0Labels permutation53 permutation2
    _ = mixedMoment B node640 node640Labels := by rfl

theorem canonical26574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26574 raw26574Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw26574 raw26574Labels = mixedMoment B raw26574step0 raw26574step0Labels := by
      have hz : ∀ j, raw26574 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26574step0 = (fun i j => raw26574 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26574step0 raw26574; decide +kernel
      have hl : raw26574step0Labels = raw26574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26574 raw26574Labels permutation265 hz
    mixedMoment B raw26574step0 raw26574step0Labels = mixedMoment B raw26574step1 raw26574step1Labels := by
      have ha : raw26574step1 = (fun i j => raw26574step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26574step1 raw26574step0; decide +kernel
      have hl : raw26574step1Labels = raw26574step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26574step0 raw26574step0Labels permutation51 permutation2
    _ = mixedMoment B node640 node640Labels := by rfl

theorem canonical26575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26575 raw26575Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw26575 raw26575Labels = mixedMoment B raw26575step0 raw26575step0Labels := by
      have hz : ∀ j, raw26575 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26575step0 = (fun i j => raw26575 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26575step0 raw26575; decide +kernel
      have hl : raw26575step0Labels = raw26575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26575 raw26575Labels permutation265 hz
    mixedMoment B raw26575step0 raw26575step0Labels = mixedMoment B raw26575step1 raw26575step1Labels := by
      have ha : raw26575step1 = (fun i j => raw26575step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26575step1 raw26575step0; decide +kernel
      have hl : raw26575step1Labels = raw26575step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26575step0 raw26575step0Labels permutation50 permutation2
    _ = mixedMoment B node640 node640Labels := by rfl

theorem canonical26576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26576 raw26576Labels = mixedMoment B node651 node651Labels := by
  calc
    mixedMoment B raw26576 raw26576Labels = mixedMoment B raw26576step0 raw26576step0Labels := by
      have hz : ∀ j, raw26576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26576step0 = (fun i j => raw26576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26576step0 raw26576; decide +kernel
      have hl : raw26576step0Labels = raw26576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26576 raw26576Labels permutation265 hz
    _ = mixedMoment B node651 node651Labels := by rfl

theorem canonical26607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26607 raw26607Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw26607 raw26607Labels = mixedMoment B raw26607step0 raw26607step0Labels := by
      have ha : raw26607step0 = (fun i j => raw26607 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26607step0 raw26607; decide +kernel
      have hl : raw26607step0Labels = raw26607Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26607 raw26607Labels permutation170 permutation7
    mixedMoment B raw26607step0 raw26607step0Labels = mixedMoment B raw26607step1 raw26607step1Labels := by
      have ha : raw26607step1 = raw26607step0 := by apply Matrix.ext; unfold raw26607step1 raw26607step0; decide +kernel
      have hl : raw26607step0Labels = labelEmbedding1 ∘ raw26607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26607step0 raw26607step0Labels raw26607step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1034 node1034Labels := by rfl

theorem canonical26608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26608 raw26608Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26608 raw26608Labels = mixedMoment B raw26608step0 raw26608step0Labels := by
      have hz : ∀ j, raw26608 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26608step0 = (fun i j => raw26608 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26608step0 raw26608; decide +kernel
      have hl : raw26608step0Labels = raw26608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26608 raw26608Labels permutation265 hz
    mixedMoment B raw26608step0 raw26608step0Labels = mixedMoment B raw26608step1 raw26608step1Labels := by
      have ha : raw26608step1 = (fun i j => raw26608step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26608step1 raw26608step0; decide +kernel
      have hl : raw26608step1Labels = raw26608step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26608step0 raw26608step0Labels permutation53 permutation7
    mixedMoment B raw26608step1 raw26608step1Labels = mixedMoment B raw26608step2 raw26608step2Labels := by
      have ha : raw26608step2 = raw26608step1 := by apply Matrix.ext; unfold raw26608step2 raw26608step1; decide +kernel
      have hl : raw26608step1Labels = labelEmbedding1 ∘ raw26608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26608step1 raw26608step1Labels raw26608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical26609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26609 raw26609Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26609 raw26609Labels = mixedMoment B raw26609step0 raw26609step0Labels := by
      have hz : ∀ j, raw26609 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26609step0 = (fun i j => raw26609 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26609step0 raw26609; decide +kernel
      have hl : raw26609step0Labels = raw26609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26609 raw26609Labels permutation265 hz
    mixedMoment B raw26609step0 raw26609step0Labels = mixedMoment B raw26609step1 raw26609step1Labels := by
      have ha : raw26609step1 = (fun i j => raw26609step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26609step1 raw26609step0; decide +kernel
      have hl : raw26609step1Labels = raw26609step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26609step0 raw26609step0Labels permutation51 permutation7
    mixedMoment B raw26609step1 raw26609step1Labels = mixedMoment B raw26609step2 raw26609step2Labels := by
      have ha : raw26609step2 = raw26609step1 := by apply Matrix.ext; unfold raw26609step2 raw26609step1; decide +kernel
      have hl : raw26609step1Labels = labelEmbedding1 ∘ raw26609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26609step1 raw26609step1Labels raw26609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical26610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26610 raw26610Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26610 raw26610Labels = mixedMoment B raw26610step0 raw26610step0Labels := by
      have hz : ∀ j, raw26610 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26610step0 = (fun i j => raw26610 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26610step0 raw26610; decide +kernel
      have hl : raw26610step0Labels = raw26610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26610 raw26610Labels permutation265 hz
    mixedMoment B raw26610step0 raw26610step0Labels = mixedMoment B raw26610step1 raw26610step1Labels := by
      have ha : raw26610step1 = (fun i j => raw26610step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26610step1 raw26610step0; decide +kernel
      have hl : raw26610step1Labels = raw26610step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26610step0 raw26610step0Labels permutation50 permutation7
    mixedMoment B raw26610step1 raw26610step1Labels = mixedMoment B raw26610step2 raw26610step2Labels := by
      have ha : raw26610step2 = raw26610step1 := by apply Matrix.ext; unfold raw26610step2 raw26610step1; decide +kernel
      have hl : raw26610step1Labels = labelEmbedding1 ∘ raw26610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26610step1 raw26610step1Labels raw26610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical26611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26611 raw26611Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw26611 raw26611Labels = mixedMoment B raw26611step0 raw26611step0Labels := by
      have hz : ∀ j, raw26611 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26611step0 = (fun i j => raw26611 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26611step0 raw26611; decide +kernel
      have hl : raw26611step0Labels = raw26611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26611 raw26611Labels permutation265 hz
    mixedMoment B raw26611step0 raw26611step0Labels = mixedMoment B raw26611step1 raw26611step1Labels := by
      have ha : raw26611step1 = (fun i j => raw26611step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26611step1 raw26611step0; decide +kernel
      have hl : raw26611step1Labels = raw26611step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26611step0 raw26611step0Labels permutation50 permutation7
    mixedMoment B raw26611step1 raw26611step1Labels = mixedMoment B raw26611step2 raw26611step2Labels := by
      have ha : raw26611step2 = raw26611step1 := by apply Matrix.ext; unfold raw26611step2 raw26611step1; decide +kernel
      have hl : raw26611step1Labels = labelEmbedding1 ∘ raw26611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26611step1 raw26611step1Labels raw26611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1081 node1081Labels := by rfl

theorem canonical26612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26612 raw26612Labels = mixedMoment B node1405 node1405Labels := by
  calc
    mixedMoment B raw26612 raw26612Labels = mixedMoment B raw26612step0 raw26612step0Labels := by
      have ha : raw26612step0 = (fun i j => raw26612 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26612step0 raw26612; decide +kernel
      have hl : raw26612step0Labels = raw26612Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26612 raw26612Labels permutation170 permutation7
    mixedMoment B raw26612step0 raw26612step0Labels = mixedMoment B raw26612step1 raw26612step1Labels := by
      have ha : raw26612step1 = raw26612step0 := by apply Matrix.ext; unfold raw26612step1 raw26612step0; decide +kernel
      have hl : raw26612step0Labels = labelEmbedding1 ∘ raw26612step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26612step0 raw26612step0Labels raw26612step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1405 node1405Labels := by rfl

theorem canonical26613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26613 raw26613Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw26613 raw26613Labels = mixedMoment B raw26613step0 raw26613step0Labels := by
      have ha : raw26613step0 = (fun i j => raw26613 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26613step0 raw26613; decide +kernel
      have hl : raw26613step0Labels = raw26613Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26613 raw26613Labels permutation173 permutation7
    mixedMoment B raw26613step0 raw26613step0Labels = mixedMoment B raw26613step1 raw26613step1Labels := by
      have ha : raw26613step1 = raw26613step0 := by apply Matrix.ext; unfold raw26613step1 raw26613step0; decide +kernel
      have hl : raw26613step0Labels = labelEmbedding1 ∘ raw26613step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26613step0 raw26613step0Labels raw26613step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1228 node1228Labels := by rfl

theorem canonical26614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26614 raw26614Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw26614 raw26614Labels = mixedMoment B raw26614step0 raw26614step0Labels := by
      have ha : raw26614step0 = (fun i j => raw26614 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26614step0 raw26614; decide +kernel
      have hl : raw26614step0Labels = raw26614Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26614 raw26614Labels permutation171 permutation7
    mixedMoment B raw26614step0 raw26614step0Labels = mixedMoment B raw26614step1 raw26614step1Labels := by
      have ha : raw26614step1 = raw26614step0 := by apply Matrix.ext; unfold raw26614step1 raw26614step0; decide +kernel
      have hl : raw26614step0Labels = labelEmbedding1 ∘ raw26614step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26614step0 raw26614step0Labels raw26614step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1228 node1228Labels := by rfl

theorem canonical26615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26615 raw26615Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw26615 raw26615Labels = mixedMoment B raw26615step0 raw26615step0Labels := by
      have ha : raw26615step0 = (fun i j => raw26615 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26615step0 raw26615; decide +kernel
      have hl : raw26615step0Labels = raw26615Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26615 raw26615Labels permutation170 permutation7
    mixedMoment B raw26615step0 raw26615step0Labels = mixedMoment B raw26615step1 raw26615step1Labels := by
      have ha : raw26615step1 = raw26615step0 := by apply Matrix.ext; unfold raw26615step1 raw26615step0; decide +kernel
      have hl : raw26615step0Labels = labelEmbedding1 ∘ raw26615step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26615step0 raw26615step0Labels raw26615step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1228 node1228Labels := by rfl

theorem canonical26616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26616 raw26616Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw26616 raw26616Labels = mixedMoment B raw26616step0 raw26616step0Labels := by
      have ha : raw26616step0 = (fun i j => raw26616 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26616step0 raw26616; decide +kernel
      have hl : raw26616step0Labels = raw26616Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26616 raw26616Labels permutation170 permutation7
    mixedMoment B raw26616step0 raw26616step0Labels = mixedMoment B raw26616step1 raw26616step1Labels := by
      have ha : raw26616step1 = raw26616step0 := by apply Matrix.ext; unfold raw26616step1 raw26616step0; decide +kernel
      have hl : raw26616step0Labels = labelEmbedding1 ∘ raw26616step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26616step0 raw26616step0Labels raw26616step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical26617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26617 raw26617Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw26617 raw26617Labels = mixedMoment B raw26617step0 raw26617step0Labels := by
      have hz : ∀ j, raw26617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26617step0 = (fun i j => raw26617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26617step0 raw26617; decide +kernel
      have hl : raw26617step0Labels = raw26617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26617 raw26617Labels permutation265 hz
    mixedMoment B raw26617step0 raw26617step0Labels = mixedMoment B raw26617step1 raw26617step1Labels := by
      have ha : raw26617step1 = (fun i j => raw26617step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26617step1 raw26617step0; decide +kernel
      have hl : raw26617step1Labels = raw26617step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26617step0 raw26617step0Labels permutation50 permutation7
    mixedMoment B raw26617step1 raw26617step1Labels = mixedMoment B raw26617step2 raw26617step2Labels := by
      have ha : raw26617step2 = raw26617step1 := by apply Matrix.ext; unfold raw26617step2 raw26617step1; decide +kernel
      have hl : raw26617step1Labels = labelEmbedding1 ∘ raw26617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26617step1 raw26617step1Labels raw26617step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1441 node1441Labels := by rfl

theorem canonical26618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26618 raw26618Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26618 raw26618Labels = mixedMoment B raw26618step0 raw26618step0Labels := by
      have ha : raw26618step0 = (fun i j => raw26618 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26618step0 raw26618; decide +kernel
      have hl : raw26618step0Labels = raw26618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26618 raw26618Labels permutation170 permutation7
    mixedMoment B raw26618step0 raw26618step0Labels = mixedMoment B raw26618step1 raw26618step1Labels := by
      have ha : raw26618step1 = raw26618step0 := by apply Matrix.ext; unfold raw26618step1 raw26618step0; decide +kernel
      have hl : raw26618step0Labels = labelEmbedding1 ∘ raw26618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26618step0 raw26618step0Labels raw26618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical26619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26619 raw26619Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26619 raw26619Labels = mixedMoment B raw26619step0 raw26619step0Labels := by
      have hz : ∀ j, raw26619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26619step0 = (fun i j => raw26619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26619step0 raw26619; decide +kernel
      have hl : raw26619step0Labels = raw26619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26619 raw26619Labels permutation265 hz
    mixedMoment B raw26619step0 raw26619step0Labels = mixedMoment B raw26619step1 raw26619step1Labels := by
      have ha : raw26619step1 = (fun i j => raw26619step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26619step1 raw26619step0; decide +kernel
      have hl : raw26619step1Labels = raw26619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26619step0 raw26619step0Labels permutation51 permutation7
    mixedMoment B raw26619step1 raw26619step1Labels = mixedMoment B raw26619step2 raw26619step2Labels := by
      have ha : raw26619step2 = raw26619step1 := by apply Matrix.ext; unfold raw26619step2 raw26619step1; decide +kernel
      have hl : raw26619step1Labels = labelEmbedding1 ∘ raw26619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26619step1 raw26619step1Labels raw26619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical26620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26620 raw26620Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26620 raw26620Labels = mixedMoment B raw26620step0 raw26620step0Labels := by
      have hz : ∀ j, raw26620 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26620step0 = (fun i j => raw26620 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26620step0 raw26620; decide +kernel
      have hl : raw26620step0Labels = raw26620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26620 raw26620Labels permutation265 hz
    mixedMoment B raw26620step0 raw26620step0Labels = mixedMoment B raw26620step1 raw26620step1Labels := by
      have ha : raw26620step1 = (fun i j => raw26620step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26620step1 raw26620step0; decide +kernel
      have hl : raw26620step1Labels = raw26620step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26620step0 raw26620step0Labels permutation50 permutation7
    mixedMoment B raw26620step1 raw26620step1Labels = mixedMoment B raw26620step2 raw26620step2Labels := by
      have ha : raw26620step2 = raw26620step1 := by apply Matrix.ext; unfold raw26620step2 raw26620step1; decide +kernel
      have hl : raw26620step1Labels = labelEmbedding1 ∘ raw26620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26620step1 raw26620step1Labels raw26620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical26621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26621 raw26621Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26621 raw26621Labels = mixedMoment B raw26621step0 raw26621step0Labels := by
      have hz : ∀ j, raw26621 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26621step0 = (fun i j => raw26621 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26621step0 raw26621; decide +kernel
      have hl : raw26621step0Labels = raw26621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26621 raw26621Labels permutation265 hz
    mixedMoment B raw26621step0 raw26621step0Labels = mixedMoment B raw26621step1 raw26621step1Labels := by
      have ha : raw26621step1 = (fun i j => raw26621step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26621step1 raw26621step0; decide +kernel
      have hl : raw26621step1Labels = raw26621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26621step0 raw26621step0Labels permutation36 permutation7
    mixedMoment B raw26621step1 raw26621step1Labels = mixedMoment B raw26621step2 raw26621step2Labels := by
      have ha : raw26621step2 = raw26621step1 := by apply Matrix.ext; unfold raw26621step2 raw26621step1; decide +kernel
      have hl : raw26621step1Labels = labelEmbedding1 ∘ raw26621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26621step1 raw26621step1Labels raw26621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical26622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26622 raw26622Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw26622 raw26622Labels = mixedMoment B raw26622step0 raw26622step0Labels := by
      have hz : ∀ j, raw26622 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26622step0 = (fun i j => raw26622 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26622step0 raw26622; decide +kernel
      have hl : raw26622step0Labels = raw26622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26622 raw26622Labels permutation265 hz
    mixedMoment B raw26622step0 raw26622step0Labels = mixedMoment B raw26622step1 raw26622step1Labels := by
      have ha : raw26622step1 = (fun i j => raw26622step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26622step1 raw26622step0; decide +kernel
      have hl : raw26622step1Labels = raw26622step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26622step0 raw26622step0Labels permutation52 permutation7
    mixedMoment B raw26622step1 raw26622step1Labels = mixedMoment B raw26622step2 raw26622step2Labels := by
      have ha : raw26622step2 = raw26622step1 := by apply Matrix.ext; unfold raw26622step2 raw26622step1; decide +kernel
      have hl : raw26622step1Labels = labelEmbedding1 ∘ raw26622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26622step1 raw26622step1Labels raw26622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1441 node1441Labels := by rfl

theorem canonical26623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26623 raw26623Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26623 raw26623Labels = mixedMoment B raw26623step0 raw26623step0Labels := by
      have ha : raw26623step0 = (fun i j => raw26623 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26623step0 raw26623; decide +kernel
      have hl : raw26623step0Labels = raw26623Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26623 raw26623Labels permutation172 permutation7
    mixedMoment B raw26623step0 raw26623step0Labels = mixedMoment B raw26623step1 raw26623step1Labels := by
      have ha : raw26623step1 = raw26623step0 := by apply Matrix.ext; unfold raw26623step1 raw26623step0; decide +kernel
      have hl : raw26623step0Labels = labelEmbedding1 ∘ raw26623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26623step0 raw26623step0Labels raw26623step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1260 node1260Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical208
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26624 raw26624Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26624 raw26624Labels = mixedMoment B raw26624step0 raw26624step0Labels := by
      have hz : ∀ j, raw26624 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26624step0 = (fun i j => raw26624 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26624step0 raw26624; decide +kernel
      have hl : raw26624step0Labels = raw26624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26624 raw26624Labels permutation265 hz
    mixedMoment B raw26624step0 raw26624step0Labels = mixedMoment B raw26624step1 raw26624step1Labels := by
      have ha : raw26624step1 = (fun i j => raw26624step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26624step1 raw26624step0; decide +kernel
      have hl : raw26624step1Labels = raw26624step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26624step0 raw26624step0Labels permutation53 permutation7
    mixedMoment B raw26624step1 raw26624step1Labels = mixedMoment B raw26624step2 raw26624step2Labels := by
      have ha : raw26624step2 = raw26624step1 := by apply Matrix.ext; unfold raw26624step2 raw26624step1; decide +kernel
      have hl : raw26624step1Labels = labelEmbedding1 ∘ raw26624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26624step1 raw26624step1Labels raw26624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical26625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26625 raw26625Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26625 raw26625Labels = mixedMoment B raw26625step0 raw26625step0Labels := by
      have hz : ∀ j, raw26625 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26625step0 = (fun i j => raw26625 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26625step0 raw26625; decide +kernel
      have hl : raw26625step0Labels = raw26625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26625 raw26625Labels permutation265 hz
    mixedMoment B raw26625step0 raw26625step0Labels = mixedMoment B raw26625step1 raw26625step1Labels := by
      have ha : raw26625step1 = (fun i j => raw26625step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26625step1 raw26625step0; decide +kernel
      have hl : raw26625step1Labels = raw26625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26625step0 raw26625step0Labels permutation52 permutation7
    mixedMoment B raw26625step1 raw26625step1Labels = mixedMoment B raw26625step2 raw26625step2Labels := by
      have ha : raw26625step2 = raw26625step1 := by apply Matrix.ext; unfold raw26625step2 raw26625step1; decide +kernel
      have hl : raw26625step1Labels = labelEmbedding1 ∘ raw26625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26625step1 raw26625step1Labels raw26625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical26626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26626 raw26626Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26626 raw26626Labels = mixedMoment B raw26626step0 raw26626step0Labels := by
      have hz : ∀ j, raw26626 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26626step0 = (fun i j => raw26626 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26626step0 raw26626; decide +kernel
      have hl : raw26626step0Labels = raw26626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26626 raw26626Labels permutation265 hz
    mixedMoment B raw26626step0 raw26626step0Labels = mixedMoment B raw26626step1 raw26626step1Labels := by
      have ha : raw26626step1 = (fun i j => raw26626step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26626step1 raw26626step0; decide +kernel
      have hl : raw26626step1Labels = raw26626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26626step0 raw26626step0Labels permutation42 permutation7
    mixedMoment B raw26626step1 raw26626step1Labels = mixedMoment B raw26626step2 raw26626step2Labels := by
      have ha : raw26626step2 = raw26626step1 := by apply Matrix.ext; unfold raw26626step2 raw26626step1; decide +kernel
      have hl : raw26626step1Labels = labelEmbedding1 ∘ raw26626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26626step1 raw26626step1Labels raw26626step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical26627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26627 raw26627Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw26627 raw26627Labels = mixedMoment B raw26627step0 raw26627step0Labels := by
      have hz : ∀ j, raw26627 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26627step0 = (fun i j => raw26627 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26627step0 raw26627; decide +kernel
      have hl : raw26627step0Labels = raw26627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26627 raw26627Labels permutation265 hz
    mixedMoment B raw26627step0 raw26627step0Labels = mixedMoment B raw26627step1 raw26627step1Labels := by
      have ha : raw26627step1 = (fun i j => raw26627step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26627step1 raw26627step0; decide +kernel
      have hl : raw26627step1Labels = raw26627step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26627step0 raw26627step0Labels permutation54 permutation7
    mixedMoment B raw26627step1 raw26627step1Labels = mixedMoment B raw26627step2 raw26627step2Labels := by
      have ha : raw26627step2 = raw26627step1 := by apply Matrix.ext; unfold raw26627step2 raw26627step1; decide +kernel
      have hl : raw26627step1Labels = labelEmbedding1 ∘ raw26627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26627step1 raw26627step1Labels raw26627step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1441 node1441Labels := by rfl

theorem canonical26628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26628 raw26628Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw26628 raw26628Labels = mixedMoment B raw26628step0 raw26628step0Labels := by
      have ha : raw26628step0 = (fun i j => raw26628 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26628step0 raw26628; decide +kernel
      have hl : raw26628step0Labels = raw26628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26628 raw26628Labels permutation174 permutation7
    mixedMoment B raw26628step0 raw26628step0Labels = mixedMoment B raw26628step1 raw26628step1Labels := by
      have ha : raw26628step1 = raw26628step0 := by apply Matrix.ext; unfold raw26628step1 raw26628step0; decide +kernel
      have hl : raw26628step0Labels = labelEmbedding1 ∘ raw26628step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26628step0 raw26628step0Labels raw26628step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical26629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26629 raw26629Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26629 raw26629Labels = mixedMoment B raw26629step0 raw26629step0Labels := by
      have hz : ∀ j, raw26629 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26629step0 = (fun i j => raw26629 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26629step0 raw26629; decide +kernel
      have hl : raw26629step0Labels = raw26629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26629 raw26629Labels permutation265 hz
    mixedMoment B raw26629step0 raw26629step0Labels = mixedMoment B raw26629step1 raw26629step1Labels := by
      have ha : raw26629step1 = (fun i j => raw26629step0 (permutation55 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26629step1 raw26629step0; decide +kernel
      have hl : raw26629step1Labels = raw26629step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26629step0 raw26629step0Labels permutation55 permutation7
    mixedMoment B raw26629step1 raw26629step1Labels = mixedMoment B raw26629step2 raw26629step2Labels := by
      have ha : raw26629step2 = raw26629step1 := by apply Matrix.ext; unfold raw26629step2 raw26629step1; decide +kernel
      have hl : raw26629step1Labels = labelEmbedding1 ∘ raw26629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26629step1 raw26629step1Labels raw26629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical26630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26630 raw26630Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw26630 raw26630Labels = mixedMoment B raw26630step0 raw26630step0Labels := by
      have hz : ∀ j, raw26630 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26630step0 = (fun i j => raw26630 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26630step0 raw26630; decide +kernel
      have hl : raw26630step0Labels = raw26630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26630 raw26630Labels permutation265 hz
    mixedMoment B raw26630step0 raw26630step0Labels = mixedMoment B raw26630step1 raw26630step1Labels := by
      have ha : raw26630step1 = (fun i j => raw26630step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26630step1 raw26630step0; decide +kernel
      have hl : raw26630step1Labels = raw26630step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26630step0 raw26630step0Labels permutation54 permutation7
    mixedMoment B raw26630step1 raw26630step1Labels = mixedMoment B raw26630step2 raw26630step2Labels := by
      have ha : raw26630step2 = raw26630step1 := by apply Matrix.ext; unfold raw26630step2 raw26630step1; decide +kernel
      have hl : raw26630step1Labels = labelEmbedding1 ∘ raw26630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26630step1 raw26630step1Labels raw26630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical26631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26631 raw26631Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw26631 raw26631Labels = mixedMoment B raw26631step0 raw26631step0Labels := by
      have hz : ∀ j, raw26631 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26631step0 = (fun i j => raw26631 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26631step0 raw26631; decide +kernel
      have hl : raw26631step0Labels = raw26631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26631 raw26631Labels permutation265 hz
    mixedMoment B raw26631step0 raw26631step0Labels = mixedMoment B raw26631step1 raw26631step1Labels := by
      have ha : raw26631step1 = (fun i j => raw26631step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26631step1 raw26631step0; decide +kernel
      have hl : raw26631step1Labels = raw26631step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26631step0 raw26631step0Labels permutation48 permutation7
    mixedMoment B raw26631step1 raw26631step1Labels = mixedMoment B raw26631step2 raw26631step2Labels := by
      have ha : raw26631step2 = raw26631step1 := by apply Matrix.ext; unfold raw26631step2 raw26631step1; decide +kernel
      have hl : raw26631step1Labels = labelEmbedding1 ∘ raw26631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26631step1 raw26631step1Labels raw26631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical26632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26632 raw26632Labels = mixedMoment B node1435 node1435Labels := by
  calc
    mixedMoment B raw26632 raw26632Labels = mixedMoment B raw26632step0 raw26632step0Labels := by
      have hz : ∀ j, raw26632 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26632step0 = (fun i j => raw26632 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26632step0 raw26632; decide +kernel
      have hl : raw26632step0Labels = raw26632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26632 raw26632Labels permutation265 hz
    mixedMoment B raw26632step0 raw26632step0Labels = mixedMoment B raw26632step1 raw26632step1Labels := by
      have ha : raw26632step1 = (fun i j => raw26632step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26632step1 raw26632step0; decide +kernel
      have hl : raw26632step1Labels = raw26632step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26632step0 raw26632step0Labels permutation50 permutation7
    mixedMoment B raw26632step1 raw26632step1Labels = mixedMoment B raw26632step2 raw26632step2Labels := by
      have ha : raw26632step2 = raw26632step1 := by apply Matrix.ext; unfold raw26632step2 raw26632step1; decide +kernel
      have hl : raw26632step1Labels = labelEmbedding1 ∘ raw26632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26632step1 raw26632step1Labels raw26632step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1435 node1435Labels := by rfl

theorem canonical26633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26633 raw26633Labels = mixedMoment B node1256 node1256Labels := by
  calc
    mixedMoment B raw26633 raw26633Labels = mixedMoment B raw26633step0 raw26633step0Labels := by
      have ha : raw26633step0 = (fun i j => raw26633 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26633step0 raw26633; decide +kernel
      have hl : raw26633step0Labels = raw26633Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26633 raw26633Labels permutation170 permutation7
    mixedMoment B raw26633step0 raw26633step0Labels = mixedMoment B raw26633step1 raw26633step1Labels := by
      have ha : raw26633step1 = raw26633step0 := by apply Matrix.ext; unfold raw26633step1 raw26633step0; decide +kernel
      have hl : raw26633step0Labels = labelEmbedding1 ∘ raw26633step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26633step0 raw26633step0Labels raw26633step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1256 node1256Labels := by rfl

theorem canonical26634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26634 raw26634Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw26634 raw26634Labels = mixedMoment B raw26634step0 raw26634step0Labels := by
      have hz : ∀ j, raw26634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26634step0 = (fun i j => raw26634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26634step0 raw26634; decide +kernel
      have hl : raw26634step0Labels = raw26634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26634 raw26634Labels permutation265 hz
    mixedMoment B raw26634step0 raw26634step0Labels = mixedMoment B raw26634step1 raw26634step1Labels := by
      have ha : raw26634step1 = (fun i j => raw26634step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26634step1 raw26634step0; decide +kernel
      have hl : raw26634step1Labels = raw26634step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26634step0 raw26634step0Labels permutation53 permutation7
    mixedMoment B raw26634step1 raw26634step1Labels = mixedMoment B raw26634step2 raw26634step2Labels := by
      have ha : raw26634step2 = raw26634step1 := by apply Matrix.ext; unfold raw26634step2 raw26634step1; decide +kernel
      have hl : raw26634step1Labels = labelEmbedding1 ∘ raw26634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26634step1 raw26634step1Labels raw26634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1286 node1286Labels := by rfl

theorem canonical26635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26635 raw26635Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw26635 raw26635Labels = mixedMoment B raw26635step0 raw26635step0Labels := by
      have hz : ∀ j, raw26635 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26635step0 = (fun i j => raw26635 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26635step0 raw26635; decide +kernel
      have hl : raw26635step0Labels = raw26635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26635 raw26635Labels permutation265 hz
    mixedMoment B raw26635step0 raw26635step0Labels = mixedMoment B raw26635step1 raw26635step1Labels := by
      have ha : raw26635step1 = (fun i j => raw26635step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26635step1 raw26635step0; decide +kernel
      have hl : raw26635step1Labels = raw26635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26635step0 raw26635step0Labels permutation51 permutation7
    mixedMoment B raw26635step1 raw26635step1Labels = mixedMoment B raw26635step2 raw26635step2Labels := by
      have ha : raw26635step2 = raw26635step1 := by apply Matrix.ext; unfold raw26635step2 raw26635step1; decide +kernel
      have hl : raw26635step1Labels = labelEmbedding1 ∘ raw26635step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26635step1 raw26635step1Labels raw26635step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1286 node1286Labels := by rfl

theorem canonical26636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26636 raw26636Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw26636 raw26636Labels = mixedMoment B raw26636step0 raw26636step0Labels := by
      have hz : ∀ j, raw26636 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26636step0 = (fun i j => raw26636 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26636step0 raw26636; decide +kernel
      have hl : raw26636step0Labels = raw26636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26636 raw26636Labels permutation265 hz
    mixedMoment B raw26636step0 raw26636step0Labels = mixedMoment B raw26636step1 raw26636step1Labels := by
      have ha : raw26636step1 = (fun i j => raw26636step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26636step1 raw26636step0; decide +kernel
      have hl : raw26636step1Labels = raw26636step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26636step0 raw26636step0Labels permutation50 permutation7
    mixedMoment B raw26636step1 raw26636step1Labels = mixedMoment B raw26636step2 raw26636step2Labels := by
      have ha : raw26636step2 = raw26636step1 := by apply Matrix.ext; unfold raw26636step2 raw26636step1; decide +kernel
      have hl : raw26636step1Labels = labelEmbedding1 ∘ raw26636step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26636step1 raw26636step1Labels raw26636step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1286 node1286Labels := by rfl

theorem canonical26637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26637 raw26637Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw26637 raw26637Labels = mixedMoment B raw26637step0 raw26637step0Labels := by
      have hz : ∀ j, raw26637 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26637step0 = (fun i j => raw26637 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26637step0 raw26637; decide +kernel
      have hl : raw26637step0Labels = raw26637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26637 raw26637Labels permutation265 hz
    mixedMoment B raw26637step0 raw26637step0Labels = mixedMoment B raw26637step1 raw26637step1Labels := by
      have ha : raw26637step1 = (fun i j => raw26637step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26637step1 raw26637step0; decide +kernel
      have hl : raw26637step1Labels = raw26637step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26637step0 raw26637step0Labels permutation51 permutation2
    mixedMoment B raw26637step1 raw26637step1Labels = mixedMoment B raw26637step2 raw26637step2Labels := by
      have ha : raw26637step2 = -raw26637step1 := by apply Matrix.ext; change ∀ i j, raw26637step2 i j = -(raw26637step1 i j); unfold raw26637step2 raw26637step1; decide +kernel
      have hl : raw26637step2Labels = raw26637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1648 node1648Labels := by rfl

theorem canonical26638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26638 raw26638Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw26638 raw26638Labels = mixedMoment B raw26638step0 raw26638step0Labels := by
      have hz : ∀ j, raw26638 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26638step0 = (fun i j => raw26638 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26638step0 raw26638; decide +kernel
      have hl : raw26638step0Labels = raw26638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26638 raw26638Labels permutation265 hz
    mixedMoment B raw26638step0 raw26638step0Labels = mixedMoment B raw26638step1 raw26638step1Labels := by
      have ha : raw26638step1 = (fun i j => raw26638step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26638step1 raw26638step0; decide +kernel
      have hl : raw26638step1Labels = raw26638step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26638step0 raw26638step0Labels permutation50 permutation2
    mixedMoment B raw26638step1 raw26638step1Labels = mixedMoment B raw26638step2 raw26638step2Labels := by
      have ha : raw26638step2 = -raw26638step1 := by apply Matrix.ext; change ∀ i j, raw26638step2 i j = -(raw26638step1 i j); unfold raw26638step2 raw26638step1; decide +kernel
      have hl : raw26638step2Labels = raw26638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1648 node1648Labels := by rfl

theorem canonical26639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26639 raw26639Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw26639 raw26639Labels = mixedMoment B raw26639step0 raw26639step0Labels := by
      have hz : ∀ j, raw26639 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26639step0 = (fun i j => raw26639 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26639step0 raw26639; decide +kernel
      have hl : raw26639step0Labels = raw26639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26639 raw26639Labels permutation265 hz
    mixedMoment B raw26639step0 raw26639step0Labels = mixedMoment B raw26639step1 raw26639step1Labels := by
      have ha : raw26639step1 = (fun i j => raw26639step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26639step1 raw26639step0; decide +kernel
      have hl : raw26639step1Labels = raw26639step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26639step0 raw26639step0Labels permutation50 permutation2
    mixedMoment B raw26639step1 raw26639step1Labels = mixedMoment B raw26639step2 raw26639step2Labels := by
      have ha : raw26639step2 = -raw26639step1 := by apply Matrix.ext; change ∀ i j, raw26639step2 i j = -(raw26639step1 i j); unfold raw26639step2 raw26639step1; decide +kernel
      have hl : raw26639step2Labels = raw26639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1726 node1726Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9262 raw9262Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw9262 raw9262Labels = mixedMoment B raw9262step0 raw9262step0Labels := by
      have hz : ∀ j, raw9262 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9262step0 = (fun i j => raw9262 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9262step0 raw9262; decide +kernel
      have hl : raw9262step0Labels = raw9262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9262 raw9262Labels permutation265 hz
    mixedMoment B raw9262step0 raw9262step0Labels = mixedMoment B raw9262step1 raw9262step1Labels := by
      have ha : raw9262step1 = (fun i j => raw9262step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9262step1 raw9262step0; decide +kernel
      have hl : raw9262step1Labels = raw9262step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9262step0 raw9262step0Labels permutation38 permutation3
    mixedMoment B raw9262step1 raw9262step1Labels = mixedMoment B raw9262step2 raw9262step2Labels := by
      have ha : raw9262step2 = raw9262step1 := by apply Matrix.ext; unfold raw9262step2 raw9262step1; decide +kernel
      have hl : raw9262step1Labels = labelEmbedding6 ∘ raw9262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9262step1 raw9262step1Labels raw9262step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

theorem canonical9266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9266 raw9266Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9266 raw9266Labels = mixedMoment B raw9266step0 raw9266step0Labels := by
      have hz : ∀ j, raw9266 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9266step0 = (fun i j => raw9266 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9266step0 raw9266; decide +kernel
      have hl : raw9266step0Labels = raw9266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9266 raw9266Labels permutation265 hz
    mixedMoment B raw9266step0 raw9266step0Labels = mixedMoment B raw9266step1 raw9266step1Labels := by
      have ha : raw9266step1 = (fun i j => raw9266step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9266step1 raw9266step0; decide +kernel
      have hl : raw9266step1Labels = raw9266step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9266step0 raw9266step0Labels permutation42 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical9267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9267 raw9267Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw9267 raw9267Labels = mixedMoment B raw9267step0 raw9267step0Labels := by
      have hz : ∀ j, raw9267 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9267step0 = (fun i j => raw9267 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9267step0 raw9267; decide +kernel
      have hl : raw9267step0Labels = raw9267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9267 raw9267Labels permutation265 hz
    mixedMoment B raw9267step0 raw9267step0Labels = mixedMoment B raw9267step1 raw9267step1Labels := by
      have ha : raw9267step1 = (fun i j => raw9267step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9267step1 raw9267step0; decide +kernel
      have hl : raw9267step1Labels = raw9267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9267step0 raw9267step0Labels permutation32 permutation3
    mixedMoment B raw9267step1 raw9267step1Labels = mixedMoment B raw9267step2 raw9267step2Labels := by
      have ha : raw9267step2 = raw9267step1 := by apply Matrix.ext; unfold raw9267step2 raw9267step1; decide +kernel
      have hl : raw9267step1Labels = labelEmbedding6 ∘ raw9267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9267step1 raw9267step1Labels raw9267step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

theorem canonical9271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9271 raw9271Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9271 raw9271Labels = mixedMoment B raw9271step0 raw9271step0Labels := by
      have hz : ∀ j, raw9271 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9271step0 = (fun i j => raw9271 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9271step0 raw9271; decide +kernel
      have hl : raw9271step0Labels = raw9271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9271 raw9271Labels permutation265 hz
    mixedMoment B raw9271step0 raw9271step0Labels = mixedMoment B raw9271step1 raw9271step1Labels := by
      have ha : raw9271step1 = (fun i j => raw9271step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9271step1 raw9271step0; decide +kernel
      have hl : raw9271step1Labels = raw9271step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9271step0 raw9271step0Labels permutation36 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical9322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9322 raw9322Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw9322 raw9322Labels = mixedMoment B raw9322step0 raw9322step0Labels := by
      have hz : ∀ j, raw9322 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9322step0 = (fun i j => raw9322 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9322step0 raw9322; decide +kernel
      have hl : raw9322step0Labels = raw9322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9322 raw9322Labels permutation265 hz
    mixedMoment B raw9322step0 raw9322step0Labels = mixedMoment B raw9322step1 raw9322step1Labels := by
      have ha : raw9322step1 = (fun i j => raw9322step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9322step1 raw9322step0; decide +kernel
      have hl : raw9322step1Labels = raw9322step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9322step0 raw9322step0Labels permutation139 permutation5
    mixedMoment B raw9322step1 raw9322step1Labels = mixedMoment B raw9322step2 raw9322step2Labels := by
      have ha : raw9322step2 = raw9322step1 := by apply Matrix.ext; unfold raw9322step2 raw9322step1; decide +kernel
      have hl : raw9322step1Labels = labelEmbedding1 ∘ raw9322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9322step1 raw9322step1Labels raw9322step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical9326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9326 raw9326Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9326 raw9326Labels = mixedMoment B raw9326step0 raw9326step0Labels := by
      have hz : ∀ j, raw9326 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9326step0 = (fun i j => raw9326 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9326step0 raw9326; decide +kernel
      have hl : raw9326step0Labels = raw9326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9326 raw9326Labels permutation265 hz
    mixedMoment B raw9326step0 raw9326step0Labels = mixedMoment B raw9326step1 raw9326step1Labels := by
      have ha : raw9326step1 = (fun i j => raw9326step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9326step1 raw9326step0; decide +kernel
      have hl : raw9326step1Labels = raw9326step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9326step0 raw9326step0Labels permutation52 permutation7
    mixedMoment B raw9326step1 raw9326step1Labels = mixedMoment B raw9326step2 raw9326step2Labels := by
      have ha : raw9326step2 = -raw9326step1 := by apply Matrix.ext; change ∀ i j, raw9326step2 i j = -(raw9326step1 i j); unfold raw9326step2 raw9326step1; decide +kernel
      have hl : raw9326step2Labels = raw9326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9326step2 raw9326step2Labels = mixedMoment B raw9326step3 raw9326step3Labels := by
      have ha : raw9326step3 = raw9326step2 := by apply Matrix.ext; unfold raw9326step3 raw9326step2; decide +kernel
      have hl : raw9326step2Labels = labelEmbedding1 ∘ raw9326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9326step2 raw9326step2Labels raw9326step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical9327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9327 raw9327Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw9327 raw9327Labels = mixedMoment B raw9327step0 raw9327step0Labels := by
      have hz : ∀ j, raw9327 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9327step0 = (fun i j => raw9327 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9327step0 raw9327; decide +kernel
      have hl : raw9327step0Labels = raw9327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9327 raw9327Labels permutation265 hz
    mixedMoment B raw9327step0 raw9327step0Labels = mixedMoment B raw9327step1 raw9327step1Labels := by
      have ha : raw9327step1 = (fun i j => raw9327step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9327step1 raw9327step0; decide +kernel
      have hl : raw9327step1Labels = raw9327step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9327step0 raw9327step0Labels permutation145 permutation5
    mixedMoment B raw9327step1 raw9327step1Labels = mixedMoment B raw9327step2 raw9327step2Labels := by
      have ha : raw9327step2 = raw9327step1 := by apply Matrix.ext; unfold raw9327step2 raw9327step1; decide +kernel
      have hl : raw9327step1Labels = labelEmbedding1 ∘ raw9327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9327step1 raw9327step1Labels raw9327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical9331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9331 raw9331Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9331 raw9331Labels = mixedMoment B raw9331step0 raw9331step0Labels := by
      have hz : ∀ j, raw9331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9331step0 = (fun i j => raw9331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9331step0 raw9331; decide +kernel
      have hl : raw9331step0Labels = raw9331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9331 raw9331Labels permutation265 hz
    mixedMoment B raw9331step0 raw9331step0Labels = mixedMoment B raw9331step1 raw9331step1Labels := by
      have ha : raw9331step1 = (fun i j => raw9331step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9331step1 raw9331step0; decide +kernel
      have hl : raw9331step1Labels = raw9331step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9331step0 raw9331step0Labels permutation50 permutation7
    mixedMoment B raw9331step1 raw9331step1Labels = mixedMoment B raw9331step2 raw9331step2Labels := by
      have ha : raw9331step2 = -raw9331step1 := by apply Matrix.ext; change ∀ i j, raw9331step2 i j = -(raw9331step1 i j); unfold raw9331step2 raw9331step1; decide +kernel
      have hl : raw9331step2Labels = raw9331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9331step2 raw9331step2Labels = mixedMoment B raw9331step3 raw9331step3Labels := by
      have ha : raw9331step3 = raw9331step2 := by apply Matrix.ext; unfold raw9331step3 raw9331step2; decide +kernel
      have hl : raw9331step2Labels = labelEmbedding1 ∘ raw9331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9331step2 raw9331step2Labels raw9331step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9348 raw9348Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9348 raw9348Labels = mixedMoment B raw9348step0 raw9348step0Labels := by
      have hz : ∀ j, raw9348 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9348step0 = (fun i j => raw9348 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9348step0 raw9348; decide +kernel
      have hl : raw9348step0Labels = raw9348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9348 raw9348Labels permutation265 hz
    mixedMoment B raw9348step0 raw9348step0Labels = mixedMoment B raw9348step1 raw9348step1Labels := by
      have ha : raw9348step1 = (fun i j => raw9348step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9348step1 raw9348step0; decide +kernel
      have hl : raw9348step1Labels = raw9348step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9348step0 raw9348step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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

theorem singleton4601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4601 node4601Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1235 node1235Labels + mixedMoment B node3292 node3292Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1422 singletonSmall4601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4601) = raw1422Labels := by decide +kernel
  rw [hl, canonical1422 B hB] at h
  have hc0 : mixedMoment B raw1422 (Fin.cases (0 : Fin 2) singletonSmall4601) =
      mixedMoment B node1235 node1235Labels := by
    have ha : raw1422 = raw1423 := by apply Matrix.ext; unfold raw1422 raw1423; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4601 = raw1423Labels := by decide +kernel
    rw [ha, hj, canonical1423 B hB]
  have hc1 : mixedMoment B raw1422 (Fin.cases (1 : Fin 2) singletonSmall4601) =
      mixedMoment B node3292 node3292Labels := by
    have ha : raw1422 = raw1424 := by apply Matrix.ext; unfold raw1422 raw1424; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4601 = raw1424Labels := by decide +kernel
    rw [ha, hj, canonical1424 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4606 node4606Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1240 node1240Labels + mixedMoment B node3299 node3299Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1431 singletonSmall4606
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4606) = raw1431Labels := by decide +kernel
  rw [hl, canonical1431 B hB] at h
  have hc0 : mixedMoment B raw1431 (Fin.cases (0 : Fin 2) singletonSmall4606) =
      mixedMoment B node1240 node1240Labels := by
    have ha : raw1431 = raw1432 := by apply Matrix.ext; unfold raw1431 raw1432; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4606 = raw1432Labels := by decide +kernel
    rw [ha, hj, canonical1432 B hB]
  have hc1 : mixedMoment B raw1431 (Fin.cases (1 : Fin 2) singletonSmall4606) =
      mixedMoment B node3299 node3299Labels := by
    have ha : raw1431 = raw1433 := by apply Matrix.ext; unfold raw1431 raw1433; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4606 = raw1433Labels := by decide +kernel
    rw [ha, hj, canonical1433 B hB]
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

theorem singleton5162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5162 node5162Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2589 node2589Labels + mixedMoment B node3563 node3563Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2187 singletonSmall5162
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5162) = raw2187Labels := by decide +kernel
  rw [hl, canonical2187 B hB] at h
  have hc0 : mixedMoment B raw2187 (Fin.cases (0 : Fin 2) singletonSmall5162) =
      mixedMoment B node2589 node2589Labels := by
    have ha : raw2187 = raw2188 := by apply Matrix.ext; unfold raw2187 raw2188; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5162 = raw2188Labels := by decide +kernel
    rw [ha, hj, canonical2188 B hB]
  have hc1 : mixedMoment B raw2187 (Fin.cases (1 : Fin 2) singletonSmall5162) =
      mixedMoment B node3563 node3563Labels := by
    have ha : raw2187 = raw2189 := by apply Matrix.ext; unfold raw2187 raw2189; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5162 = raw2189Labels := by decide +kernel
    rw [ha, hj, canonical2189 B hB]
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

theorem singleton5290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5290 node5290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2764 node2764Labels + mixedMoment B node3581 node3581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2292 singletonSmall5290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5290) = raw2292Labels := by decide +kernel
  rw [hl, canonical2292 B hB] at h
  have hc0 : mixedMoment B raw2292 (Fin.cases (0 : Fin 2) singletonSmall5290) =
      mixedMoment B node2764 node2764Labels := by
    have ha : raw2292 = raw2293 := by apply Matrix.ext; unfold raw2292 raw2293; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5290 = raw2293Labels := by decide +kernel
    rw [ha, hj, canonical2293 B hB]
  have hc1 : mixedMoment B raw2292 (Fin.cases (1 : Fin 2) singletonSmall5290) =
      mixedMoment B node3581 node3581Labels := by
    have ha : raw2292 = raw2294 := by apply Matrix.ext; unfold raw2292 raw2294; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5290 = raw2294Labels := by decide +kernel
    rw [ha, hj, canonical2294 B hB]
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

theorem sound640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node640 node640Labels = Sparse.eval nodeValue640 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 640) = mixedMoment B node640 node640Labels := rfl
  simpa [nodeValue640, Sparse.eval] using hc.symm

theorem sound651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node651 node651Labels = Sparse.eval nodeValue651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 651) = mixedMoment B node651 node651Labels := rfl
  simpa [nodeValue651, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = 0 := by
  exact mixedMoment_order_one B hB node1081 node1081Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1034 node1034Labels = Sparse.eval nodeValue1034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1034) = mixedMoment B node1034 node1034Labels := rfl
  simpa [nodeValue1034, Sparse.eval] using hc.symm

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

theorem sound1081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = Sparse.eval nodeValue1081 (mixedVector B) := by
  simpa only [nodeValue1081, Sparse.eval_nil] using zero1081 B _hB _hF

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

theorem sound1228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1228 node1228Labels = Sparse.eval nodeValue1228 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1228) = mixedMoment B node1228 node1228Labels := rfl
  simpa [nodeValue1228, Sparse.eval] using hc.symm

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1256 node1256Labels = Sparse.eval nodeValue1256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1256) = mixedMoment B node1256 node1256Labels := rfl
  simpa [nodeValue1256, Sparse.eval] using hc.symm

theorem sound1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1260 node1260Labels = Sparse.eval nodeValue1260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1260) = mixedMoment B node1260 node1260Labels := rfl
  simpa [nodeValue1260, Sparse.eval] using hc.symm

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

theorem sound1286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1286 node1286Labels = Sparse.eval nodeValue1286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1286) = mixedMoment B node1286 node1286Labels := rfl
  simpa [nodeValue1286, Sparse.eval] using hc.symm

theorem sound1291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1291 node1291Labels = Sparse.eval nodeValue1291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1291) = mixedMoment B node1291 node1291Labels := rfl
  simpa [nodeValue1291, Sparse.eval] using hc.symm

theorem sound1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1293 node1293Labels = Sparse.eval nodeValue1293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1293) = mixedMoment B node1293 node1293Labels := rfl
  simpa [nodeValue1293, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1405 node1405Labels = 0 := by
  exact mixedMoment_alpha B hF node1405 node1405Labels 2 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1405 node1405Labels = Sparse.eval nodeValue1405 (mixedVector B) := by
  simpa only [nodeValue1405, Sparse.eval_nil] using zero1405 B _hB _hF

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

theorem sound1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1435 node1435Labels = Sparse.eval nodeValue1435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1435) = mixedMoment B node1435 node1435Labels := rfl
  simpa [nodeValue1435, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1502 node1502Labels = Sparse.eval nodeValue1502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1502) = mixedMoment B node1502 node1502Labels := rfl
  simpa [nodeValue1502, Sparse.eval] using hc.symm

theorem sound1503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1503 node1503Labels = Sparse.eval nodeValue1503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1503) = mixedMoment B node1503 node1503Labels := rfl
  simpa [nodeValue1503, Sparse.eval] using hc.symm

theorem sound1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1508 node1508Labels = Sparse.eval nodeValue1508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1508) = mixedMoment B node1508 node1508Labels := rfl
  simpa [nodeValue1508, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1595 node1595Labels = 0 := by
  exact mixedMoment_alpha B hF node1595 node1595Labels 1 permutation434
    (by decide +kernel)

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

theorem sound1593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1593 node1593Labels = Sparse.eval nodeValue1593 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1593) = mixedMoment B node1593 node1593Labels := rfl
  simpa [nodeValue1593, Sparse.eval] using hc.symm

theorem sound1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1595 node1595Labels = Sparse.eval nodeValue1595 (mixedVector B) := by
  simpa only [nodeValue1595, Sparse.eval_nil] using zero1595 B _hB _hF

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

theorem sound1600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1600 node1600Labels = Sparse.eval nodeValue1600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1600) = mixedMoment B node1600 node1600Labels := rfl
  simpa [nodeValue1600, Sparse.eval] using hc.symm

theorem sound1636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1636 node1636Labels = Sparse.eval nodeValue1636 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1636) = mixedMoment B node1636 node1636Labels := rfl
  simpa [nodeValue1636, Sparse.eval] using hc.symm

theorem sound1638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1638 node1638Labels = Sparse.eval nodeValue1638 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1638) = mixedMoment B node1638 node1638Labels := rfl
  simpa [nodeValue1638, Sparse.eval] using hc.symm

theorem sound1639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1639 node1639Labels = Sparse.eval nodeValue1639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1639) = mixedMoment B node1639 node1639Labels := rfl
  simpa [nodeValue1639, Sparse.eval] using hc.symm

theorem sound1641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1641 node1641Labels = Sparse.eval nodeValue1641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1641) = mixedMoment B node1641 node1641Labels := rfl
  simpa [nodeValue1641, Sparse.eval] using hc.symm

theorem sound1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1644 node1644Labels = Sparse.eval nodeValue1644 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1644) = mixedMoment B node1644 node1644Labels := rfl
  simpa [nodeValue1644, Sparse.eval] using hc.symm

theorem sound1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1648 node1648Labels = Sparse.eval nodeValue1648 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1648) = mixedMoment B node1648 node1648Labels := rfl
  simpa [nodeValue1648, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1726 node1726Labels = 0 := by
  exact mixedMoment_order_one B hB node1726 node1726Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1726 node1726Labels = Sparse.eval nodeValue1726 (mixedVector B) := by
  simpa only [nodeValue1726, Sparse.eval_nil] using zero1726 B _hB _hF

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

theorem sound2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2589 node2589Labels = Sparse.eval nodeValue2589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2589) = mixedMoment B node2589 node2589Labels := rfl
  simpa [nodeValue2589, Sparse.eval] using hc.symm

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

theorem sound2688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2688 node2688Labels = Sparse.eval nodeValue2688 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2688) = mixedMoment B node2688 node2688Labels := rfl
  simpa [nodeValue2688, Sparse.eval] using hc.symm

theorem sound2702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2702 node2702Labels = Sparse.eval nodeValue2702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2702) = mixedMoment B node2702 node2702Labels := rfl
  simpa [nodeValue2702, Sparse.eval] using hc.symm

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

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

theorem sound3072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3072 node3072Labels = Sparse.eval nodeValue3072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3072) = mixedMoment B node3072 node3072Labels := rfl
  simpa [nodeValue3072, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3239 node3239Labels = Sparse.eval nodeValue3239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3239) = mixedMoment B node3239 node3239Labels := rfl
  simpa [nodeValue3239, Sparse.eval] using hc.symm

theorem sound3257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3257 node3257Labels = Sparse.eval nodeValue3257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3257) = mixedMoment B node3257 node3257Labels := rfl
  simpa [nodeValue3257, Sparse.eval] using hc.symm

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

theorem sound3286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3286 node3286Labels = Sparse.eval nodeValue3286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3286) = mixedMoment B node3286 node3286Labels := rfl
  simpa [nodeValue3286, Sparse.eval] using hc.symm

theorem sound3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3289 node3289Labels = Sparse.eval nodeValue3289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3289) = mixedMoment B node3289 node3289Labels := rfl
  simpa [nodeValue3289, Sparse.eval] using hc.symm

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

theorem sound3294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3294 node3294Labels = Sparse.eval nodeValue3294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3294) = mixedMoment B node3294 node3294Labels := rfl
  simpa [nodeValue3294, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3303 node3303Labels = Sparse.eval nodeValue3303 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3303) = mixedMoment B node3303 node3303Labels := rfl
  simpa [nodeValue3303, Sparse.eval] using hc.symm

theorem sound3304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3304 node3304Labels = Sparse.eval nodeValue3304 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3304) = mixedMoment B node3304 node3304Labels := rfl
  simpa [nodeValue3304, Sparse.eval] using hc.symm

theorem sound3307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3307 node3307Labels = Sparse.eval nodeValue3307 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3307) = mixedMoment B node3307 node3307Labels := rfl
  simpa [nodeValue3307, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = 0 := by
  exact mixedMoment_order_one B hB node3546 node3546Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = Sparse.eval nodeValue3546 (mixedVector B) := by
  simpa only [nodeValue3546, Sparse.eval_nil] using zero3546 B _hB _hF

theorem sound3563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3563 node3563Labels = Sparse.eval nodeValue3563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3563) = mixedMoment B node3563 node3563Labels := rfl
  simpa [nodeValue3563, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem sound637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node637 node637Labels = Sparse.eval nodeValue637 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 637) = mixedMoment B node637 node637Labels := rfl
  simpa [nodeValue637, Sparse.eval] using hc.symm

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

theorem sound4169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4169 node4169Labels = Sparse.eval nodeValue4169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4169) = mixedMoment B node4169 node4169Labels := rfl
  simpa [nodeValue4169, Sparse.eval] using hc.symm

theorem sound4170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4170 node4170Labels = Sparse.eval nodeValue4170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4170) = mixedMoment B node4170 node4170Labels := rfl
  simpa [nodeValue4170, Sparse.eval] using hc.symm

theorem sound4173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4173 node4173Labels = Sparse.eval nodeValue4173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4173) = mixedMoment B node4173 node4173Labels := rfl
  simpa [nodeValue4173, Sparse.eval] using hc.symm

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

theorem sound4540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4540 node4540Labels = Sparse.eval nodeValue4540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4540) = mixedMoment B node4540 node4540Labels := rfl
  simpa [nodeValue4540, Sparse.eval] using hc.symm

theorem sound4542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4542 node4542Labels = Sparse.eval nodeValue4542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4542) = mixedMoment B node4542 node4542Labels := rfl
  simpa [nodeValue4542, Sparse.eval] using hc.symm

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

theorem sound4599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4599 node4599Labels = Sparse.eval nodeValue4599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4599) = mixedMoment B node4599 node4599Labels := rfl
  simpa [nodeValue4599, Sparse.eval] using hc.symm

theorem sound4600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4600 node4600Labels = Sparse.eval nodeValue4600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4600) = mixedMoment B node4600 node4600Labels := rfl
  simpa [nodeValue4600, Sparse.eval] using hc.symm

theorem sound4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4601 node4601Labels = Sparse.eval nodeValue4601 (mixedVector B) := by
  have h := singleton4601 B _hB
  rw [sound1235 B _hB _hF, sound3292 B _hB _hF] at h
  norm_num [nodeValue4601, nodeValue1235, nodeValue3292, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4603 node4603Labels = Sparse.eval nodeValue4603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4603) = mixedMoment B node4603 node4603Labels := rfl
  simpa [nodeValue4603, Sparse.eval] using hc.symm

theorem sound4606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4606 node4606Labels = Sparse.eval nodeValue4606 (mixedVector B) := by
  have h := singleton4606 B _hB
  rw [sound1240 B _hB _hF, sound3299 B _hB _hF] at h
  norm_num [nodeValue4606, nodeValue1240, nodeValue3299, Sparse.eval] at h ⊢
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

theorem sound5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5162 node5162Labels = Sparse.eval nodeValue5162 (mixedVector B) := by
  have h := singleton5162 B _hB
  rw [sound2589 B _hB _hF, sound3563 B _hB _hF] at h
  norm_num [nodeValue5162, nodeValue2589, nodeValue3563, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = 0 := by
  exact mixedMoment_order_one B hB node5273 node5273Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = Sparse.eval nodeValue5273 (mixedVector B) := by
  simpa only [nodeValue5273, Sparse.eval_nil] using zero5273 B _hB _hF

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources57
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1835 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 0) (sourceB1835 + difference 0 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 0) (sourceB1835 + difference 0 0) sourceC1835) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 1) (sourceB1835 + difference 1 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1638) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 1) (sourceB1835 + difference 1 0) sourceC1835) = raw26433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26433; decide +kernel
    rw [ha]
    exact (canonical26433 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 2) (sourceB1835 + difference 2 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 2) (sourceB1835 + difference 2 0) sourceC1835) = raw26434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26434; decide +kernel
    rw [ha]
    exact (canonical26434 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 3) (sourceB1835 + difference 3 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 3) (sourceB1835 + difference 3 0) sourceC1835) = raw26435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26435; decide +kernel
    rw [ha]
    exact (canonical26435 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 4) (sourceB1835 + difference 4 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1644) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 4) (sourceB1835 + difference 4 0) sourceC1835) = raw26416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26416; decide +kernel
    rw [ha]
    exact (canonical26416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 5) (sourceB1835 + difference 5 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 5) (sourceB1835 + difference 5 0) sourceC1835) = raw26436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26436; decide +kernel
    rw [ha]
    exact (canonical26436 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1835 + sourceB1835) sourceC1835) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1835 + sourceB1835) sourceC1835) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1835 sourceB1835 sourceC1835 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1835 sourceB1835 sourceC1835
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1835, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1836 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1836 + difference 0 0) (sourceB1836 + difference 0 0) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1836 + difference 0 0) (sourceB1836 + difference 0 0) sourceC1836) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1836 + difference 1 0) (sourceB1836 + difference 0 1) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1836 + difference 1 0) (sourceB1836 + difference 0 1) sourceC1836) = raw26374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26374; decide +kernel
    rw [ha]
    exact (canonical26374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1836 + difference 2 0) (sourceB1836 + difference 0 2) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1600) := by
    have ha : (tripleCharges (sourceA1836 + difference 2 0) (sourceB1836 + difference 0 2) sourceC1836) = raw26437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26437; decide +kernel
    rw [ha]
    exact (canonical26437 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1836 + difference 3 0) (sourceB1836 + difference 0 3) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1600) := by
    have ha : (tripleCharges (sourceA1836 + difference 3 0) (sourceB1836 + difference 0 3) sourceC1836) = raw26438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26438; decide +kernel
    rw [ha]
    exact (canonical26438 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1836 + difference 4 0) (sourceB1836 + difference 0 4) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1595) := by
    have ha : (tripleCharges (sourceA1836 + difference 4 0) (sourceB1836 + difference 0 4) sourceC1836) = raw26439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26439; decide +kernel
    rw [ha]
    exact (canonical26439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1836 + difference 5 0) (sourceB1836 + difference 0 5) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1593) := by
    have ha : (tripleCharges (sourceA1836 + difference 5 0) (sourceB1836 + difference 0 5) sourceC1836) = raw26440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26440; decide +kernel
    rw [ha]
    exact (canonical26440 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1836 + sourceB1836) sourceC1836) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1836 + sourceB1836) sourceC1836) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1836 sourceB1836 sourceC1836 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1836 sourceB1836 sourceC1836
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1836, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1837 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 0) (sourceB1837 + difference 0 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 0) (sourceB1837 + difference 0 1) sourceC1837) = raw26374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26374; decide +kernel
    rw [ha]
    exact (canonical26374 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 1) (sourceB1837 + difference 1 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 1) (sourceB1837 + difference 1 1) sourceC1837) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 2) (sourceB1837 + difference 2 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 2) (sourceB1837 + difference 2 1) sourceC1837) = raw26441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26441; decide +kernel
    rw [ha]
    exact (canonical26441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 3) (sourceB1837 + difference 3 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 3) (sourceB1837 + difference 3 1) sourceC1837) = raw26442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26442; decide +kernel
    rw [ha]
    exact (canonical26442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 4) (sourceB1837 + difference 4 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 4) (sourceB1837 + difference 4 1) sourceC1837) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 5) (sourceB1837 + difference 5 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3307) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 5) (sourceB1837 + difference 5 1) sourceC1837) = raw26443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26443; decide +kernel
    rw [ha]
    exact (canonical26443 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1837 + sourceB1837) sourceC1837) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1837 + sourceB1837) sourceC1837) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1837 sourceB1837 sourceC1837 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1837 sourceB1837 sourceC1837
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1837, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1838 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 0) (sourceB1838 + difference 0 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1600) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 0) (sourceB1838 + difference 0 2) sourceC1838) = raw26437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26437; decide +kernel
    rw [ha]
    exact (canonical26437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 1) (sourceB1838 + difference 1 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 1) (sourceB1838 + difference 1 2) sourceC1838) = raw26444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26444; decide +kernel
    rw [ha]
    exact (canonical26444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 2) (sourceB1838 + difference 2 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 2) (sourceB1838 + difference 2 2) sourceC1838) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 3) (sourceB1838 + difference 3 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 3) (sourceB1838 + difference 3 2) sourceC1838) = raw26445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26445; decide +kernel
    rw [ha]
    exact (canonical26445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 4) (sourceB1838 + difference 4 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 4) (sourceB1838 + difference 4 2) sourceC1838) = raw26417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26417; decide +kernel
    rw [ha]
    exact (canonical26417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 5) (sourceB1838 + difference 5 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 5) (sourceB1838 + difference 5 2) sourceC1838) = raw26446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26446; decide +kernel
    rw [ha]
    exact (canonical26446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1838 + sourceB1838) sourceC1838) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1838 + sourceB1838) sourceC1838) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1838 sourceB1838 sourceC1838 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1838 sourceB1838 sourceC1838
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1838, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1839 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1839 + difference 0 5) (sourceB1839 + difference 5 0) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1839 + difference 0 5) (sourceB1839 + difference 5 0) sourceC1839) = raw26436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26436; decide +kernel
    rw [ha]
    exact (canonical26436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1839 + difference 1 5) (sourceB1839 + difference 5 1) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3307) := by
    have ha : (tripleCharges (sourceA1839 + difference 1 5) (sourceB1839 + difference 5 1) sourceC1839) = raw26443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26443; decide +kernel
    rw [ha]
    exact (canonical26443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1839 + difference 2 5) (sourceB1839 + difference 5 2) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1839 + difference 2 5) (sourceB1839 + difference 5 2) sourceC1839) = raw26446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26446; decide +kernel
    rw [ha]
    exact (canonical26446 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1839 + difference 3 5) (sourceB1839 + difference 5 3) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1839 + difference 3 5) (sourceB1839 + difference 5 3) sourceC1839) = raw26447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26447; decide +kernel
    rw [ha]
    exact (canonical26447 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1839 + difference 4 5) (sourceB1839 + difference 5 4) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1839 + difference 4 5) (sourceB1839 + difference 5 4) sourceC1839) = raw26448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26448; decide +kernel
    rw [ha]
    exact (canonical26448 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1839 + difference 5 5) (sourceB1839 + difference 5 5) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1839 + difference 5 5) (sourceB1839 + difference 5 5) sourceC1839) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1839 + sourceB1839) sourceC1839) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1839 + sourceB1839) sourceC1839) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1839 sourceB1839 sourceC1839 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1839 sourceB1839 sourceC1839
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1839, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1841 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1841 + difference 0 5) (sourceB1841 + difference 5 0) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1841 + difference 0 5) (sourceB1841 + difference 5 0) sourceC1841) = raw26456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26456; decide +kernel
    rw [ha]
    exact (canonical26456 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1841 + difference 1 5) (sourceB1841 + difference 5 1) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1841 + difference 1 5) (sourceB1841 + difference 5 1) sourceC1841) = raw26379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26379; decide +kernel
    rw [ha]
    exact (canonical26379 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1841 + difference 2 5) (sourceB1841 + difference 5 2) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1841 + difference 2 5) (sourceB1841 + difference 5 2) sourceC1841) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1841 + difference 3 5) (sourceB1841 + difference 5 3) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1841 + difference 3 5) (sourceB1841 + difference 5 3) sourceC1841) = raw26457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26457; decide +kernel
    rw [ha]
    exact (canonical26457 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1841 + difference 4 5) (sourceB1841 + difference 5 4) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1841 + difference 4 5) (sourceB1841 + difference 5 4) sourceC1841) = raw26441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26441; decide +kernel
    rw [ha]
    exact (canonical26441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1841 + difference 5 5) (sourceB1841 + difference 5 5) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA1841 + difference 5 5) (sourceB1841 + difference 5 5) sourceC1841) = raw26366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26366; decide +kernel
    rw [ha]
    exact (canonical26366 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1841 + sourceB1841) sourceC1841) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1841 + sourceB1841) sourceC1841) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1841 sourceB1841 sourceC1841 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1841 sourceB1841 sourceC1841
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1841, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1842 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 0) (sourceB1842 + difference 0 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 0) (sourceB1842 + difference 0 0) sourceC1842) = raw26441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26441; decide +kernel
    rw [ha]
    exact (canonical26441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 1) (sourceB1842 + difference 1 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 1) (sourceB1842 + difference 1 0) sourceC1842) = raw26434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26434; decide +kernel
    rw [ha]
    exact (canonical26434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 2) (sourceB1842 + difference 2 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 2) (sourceB1842 + difference 2 0) sourceC1842) = raw26458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26458; decide +kernel
    rw [ha]
    exact (canonical26458 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 3) (sourceB1842 + difference 3 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 3) (sourceB1842 + difference 3 0) sourceC1842) = raw26459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26459; decide +kernel
    rw [ha]
    exact (canonical26459 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 4) (sourceB1842 + difference 4 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 4) (sourceB1842 + difference 4 0) sourceC1842) = raw26456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26456; decide +kernel
    rw [ha]
    exact (canonical26456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 5) (sourceB1842 + difference 5 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 5) (sourceB1842 + difference 5 0) sourceC1842) = raw26460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26460; decide +kernel
    rw [ha]
    exact (canonical26460 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1842 + sourceB1842) sourceC1842) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1842 + sourceB1842) sourceC1842) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1842 sourceB1842 sourceC1842 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1842 sourceB1842 sourceC1842
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1842, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1845 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 1) (sourceB1845 + difference 1 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 1) (sourceB1845 + difference 1 0) sourceC1845) = raw26493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26493; decide +kernel
    rw [ha]
    exact (canonical26493 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 2) (sourceB1845 + difference 2 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 2) (sourceB1845 + difference 2 0) sourceC1845) = raw9271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw9271; decide +kernel
    rw [ha]
    exact (canonical9271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 3) (sourceB1845 + difference 3 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 3) (sourceB1845 + difference 3 0) sourceC1845) = raw9266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw9266; decide +kernel
    rw [ha]
    exact (canonical9266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 4) (sourceB1845 + difference 4 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 4) (sourceB1845 + difference 4 0) sourceC1845) = raw26494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26494; decide +kernel
    rw [ha]
    exact (canonical26494 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 5) (sourceB1845 + difference 5 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 5) (sourceB1845 + difference 5 0) sourceC1845) = raw26495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26495; decide +kernel
    rw [ha]
    exact (canonical26495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 0) (sourceB1845 + difference 0 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4169) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 0) (sourceB1845 + difference 0 1) sourceC1845) = raw26496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26496; decide +kernel
    rw [ha]
    exact (canonical26496 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 2) (sourceB1845 + difference 2 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 2) (sourceB1845 + difference 2 1) sourceC1845) = raw26497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26497; decide +kernel
    rw [ha]
    exact (canonical26497 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 3) (sourceB1845 + difference 3 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 3) (sourceB1845 + difference 3 1) sourceC1845) = raw26498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26498; decide +kernel
    rw [ha]
    exact (canonical26498 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 4) (sourceB1845 + difference 4 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 4) (sourceB1845 + difference 4 1) sourceC1845) = raw26499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26499; decide +kernel
    rw [ha]
    exact (canonical26499 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 5) (sourceB1845 + difference 5 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 5) (sourceB1845 + difference 5 1) sourceC1845) = raw26500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26500; decide +kernel
    rw [ha]
    exact (canonical26500 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 0) (sourceB1845 + difference 0 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 0) (sourceB1845 + difference 0 2) sourceC1845) = raw26501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26501; decide +kernel
    rw [ha]
    exact (canonical26501 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 1) (sourceB1845 + difference 1 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4542) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 1) (sourceB1845 + difference 1 2) sourceC1845) = raw26502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26502; decide +kernel
    rw [ha]
    exact (canonical26502 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 3) (sourceB1845 + difference 3 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 3) (sourceB1845 + difference 3 2) sourceC1845) = raw26503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26503; decide +kernel
    rw [ha]
    exact (canonical26503 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 4) (sourceB1845 + difference 4 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 4) (sourceB1845 + difference 4 2) sourceC1845) = raw26504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26504; decide +kernel
    rw [ha]
    exact (canonical26504 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 5) (sourceB1845 + difference 5 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 5) (sourceB1845 + difference 5 2) sourceC1845) = raw26505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26505; decide +kernel
    rw [ha]
    exact (canonical26505 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 0) (sourceB1845 + difference 0 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 0) (sourceB1845 + difference 0 3) sourceC1845) = raw26506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26506; decide +kernel
    rw [ha]
    exact (canonical26506 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 1) (sourceB1845 + difference 1 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4542) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 1) (sourceB1845 + difference 1 3) sourceC1845) = raw26507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26507; decide +kernel
    rw [ha]
    exact (canonical26507 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 2) (sourceB1845 + difference 2 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 2) (sourceB1845 + difference 2 3) sourceC1845) = raw26508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26508; decide +kernel
    rw [ha]
    exact (canonical26508 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 4) (sourceB1845 + difference 4 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 4) (sourceB1845 + difference 4 3) sourceC1845) = raw26509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26509; decide +kernel
    rw [ha]
    exact (canonical26509 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 5) (sourceB1845 + difference 5 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 5) (sourceB1845 + difference 5 3) sourceC1845) = raw26510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26510; decide +kernel
    rw [ha]
    exact (canonical26510 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 0) (sourceB1845 + difference 0 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 0) (sourceB1845 + difference 0 4) sourceC1845) = raw26511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26511; decide +kernel
    rw [ha]
    exact (canonical26511 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 1) (sourceB1845 + difference 1 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4542) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 1) (sourceB1845 + difference 1 4) sourceC1845) = raw26512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26512; decide +kernel
    rw [ha]
    exact (canonical26512 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 2) (sourceB1845 + difference 2 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 2) (sourceB1845 + difference 2 4) sourceC1845) = raw26513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26513; decide +kernel
    rw [ha]
    exact (canonical26513 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 3) (sourceB1845 + difference 3 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 3) (sourceB1845 + difference 3 4) sourceC1845) = raw26514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26514; decide +kernel
    rw [ha]
    exact (canonical26514 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 5) (sourceB1845 + difference 5 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 5) (sourceB1845 + difference 5 4) sourceC1845) = raw26515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26515; decide +kernel
    rw [ha]
    exact (canonical26515 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 0) (sourceB1845 + difference 0 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4170) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 0) (sourceB1845 + difference 0 5) sourceC1845) = raw26516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26516; decide +kernel
    rw [ha]
    exact (canonical26516 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 1) (sourceB1845 + difference 1 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4540) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 1) (sourceB1845 + difference 1 5) sourceC1845) = raw26517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26517; decide +kernel
    rw [ha]
    exact (canonical26517 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 2) (sourceB1845 + difference 2 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 2) (sourceB1845 + difference 2 5) sourceC1845) = raw9267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw9267; decide +kernel
    rw [ha]
    exact (canonical9267 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 3) (sourceB1845 + difference 3 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 3) (sourceB1845 + difference 3 5) sourceC1845) = raw9262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw9262; decide +kernel
    rw [ha]
    exact (canonical9262 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 4) (sourceB1845 + difference 4 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 4) (sourceB1845 + difference 4 5) sourceC1845) = raw26518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26518; decide +kernel
    rw [ha]
    exact (canonical26518 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1845 sourceB1845 sourceC1845
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1845, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1847 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 1) (sourceB1847 + difference 1 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 1) (sourceB1847 + difference 1 0) sourceC1847) = raw26545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26545; decide +kernel
    rw [ha]
    exact (canonical26545 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 2) (sourceB1847 + difference 2 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 2) (sourceB1847 + difference 2 0) sourceC1847) = raw9331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw9331; decide +kernel
    rw [ha]
    exact (canonical9331 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 3) (sourceB1847 + difference 3 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 3) (sourceB1847 + difference 3 0) sourceC1847) = raw9326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw9326; decide +kernel
    rw [ha]
    exact (canonical9326 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 4) (sourceB1847 + difference 4 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 4) (sourceB1847 + difference 4 0) sourceC1847) = raw26546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26546; decide +kernel
    rw [ha]
    exact (canonical26546 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 5) (sourceB1847 + difference 5 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 5) (sourceB1847 + difference 5 0) sourceC1847) = raw26547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26547; decide +kernel
    rw [ha]
    exact (canonical26547 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 0) (sourceB1847 + difference 0 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 0) (sourceB1847 + difference 0 1) sourceC1847) = raw26548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26548; decide +kernel
    rw [ha]
    exact (canonical26548 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 2) (sourceB1847 + difference 2 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 2) (sourceB1847 + difference 2 1) sourceC1847) = raw26549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26549; decide +kernel
    rw [ha]
    exact (canonical26549 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 3) (sourceB1847 + difference 3 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 3) (sourceB1847 + difference 3 1) sourceC1847) = raw26550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26550; decide +kernel
    rw [ha]
    exact (canonical26550 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 4) (sourceB1847 + difference 4 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 4) (sourceB1847 + difference 4 1) sourceC1847) = raw26551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26551; decide +kernel
    rw [ha]
    exact (canonical26551 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 5) (sourceB1847 + difference 5 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 5) (sourceB1847 + difference 5 1) sourceC1847) = raw26552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26552; decide +kernel
    rw [ha]
    exact (canonical26552 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 0) (sourceB1847 + difference 0 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 0) (sourceB1847 + difference 0 2) sourceC1847) = raw26553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26553; decide +kernel
    rw [ha]
    exact (canonical26553 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 1) (sourceB1847 + difference 1 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 1) (sourceB1847 + difference 1 2) sourceC1847) = raw26554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26554; decide +kernel
    rw [ha]
    exact (canonical26554 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 3) (sourceB1847 + difference 3 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 3) (sourceB1847 + difference 3 2) sourceC1847) = raw26555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26555; decide +kernel
    rw [ha]
    exact (canonical26555 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 4) (sourceB1847 + difference 4 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 4) (sourceB1847 + difference 4 2) sourceC1847) = raw26556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26556; decide +kernel
    rw [ha]
    exact (canonical26556 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 5) (sourceB1847 + difference 5 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 5) (sourceB1847 + difference 5 2) sourceC1847) = raw26557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26557; decide +kernel
    rw [ha]
    exact (canonical26557 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 0) (sourceB1847 + difference 0 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 0) (sourceB1847 + difference 0 3) sourceC1847) = raw26558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26558; decide +kernel
    rw [ha]
    exact (canonical26558 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 1) (sourceB1847 + difference 1 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 1) (sourceB1847 + difference 1 3) sourceC1847) = raw26559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26559; decide +kernel
    rw [ha]
    exact (canonical26559 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 2) (sourceB1847 + difference 2 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 2) (sourceB1847 + difference 2 3) sourceC1847) = raw26560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26560; decide +kernel
    rw [ha]
    exact (canonical26560 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 4) (sourceB1847 + difference 4 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 4) (sourceB1847 + difference 4 3) sourceC1847) = raw26561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26561; decide +kernel
    rw [ha]
    exact (canonical26561 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 5) (sourceB1847 + difference 5 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 5) (sourceB1847 + difference 5 3) sourceC1847) = raw26562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26562; decide +kernel
    rw [ha]
    exact (canonical26562 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 0) (sourceB1847 + difference 0 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 0) (sourceB1847 + difference 0 4) sourceC1847) = raw26563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26563; decide +kernel
    rw [ha]
    exact (canonical26563 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 1) (sourceB1847 + difference 1 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 1) (sourceB1847 + difference 1 4) sourceC1847) = raw26564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26564; decide +kernel
    rw [ha]
    exact (canonical26564 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 2) (sourceB1847 + difference 2 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 2) (sourceB1847 + difference 2 4) sourceC1847) = raw26565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26565; decide +kernel
    rw [ha]
    exact (canonical26565 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 3) (sourceB1847 + difference 3 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 3) (sourceB1847 + difference 3 4) sourceC1847) = raw26566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26566; decide +kernel
    rw [ha]
    exact (canonical26566 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 5) (sourceB1847 + difference 5 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 5) (sourceB1847 + difference 5 4) sourceC1847) = raw26567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26567; decide +kernel
    rw [ha]
    exact (canonical26567 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 0) (sourceB1847 + difference 0 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1503) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 0) (sourceB1847 + difference 0 5) sourceC1847) = raw26568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26568; decide +kernel
    rw [ha]
    exact (canonical26568 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 1) (sourceB1847 + difference 1 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2688) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 1) (sourceB1847 + difference 1 5) sourceC1847) = raw26569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26569; decide +kernel
    rw [ha]
    exact (canonical26569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 2) (sourceB1847 + difference 2 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 2) (sourceB1847 + difference 2 5) sourceC1847) = raw9327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw9327; decide +kernel
    rw [ha]
    exact (canonical9327 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 3) (sourceB1847 + difference 3 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 3) (sourceB1847 + difference 3 5) sourceC1847) = raw9322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw9322; decide +kernel
    rw [ha]
    exact (canonical9322 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 4) (sourceB1847 + difference 4 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 4) (sourceB1847 + difference 4 5) sourceC1847) = raw26570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26570; decide +kernel
    rw [ha]
    exact (canonical26570 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1847 sourceB1847 sourceC1847
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1847, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1848 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1848 + difference 0 0) (sourceB1848 + difference 0 0) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1848 + difference 0 0) (sourceB1848 + difference 0 0) sourceC1848) = raw26571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26571; decide +kernel
    rw [ha]
    exact (canonical26571 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1848 + difference 1 0) (sourceB1848 + difference 0 1) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 637) := by
    have ha : (tripleCharges (sourceA1848 + difference 1 0) (sourceB1848 + difference 0 1) sourceC1848) = raw26572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26572; decide +kernel
    rw [ha]
    exact (canonical26572 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1848 + difference 2 0) (sourceB1848 + difference 0 2) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1848 + difference 2 0) (sourceB1848 + difference 0 2) sourceC1848) = raw26573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26573; decide +kernel
    rw [ha]
    exact (canonical26573 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1848 + difference 3 0) (sourceB1848 + difference 0 3) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1848 + difference 3 0) (sourceB1848 + difference 0 3) sourceC1848) = raw26574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26574; decide +kernel
    rw [ha]
    exact (canonical26574 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1848 + difference 4 0) (sourceB1848 + difference 0 4) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1848 + difference 4 0) (sourceB1848 + difference 0 4) sourceC1848) = raw26575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26575; decide +kernel
    rw [ha]
    exact (canonical26575 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1848 + difference 5 0) (sourceB1848 + difference 0 5) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 651) := by
    have ha : (tripleCharges (sourceA1848 + difference 5 0) (sourceB1848 + difference 0 5) sourceC1848) = raw26576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26576; decide +kernel
    rw [ha]
    exact (canonical26576 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1848 + sourceB1848) sourceC1848) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1848 + sourceB1848) sourceC1848) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA1848 sourceB1848 sourceC1848 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1848 sourceB1848 sourceC1848
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1848, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1850 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 1) (sourceB1850 + difference 1 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 1) (sourceB1850 + difference 1 0) sourceC1850) = raw26607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26607; decide +kernel
    rw [ha]
    exact (canonical26607 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 2) (sourceB1850 + difference 2 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 2) (sourceB1850 + difference 2 0) sourceC1850) = raw26608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26608; decide +kernel
    rw [ha]
    exact (canonical26608 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 3) (sourceB1850 + difference 3 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 3) (sourceB1850 + difference 3 0) sourceC1850) = raw26609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26609; decide +kernel
    rw [ha]
    exact (canonical26609 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 4) (sourceB1850 + difference 4 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 4) (sourceB1850 + difference 4 0) sourceC1850) = raw26610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26610; decide +kernel
    rw [ha]
    exact (canonical26610 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 5) (sourceB1850 + difference 5 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 5) (sourceB1850 + difference 5 0) sourceC1850) = raw26611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26611; decide +kernel
    rw [ha]
    exact (canonical26611 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 0) (sourceB1850 + difference 0 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1405) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 0) (sourceB1850 + difference 0 1) sourceC1850) = raw26612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26612; decide +kernel
    rw [ha]
    exact (canonical26612 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 2) (sourceB1850 + difference 2 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 2) (sourceB1850 + difference 2 1) sourceC1850) = raw26613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26613; decide +kernel
    rw [ha]
    exact (canonical26613 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 3) (sourceB1850 + difference 3 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 3) (sourceB1850 + difference 3 1) sourceC1850) = raw26614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26614; decide +kernel
    rw [ha]
    exact (canonical26614 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 4) (sourceB1850 + difference 4 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 4) (sourceB1850 + difference 4 1) sourceC1850) = raw26615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26615; decide +kernel
    rw [ha]
    exact (canonical26615 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 5) (sourceB1850 + difference 5 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 5) (sourceB1850 + difference 5 1) sourceC1850) = raw26616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26616; decide +kernel
    rw [ha]
    exact (canonical26616 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 0) (sourceB1850 + difference 0 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 0) (sourceB1850 + difference 0 2) sourceC1850) = raw26617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26617; decide +kernel
    rw [ha]
    exact (canonical26617 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 1) (sourceB1850 + difference 1 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 1) (sourceB1850 + difference 1 2) sourceC1850) = raw26618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26618; decide +kernel
    rw [ha]
    exact (canonical26618 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 3) (sourceB1850 + difference 3 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 3) (sourceB1850 + difference 3 2) sourceC1850) = raw26619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26619; decide +kernel
    rw [ha]
    exact (canonical26619 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 4) (sourceB1850 + difference 4 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 4) (sourceB1850 + difference 4 2) sourceC1850) = raw26620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26620; decide +kernel
    rw [ha]
    exact (canonical26620 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 5) (sourceB1850 + difference 5 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 5) (sourceB1850 + difference 5 2) sourceC1850) = raw26621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26621; decide +kernel
    rw [ha]
    exact (canonical26621 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 0) (sourceB1850 + difference 0 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 0) (sourceB1850 + difference 0 3) sourceC1850) = raw26622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26622; decide +kernel
    rw [ha]
    exact (canonical26622 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 1) (sourceB1850 + difference 1 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 1) (sourceB1850 + difference 1 3) sourceC1850) = raw26623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26623; decide +kernel
    rw [ha]
    exact (canonical26623 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 2) (sourceB1850 + difference 2 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 2) (sourceB1850 + difference 2 3) sourceC1850) = raw26624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26624; decide +kernel
    rw [ha]
    exact (canonical26624 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 4) (sourceB1850 + difference 4 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 4) (sourceB1850 + difference 4 3) sourceC1850) = raw26625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26625; decide +kernel
    rw [ha]
    exact (canonical26625 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 5) (sourceB1850 + difference 5 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 5) (sourceB1850 + difference 5 3) sourceC1850) = raw26626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26626; decide +kernel
    rw [ha]
    exact (canonical26626 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 0) (sourceB1850 + difference 0 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 0) (sourceB1850 + difference 0 4) sourceC1850) = raw26627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26627; decide +kernel
    rw [ha]
    exact (canonical26627 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 1) (sourceB1850 + difference 1 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 1) (sourceB1850 + difference 1 4) sourceC1850) = raw26628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26628; decide +kernel
    rw [ha]
    exact (canonical26628 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 2) (sourceB1850 + difference 2 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 2) (sourceB1850 + difference 2 4) sourceC1850) = raw26629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26629; decide +kernel
    rw [ha]
    exact (canonical26629 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 3) (sourceB1850 + difference 3 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 3) (sourceB1850 + difference 3 4) sourceC1850) = raw26630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26630; decide +kernel
    rw [ha]
    exact (canonical26630 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 5) (sourceB1850 + difference 5 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 5) (sourceB1850 + difference 5 4) sourceC1850) = raw26631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26631; decide +kernel
    rw [ha]
    exact (canonical26631 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 0) (sourceB1850 + difference 0 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1435) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 0) (sourceB1850 + difference 0 5) sourceC1850) = raw26632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26632; decide +kernel
    rw [ha]
    exact (canonical26632 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 1) (sourceB1850 + difference 1 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1256) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 1) (sourceB1850 + difference 1 5) sourceC1850) = raw26633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26633; decide +kernel
    rw [ha]
    exact (canonical26633 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 2) (sourceB1850 + difference 2 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 2) (sourceB1850 + difference 2 5) sourceC1850) = raw26634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26634; decide +kernel
    rw [ha]
    exact (canonical26634 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 3) (sourceB1850 + difference 3 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 3) (sourceB1850 + difference 3 5) sourceC1850) = raw26635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26635; decide +kernel
    rw [ha]
    exact (canonical26635 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 4) (sourceB1850 + difference 4 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 4) (sourceB1850 + difference 4 5) sourceC1850) = raw26636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26636; decide +kernel
    rw [ha]
    exact (canonical26636 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1850 sourceB1850 sourceC1850
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1850, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1851 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 0) (sourceB1851 + difference 0 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 0) (sourceB1851 + difference 0 0) sourceC1851) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 1) (sourceB1851 + difference 1 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1644) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 1) (sourceB1851 + difference 1 0) sourceC1851) = raw26416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26416; decide +kernel
    rw [ha]
    exact (canonical26416 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 2) (sourceB1851 + difference 2 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 2) (sourceB1851 + difference 2 0) sourceC1851) = raw26456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26456; decide +kernel
    rw [ha]
    exact (canonical26456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 3) (sourceB1851 + difference 3 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 3) (sourceB1851 + difference 3 0) sourceC1851) = raw26637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26637; decide +kernel
    rw [ha]
    exact (canonical26637 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 4) (sourceB1851 + difference 4 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 4) (sourceB1851 + difference 4 0) sourceC1851) = raw26638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26638; decide +kernel
    rw [ha]
    exact (canonical26638 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 5) (sourceB1851 + difference 5 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 5) (sourceB1851 + difference 5 0) sourceC1851) = raw26639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26639; decide +kernel
    rw [ha]
    exact (canonical26639 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1851 + sourceB1851) sourceC1851) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1851 + sourceB1851) sourceC1851) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1851 sourceB1851 sourceC1851 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1851 sourceB1851 sourceC1851
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1851, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1552 : Integer.Sparse.reindex keyMap MixedData.row1552 = numericRow1552 := by decide +kernel

theorem numericCheck1552 (x : Master → ℝ) : Integer.Sparse.eval numericRow1552 x =
    (1 : ℝ) * reducedSource1552 x := by
  norm_num [numericRow1552, reducedSource1552, Integer.Sparse.eval, Sparse.eval, nodeValue1636, nodeValue1638, nodeValue1644, nodeValue1706, nodeValue3289, nodeValue4068]

theorem reindexCheck1553 : Integer.Sparse.reindex keyMap MixedData.row1553 = numericRow1553 := by decide +kernel

theorem numericCheck1553 (x : Master → ℝ) : Integer.Sparse.eval numericRow1553 x =
    (1 : ℝ) * reducedSource1553 x := by
  norm_num [numericRow1553, reducedSource1553, Integer.Sparse.eval, Sparse.eval, nodeValue1593, nodeValue1595, nodeValue1600, nodeValue1708, nodeValue3289, nodeValue4068]

theorem reindexCheck1554 : Integer.Sparse.reindex keyMap MixedData.row1554 = numericRow1554 := by decide +kernel

theorem numericCheck1554 (x : Master → ℝ) : Integer.Sparse.eval numericRow1554 x =
    (1 : ℝ) * reducedSource1554 x := by
  norm_num [numericRow1554, reducedSource1554, Integer.Sparse.eval, Sparse.eval, nodeValue1708, nodeValue3289, nodeValue3303, nodeValue3304, nodeValue3307, nodeValue4068]

theorem reindexCheck1555 : Integer.Sparse.reindex keyMap MixedData.row1555 = numericRow1555 := by decide +kernel

theorem numericCheck1555 (x : Master → ℝ) : Integer.Sparse.eval numericRow1555 x =
    (1 : ℝ) * reducedSource1555 x := by
  norm_num [numericRow1555, reducedSource1555, Integer.Sparse.eval, Sparse.eval, nodeValue1600, nodeValue3239, nodeValue3286, nodeValue3289, nodeValue3292, nodeValue4068]

theorem reindexCheck1556 : Integer.Sparse.reindex keyMap MixedData.row1556 = numericRow1556 := by decide +kernel

theorem numericCheck1556 (x : Master → ℝ) : Integer.Sparse.eval numericRow1556 x =
    (1 : ℝ) * reducedSource1556 x := by
  norm_num [numericRow1556, reducedSource1556, Integer.Sparse.eval, Sparse.eval, nodeValue1706, nodeValue3289, nodeValue3292, nodeValue3307, nodeValue4068]

theorem reindexCheck1557 : Integer.Sparse.reindex keyMap MixedData.row1557 = numericRow1557 := by decide +kernel

theorem numericCheck1557 (x : Master → ℝ) : Integer.Sparse.eval numericRow1557 x =
    (1 : ℝ) * reducedSource1557 x := by
  norm_num [numericRow1557, reducedSource1557, Integer.Sparse.eval, Sparse.eval, nodeValue1648, nodeValue3072, nodeValue3286, nodeValue3303, nodeValue3304, nodeValue4068]

theorem reindexCheck1558 : Integer.Sparse.reindex keyMap MixedData.row1558 = numericRow1558 := by decide +kernel

theorem numericCheck1558 (x : Master → ℝ) : Integer.Sparse.eval numericRow1558 x =
    (1 : ℝ) * reducedSource1558 x := by
  norm_num [numericRow1558, reducedSource1558, Integer.Sparse.eval, Sparse.eval, nodeValue1636, nodeValue1639, nodeValue1641, nodeValue1648, nodeValue1708, nodeValue3303, nodeValue4068]

theorem reindexCheck1561 : Integer.Sparse.reindex keyMap MixedData.row1561 = numericRow1561 := by decide +kernel

theorem numericCheck1561 (x : Master → ℝ) : Integer.Sparse.eval numericRow1561 x =
    (4 : ℝ) * reducedSource1561 x := by
  norm_num [numericRow1561, reducedSource1561, Integer.Sparse.eval, Sparse.eval, nodeValue4169, nodeValue4170, nodeValue4173, nodeValue4540, nodeValue4542, nodeValue4599, nodeValue4600, nodeValue4601, nodeValue4603, nodeValue4606, nodeValue5162, nodeValue5273, nodeValue5290] <;> ring

theorem reindexCheck1563 : Integer.Sparse.reindex keyMap MixedData.row1563 = numericRow1563 := by decide +kernel

theorem numericCheck1563 (x : Master → ℝ) : Integer.Sparse.eval numericRow1563 x =
    (1 : ℝ) * reducedSource1563 x := by
  norm_num [numericRow1563, reducedSource1563, Integer.Sparse.eval, Sparse.eval, nodeValue1502, nodeValue1503, nodeValue1508, nodeValue2688, nodeValue2702, nodeValue3257, nodeValue3289, nodeValue3292, nodeValue3294, nodeValue3299, nodeValue3546, nodeValue3563, nodeValue3581]

theorem reindexCheck1564 : Integer.Sparse.reindex keyMap MixedData.row1564 = numericRow1564 := by decide +kernel

theorem numericCheck1564 (x : Master → ℝ) : Integer.Sparse.eval numericRow1564 x =
    (1 : ℝ) * reducedSource1564 x := by
  norm_num [numericRow1564, reducedSource1564, Integer.Sparse.eval, Sparse.eval, nodeValue637, nodeValue640, nodeValue651, nodeValue1293, nodeValue4091]

theorem reindexCheck1565 : Integer.Sparse.reindex keyMap MixedData.row1565 = numericRow1565 := by decide +kernel

theorem numericCheck1565 (x : Master → ℝ) : Integer.Sparse.eval numericRow1565 x =
    (1440 : ℝ) * reducedSource1565 x := by
  norm_num [numericRow1565, reducedSource1565, Integer.Sparse.eval, Sparse.eval, nodeValue1034, nodeValue1073, nodeValue1081, nodeValue1228, nodeValue1235, nodeValue1256, nodeValue1260, nodeValue1286, nodeValue1291, nodeValue1299, nodeValue1405, nodeValue1435, nodeValue1441] <;> ring

theorem reindexCheck1566 : Integer.Sparse.reindex keyMap MixedData.row1566 = numericRow1566 := by decide +kernel

theorem numericCheck1566 (x : Master → ℝ) : Integer.Sparse.eval numericRow1566 x =
    (1 : ℝ) * reducedSource1566 x := by
  norm_num [numericRow1566, reducedSource1566, Integer.Sparse.eval, Sparse.eval, nodeValue1644, nodeValue1648, nodeValue1726, nodeValue3304, nodeValue4068]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1552 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1552 (mixedVector B) = 0 := by
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1638 : mixedVector B (Sum.inr 1638) = Sparse.eval nodeValue1638 (mixedVector B) := by
    change mixedMoment B node1638 node1638Labels = _
    exact sound1638 B hB hF
  have h1644 : mixedVector B (Sum.inr 1644) = Sparse.eval nodeValue1644 (mixedVector B) := by
    change mixedMoment B node1644 node1644Labels = _
    exact sound1644 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1835, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1636, h1638, h1644, h1706, h3289, h4068, reducedSource1552] using sourceEq1835 B hB

theorem rowSound1552 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1552 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1552, numericCheck1552, reducedZero1552 B hB hF, mul_zero]

theorem reducedZero1553 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1553 (mixedVector B) = 0 := by
  have h1593 : mixedVector B (Sum.inr 1593) = Sparse.eval nodeValue1593 (mixedVector B) := by
    change mixedMoment B node1593 node1593Labels = _
    exact sound1593 B hB hF
  have h1595 : mixedVector B (Sum.inr 1595) = Sparse.eval nodeValue1595 (mixedVector B) := by
    change mixedMoment B node1595 node1595Labels = _
    exact sound1595 B hB hF
  have h1600 : mixedVector B (Sum.inr 1600) = Sparse.eval nodeValue1600 (mixedVector B) := by
    change mixedMoment B node1600 node1600Labels = _
    exact sound1600 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1836, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1593, h1595, h1600, h1708, h3289, h4068, reducedSource1553] using sourceEq1836 B hB

theorem rowSound1553 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1553 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1553, numericCheck1553, reducedZero1553 B hB hF, mul_zero]

theorem reducedZero1554 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1554 (mixedVector B) = 0 := by
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h3307 : mixedVector B (Sum.inr 3307) = Sparse.eval nodeValue3307 (mixedVector B) := by
    change mixedMoment B node3307 node3307Labels = _
    exact sound3307 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1837, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1708, h3289, h3303, h3304, h3307, h4068, reducedSource1554] using sourceEq1837 B hB

theorem rowSound1554 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1554 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1554, numericCheck1554, reducedZero1554 B hB hF, mul_zero]

theorem reducedZero1555 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1555 (mixedVector B) = 0 := by
  have h1600 : mixedVector B (Sum.inr 1600) = Sparse.eval nodeValue1600 (mixedVector B) := by
    change mixedMoment B node1600 node1600Labels = _
    exact sound1600 B hB hF
  have h3239 : mixedVector B (Sum.inr 3239) = Sparse.eval nodeValue3239 (mixedVector B) := by
    change mixedMoment B node3239 node3239Labels = _
    exact sound3239 B hB hF
  have h3286 : mixedVector B (Sum.inr 3286) = Sparse.eval nodeValue3286 (mixedVector B) := by
    change mixedMoment B node3286 node3286Labels = _
    exact sound3286 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1838, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1600, h3239, h3286, h3289, h3292, h4068, reducedSource1555] using sourceEq1838 B hB

theorem rowSound1555 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1555 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1555, numericCheck1555, reducedZero1555 B hB hF, mul_zero]

theorem reducedZero1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1556 (mixedVector B) = 0 := by
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3307 : mixedVector B (Sum.inr 3307) = Sparse.eval nodeValue3307 (mixedVector B) := by
    change mixedMoment B node3307 node3307Labels = _
    exact sound3307 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1839, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1706, h3289, h3292, h3307, h4068, reducedSource1556] using sourceEq1839 B hB

theorem rowSound1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1556 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1556, numericCheck1556, reducedZero1556 B hB hF, mul_zero]

theorem reducedZero1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1557 (mixedVector B) = 0 := by
  have h1648 : mixedVector B (Sum.inr 1648) = Sparse.eval nodeValue1648 (mixedVector B) := by
    change mixedMoment B node1648 node1648Labels = _
    exact sound1648 B hB hF
  have h3072 : mixedVector B (Sum.inr 3072) = Sparse.eval nodeValue3072 (mixedVector B) := by
    change mixedMoment B node3072 node3072Labels = _
    exact sound3072 B hB hF
  have h3286 : mixedVector B (Sum.inr 3286) = Sparse.eval nodeValue3286 (mixedVector B) := by
    change mixedMoment B node3286 node3286Labels = _
    exact sound3286 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1841, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1648, h3072, h3286, h3303, h3304, h4068, reducedSource1557] using sourceEq1841 B hB

theorem rowSound1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1557 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1557, numericCheck1557, reducedZero1557 B hB hF, mul_zero]

theorem reducedZero1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1558 (mixedVector B) = 0 := by
  have h1636 : mixedVector B (Sum.inr 1636) = Sparse.eval nodeValue1636 (mixedVector B) := by
    change mixedMoment B node1636 node1636Labels = _
    exact sound1636 B hB hF
  have h1639 : mixedVector B (Sum.inr 1639) = Sparse.eval nodeValue1639 (mixedVector B) := by
    change mixedMoment B node1639 node1639Labels = _
    exact sound1639 B hB hF
  have h1641 : mixedVector B (Sum.inr 1641) = Sparse.eval nodeValue1641 (mixedVector B) := by
    change mixedMoment B node1641 node1641Labels = _
    exact sound1641 B hB hF
  have h1648 : mixedVector B (Sum.inr 1648) = Sparse.eval nodeValue1648 (mixedVector B) := by
    change mixedMoment B node1648 node1648Labels = _
    exact sound1648 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h3303 : mixedVector B (Sum.inr 3303) = Sparse.eval nodeValue3303 (mixedVector B) := by
    change mixedMoment B node3303 node3303Labels = _
    exact sound3303 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1842, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1636, h1639, h1641, h1648, h1708, h3303, h4068, reducedSource1558] using sourceEq1842 B hB

theorem rowSound1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1558 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1558, numericCheck1558, reducedZero1558 B hB hF, mul_zero]

theorem reducedZero1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1561 (mixedVector B) = 0 := by
  have h4169 : mixedVector B (Sum.inr 4169) = Sparse.eval nodeValue4169 (mixedVector B) := by
    change mixedMoment B node4169 node4169Labels = _
    exact sound4169 B hB hF
  have h4170 : mixedVector B (Sum.inr 4170) = Sparse.eval nodeValue4170 (mixedVector B) := by
    change mixedMoment B node4170 node4170Labels = _
    exact sound4170 B hB hF
  have h4173 : mixedVector B (Sum.inr 4173) = Sparse.eval nodeValue4173 (mixedVector B) := by
    change mixedMoment B node4173 node4173Labels = _
    exact sound4173 B hB hF
  have h4540 : mixedVector B (Sum.inr 4540) = Sparse.eval nodeValue4540 (mixedVector B) := by
    change mixedMoment B node4540 node4540Labels = _
    exact sound4540 B hB hF
  have h4542 : mixedVector B (Sum.inr 4542) = Sparse.eval nodeValue4542 (mixedVector B) := by
    change mixedMoment B node4542 node4542Labels = _
    exact sound4542 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4600 : mixedVector B (Sum.inr 4600) = Sparse.eval nodeValue4600 (mixedVector B) := by
    change mixedMoment B node4600 node4600Labels = _
    exact sound4600 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4603 : mixedVector B (Sum.inr 4603) = Sparse.eval nodeValue4603 (mixedVector B) := by
    change mixedMoment B node4603 node4603Labels = _
    exact sound4603 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h5162 : mixedVector B (Sum.inr 5162) = Sparse.eval nodeValue5162 (mixedVector B) := by
    change mixedMoment B node5162 node5162Labels = _
    exact sound5162 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  simpa only [sourceForm1845, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4169, h4170, h4173, h4540, h4542, h4599, h4600, h4601, h4603, h4606, h5162, h5273, h5290, reducedSource1561] using sourceEq1845 B hB

theorem rowSound1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1561 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1561, numericCheck1561, reducedZero1561 B hB hF, mul_zero]

theorem reducedZero1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1563 (mixedVector B) = 0 := by
  have h1502 : mixedVector B (Sum.inr 1502) = Sparse.eval nodeValue1502 (mixedVector B) := by
    change mixedMoment B node1502 node1502Labels = _
    exact sound1502 B hB hF
  have h1503 : mixedVector B (Sum.inr 1503) = Sparse.eval nodeValue1503 (mixedVector B) := by
    change mixedMoment B node1503 node1503Labels = _
    exact sound1503 B hB hF
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h2688 : mixedVector B (Sum.inr 2688) = Sparse.eval nodeValue2688 (mixedVector B) := by
    change mixedMoment B node2688 node2688Labels = _
    exact sound2688 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h3257 : mixedVector B (Sum.inr 3257) = Sparse.eval nodeValue3257 (mixedVector B) := by
    change mixedMoment B node3257 node3257Labels = _
    exact sound3257 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3563 : mixedVector B (Sum.inr 3563) = Sparse.eval nodeValue3563 (mixedVector B) := by
    change mixedMoment B node3563 node3563Labels = _
    exact sound3563 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  simpa only [sourceForm1847, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1502, h1503, h1508, h2688, h2702, h3257, h3289, h3292, h3294, h3299, h3546, h3563, h3581, reducedSource1563] using sourceEq1847 B hB

theorem rowSound1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1563 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1563, numericCheck1563, reducedZero1563 B hB hF, mul_zero]

theorem reducedZero1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1564 (mixedVector B) = 0 := by
  have h637 : mixedVector B (Sum.inr 637) = Sparse.eval nodeValue637 (mixedVector B) := by
    change mixedMoment B node637 node637Labels = _
    exact sound637 B hB hF
  have h640 : mixedVector B (Sum.inr 640) = Sparse.eval nodeValue640 (mixedVector B) := by
    change mixedMoment B node640 node640Labels = _
    exact sound640 B hB hF
  have h651 : mixedVector B (Sum.inr 651) = Sparse.eval nodeValue651 (mixedVector B) := by
    change mixedMoment B node651 node651Labels = _
    exact sound651 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1848, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h637, h640, h651, h1293, h4091, reducedSource1564] using sourceEq1848 B hB

theorem rowSound1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1564 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1564, numericCheck1564, reducedZero1564 B hB hF, mul_zero]

theorem reducedZero1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1565 (mixedVector B) = 0 := by
  have h1034 : mixedVector B (Sum.inr 1034) = Sparse.eval nodeValue1034 (mixedVector B) := by
    change mixedMoment B node1034 node1034Labels = _
    exact sound1034 B hB hF
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h1228 : mixedVector B (Sum.inr 1228) = Sparse.eval nodeValue1228 (mixedVector B) := by
    change mixedMoment B node1228 node1228Labels = _
    exact sound1228 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1256 : mixedVector B (Sum.inr 1256) = Sparse.eval nodeValue1256 (mixedVector B) := by
    change mixedMoment B node1256 node1256Labels = _
    exact sound1256 B hB hF
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h1286 : mixedVector B (Sum.inr 1286) = Sparse.eval nodeValue1286 (mixedVector B) := by
    change mixedMoment B node1286 node1286Labels = _
    exact sound1286 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h1299 : mixedVector B (Sum.inr 1299) = Sparse.eval nodeValue1299 (mixedVector B) := by
    change mixedMoment B node1299 node1299Labels = _
    exact sound1299_e B hB hF
  have h1405 : mixedVector B (Sum.inr 1405) = Sparse.eval nodeValue1405 (mixedVector B) := by
    change mixedMoment B node1405 node1405Labels = _
    exact sound1405 B hB hF
  have h1435 : mixedVector B (Sum.inr 1435) = Sparse.eval nodeValue1435 (mixedVector B) := by
    change mixedMoment B node1435 node1435Labels = _
    exact sound1435 B hB hF
  have h1441 : mixedVector B (Sum.inr 1441) = Sparse.eval nodeValue1441 (mixedVector B) := by
    change mixedMoment B node1441 node1441Labels = _
    exact sound1441_e B hB hF
  simpa only [sourceForm1850, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1034, h1073, h1081, h1228, h1235, h1256, h1260, h1286, h1291, h1299, h1405, h1435, h1441, reducedSource1565] using sourceEq1850 B hB

theorem rowSound1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1565 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1565, numericCheck1565, reducedZero1565 B hB hF, mul_zero]

theorem reducedZero1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1566 (mixedVector B) = 0 := by
  have h1644 : mixedVector B (Sum.inr 1644) = Sparse.eval nodeValue1644 (mixedVector B) := by
    change mixedMoment B node1644 node1644Labels = _
    exact sound1644 B hB hF
  have h1648 : mixedVector B (Sum.inr 1648) = Sparse.eval nodeValue1648 (mixedVector B) := by
    change mixedMoment B node1648 node1648Labels = _
    exact sound1648 B hB hF
  have h1726 : mixedVector B (Sum.inr 1726) = Sparse.eval nodeValue1726 (mixedVector B) := by
    change mixedMoment B node1726 node1726Labels = _
    exact sound1726 B hB hF
  have h3304 : mixedVector B (Sum.inr 3304) = Sparse.eval nodeValue3304 (mixedVector B) := by
    change mixedMoment B node3304 node3304Labels = _
    exact sound3304 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1851, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1644, h1648, h1726, h3304, h4068, reducedSource1566] using sourceEq1851 B hB

theorem rowSound1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1566 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1566, numericCheck1566, reducedZero1566 B hB hF, mul_zero]

theorem sourceRowsAt1552 : MixedData.sourceRows (1552 : Fin 2425) =
    MixedData.row1552 := by decide +kernel

theorem sourceRowsAt1553 : MixedData.sourceRows (1553 : Fin 2425) =
    MixedData.row1553 := by decide +kernel

theorem sourceRowsAt1554 : MixedData.sourceRows (1554 : Fin 2425) =
    MixedData.row1554 := by decide +kernel

theorem sourceRowsAt1555 : MixedData.sourceRows (1555 : Fin 2425) =
    MixedData.row1555 := by decide +kernel

theorem sourceRowsAt1556 : MixedData.sourceRows (1556 : Fin 2425) =
    MixedData.row1556 := by decide +kernel

theorem sourceRowsAt1557 : MixedData.sourceRows (1557 : Fin 2425) =
    MixedData.row1557 := by decide +kernel

theorem sourceRowsAt1558 : MixedData.sourceRows (1558 : Fin 2425) =
    MixedData.row1558 := by decide +kernel

theorem sourceRowsAt1559 : MixedData.sourceRows (1559 : Fin 2425) =
    MixedData.row1559 := by decide +kernel

theorem sourceRowsAt1560 : MixedData.sourceRows (1560 : Fin 2425) =
    MixedData.row1560 := by decide +kernel

theorem sourceRowsAt1561 : MixedData.sourceRows (1561 : Fin 2425) =
    MixedData.row1561 := by decide +kernel

theorem sourceRowsAt1562 : MixedData.sourceRows (1562 : Fin 2425) =
    MixedData.row1562 := by decide +kernel

theorem sourceRowsAt1563 : MixedData.sourceRows (1563 : Fin 2425) =
    MixedData.row1563 := by decide +kernel

theorem sourceRowsAt1564 : MixedData.sourceRows (1564 : Fin 2425) =
    MixedData.row1564 := by decide +kernel

theorem sourceRowsAt1565 : MixedData.sourceRows (1565 : Fin 2425) =
    MixedData.row1565 := by decide +kernel

theorem sourceRowsAt1566 : MixedData.sourceRows (1566 : Fin 2425) =
    MixedData.row1566 := by decide +kernel

theorem sourceRowsAt1567 : MixedData.sourceRows (1567 : Fin 2425) =
    MixedData.row1567 := by decide +kernel

theorem chunkSound97_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 97) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1552 ∨ k.val = 1553 ∨ k.val = 1554 ∨ k.val = 1555 ∨ k.val = 1556 ∨ k.val = 1557 ∨ k.val = 1558 ∨ k.val = 1559 ∨ k.val = 1560 ∨ k.val = 1561 ∨ k.val = 1562 ∨ k.val = 1563 ∨ k.val = 1564 ∨ k.val = 1565 ∨ k.val = 1566 ∨ k.val = 1567 := by omega
  rcases heq with h1552 | h1553 | h1554 | h1555 | h1556 | h1557 | h1558 | h1559 | h1560 | h1561 | h1562 | h1563 | h1564 | h1565 | h1566 | h1567
  · have he : k = (1552 : Fin 2425) := Fin.ext h1552
    subst k
    rw [sourceRowsAt1552]
    exact rowSound1552 B hB hF
  · have he : k = (1553 : Fin 2425) := Fin.ext h1553
    subst k
    rw [sourceRowsAt1553]
    exact rowSound1553 B hB hF
  · have he : k = (1554 : Fin 2425) := Fin.ext h1554
    subst k
    rw [sourceRowsAt1554]
    exact rowSound1554 B hB hF
  · have he : k = (1555 : Fin 2425) := Fin.ext h1555
    subst k
    rw [sourceRowsAt1555]
    exact rowSound1555 B hB hF
  · have he : k = (1556 : Fin 2425) := Fin.ext h1556
    subst k
    rw [sourceRowsAt1556]
    exact rowSound1556 B hB hF
  · have he : k = (1557 : Fin 2425) := Fin.ext h1557
    subst k
    rw [sourceRowsAt1557]
    exact rowSound1557 B hB hF
  · have he : k = (1558 : Fin 2425) := Fin.ext h1558
    subst k
    rw [sourceRowsAt1558]
    exact rowSound1558 B hB hF
  · have he : k = (1559 : Fin 2425) := Fin.ext h1559
    subst k
    rw [sourceRowsAt1559]
    exact rowSound1559_e B hB hF
  · have he : k = (1560 : Fin 2425) := Fin.ext h1560
    subst k
    rw [sourceRowsAt1560]
    exact rowSound1560_e B hB hF
  · have he : k = (1561 : Fin 2425) := Fin.ext h1561
    subst k
    rw [sourceRowsAt1561]
    exact rowSound1561 B hB hF
  · have he : k = (1562 : Fin 2425) := Fin.ext h1562
    subst k
    rw [sourceRowsAt1562]
    exact rowSound1562_e B hB hF
  · have he : k = (1563 : Fin 2425) := Fin.ext h1563
    subst k
    rw [sourceRowsAt1563]
    exact rowSound1563 B hB hF
  · have he : k = (1564 : Fin 2425) := Fin.ext h1564
    subst k
    rw [sourceRowsAt1564]
    exact rowSound1564 B hB hF
  · have he : k = (1565 : Fin 2425) := Fin.ext h1565
    subst k
    rw [sourceRowsAt1565]
    exact rowSound1565 B hB hF
  · have he : k = (1566 : Fin 2425) := Fin.ext h1566
    subst k
    rw [sourceRowsAt1566]
    exact rowSound1566 B hB hF
  · have he : k = (1567 : Fin 2425) := Fin.ext h1567
    subst k
    rw [sourceRowsAt1567]
    exact rowSound1567_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e_oai
