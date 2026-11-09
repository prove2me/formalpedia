-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:21:16.35417+00:00
-- url     : https://prove2.me/submissions/fd4b1737-cb2f-4b91-97b9-059ccbd65a2b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero818_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound817_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound822_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound823_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15465 raw15465Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw15465 raw15465Labels = mixedMoment B raw15465step0 raw15465step0Labels := by
      have ha : raw15465step0 = (fun i j => raw15465 (permutation296 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15465step0 raw15465; decide +kernel
      have hl : raw15465step0Labels = raw15465Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15465 raw15465Labels permutation296 permutation5
    mixedMoment B raw15465step0 raw15465step0Labels = mixedMoment B raw15465step1 raw15465step1Labels := by
      have ha : raw15465step1 = -raw15465step0 := by apply Matrix.ext; change ∀ i j, raw15465step1 i j = -(raw15465step0 i j); unfold raw15465step1 raw15465step0; decide +kernel
      have hl : raw15465step1Labels = raw15465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15465step1 raw15465step1Labels = mixedMoment B raw15465step2 raw15465step2Labels := by
      have ha : raw15465step2 = raw15465step1 := by apply Matrix.ext; unfold raw15465step2 raw15465step1; decide +kernel
      have hl : raw15465step1Labels = labelEmbedding8 ∘ raw15465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15465step1 raw15465step1Labels raw15465step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

theorem canonical15466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15466 raw15466Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw15466 raw15466Labels = mixedMoment B raw15466step0 raw15466step0Labels := by
      have ha : raw15466step0 = (fun i j => raw15466 (permutation527 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15466step0 raw15466; decide +kernel
      have hl : raw15466step0Labels = raw15466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15466 raw15466Labels permutation527 permutation4
    mixedMoment B raw15466step0 raw15466step0Labels = mixedMoment B raw15466step1 raw15466step1Labels := by
      have ha : raw15466step1 = raw15466step0 := by apply Matrix.ext; unfold raw15466step1 raw15466step0; decide +kernel
      have hl : raw15466step0Labels = labelEmbedding7 ∘ raw15466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15466step0 raw15466step0Labels raw15466step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

theorem canonical15467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15467 raw15467Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw15467 raw15467Labels = mixedMoment B raw15467step0 raw15467step0Labels := by
      have ha : raw15467step0 = (fun i j => raw15467 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15467step0 raw15467; decide +kernel
      have hl : raw15467step0Labels = raw15467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15467 raw15467Labels permutation526 permutation4
    mixedMoment B raw15467step0 raw15467step0Labels = mixedMoment B raw15467step1 raw15467step1Labels := by
      have ha : raw15467step1 = raw15467step0 := by apply Matrix.ext; unfold raw15467step1 raw15467step0; decide +kernel
      have hl : raw15467step0Labels = labelEmbedding7 ∘ raw15467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15467step0 raw15467step0Labels raw15467step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

theorem canonical15468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15468 raw15468Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw15468 raw15468Labels = mixedMoment B raw15468step0 raw15468step0Labels := by
      have ha : raw15468step0 = (fun i j => raw15468 (permutation228 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15468step0 raw15468; decide +kernel
      have hl : raw15468step0Labels = raw15468Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15468 raw15468Labels permutation228 permutation6
    mixedMoment B raw15468step0 raw15468step0Labels = mixedMoment B raw15468step1 raw15468step1Labels := by
      have ha : raw15468step1 = -raw15468step0 := by apply Matrix.ext; change ∀ i j, raw15468step1 i j = -(raw15468step0 i j); unfold raw15468step1 raw15468step0; decide +kernel
      have hl : raw15468step1Labels = raw15468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15468step1 raw15468step1Labels = mixedMoment B raw15468step2 raw15468step2Labels := by
      have ha : raw15468step2 = raw15468step1 := by apply Matrix.ext; unfold raw15468step2 raw15468step1; decide +kernel
      have hl : raw15468step1Labels = labelEmbedding9 ∘ raw15468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15468step1 raw15468step1Labels raw15468step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical15469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15469 raw15469Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw15469 raw15469Labels = mixedMoment B raw15469step0 raw15469step0Labels := by
      have ha : raw15469step0 = (fun i j => raw15469 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15469step0 raw15469; decide +kernel
      have hl : raw15469step0Labels = raw15469Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15469 raw15469Labels permutation526 permutation4
    mixedMoment B raw15469step0 raw15469step0Labels = mixedMoment B raw15469step1 raw15469step1Labels := by
      have ha : raw15469step1 = raw15469step0 := by apply Matrix.ext; unfold raw15469step1 raw15469step0; decide +kernel
      have hl : raw15469step0Labels = labelEmbedding7 ∘ raw15469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15469step0 raw15469step0Labels raw15469step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical15470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15470 raw15470Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw15470 raw15470Labels = mixedMoment B raw15470step0 raw15470step0Labels := by
      have hz : ∀ j, raw15470 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw15470step0 = (fun i j => raw15470 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw15470step0 raw15470; decide +kernel
      have hl : raw15470step0Labels = raw15470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15470 raw15470Labels permutation265 hz
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical15471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15471 raw15471Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw15471 raw15471Labels = mixedMoment B raw15471step0 raw15471step0Labels := by
      have ha : raw15471step0 = (fun i j => raw15471 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15471step0 raw15471; decide +kernel
      have hl : raw15471step0Labels = raw15471Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15471 raw15471Labels permutation271 permutation3
    mixedMoment B raw15471step0 raw15471step0Labels = mixedMoment B raw15471step1 raw15471step1Labels := by
      have ha : raw15471step1 = raw15471step0 := by apply Matrix.ext; unfold raw15471step1 raw15471step0; decide +kernel
      have hl : raw15471step0Labels = labelEmbedding6 ∘ raw15471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15471step0 raw15471step0Labels raw15471step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical15472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15472 raw15472Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw15472 raw15472Labels = mixedMoment B raw15472step0 raw15472step0Labels := by
      have ha : raw15472step0 = (fun i j => raw15472 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15472step0 raw15472; decide +kernel
      have hl : raw15472step0Labels = raw15472Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15472 raw15472Labels permutation160 permutation2
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical15473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15473 raw15473Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw15473 raw15473Labels = mixedMoment B raw15473step0 raw15473step0Labels := by
      have ha : raw15473step0 = (fun i j => raw15473 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15473step0 raw15473; decide +kernel
      have hl : raw15473step0Labels = raw15473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15473 raw15473Labels permutation166 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical15474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15474 raw15474Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw15474 raw15474Labels = mixedMoment B raw15474step0 raw15474step0Labels := by
      have ha : raw15474step0 = (fun i j => raw15474 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15474step0 raw15474; decide +kernel
      have hl : raw15474step0Labels = raw15474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15474 raw15474Labels permutation160 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical15475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15475 raw15475Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw15475 raw15475Labels = mixedMoment B raw15475step0 raw15475step0Labels := by
      have ha : raw15475step0 = (fun i j => raw15475 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15475step0 raw15475; decide +kernel
      have hl : raw15475step0Labels = raw15475Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15475 raw15475Labels permutation265 permutation3
    mixedMoment B raw15475step0 raw15475step0Labels = mixedMoment B raw15475step1 raw15475step1Labels := by
      have ha : raw15475step1 = raw15475step0 := by apply Matrix.ext; unfold raw15475step1 raw15475step0; decide +kernel
      have hl : raw15475step0Labels = labelEmbedding6 ∘ raw15475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15475step0 raw15475step0Labels raw15475step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical15476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15476 raw15476Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw15476 raw15476Labels = mixedMoment B raw15476step0 raw15476step0Labels := by
      have ha : raw15476step0 = (fun i j => raw15476 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15476step0 raw15476; decide +kernel
      have hl : raw15476step0Labels = raw15476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15476 raw15476Labels permutation154 permutation2
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical15477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15477 raw15477Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw15477 raw15477Labels = mixedMoment B raw15477step0 raw15477step0Labels := by
      have ha : raw15477step0 = (fun i j => raw15477 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15477step0 raw15477; decide +kernel
      have hl : raw15477step0Labels = raw15477Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15477 raw15477Labels permutation164 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical15478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15478 raw15478Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw15478 raw15478Labels = mixedMoment B raw15478step0 raw15478step0Labels := by
      have ha : raw15478step0 = (fun i j => raw15478 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15478step0 raw15478; decide +kernel
      have hl : raw15478step0Labels = raw15478Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15478 raw15478Labels permutation154 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical15479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15479 raw15479Labels = mixedMoment B node5004 node5004Labels := by
  calc
    mixedMoment B raw15479 raw15479Labels = mixedMoment B raw15479step0 raw15479step0Labels := by
      have ha : raw15479step0 = (fun i j => raw15479 (permutation572 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15479step0 raw15479; decide +kernel
      have hl : raw15479step0Labels = raw15479Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15479 raw15479Labels permutation572 permutation5
    mixedMoment B raw15479step0 raw15479step0Labels = mixedMoment B raw15479step1 raw15479step1Labels := by
      have ha : raw15479step1 = raw15479step0 := by apply Matrix.ext; unfold raw15479step1 raw15479step0; decide +kernel
      have hl : raw15479step0Labels = labelEmbedding8 ∘ raw15479step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15479step0 raw15479step0Labels raw15479step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5004 node5004Labels := by rfl

theorem canonical15480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15480 raw15480Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw15480 raw15480Labels = mixedMoment B raw15480step0 raw15480step0Labels := by
      have ha : raw15480step0 = (fun i j => raw15480 (permutation573 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15480step0 raw15480; decide +kernel
      have hl : raw15480step0Labels = raw15480Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15480 raw15480Labels permutation573 permutation5
    mixedMoment B raw15480step0 raw15480step0Labels = mixedMoment B raw15480step1 raw15480step1Labels := by
      have ha : raw15480step1 = raw15480step0 := by apply Matrix.ext; unfold raw15480step1 raw15480step0; decide +kernel
      have hl : raw15480step0Labels = labelEmbedding8 ∘ raw15480step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15480step0 raw15480step0Labels raw15480step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

theorem canonical15481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15481 raw15481Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw15481 raw15481Labels = mixedMoment B raw15481step0 raw15481step0Labels := by
      have ha : raw15481step0 = (fun i j => raw15481 (permutation571 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15481step0 raw15481; decide +kernel
      have hl : raw15481step0Labels = raw15481Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15481 raw15481Labels permutation571 permutation5
    mixedMoment B raw15481step0 raw15481step0Labels = mixedMoment B raw15481step1 raw15481step1Labels := by
      have ha : raw15481step1 = raw15481step0 := by apply Matrix.ext; unfold raw15481step1 raw15481step0; decide +kernel
      have hl : raw15481step0Labels = labelEmbedding8 ∘ raw15481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15481step0 raw15481step0Labels raw15481step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

theorem canonical15482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15482 raw15482Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw15482 raw15482Labels = mixedMoment B raw15482step0 raw15482step0Labels := by
      have ha : raw15482step0 = (fun i j => raw15482 (permutation572 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15482step0 raw15482; decide +kernel
      have hl : raw15482step0Labels = raw15482Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15482 raw15482Labels permutation572 permutation5
    mixedMoment B raw15482step0 raw15482step0Labels = mixedMoment B raw15482step1 raw15482step1Labels := by
      have ha : raw15482step1 = raw15482step0 := by apply Matrix.ext; unfold raw15482step1 raw15482step0; decide +kernel
      have hl : raw15482step0Labels = labelEmbedding8 ∘ raw15482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15482step0 raw15482step0Labels raw15482step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical15483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15483 raw15483Labels = mixedMoment B node4993 node4993Labels := by
  calc
    mixedMoment B raw15483 raw15483Labels = mixedMoment B raw15483step0 raw15483step0Labels := by
      have ha : raw15483step0 = (fun i j => raw15483 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15483step0 raw15483; decide +kernel
      have hl : raw15483step0Labels = raw15483Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15483 raw15483Labels permutation681 permutation3
    mixedMoment B raw15483step0 raw15483step0Labels = mixedMoment B raw15483step1 raw15483step1Labels := by
      have ha : raw15483step1 = -raw15483step0 := by apply Matrix.ext; change ∀ i j, raw15483step1 i j = -(raw15483step0 i j); unfold raw15483step1 raw15483step0; decide +kernel
      have hl : raw15483step1Labels = raw15483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15483step1 raw15483step1Labels = mixedMoment B raw15483step2 raw15483step2Labels := by
      have ha : raw15483step2 = raw15483step1 := by apply Matrix.ext; unfold raw15483step2 raw15483step1; decide +kernel
      have hl : raw15483step1Labels = labelEmbedding6 ∘ raw15483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15483step1 raw15483step1Labels raw15483step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4993 node4993Labels := by rfl

theorem canonical15484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15484 raw15484Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw15484 raw15484Labels = mixedMoment B raw15484step0 raw15484step0Labels := by
      have ha : raw15484step0 = (fun i j => raw15484 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15484step0 raw15484; decide +kernel
      have hl : raw15484step0Labels = raw15484Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15484 raw15484Labels permutation686 permutation3
    mixedMoment B raw15484step0 raw15484step0Labels = mixedMoment B raw15484step1 raw15484step1Labels := by
      have ha : raw15484step1 = -raw15484step0 := by apply Matrix.ext; change ∀ i j, raw15484step1 i j = -(raw15484step0 i j); unfold raw15484step1 raw15484step0; decide +kernel
      have hl : raw15484step1Labels = raw15484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15484step1 raw15484step1Labels = mixedMoment B raw15484step2 raw15484step2Labels := by
      have ha : raw15484step2 = raw15484step1 := by apply Matrix.ext; unfold raw15484step2 raw15484step1; decide +kernel
      have hl : raw15484step1Labels = labelEmbedding6 ∘ raw15484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15484step1 raw15484step1Labels raw15484step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

theorem canonical15485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15485 raw15485Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw15485 raw15485Labels = mixedMoment B raw15485step0 raw15485step0Labels := by
      have ha : raw15485step0 = (fun i j => raw15485 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15485step0 raw15485; decide +kernel
      have hl : raw15485step0Labels = raw15485Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15485 raw15485Labels permutation680 permutation3
    mixedMoment B raw15485step0 raw15485step0Labels = mixedMoment B raw15485step1 raw15485step1Labels := by
      have ha : raw15485step1 = -raw15485step0 := by apply Matrix.ext; change ∀ i j, raw15485step1 i j = -(raw15485step0 i j); unfold raw15485step1 raw15485step0; decide +kernel
      have hl : raw15485step1Labels = raw15485step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15485step1 raw15485step1Labels = mixedMoment B raw15485step2 raw15485step2Labels := by
      have ha : raw15485step2 = raw15485step1 := by apply Matrix.ext; unfold raw15485step2 raw15485step1; decide +kernel
      have hl : raw15485step1Labels = labelEmbedding6 ∘ raw15485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15485step1 raw15485step1Labels raw15485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

theorem canonical15486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15486 raw15486Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw15486 raw15486Labels = mixedMoment B raw15486step0 raw15486step0Labels := by
      have ha : raw15486step0 = (fun i j => raw15486 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15486step0 raw15486; decide +kernel
      have hl : raw15486step0Labels = raw15486Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15486 raw15486Labels permutation682 permutation3
    mixedMoment B raw15486step0 raw15486step0Labels = mixedMoment B raw15486step1 raw15486step1Labels := by
      have ha : raw15486step1 = -raw15486step0 := by apply Matrix.ext; change ∀ i j, raw15486step1 i j = -(raw15486step0 i j); unfold raw15486step1 raw15486step0; decide +kernel
      have hl : raw15486step1Labels = raw15486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15486step1 raw15486step1Labels = mixedMoment B raw15486step2 raw15486step2Labels := by
      have ha : raw15486step2 = raw15486step1 := by apply Matrix.ext; unfold raw15486step2 raw15486step1; decide +kernel
      have hl : raw15486step1Labels = labelEmbedding6 ∘ raw15486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15486step1 raw15486step1Labels raw15486step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15531 raw15531Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw15531 raw15531Labels = mixedMoment B raw15531step0 raw15531step0Labels := by
      have ha : raw15531step0 = (fun i j => raw15531 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15531step0 raw15531; decide +kernel
      have hl : raw15531step0Labels = raw15531Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15531 raw15531Labels permutation528 permutation4
    _ = mixedMoment B node3949 node3949Labels := by rfl

theorem canonical15532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15532 raw15532Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw15532 raw15532Labels = mixedMoment B raw15532step0 raw15532step0Labels := by
      have ha : raw15532step0 = (fun i j => raw15532 (permutation527 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15532step0 raw15532; decide +kernel
      have hl : raw15532step0Labels = raw15532Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15532 raw15532Labels permutation527 permutation4
    _ = mixedMoment B node3947 node3947Labels := by rfl

theorem canonical15533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15533 raw15533Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw15533 raw15533Labels = mixedMoment B raw15533step0 raw15533step0Labels := by
      have ha : raw15533step0 = (fun i j => raw15533 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15533step0 raw15533; decide +kernel
      have hl : raw15533step0Labels = raw15533Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15533 raw15533Labels permutation526 permutation4
    _ = mixedMoment B node3947 node3947Labels := by rfl

theorem canonical15534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15534 raw15534Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw15534 raw15534Labels = mixedMoment B raw15534step0 raw15534step0Labels := by
      have ha : raw15534step0 = (fun i j => raw15534 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15534step0 raw15534; decide +kernel
      have hl : raw15534step0Labels = raw15534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15534 raw15534Labels permutation640 permutation2
    mixedMoment B raw15534step0 raw15534step0Labels = mixedMoment B raw15534step1 raw15534step1Labels := by
      have ha : raw15534step1 = -raw15534step0 := by apply Matrix.ext; change ∀ i j, raw15534step1 i j = -(raw15534step0 i j); unfold raw15534step1 raw15534step0; decide +kernel
      have hl : raw15534step1Labels = raw15534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4008 node4008Labels := by rfl

theorem canonical15535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15535 raw15535Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15535 raw15535Labels = mixedMoment B raw15535step0 raw15535step0Labels := by
      have ha : raw15535step0 = (fun i j => raw15535 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15535step0 raw15535; decide +kernel
      have hl : raw15535step0Labels = raw15535Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15535 raw15535Labels permutation526 permutation4
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical15536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15536 raw15536Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw15536 raw15536Labels = mixedMoment B raw15536step0 raw15536step0Labels := by
      have ha : raw15536step0 = (fun i j => raw15536 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15536step0 raw15536; decide +kernel
      have hl : raw15536step0Labels = raw15536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15536 raw15536Labels permutation160 permutation2
    _ = mixedMoment B node3724 node3724Labels := by rfl

theorem canonical15540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15540 raw15540Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw15540 raw15540Labels = mixedMoment B raw15540step0 raw15540step0Labels := by
      have ha : raw15540step0 = (fun i j => raw15540 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15540step0 raw15540; decide +kernel
      have hl : raw15540step0Labels = raw15540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15540 raw15540Labels permutation160 permutation2
    _ = mixedMoment B node3827 node3827Labels := by rfl

theorem canonical15541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15541 raw15541Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw15541 raw15541Labels = mixedMoment B raw15541step0 raw15541step0Labels := by
      have ha : raw15541step0 = (fun i j => raw15541 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15541step0 raw15541; decide +kernel
      have hl : raw15541step0Labels = raw15541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15541 raw15541Labels permutation166 permutation2
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical15542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15542 raw15542Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw15542 raw15542Labels = mixedMoment B raw15542step0 raw15542step0Labels := by
      have ha : raw15542step0 = (fun i j => raw15542 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15542step0 raw15542; decide +kernel
      have hl : raw15542step0Labels = raw15542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15542 raw15542Labels permutation160 permutation2
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical15543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15543 raw15543Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw15543 raw15543Labels = mixedMoment B raw15543step0 raw15543step0Labels := by
      have ha : raw15543step0 = (fun i j => raw15543 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15543step0 raw15543; decide +kernel
      have hl : raw15543step0Labels = raw15543Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15543 raw15543Labels permutation681 permutation2
    mixedMoment B raw15543step0 raw15543step0Labels = mixedMoment B raw15543step1 raw15543step1Labels := by
      have ha : raw15543step1 = -raw15543step0 := by apply Matrix.ext; change ∀ i j, raw15543step1 i j = -(raw15543step0 i j); unfold raw15543step1 raw15543step0; decide +kernel
      have hl : raw15543step1Labels = raw15543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5471 node5471Labels := by rfl

theorem canonical15544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15544 raw15544Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw15544 raw15544Labels = mixedMoment B raw15544step0 raw15544step0Labels := by
      have ha : raw15544step0 = (fun i j => raw15544 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15544step0 raw15544; decide +kernel
      have hl : raw15544step0Labels = raw15544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15544 raw15544Labels permutation683 permutation2
    mixedMoment B raw15544step0 raw15544step0Labels = mixedMoment B raw15544step1 raw15544step1Labels := by
      have ha : raw15544step1 = -raw15544step0 := by apply Matrix.ext; change ∀ i j, raw15544step1 i j = -(raw15544step0 i j); unfold raw15544step1 raw15544step0; decide +kernel
      have hl : raw15544step1Labels = raw15544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical15545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15545 raw15545Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw15545 raw15545Labels = mixedMoment B raw15545step0 raw15545step0Labels := by
      have ha : raw15545step0 = (fun i j => raw15545 (permutation677 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15545step0 raw15545; decide +kernel
      have hl : raw15545step0Labels = raw15545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15545 raw15545Labels permutation677 permutation2
    mixedMoment B raw15545step0 raw15545step0Labels = mixedMoment B raw15545step1 raw15545step1Labels := by
      have ha : raw15545step1 = -raw15545step0 := by apply Matrix.ext; change ∀ i j, raw15545step1 i j = -(raw15545step0 i j); unfold raw15545step1 raw15545step0; decide +kernel
      have hl : raw15545step1Labels = raw15545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical15546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15546 raw15546Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw15546 raw15546Labels = mixedMoment B raw15546step0 raw15546step0Labels := by
      have ha : raw15546step0 = (fun i j => raw15546 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15546step0 raw15546; decide +kernel
      have hl : raw15546step0Labels = raw15546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15546 raw15546Labels permutation524 permutation4
    mixedMoment B raw15546step0 raw15546step0Labels = mixedMoment B raw15546step1 raw15546step1Labels := by
      have ha : raw15546step1 = -raw15546step0 := by apply Matrix.ext; change ∀ i j, raw15546step1 i j = -(raw15546step0 i j); unfold raw15546step1 raw15546step0; decide +kernel
      have hl : raw15546step1Labels = raw15546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15546step1 raw15546step1Labels = mixedMoment B raw15546step2 raw15546step2Labels := by
      have ha : raw15546step2 = raw15546step1 := by apply Matrix.ext; unfold raw15546step2 raw15546step1; decide +kernel
      have hl : raw15546step1Labels = labelEmbedding7 ∘ raw15546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15546step1 raw15546step1Labels raw15546step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical15547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15547 raw15547Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw15547 raw15547Labels = mixedMoment B raw15547step0 raw15547step0Labels := by
      have ha : raw15547step0 = (fun i j => raw15547 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15547step0 raw15547; decide +kernel
      have hl : raw15547step0Labels = raw15547Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15547 raw15547Labels permutation572 permutation7
    mixedMoment B raw15547step0 raw15547step0Labels = mixedMoment B raw15547step1 raw15547step1Labels := by
      have ha : raw15547step1 = raw15547step0 := by apply Matrix.ext; unfold raw15547step1 raw15547step0; decide +kernel
      have hl : raw15547step0Labels = labelEmbedding10 ∘ raw15547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15547step0 raw15547step0Labels raw15547step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical15548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15548 raw15548Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw15548 raw15548Labels = mixedMoment B raw15548step0 raw15548step0Labels := by
      have ha : raw15548step0 = (fun i j => raw15548 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15548step0 raw15548; decide +kernel
      have hl : raw15548step0Labels = raw15548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15548 raw15548Labels permutation224 permutation5
    mixedMoment B raw15548step0 raw15548step0Labels = mixedMoment B raw15548step1 raw15548step1Labels := by
      have ha : raw15548step1 = -raw15548step0 := by apply Matrix.ext; change ∀ i j, raw15548step1 i j = -(raw15548step0 i j); unfold raw15548step1 raw15548step0; decide +kernel
      have hl : raw15548step1Labels = raw15548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15548step1 raw15548step1Labels = mixedMoment B raw15548step2 raw15548step2Labels := by
      have ha : raw15548step2 = raw15548step1 := by apply Matrix.ext; unfold raw15548step2 raw15548step1; decide +kernel
      have hl : raw15548step1Labels = labelEmbedding8 ∘ raw15548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15548step1 raw15548step1Labels raw15548step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

theorem canonical15549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15549 raw15549Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw15549 raw15549Labels = mixedMoment B raw15549step0 raw15549step0Labels := by
      have ha : raw15549step0 = (fun i j => raw15549 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15549step0 raw15549; decide +kernel
      have hl : raw15549step0Labels = raw15549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15549 raw15549Labels permutation176 permutation3
    mixedMoment B raw15549step0 raw15549step0Labels = mixedMoment B raw15549step1 raw15549step1Labels := by
      have ha : raw15549step1 = raw15549step0 := by apply Matrix.ext; unfold raw15549step1 raw15549step0; decide +kernel
      have hl : raw15549step0Labels = labelEmbedding6 ∘ raw15549step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15549step0 raw15549step0Labels raw15549step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical15550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15550 raw15550Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw15550 raw15550Labels = mixedMoment B raw15550step0 raw15550step0Labels := by
      have ha : raw15550step0 = (fun i j => raw15550 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15550step0 raw15550; decide +kernel
      have hl : raw15550step0Labels = raw15550Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15550 raw15550Labels permutation200 permutation3
    mixedMoment B raw15550step0 raw15550step0Labels = mixedMoment B raw15550step1 raw15550step1Labels := by
      have ha : raw15550step1 = raw15550step0 := by apply Matrix.ext; unfold raw15550step1 raw15550step0; decide +kernel
      have hl : raw15550step0Labels = labelEmbedding6 ∘ raw15550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15550step0 raw15550step0Labels raw15550step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical15551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15551 raw15551Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw15551 raw15551Labels = mixedMoment B raw15551step0 raw15551step0Labels := by
      have ha : raw15551step0 = (fun i j => raw15551 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15551step0 raw15551; decide +kernel
      have hl : raw15551step0Labels = raw15551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15551 raw15551Labels permutation526 permutation4
    mixedMoment B raw15551step0 raw15551step0Labels = mixedMoment B raw15551step1 raw15551step1Labels := by
      have ha : raw15551step1 = -raw15551step0 := by apply Matrix.ext; change ∀ i j, raw15551step1 i j = -(raw15551step0 i j); unfold raw15551step1 raw15551step0; decide +kernel
      have hl : raw15551step1Labels = raw15551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15551step1 raw15551step1Labels = mixedMoment B raw15551step2 raw15551step2Labels := by
      have ha : raw15551step2 = raw15551step1 := by apply Matrix.ext; unfold raw15551step2 raw15551step1; decide +kernel
      have hl : raw15551step1Labels = labelEmbedding7 ∘ raw15551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15551step1 raw15551step1Labels raw15551step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical15552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15552 raw15552Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw15552 raw15552Labels = mixedMoment B raw15552step0 raw15552step0Labels := by
      have ha : raw15552step0 = (fun i j => raw15552 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15552step0 raw15552; decide +kernel
      have hl : raw15552step0Labels = raw15552Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15552 raw15552Labels permutation240 permutation5
    mixedMoment B raw15552step0 raw15552step0Labels = mixedMoment B raw15552step1 raw15552step1Labels := by
      have ha : raw15552step1 = -raw15552step0 := by apply Matrix.ext; change ∀ i j, raw15552step1 i j = -(raw15552step0 i j); unfold raw15552step1 raw15552step0; decide +kernel
      have hl : raw15552step1Labels = raw15552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15552step1 raw15552step1Labels = mixedMoment B raw15552step2 raw15552step2Labels := by
      have ha : raw15552step2 = raw15552step1 := by apply Matrix.ext; unfold raw15552step2 raw15552step1; decide +kernel
      have hl : raw15552step1Labels = labelEmbedding8 ∘ raw15552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15552step1 raw15552step1Labels raw15552step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical15553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15553 raw15553Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw15553 raw15553Labels = mixedMoment B raw15553step0 raw15553step0Labels := by
      have ha : raw15553step0 = (fun i j => raw15553 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15553step0 raw15553; decide +kernel
      have hl : raw15553step0Labels = raw15553Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15553 raw15553Labels permutation160 permutation3
    mixedMoment B raw15553step0 raw15553step0Labels = mixedMoment B raw15553step1 raw15553step1Labels := by
      have ha : raw15553step1 = raw15553step0 := by apply Matrix.ext; unfold raw15553step1 raw15553step0; decide +kernel
      have hl : raw15553step0Labels = labelEmbedding6 ∘ raw15553step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15553step0 raw15553step0Labels raw15553step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

theorem canonical15554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15554 raw15554Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw15554 raw15554Labels = mixedMoment B raw15554step0 raw15554step0Labels := by
      have ha : raw15554step0 = (fun i j => raw15554 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15554step0 raw15554; decide +kernel
      have hl : raw15554step0Labels = raw15554Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15554 raw15554Labels permutation160 permutation3
    mixedMoment B raw15554step0 raw15554step0Labels = mixedMoment B raw15554step1 raw15554step1Labels := by
      have ha : raw15554step1 = raw15554step0 := by apply Matrix.ext; unfold raw15554step1 raw15554step0; decide +kernel
      have hl : raw15554step0Labels = labelEmbedding6 ∘ raw15554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15554step0 raw15554step0Labels raw15554step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

theorem canonical15555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15555 raw15555Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw15555 raw15555Labels = mixedMoment B raw15555step0 raw15555step0Labels := by
      have ha : raw15555step0 = (fun i j => raw15555 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15555step0 raw15555; decide +kernel
      have hl : raw15555step0Labels = raw15555Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15555 raw15555Labels permutation160 permutation3
    mixedMoment B raw15555step0 raw15555step0Labels = mixedMoment B raw15555step1 raw15555step1Labels := by
      have ha : raw15555step1 = raw15555step0 := by apply Matrix.ext; unfold raw15555step1 raw15555step0; decide +kernel
      have hl : raw15555step0Labels = labelEmbedding6 ∘ raw15555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15555step0 raw15555step0Labels raw15555step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

theorem canonical15556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15556 raw15556Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw15556 raw15556Labels = mixedMoment B raw15556step0 raw15556step0Labels := by
      have ha : raw15556step0 = (fun i j => raw15556 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15556step0 raw15556; decide +kernel
      have hl : raw15556step0Labels = raw15556Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15556 raw15556Labels permutation227 permutation5
    mixedMoment B raw15556step0 raw15556step0Labels = mixedMoment B raw15556step1 raw15556step1Labels := by
      have ha : raw15556step1 = -raw15556step0 := by apply Matrix.ext; change ∀ i j, raw15556step1 i j = -(raw15556step0 i j); unfold raw15556step1 raw15556step0; decide +kernel
      have hl : raw15556step1Labels = raw15556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15556step1 raw15556step1Labels = mixedMoment B raw15556step2 raw15556step2Labels := by
      have ha : raw15556step2 = raw15556step1 := by apply Matrix.ext; unfold raw15556step2 raw15556step1; decide +kernel
      have hl : raw15556step1Labels = labelEmbedding8 ∘ raw15556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15556step1 raw15556step1Labels raw15556step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical15557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15557 raw15557Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw15557 raw15557Labels = mixedMoment B raw15557step0 raw15557step0Labels := by
      have ha : raw15557step0 = (fun i j => raw15557 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15557step0 raw15557; decide +kernel
      have hl : raw15557step0Labels = raw15557Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15557 raw15557Labels permutation161 permutation3
    mixedMoment B raw15557step0 raw15557step0Labels = mixedMoment B raw15557step1 raw15557step1Labels := by
      have ha : raw15557step1 = raw15557step0 := by apply Matrix.ext; unfold raw15557step1 raw15557step0; decide +kernel
      have hl : raw15557step0Labels = labelEmbedding6 ∘ raw15557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15557step0 raw15557step0Labels raw15557step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical15558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15558 raw15558Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw15558 raw15558Labels = mixedMoment B raw15558step0 raw15558step0Labels := by
      have ha : raw15558step0 = (fun i j => raw15558 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15558step0 raw15558; decide +kernel
      have hl : raw15558step0Labels = raw15558Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15558 raw15558Labels permutation154 permutation3
    mixedMoment B raw15558step0 raw15558step0Labels = mixedMoment B raw15558step1 raw15558step1Labels := by
      have ha : raw15558step1 = raw15558step0 := by apply Matrix.ext; unfold raw15558step1 raw15558step0; decide +kernel
      have hl : raw15558step0Labels = labelEmbedding6 ∘ raw15558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15558step0 raw15558step0Labels raw15558step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

theorem canonical15559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15559 raw15559Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw15559 raw15559Labels = mixedMoment B raw15559step0 raw15559step0Labels := by
      have ha : raw15559step0 = (fun i j => raw15559 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15559step0 raw15559; decide +kernel
      have hl : raw15559step0Labels = raw15559Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15559 raw15559Labels permutation154 permutation3
    mixedMoment B raw15559step0 raw15559step0Labels = mixedMoment B raw15559step1 raw15559step1Labels := by
      have ha : raw15559step1 = raw15559step0 := by apply Matrix.ext; unfold raw15559step1 raw15559step0; decide +kernel
      have hl : raw15559step0Labels = labelEmbedding6 ∘ raw15559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15559step0 raw15559step0Labels raw15559step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

theorem canonical15560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15560 raw15560Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw15560 raw15560Labels = mixedMoment B raw15560step0 raw15560step0Labels := by
      have ha : raw15560step0 = (fun i j => raw15560 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15560step0 raw15560; decide +kernel
      have hl : raw15560step0Labels = raw15560Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15560 raw15560Labels permutation154 permutation3
    mixedMoment B raw15560step0 raw15560step0Labels = mixedMoment B raw15560step1 raw15560step1Labels := by
      have ha : raw15560step1 = raw15560step0 := by apply Matrix.ext; unfold raw15560step1 raw15560step0; decide +kernel
      have hl : raw15560step0Labels = labelEmbedding6 ∘ raw15560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15560step0 raw15560step0Labels raw15560step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

theorem canonical15561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15561 raw15561Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw15561 raw15561Labels = mixedMoment B raw15561step0 raw15561step0Labels := by
      have ha : raw15561step0 = (fun i j => raw15561 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15561step0 raw15561; decide +kernel
      have hl : raw15561step0Labels = raw15561Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15561 raw15561Labels permutation225 permutation5
    mixedMoment B raw15561step0 raw15561step0Labels = mixedMoment B raw15561step1 raw15561step1Labels := by
      have ha : raw15561step1 = -raw15561step0 := by apply Matrix.ext; change ∀ i j, raw15561step1 i j = -(raw15561step0 i j); unfold raw15561step1 raw15561step0; decide +kernel
      have hl : raw15561step1Labels = raw15561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15561step1 raw15561step1Labels = mixedMoment B raw15561step2 raw15561step2Labels := by
      have ha : raw15561step2 = raw15561step1 := by apply Matrix.ext; unfold raw15561step2 raw15561step1; decide +kernel
      have hl : raw15561step1Labels = labelEmbedding8 ∘ raw15561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15561step1 raw15561step1Labels raw15561step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical15562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15562 raw15562Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw15562 raw15562Labels = mixedMoment B raw15562step0 raw15562step0Labels := by
      have ha : raw15562step0 = (fun i j => raw15562 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15562step0 raw15562; decide +kernel
      have hl : raw15562step0Labels = raw15562Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15562 raw15562Labels permutation155 permutation3
    mixedMoment B raw15562step0 raw15562step0Labels = mixedMoment B raw15562step1 raw15562step1Labels := by
      have ha : raw15562step1 = raw15562step0 := by apply Matrix.ext; unfold raw15562step1 raw15562step0; decide +kernel
      have hl : raw15562step0Labels = labelEmbedding6 ∘ raw15562step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15562step0 raw15562step0Labels raw15562step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical15563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15563 raw15563Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw15563 raw15563Labels = mixedMoment B raw15563step0 raw15563step0Labels := by
      have ha : raw15563step0 = (fun i j => raw15563 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15563step0 raw15563; decide +kernel
      have hl : raw15563step0Labels = raw15563Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15563 raw15563Labels permutation152 permutation3
    mixedMoment B raw15563step0 raw15563step0Labels = mixedMoment B raw15563step1 raw15563step1Labels := by
      have ha : raw15563step1 = raw15563step0 := by apply Matrix.ext; unfold raw15563step1 raw15563step0; decide +kernel
      have hl : raw15563step0Labels = labelEmbedding6 ∘ raw15563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15563step0 raw15563step0Labels raw15563step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

theorem canonical15564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15564 raw15564Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw15564 raw15564Labels = mixedMoment B raw15564step0 raw15564step0Labels := by
      have ha : raw15564step0 = (fun i j => raw15564 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15564step0 raw15564; decide +kernel
      have hl : raw15564step0Labels = raw15564Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15564 raw15564Labels permutation583 permutation2
    mixedMoment B raw15564step0 raw15564step0Labels = mixedMoment B raw15564step1 raw15564step1Labels := by
      have ha : raw15564step1 = -raw15564step0 := by apply Matrix.ext; change ∀ i j, raw15564step1 i j = -(raw15564step0 i j); unfold raw15564step1 raw15564step0; decide +kernel
      have hl : raw15564step1Labels = raw15564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5348 node5348Labels := by rfl

theorem canonical15565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15565 raw15565Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw15565 raw15565Labels = mixedMoment B raw15565step0 raw15565step0Labels := by
      have ha : raw15565step0 = (fun i j => raw15565 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15565step0 raw15565; decide +kernel
      have hl : raw15565step0Labels = raw15565Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15565 raw15565Labels permutation587 permutation2
    mixedMoment B raw15565step0 raw15565step0Labels = mixedMoment B raw15565step1 raw15565step1Labels := by
      have ha : raw15565step1 = -raw15565step0 := by apply Matrix.ext; change ∀ i j, raw15565step1 i j = -(raw15565step0 i j); unfold raw15565step1 raw15565step0; decide +kernel
      have hl : raw15565step1Labels = raw15565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical15566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15566 raw15566Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw15566 raw15566Labels = mixedMoment B raw15566step0 raw15566step0Labels := by
      have ha : raw15566step0 = (fun i j => raw15566 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15566step0 raw15566; decide +kernel
      have hl : raw15566step0Labels = raw15566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15566 raw15566Labels permutation582 permutation2
    mixedMoment B raw15566step0 raw15566step0Labels = mixedMoment B raw15566step1 raw15566step1Labels := by
      have ha : raw15566step1 = -raw15566step0 := by apply Matrix.ext; change ∀ i j, raw15566step1 i j = -(raw15566step0 i j); unfold raw15566step1 raw15566step0; decide +kernel
      have hl : raw15566step1Labels = raw15566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical15567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15567 raw15567Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15567 raw15567Labels = mixedMoment B raw15567step0 raw15567step0Labels := by
      have ha : raw15567step0 = (fun i j => raw15567 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15567step0 raw15567; decide +kernel
      have hl : raw15567step0Labels = raw15567Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15567 raw15567Labels permutation584 permutation2
    mixedMoment B raw15567step0 raw15567step0Labels = mixedMoment B raw15567step1 raw15567step1Labels := by
      have ha : raw15567step1 = -raw15567step0 := by apply Matrix.ext; change ∀ i j, raw15567step1 i j = -(raw15567step0 i j); unfold raw15567step1 raw15567step0; decide +kernel
      have hl : raw15567step1Labels = raw15567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical15568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15568 raw15568Labels = mixedMoment B node4791 node4791Labels := by
  calc
    mixedMoment B raw15568 raw15568Labels = mixedMoment B raw15568step0 raw15568step0Labels := by
      have ha : raw15568step0 = (fun i j => raw15568 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15568step0 raw15568; decide +kernel
      have hl : raw15568step0Labels = raw15568Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15568 raw15568Labels permutation152 permutation3
    mixedMoment B raw15568step0 raw15568step0Labels = mixedMoment B raw15568step1 raw15568step1Labels := by
      have ha : raw15568step1 = raw15568step0 := by apply Matrix.ext; unfold raw15568step1 raw15568step0; decide +kernel
      have hl : raw15568step0Labels = labelEmbedding6 ∘ raw15568step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15568step0 raw15568step0Labels raw15568step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4791 node4791Labels := by rfl

theorem canonical15569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15569 raw15569Labels = mixedMoment B node5181 node5181Labels := by
  calc
    mixedMoment B raw15569 raw15569Labels = mixedMoment B raw15569step0 raw15569step0Labels := by
      have ha : raw15569step0 = (fun i j => raw15569 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15569step0 raw15569; decide +kernel
      have hl : raw15569step0Labels = raw15569Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15569 raw15569Labels permutation682 permutation3
    mixedMoment B raw15569step0 raw15569step0Labels = mixedMoment B raw15569step1 raw15569step1Labels := by
      have ha : raw15569step1 = -raw15569step0 := by apply Matrix.ext; change ∀ i j, raw15569step1 i j = -(raw15569step0 i j); unfold raw15569step1 raw15569step0; decide +kernel
      have hl : raw15569step1Labels = raw15569step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15569step1 raw15569step1Labels = mixedMoment B raw15569step2 raw15569step2Labels := by
      have ha : raw15569step2 = raw15569step1 := by apply Matrix.ext; unfold raw15569step2 raw15569step1; decide +kernel
      have hl : raw15569step1Labels = labelEmbedding6 ∘ raw15569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15569step1 raw15569step1Labels raw15569step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5181 node5181Labels := by rfl

theorem canonical15570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15570 raw15570Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw15570 raw15570Labels = mixedMoment B raw15570step0 raw15570step0Labels := by
      have ha : raw15570step0 = (fun i j => raw15570 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15570step0 raw15570; decide +kernel
      have hl : raw15570step0Labels = raw15570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15570 raw15570Labels permutation686 permutation3
    mixedMoment B raw15570step0 raw15570step0Labels = mixedMoment B raw15570step1 raw15570step1Labels := by
      have ha : raw15570step1 = -raw15570step0 := by apply Matrix.ext; change ∀ i j, raw15570step1 i j = -(raw15570step0 i j); unfold raw15570step1 raw15570step0; decide +kernel
      have hl : raw15570step1Labels = raw15570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15570step1 raw15570step1Labels = mixedMoment B raw15570step2 raw15570step2Labels := by
      have ha : raw15570step2 = raw15570step1 := by apply Matrix.ext; unfold raw15570step2 raw15570step1; decide +kernel
      have hl : raw15570step1Labels = labelEmbedding6 ∘ raw15570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15570step1 raw15570step1Labels raw15570step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

theorem canonical15571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15571 raw15571Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw15571 raw15571Labels = mixedMoment B raw15571step0 raw15571step0Labels := by
      have ha : raw15571step0 = (fun i j => raw15571 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15571step0 raw15571; decide +kernel
      have hl : raw15571step0Labels = raw15571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15571 raw15571Labels permutation680 permutation3
    mixedMoment B raw15571step0 raw15571step0Labels = mixedMoment B raw15571step1 raw15571step1Labels := by
      have ha : raw15571step1 = -raw15571step0 := by apply Matrix.ext; change ∀ i j, raw15571step1 i j = -(raw15571step0 i j); unfold raw15571step1 raw15571step0; decide +kernel
      have hl : raw15571step1Labels = raw15571step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15571step1 raw15571step1Labels = mixedMoment B raw15571step2 raw15571step2Labels := by
      have ha : raw15571step2 = raw15571step1 := by apply Matrix.ext; unfold raw15571step2 raw15571step1; decide +kernel
      have hl : raw15571step1Labels = labelEmbedding6 ∘ raw15571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15571step1 raw15571step1Labels raw15571step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

theorem canonical15572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15572 raw15572Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw15572 raw15572Labels = mixedMoment B raw15572step0 raw15572step0Labels := by
      have ha : raw15572step0 = (fun i j => raw15572 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15572step0 raw15572; decide +kernel
      have hl : raw15572step0Labels = raw15572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15572 raw15572Labels permutation640 permutation3
    mixedMoment B raw15572step0 raw15572step0Labels = mixedMoment B raw15572step1 raw15572step1Labels := by
      have ha : raw15572step1 = -raw15572step0 := by apply Matrix.ext; change ∀ i j, raw15572step1 i j = -(raw15572step0 i j); unfold raw15572step1 raw15572step0; decide +kernel
      have hl : raw15572step1Labels = raw15572step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15572step1 raw15572step1Labels = mixedMoment B raw15572step2 raw15572step2Labels := by
      have ha : raw15572step2 = raw15572step1 := by apply Matrix.ext; unfold raw15572step2 raw15572step1; decide +kernel
      have hl : raw15572step1Labels = labelEmbedding6 ∘ raw15572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15572step1 raw15572step1Labels raw15572step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15633 raw15633Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15633 raw15633Labels = mixedMoment B raw15633step0 raw15633step0Labels := by
      have ha : raw15633step0 = (fun i j => raw15633 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15633step0 raw15633; decide +kernel
      have hl : raw15633step0Labels = raw15633Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15633 raw15633Labels permutation682 permutation2
    mixedMoment B raw15633step0 raw15633step0Labels = mixedMoment B raw15633step1 raw15633step1Labels := by
      have ha : raw15633step1 = -raw15633step0 := by apply Matrix.ext; change ∀ i j, raw15633step1 i j = -(raw15633step0 i j); unfold raw15633step1 raw15633step0; decide +kernel
      have hl : raw15633step1Labels = raw15633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical15634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15634 raw15634Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw15634 raw15634Labels = mixedMoment B raw15634step0 raw15634step0Labels := by
      have ha : raw15634step0 = (fun i j => raw15634 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15634step0 raw15634; decide +kernel
      have hl : raw15634step0Labels = raw15634Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15634 raw15634Labels permutation681 permutation2
    mixedMoment B raw15634step0 raw15634step0Labels = mixedMoment B raw15634step1 raw15634step1Labels := by
      have ha : raw15634step1 = -raw15634step0 := by apply Matrix.ext; change ∀ i j, raw15634step1 i j = -(raw15634step0 i j); unfold raw15634step1 raw15634step0; decide +kernel
      have hl : raw15634step1Labels = raw15634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3953 node3953Labels := by rfl

theorem canonical15635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15635 raw15635Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15635 raw15635Labels = mixedMoment B raw15635step0 raw15635step0Labels := by
      have ha : raw15635step0 = (fun i j => raw15635 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15635step0 raw15635; decide +kernel
      have hl : raw15635step0Labels = raw15635Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15635 raw15635Labels permutation683 permutation2
    mixedMoment B raw15635step0 raw15635step0Labels = mixedMoment B raw15635step1 raw15635step1Labels := by
      have ha : raw15635step1 = -raw15635step0 := by apply Matrix.ext; change ∀ i j, raw15635step1 i j = -(raw15635step0 i j); unfold raw15635step1 raw15635step0; decide +kernel
      have hl : raw15635step1Labels = raw15635step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical15636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15636 raw15636Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15636 raw15636Labels = mixedMoment B raw15636step0 raw15636step0Labels := by
      have ha : raw15636step0 = (fun i j => raw15636 (permutation677 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15636step0 raw15636; decide +kernel
      have hl : raw15636step0Labels = raw15636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15636 raw15636Labels permutation677 permutation2
    mixedMoment B raw15636step0 raw15636step0Labels = mixedMoment B raw15636step1 raw15636step1Labels := by
      have ha : raw15636step1 = -raw15636step0 := by apply Matrix.ext; change ∀ i j, raw15636step1 i j = -(raw15636step0 i j); unfold raw15636step1 raw15636step0; decide +kernel
      have hl : raw15636step1Labels = raw15636step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical15637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15637 raw15637Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw15637 raw15637Labels = mixedMoment B raw15637step0 raw15637step0Labels := by
      have ha : raw15637step0 = (fun i j => raw15637 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15637step0 raw15637; decide +kernel
      have hl : raw15637step0Labels = raw15637Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15637 raw15637Labels permutation524 permutation4
    mixedMoment B raw15637step0 raw15637step0Labels = mixedMoment B raw15637step1 raw15637step1Labels := by
      have ha : raw15637step1 = -raw15637step0 := by apply Matrix.ext; change ∀ i j, raw15637step1 i j = -(raw15637step0 i j); unfold raw15637step1 raw15637step0; decide +kernel
      have hl : raw15637step1Labels = raw15637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical15638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15638 raw15638Labels = mixedMoment B node4046 node4046Labels := by
  calc
    mixedMoment B raw15638 raw15638Labels = mixedMoment B raw15638step0 raw15638step0Labels := by
      have ha : raw15638step0 = (fun i j => raw15638 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15638step0 raw15638; decide +kernel
      have hl : raw15638step0Labels = raw15638Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15638 raw15638Labels permutation583 permutation2
    mixedMoment B raw15638step0 raw15638step0Labels = mixedMoment B raw15638step1 raw15638step1Labels := by
      have ha : raw15638step1 = -raw15638step0 := by apply Matrix.ext; change ∀ i j, raw15638step1 i j = -(raw15638step0 i j); unfold raw15638step1 raw15638step0; decide +kernel
      have hl : raw15638step1Labels = raw15638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4046 node4046Labels := by rfl

theorem canonical15639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15639 raw15639Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw15639 raw15639Labels = mixedMoment B raw15639step0 raw15639step0Labels := by
      have hz : ∀ j, raw15639 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw15639step0 = (fun i j => raw15639 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw15639step0 raw15639; decide +kernel
      have hl : raw15639step0Labels = raw15639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15639 raw15639Labels permutation152 hz
    mixedMoment B raw15639step0 raw15639step0Labels = mixedMoment B raw15639step1 raw15639step1Labels := by
      have ha : raw15639step1 = (fun i j => raw15639step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw15639step1 raw15639step0; decide +kernel
      have hl : raw15639step1Labels = raw15639step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15639step0 raw15639step0Labels permutation122 permutation0
    mixedMoment B raw15639step1 raw15639step1Labels = mixedMoment B raw15639step2 raw15639step2Labels := by
      have ha : raw15639step2 = -raw15639step1 := by apply Matrix.ext; change ∀ i j, raw15639step2 i j = -(raw15639step1 i j); unfold raw15639step2 raw15639step1; decide +kernel
      have hl : raw15639step2Labels = raw15639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical15640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15640 raw15640Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw15640 raw15640Labels = mixedMoment B raw15640step0 raw15640step0Labels := by
      have ha : raw15640step0 = (fun i j => raw15640 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15640step0 raw15640; decide +kernel
      have hl : raw15640step0Labels = raw15640Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15640 raw15640Labels permutation240 permutation4
    mixedMoment B raw15640step0 raw15640step0Labels = mixedMoment B raw15640step1 raw15640step1Labels := by
      have ha : raw15640step1 = -raw15640step0 := by apply Matrix.ext; change ∀ i j, raw15640step1 i j = -(raw15640step0 i j); unfold raw15640step1 raw15640step0; decide +kernel
      have hl : raw15640step1Labels = raw15640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3179 node3179Labels := by rfl

theorem canonical15641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15641 raw15641Labels = mixedMoment B node3176 node3176Labels := by
  calc
    mixedMoment B raw15641 raw15641Labels = mixedMoment B raw15641step0 raw15641step0Labels := by
      have ha : raw15641step0 = (fun i j => raw15641 (permutation229 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15641step0 raw15641; decide +kernel
      have hl : raw15641step0Labels = raw15641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15641 raw15641Labels permutation229 permutation4
    mixedMoment B raw15641step0 raw15641step0Labels = mixedMoment B raw15641step1 raw15641step1Labels := by
      have ha : raw15641step1 = -raw15641step0 := by apply Matrix.ext; change ∀ i j, raw15641step1 i j = -(raw15641step0 i j); unfold raw15641step1 raw15641step0; decide +kernel
      have hl : raw15641step1Labels = raw15641step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3176 node3176Labels := by rfl

theorem canonical15642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15642 raw15642Labels = mixedMoment B node3176 node3176Labels := by
  calc
    mixedMoment B raw15642 raw15642Labels = mixedMoment B raw15642step0 raw15642step0Labels := by
      have ha : raw15642step0 = (fun i j => raw15642 (permutation228 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15642step0 raw15642; decide +kernel
      have hl : raw15642step0Labels = raw15642Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15642 raw15642Labels permutation228 permutation4
    mixedMoment B raw15642step0 raw15642step0Labels = mixedMoment B raw15642step1 raw15642step1Labels := by
      have ha : raw15642step1 = -raw15642step0 := by apply Matrix.ext; change ∀ i j, raw15642step1 i j = -(raw15642step0 i j); unfold raw15642step1 raw15642step0; decide +kernel
      have hl : raw15642step1Labels = raw15642step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3176 node3176Labels := by rfl

theorem canonical15643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15643 raw15643Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw15643 raw15643Labels = mixedMoment B raw15643step0 raw15643step0Labels := by
      have ha : raw15643step0 = (fun i j => raw15643 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15643step0 raw15643; decide +kernel
      have hl : raw15643step0Labels = raw15643Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15643 raw15643Labels permutation153 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

theorem canonical15644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15644 raw15644Labels = mixedMoment B node2858 node2858Labels := by
  calc
    mixedMoment B raw15644 raw15644Labels = mixedMoment B raw15644step0 raw15644step0Labels := by
      have ha : raw15644step0 = (fun i j => raw15644 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15644step0 raw15644; decide +kernel
      have hl : raw15644step0Labels = raw15644Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15644 raw15644Labels permutation682 permutation2
    mixedMoment B raw15644step0 raw15644step0Labels = mixedMoment B raw15644step1 raw15644step1Labels := by
      have ha : raw15644step1 = -raw15644step0 := by apply Matrix.ext; change ∀ i j, raw15644step1 i j = -(raw15644step0 i j); unfold raw15644step1 raw15644step0; decide +kernel
      have hl : raw15644step1Labels = raw15644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2858 node2858Labels := by rfl

theorem canonical15645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15645 raw15645Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15645 raw15645Labels = mixedMoment B raw15645step0 raw15645step0Labels := by
      have ha : raw15645step0 = (fun i j => raw15645 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15645step0 raw15645; decide +kernel
      have hl : raw15645step0Labels = raw15645Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15645 raw15645Labels permutation676 permutation2
    mixedMoment B raw15645step0 raw15645step0Labels = mixedMoment B raw15645step1 raw15645step1Labels := by
      have ha : raw15645step1 = -raw15645step0 := by apply Matrix.ext; change ∀ i j, raw15645step1 i j = -(raw15645step0 i j); unfold raw15645step1 raw15645step0; decide +kernel
      have hl : raw15645step1Labels = raw15645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical15646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15646 raw15646Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15646 raw15646Labels = mixedMoment B raw15646step0 raw15646step0Labels := by
      have ha : raw15646step0 = (fun i j => raw15646 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15646step0 raw15646; decide +kernel
      have hl : raw15646step0Labels = raw15646Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15646 raw15646Labels permutation674 permutation2
    mixedMoment B raw15646step0 raw15646step0Labels = mixedMoment B raw15646step1 raw15646step1Labels := by
      have ha : raw15646step1 = -raw15646step0 := by apply Matrix.ext; change ∀ i j, raw15646step1 i j = -(raw15646step0 i j); unfold raw15646step1 raw15646step0; decide +kernel
      have hl : raw15646step1Labels = raw15646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical15647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15647 raw15647Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw15647 raw15647Labels = mixedMoment B raw15647step0 raw15647step0Labels := by
      have ha : raw15647step0 = (fun i j => raw15647 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15647step0 raw15647; decide +kernel
      have hl : raw15647step0Labels = raw15647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15647 raw15647Labels permutation526 permutation4
    mixedMoment B raw15647step0 raw15647step0Labels = mixedMoment B raw15647step1 raw15647step1Labels := by
      have ha : raw15647step1 = -raw15647step0 := by apply Matrix.ext; change ∀ i j, raw15647step1 i j = -(raw15647step0 i j); unfold raw15647step1 raw15647step0; decide +kernel
      have hl : raw15647step1Labels = raw15647step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3731 node3731Labels := by rfl

theorem canonical15648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15648 raw15648Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw15648 raw15648Labels = mixedMoment B raw15648step0 raw15648step0Labels := by
      have ha : raw15648step0 = (fun i j => raw15648 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15648step0 raw15648; decide +kernel
      have hl : raw15648step0Labels = raw15648Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15648 raw15648Labels permutation240 permutation4
    mixedMoment B raw15648step0 raw15648step0Labels = mixedMoment B raw15648step1 raw15648step1Labels := by
      have ha : raw15648step1 = -raw15648step0 := by apply Matrix.ext; change ∀ i j, raw15648step1 i j = -(raw15648step0 i j); unfold raw15648step1 raw15648step0; decide +kernel
      have hl : raw15648step1Labels = raw15648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical15649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15649 raw15649Labels = mixedMoment B node3935 node3935Labels := by
  calc
    mixedMoment B raw15649 raw15649Labels = mixedMoment B raw15649step0 raw15649step0Labels := by
      have ha : raw15649step0 = (fun i j => raw15649 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15649step0 raw15649; decide +kernel
      have hl : raw15649step0Labels = raw15649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15649 raw15649Labels permutation271 permutation2
    _ = mixedMoment B node3935 node3935Labels := by rfl

theorem canonical15650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15650 raw15650Labels = mixedMoment B node3935 node3935Labels := by
  calc
    mixedMoment B raw15650 raw15650Labels = mixedMoment B raw15650step0 raw15650step0Labels := by
      have ha : raw15650step0 = (fun i j => raw15650 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15650step0 raw15650; decide +kernel
      have hl : raw15650step0Labels = raw15650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15650 raw15650Labels permutation265 permutation2
    _ = mixedMoment B node3935 node3935Labels := by rfl

theorem canonical15651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15651 raw15651Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw15651 raw15651Labels = mixedMoment B raw15651step0 raw15651step0Labels := by
      have ha : raw15651step0 = (fun i j => raw15651 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15651step0 raw15651; decide +kernel
      have hl : raw15651step0Labels = raw15651Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15651 raw15651Labels permutation583 permutation2
    mixedMoment B raw15651step0 raw15651step0Labels = mixedMoment B raw15651step1 raw15651step1Labels := by
      have ha : raw15651step1 = -raw15651step0 := by apply Matrix.ext; change ∀ i j, raw15651step1 i j = -(raw15651step0 i j); unfold raw15651step1 raw15651step0; decide +kernel
      have hl : raw15651step1Labels = raw15651step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3685 node3685Labels := by rfl

theorem canonical15652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15652 raw15652Labels = mixedMoment B node2859 node2859Labels := by
  calc
    mixedMoment B raw15652 raw15652Labels = mixedMoment B raw15652step0 raw15652step0Labels := by
      have ha : raw15652step0 = (fun i j => raw15652 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15652step0 raw15652; decide +kernel
      have hl : raw15652step0Labels = raw15652Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15652 raw15652Labels permutation681 permutation2
    mixedMoment B raw15652step0 raw15652step0Labels = mixedMoment B raw15652step1 raw15652step1Labels := by
      have ha : raw15652step1 = -raw15652step0 := by apply Matrix.ext; change ∀ i j, raw15652step1 i j = -(raw15652step0 i j); unfold raw15652step1 raw15652step0; decide +kernel
      have hl : raw15652step1Labels = raw15652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2859 node2859Labels := by rfl

theorem canonical15653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15653 raw15653Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw15653 raw15653Labels = mixedMoment B raw15653step0 raw15653step0Labels := by
      have ha : raw15653step0 = (fun i j => raw15653 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15653step0 raw15653; decide +kernel
      have hl : raw15653step0Labels = raw15653Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15653 raw15653Labels permutation680 permutation2
    mixedMoment B raw15653step0 raw15653step0Labels = mixedMoment B raw15653step1 raw15653step1Labels := by
      have ha : raw15653step1 = -raw15653step0 := by apply Matrix.ext; change ∀ i j, raw15653step1 i j = -(raw15653step0 i j); unfold raw15653step1 raw15653step0; decide +kernel
      have hl : raw15653step1Labels = raw15653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3949 node3949Labels := by rfl

theorem canonical15654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15654 raw15654Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw15654 raw15654Labels = mixedMoment B raw15654step0 raw15654step0Labels := by
      have ha : raw15654step0 = (fun i j => raw15654 (permutation525 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15654step0 raw15654; decide +kernel
      have hl : raw15654step0Labels = raw15654Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15654 raw15654Labels permutation525 permutation4
    mixedMoment B raw15654step0 raw15654step0Labels = mixedMoment B raw15654step1 raw15654step1Labels := by
      have ha : raw15654step1 = -raw15654step0 := by apply Matrix.ext; change ∀ i j, raw15654step1 i j = -(raw15654step0 i j); unfold raw15654step1 raw15654step0; decide +kernel
      have hl : raw15654step1Labels = raw15654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3724 node3724Labels := by rfl

theorem canonical15655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15655 raw15655Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw15655 raw15655Labels = mixedMoment B raw15655step0 raw15655step0Labels := by
      have ha : raw15655step0 = (fun i j => raw15655 (permutation388 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15655step0 raw15655; decide +kernel
      have hl : raw15655step0Labels = raw15655Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15655 raw15655Labels permutation388 permutation4
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical15656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15656 raw15656Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw15656 raw15656Labels = mixedMoment B raw15656step0 raw15656step0Labels := by
      have ha : raw15656step0 = (fun i j => raw15656 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15656step0 raw15656; decide +kernel
      have hl : raw15656step0Labels = raw15656Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15656 raw15656Labels permutation686 permutation2
    mixedMoment B raw15656step0 raw15656step0Labels = mixedMoment B raw15656step1 raw15656step1Labels := by
      have ha : raw15656step1 = -raw15656step0 := by apply Matrix.ext; change ∀ i j, raw15656step1 i j = -(raw15656step0 i j); unfold raw15656step1 raw15656step0; decide +kernel
      have hl : raw15656step1Labels = raw15656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3949 node3949Labels := by rfl

theorem canonical15657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15657 raw15657Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw15657 raw15657Labels = mixedMoment B raw15657step0 raw15657step0Labels := by
      have ha : raw15657step0 = (fun i j => raw15657 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15657step0 raw15657; decide +kernel
      have hl : raw15657step0Labels = raw15657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15657 raw15657Labels permutation587 permutation2
    mixedMoment B raw15657step0 raw15657step0Labels = mixedMoment B raw15657step1 raw15657step1Labels := by
      have ha : raw15657step1 = -raw15657step0 := by apply Matrix.ext; change ∀ i j, raw15657step1 i j = -(raw15657step0 i j); unfold raw15657step1 raw15657step0; decide +kernel
      have hl : raw15657step1Labels = raw15657step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical15658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15658 raw15658Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw15658 raw15658Labels = mixedMoment B raw15658step0 raw15658step0Labels := by
      have ha : raw15658step0 = (fun i j => raw15658 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15658step0 raw15658; decide +kernel
      have hl : raw15658step0Labels = raw15658Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15658 raw15658Labels permutation686 permutation2
    mixedMoment B raw15658step0 raw15658step0Labels = mixedMoment B raw15658step1 raw15658step1Labels := by
      have ha : raw15658step1 = -raw15658step0 := by apply Matrix.ext; change ∀ i j, raw15658step1 i j = -(raw15658step0 i j); unfold raw15658step1 raw15658step0; decide +kernel
      have hl : raw15658step1Labels = raw15658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2864 node2864Labels := by rfl

theorem canonical15659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15659 raw15659Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw15659 raw15659Labels = mixedMoment B raw15659step0 raw15659step0Labels := by
      have ha : raw15659step0 = (fun i j => raw15659 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15659step0 raw15659; decide +kernel
      have hl : raw15659step0Labels = raw15659Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15659 raw15659Labels permutation582 permutation2
    mixedMoment B raw15659step0 raw15659step0Labels = mixedMoment B raw15659step1 raw15659step1Labels := by
      have ha : raw15659step1 = -raw15659step0 := by apply Matrix.ext; change ∀ i j, raw15659step1 i j = -(raw15659step0 i j); unfold raw15659step1 raw15659step0; decide +kernel
      have hl : raw15659step1Labels = raw15659step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical15660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15660 raw15660Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw15660 raw15660Labels = mixedMoment B raw15660step0 raw15660step0Labels := by
      have ha : raw15660step0 = (fun i j => raw15660 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15660step0 raw15660; decide +kernel
      have hl : raw15660step0Labels = raw15660Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15660 raw15660Labels permutation584 permutation2
    mixedMoment B raw15660step0 raw15660step0Labels = mixedMoment B raw15660step1 raw15660step1Labels := by
      have ha : raw15660step1 = -raw15660step0 := by apply Matrix.ext; change ∀ i j, raw15660step1 i j = -(raw15660step0 i j); unfold raw15660step1 raw15660step0; decide +kernel
      have hl : raw15660step1Labels = raw15660step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical15661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15661 raw15661Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw15661 raw15661Labels = mixedMoment B raw15661step0 raw15661step0Labels := by
      have ha : raw15661step0 = (fun i j => raw15661 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15661step0 raw15661; decide +kernel
      have hl : raw15661step0Labels = raw15661Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15661 raw15661Labels permutation524 permutation4
    mixedMoment B raw15661step0 raw15661step0Labels = mixedMoment B raw15661step1 raw15661step1Labels := by
      have ha : raw15661step1 = -raw15661step0 := by apply Matrix.ext; change ∀ i j, raw15661step1 i j = -(raw15661step0 i j); unfold raw15661step1 raw15661step0; decide +kernel
      have hl : raw15661step1Labels = raw15661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3724 node3724Labels := by rfl

theorem canonical15662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15662 raw15662Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw15662 raw15662Labels = mixedMoment B raw15662step0 raw15662step0Labels := by
      have ha : raw15662step0 = (fun i j => raw15662 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15662step0 raw15662; decide +kernel
      have hl : raw15662step0Labels = raw15662Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15662 raw15662Labels permutation682 permutation2
    mixedMoment B raw15662step0 raw15662step0Labels = mixedMoment B raw15662step1 raw15662step1Labels := by
      have ha : raw15662step1 = -raw15662step0 := by apply Matrix.ext; change ∀ i j, raw15662step1 i j = -(raw15662step0 i j); unfold raw15662step1 raw15662step0; decide +kernel
      have hl : raw15662step1Labels = raw15662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3030 node3030Labels := by rfl

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

theorem canonical2397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2397 raw2397Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw2397 raw2397Labels = mixedMoment B raw2397step0 raw2397step0Labels := by
      have ha : raw2397step0 = (fun i j => raw2397 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2397step0 raw2397; decide +kernel
      have hl : raw2397step0Labels = raw2397Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2397 raw2397Labels permutation152 permutation4
    mixedMoment B raw2397step0 raw2397step0Labels = mixedMoment B raw2397step1 raw2397step1Labels := by
      have ha : raw2397step1 = raw2397step0 := by apply Matrix.ext; unfold raw2397step1 raw2397step0; decide +kernel
      have hl : raw2397step0Labels = labelEmbedding7 ∘ raw2397step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2397step0 raw2397step0Labels raw2397step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical2398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2398 raw2398Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw2398 raw2398Labels = mixedMoment B raw2398step0 raw2398step0Labels := by
      have ha : raw2398step0 = (fun i j => raw2398 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2398step0 raw2398; decide +kernel
      have hl : raw2398step0Labels = raw2398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2398 raw2398Labels permutation152 permutation4
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2399 raw2399Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw2399 raw2399Labels = mixedMoment B raw2399step0 raw2399step0Labels := by
      have ha : raw2399step0 = (fun i j => raw2399 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2399step0 raw2399; decide +kernel
      have hl : raw2399step0Labels = raw2399Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2399 raw2399Labels permutation170 permutation6
    mixedMoment B raw2399step0 raw2399step0Labels = mixedMoment B raw2399step1 raw2399step1Labels := by
      have ha : raw2399step1 = -raw2399step0 := by apply Matrix.ext; change ∀ i j, raw2399step1 i j = -(raw2399step0 i j); unfold raw2399step1 raw2399step0; decide +kernel
      have hl : raw2399step1Labels = raw2399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2399step1 raw2399step1Labels = mixedMoment B raw2399step2 raw2399step2Labels := by
      have ha : raw2399step2 = raw2399step1 := by apply Matrix.ext; unfold raw2399step2 raw2399step1; decide +kernel
      have hl : raw2399step1Labels = labelEmbedding1 ∘ raw2399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2399step1 raw2399step1Labels raw2399step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

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

theorem canonical2436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2436 raw2436Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw2436 raw2436Labels = mixedMoment B raw2436step0 raw2436step0Labels := by
      have ha : raw2436step0 = (fun i j => raw2436 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2436step0 raw2436; decide +kernel
      have hl : raw2436step0Labels = raw2436Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2436 raw2436Labels permutation152 permutation4
    mixedMoment B raw2436step0 raw2436step0Labels = mixedMoment B raw2436step1 raw2436step1Labels := by
      have ha : raw2436step1 = raw2436step0 := by apply Matrix.ext; unfold raw2436step1 raw2436step0; decide +kernel
      have hl : raw2436step0Labels = labelEmbedding7 ∘ raw2436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2436step0 raw2436step0Labels raw2436step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

theorem canonical2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2437 raw2437Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw2437 raw2437Labels = mixedMoment B raw2437step0 raw2437step0Labels := by
      have ha : raw2437step0 = (fun i j => raw2437 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2437step0 raw2437; decide +kernel
      have hl : raw2437step0Labels = raw2437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2437 raw2437Labels permutation152 permutation4
    _ = mixedMoment B node3731 node3731Labels := by rfl

theorem canonical2438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2438 raw2438Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw2438 raw2438Labels = mixedMoment B raw2438step0 raw2438step0Labels := by
      have ha : raw2438step0 = (fun i j => raw2438 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2438step0 raw2438; decide +kernel
      have hl : raw2438step0Labels = raw2438Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2438 raw2438Labels permutation176 permutation6
    mixedMoment B raw2438step0 raw2438step0Labels = mixedMoment B raw2438step1 raw2438step1Labels := by
      have ha : raw2438step1 = -raw2438step0 := by apply Matrix.ext; change ∀ i j, raw2438step1 i j = -(raw2438step0 i j); unfold raw2438step1 raw2438step0; decide +kernel
      have hl : raw2438step1Labels = raw2438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2438step1 raw2438step1Labels = mixedMoment B raw2438step2 raw2438step2Labels := by
      have ha : raw2438step2 = raw2438step1 := by apply Matrix.ext; unfold raw2438step2 raw2438step1; decide +kernel
      have hl : raw2438step1Labels = labelEmbedding1 ∘ raw2438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2438step1 raw2438step1Labels raw2438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

theorem canonical2487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2487 raw2487Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2487 raw2487Labels = mixedMoment B raw2487step0 raw2487step0Labels := by
      have ha : raw2487step0 = (fun i j => raw2487 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2487step0 raw2487; decide +kernel
      have hl : raw2487step0Labels = raw2487Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2487 raw2487Labels permutation152 permutation4
    mixedMoment B raw2487step0 raw2487step0Labels = mixedMoment B raw2487step1 raw2487step1Labels := by
      have ha : raw2487step1 = raw2487step0 := by apply Matrix.ext; unfold raw2487step1 raw2487step0; decide +kernel
      have hl : raw2487step0Labels = labelEmbedding7 ∘ raw2487step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2487step0 raw2487step0Labels raw2487step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2488 raw2488Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2488 raw2488Labels = mixedMoment B raw2488step0 raw2488step0Labels := by
      have ha : raw2488step0 = (fun i j => raw2488 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2488step0 raw2488; decide +kernel
      have hl : raw2488step0Labels = raw2488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2488 raw2488Labels permutation152 permutation4
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2489 raw2489Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw2489 raw2489Labels = mixedMoment B raw2489step0 raw2489step0Labels := by
      have ha : raw2489step0 = (fun i j => raw2489 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2489step0 raw2489; decide +kernel
      have hl : raw2489step0Labels = raw2489Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2489 raw2489Labels permutation170 permutation6
    mixedMoment B raw2489step0 raw2489step0Labels = mixedMoment B raw2489step1 raw2489step1Labels := by
      have ha : raw2489step1 = -raw2489step0 := by apply Matrix.ext; change ∀ i j, raw2489step1 i j = -(raw2489step0 i j); unfold raw2489step1 raw2489step0; decide +kernel
      have hl : raw2489step1Labels = raw2489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2489step1 raw2489step1Labels = mixedMoment B raw2489step2 raw2489step2Labels := by
      have ha : raw2489step2 = raw2489step1 := by apply Matrix.ext; unfold raw2489step2 raw2489step1; decide +kernel
      have hl : raw2489step1Labels = labelEmbedding1 ∘ raw2489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2489step1 raw2489step1Labels raw2489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

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

theorem canonical2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2547 raw2547Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2547 raw2547Labels = mixedMoment B raw2547step0 raw2547step0Labels := by
      have ha : raw2547step0 = (fun i j => raw2547 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2547step0 raw2547; decide +kernel
      have hl : raw2547step0Labels = raw2547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2547 raw2547Labels permutation152 permutation5
    mixedMoment B raw2547step0 raw2547step0Labels = mixedMoment B raw2547step1 raw2547step1Labels := by
      have ha : raw2547step1 = raw2547step0 := by apply Matrix.ext; unfold raw2547step1 raw2547step0; decide +kernel
      have hl : raw2547step0Labels = labelEmbedding8 ∘ raw2547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2547step0 raw2547step0Labels raw2547step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical2548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2548 raw2548Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2548 raw2548Labels = mixedMoment B raw2548step0 raw2548step0Labels := by
      have ha : raw2548step0 = (fun i j => raw2548 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2548step0 raw2548; decide +kernel
      have hl : raw2548step0Labels = raw2548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2548 raw2548Labels permutation152 permutation4
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2549 raw2549Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw2549 raw2549Labels = mixedMoment B raw2549step0 raw2549step0Labels := by
      have ha : raw2549step0 = (fun i j => raw2549 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2549step0 raw2549; decide +kernel
      have hl : raw2549step0Labels = raw2549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2549 raw2549Labels permutation216 permutation3
    mixedMoment B raw2549step0 raw2549step0Labels = mixedMoment B raw2549step1 raw2549step1Labels := by
      have ha : raw2549step1 = -raw2549step0 := by apply Matrix.ext; change ∀ i j, raw2549step1 i j = -(raw2549step0 i j); unfold raw2549step1 raw2549step0; decide +kernel
      have hl : raw2549step1Labels = raw2549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2549step1 raw2549step1Labels = mixedMoment B raw2549step2 raw2549step2Labels := by
      have ha : raw2549step2 = raw2549step1 := by apply Matrix.ext; unfold raw2549step2 raw2549step1; decide +kernel
      have hl : raw2549step1Labels = labelEmbedding1 ∘ raw2549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2549step1 raw2549step1Labels raw2549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8803 raw8803Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw8803 raw8803Labels = mixedMoment B raw8803step0 raw8803step0Labels := by
      have hz : ∀ j, raw8803 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8803step0 = (fun i j => raw8803 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8803step0 raw8803; decide +kernel
      have hl : raw8803step0Labels = raw8803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8803 raw8803Labels permutation265 hz
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical8804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8804 raw8804Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw8804 raw8804Labels = mixedMoment B raw8804step0 raw8804step0Labels := by
      have hz : ∀ j, raw8804 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8804step0 = (fun i j => raw8804 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8804step0 raw8804; decide +kernel
      have hl : raw8804step0Labels = raw8804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8804 raw8804Labels permutation265 hz
    mixedMoment B raw8804step0 raw8804step0Labels = mixedMoment B raw8804step1 raw8804step1Labels := by
      have ha : raw8804step1 = (fun i j => raw8804step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8804step1 raw8804step0; decide +kernel
      have hl : raw8804step1Labels = raw8804step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8804step0 raw8804step0Labels permutation38 permutation2
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical8805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8805 raw8805Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw8805 raw8805Labels = mixedMoment B raw8805step0 raw8805step0Labels := by
      have hz : ∀ j, raw8805 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8805step0 = (fun i j => raw8805 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8805step0 raw8805; decide +kernel
      have hl : raw8805step0Labels = raw8805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8805 raw8805Labels permutation265 hz
    mixedMoment B raw8805step0 raw8805step0Labels = mixedMoment B raw8805step1 raw8805step1Labels := by
      have ha : raw8805step1 = (fun i j => raw8805step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8805step1 raw8805step0; decide +kernel
      have hl : raw8805step1Labels = raw8805step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8805step0 raw8805step0Labels permutation44 permutation7
    mixedMoment B raw8805step1 raw8805step1Labels = mixedMoment B raw8805step2 raw8805step2Labels := by
      have ha : raw8805step2 = -raw8805step1 := by apply Matrix.ext; change ∀ i j, raw8805step2 i j = -(raw8805step1 i j); unfold raw8805step2 raw8805step1; decide +kernel
      have hl : raw8805step2Labels = raw8805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8805step2 raw8805step2Labels = mixedMoment B raw8805step3 raw8805step3Labels := by
      have ha : raw8805step3 = raw8805step2 := by apply Matrix.ext; unfold raw8805step3 raw8805step2; decide +kernel
      have hl : raw8805step2Labels = labelEmbedding10 ∘ raw8805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8805step2 raw8805step2Labels raw8805step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical8806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8806 raw8806Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw8806 raw8806Labels = mixedMoment B raw8806step0 raw8806step0Labels := by
      have hz : ∀ j, raw8806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8806step0 = (fun i j => raw8806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8806step0 raw8806; decide +kernel
      have hl : raw8806step0Labels = raw8806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8806 raw8806Labels permutation265 hz
    mixedMoment B raw8806step0 raw8806step0Labels = mixedMoment B raw8806step1 raw8806step1Labels := by
      have ha : raw8806step1 = (fun i j => raw8806step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8806step1 raw8806step0; decide +kernel
      have hl : raw8806step1Labels = raw8806step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8806step0 raw8806step0Labels permutation44 permutation7
    mixedMoment B raw8806step1 raw8806step1Labels = mixedMoment B raw8806step2 raw8806step2Labels := by
      have ha : raw8806step2 = -raw8806step1 := by apply Matrix.ext; change ∀ i j, raw8806step2 i j = -(raw8806step1 i j); unfold raw8806step2 raw8806step1; decide +kernel
      have hl : raw8806step2Labels = raw8806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8806step2 raw8806step2Labels = mixedMoment B raw8806step3 raw8806step3Labels := by
      have ha : raw8806step3 = raw8806step2 := by apply Matrix.ext; unfold raw8806step3 raw8806step2; decide +kernel
      have hl : raw8806step2Labels = labelEmbedding10 ∘ raw8806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8806step2 raw8806step2Labels raw8806step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical8813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8813 raw8813Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw8813 raw8813Labels = mixedMoment B raw8813step0 raw8813step0Labels := by
      have ha : raw8813step0 = (fun i j => raw8813 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8813step0 raw8813; decide +kernel
      have hl : raw8813step0Labels = raw8813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8813 raw8813Labels permutation160 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical8818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8818 raw8818Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw8818 raw8818Labels = mixedMoment B raw8818step0 raw8818step0Labels := by
      have ha : raw8818step0 = (fun i j => raw8818 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8818step0 raw8818; decide +kernel
      have hl : raw8818step0Labels = raw8818Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8818 raw8818Labels permutation154 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical8823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8823 raw8823Labels = mixedMoment B node5011 node5011Labels := by
  calc
    mixedMoment B raw8823 raw8823Labels = mixedMoment B raw8823step0 raw8823step0Labels := by
      have ha : raw8823step0 = (fun i j => raw8823 (permutation584 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8823step0 raw8823; decide +kernel
      have hl : raw8823step0Labels = raw8823Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8823 raw8823Labels permutation584 permutation5
    mixedMoment B raw8823step0 raw8823step0Labels = mixedMoment B raw8823step1 raw8823step1Labels := by
      have ha : raw8823step1 = raw8823step0 := by apply Matrix.ext; unfold raw8823step1 raw8823step0; decide +kernel
      have hl : raw8823step0Labels = labelEmbedding8 ∘ raw8823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8823step0 raw8823step0Labels raw8823step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5011 node5011Labels := by rfl

theorem canonical8828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8828 raw8828Labels = mixedMoment B node4992 node4992Labels := by
  calc
    mixedMoment B raw8828 raw8828Labels = mixedMoment B raw8828step0 raw8828step0Labels := by
      have ha : raw8828step0 = (fun i j => raw8828 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8828step0 raw8828; decide +kernel
      have hl : raw8828step0Labels = raw8828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8828 raw8828Labels permutation682 permutation3
    mixedMoment B raw8828step0 raw8828step0Labels = mixedMoment B raw8828step1 raw8828step1Labels := by
      have ha : raw8828step1 = -raw8828step0 := by apply Matrix.ext; change ∀ i j, raw8828step1 i j = -(raw8828step0 i j); unfold raw8828step1 raw8828step0; decide +kernel
      have hl : raw8828step1Labels = raw8828step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8828step1 raw8828step1Labels = mixedMoment B raw8828step2 raw8828step2Labels := by
      have ha : raw8828step2 = raw8828step1 := by apply Matrix.ext; unfold raw8828step2 raw8828step1; decide +kernel
      have hl : raw8828step1Labels = labelEmbedding6 ∘ raw8828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8828step1 raw8828step1Labels raw8828step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4992 node4992Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8893 raw8893Labels = mixedMoment B node3846 node3846Labels := by
  calc
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical8898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8898 raw8898Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw8898 raw8898Labels = mixedMoment B raw8898step0 raw8898step0Labels := by
      have hz : ∀ j, raw8898 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8898step0 = (fun i j => raw8898 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8898step0 raw8898; decide +kernel
      have hl : raw8898step0Labels = raw8898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8898 raw8898Labels permutation265 hz
    mixedMoment B raw8898step0 raw8898step0Labels = mixedMoment B raw8898step1 raw8898step1Labels := by
      have ha : raw8898step1 = (fun i j => raw8898step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8898step1 raw8898step0; decide +kernel
      have hl : raw8898step1Labels = raw8898step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8898step0 raw8898step0Labels permutation44 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical8904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8904 raw8904Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw8904 raw8904Labels = mixedMoment B raw8904step0 raw8904step0Labels := by
      have ha : raw8904step0 = (fun i j => raw8904 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8904step0 raw8904; decide +kernel
      have hl : raw8904step0Labels = raw8904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8904 raw8904Labels permutation160 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5354 node5354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3692 node3692Labels + mixedMoment B node3769 node3769Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2397 singletonSmall5354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5354) = raw2397Labels := by decide +kernel
  rw [hl, canonical2397 B hB] at h
  have hc0 : mixedMoment B raw2397 (Fin.cases (0 : Fin 2) singletonSmall5354) =
      mixedMoment B node3692 node3692Labels := by
    have ha : raw2397 = raw2398 := by apply Matrix.ext; unfold raw2397 raw2398; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5354 = raw2398Labels := by decide +kernel
    rw [ha, hj, canonical2398 B hB]
  have hc1 : mixedMoment B raw2397 (Fin.cases (1 : Fin 2) singletonSmall5354) =
      mixedMoment B node3769 node3769Labels := by
    have ha : raw2397 = raw2399 := by apply Matrix.ext; unfold raw2397 raw2399; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5354 = raw2399Labels := by decide +kernel
    rw [ha, hj, canonical2399 B hB]
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

theorem singleton5383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5383 node5383Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3731 node3731Labels + mixedMoment B node3867 node3867Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2436 singletonSmall5383
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5383) = raw2436Labels := by decide +kernel
  rw [hl, canonical2436 B hB] at h
  have hc0 : mixedMoment B raw2436 (Fin.cases (0 : Fin 2) singletonSmall5383) =
      mixedMoment B node3731 node3731Labels := by
    have ha : raw2436 = raw2437 := by apply Matrix.ext; unfold raw2436 raw2437; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5383 = raw2437Labels := by decide +kernel
    rw [ha, hj, canonical2437 B hB]
  have hc1 : mixedMoment B raw2436 (Fin.cases (1 : Fin 2) singletonSmall5383) =
      mixedMoment B node3867 node3867Labels := by
    have ha : raw2436 = raw2438 := by apply Matrix.ext; unfold raw2436 raw2438; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5383 = raw2438Labels := by decide +kernel
    rw [ha, hj, canonical2438 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5406 node5406Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3801 node3801Labels + mixedMoment B node3812 node3812Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2487 singletonSmall5406
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5406) = raw2487Labels := by decide +kernel
  rw [hl, canonical2487 B hB] at h
  have hc0 : mixedMoment B raw2487 (Fin.cases (0 : Fin 2) singletonSmall5406) =
      mixedMoment B node3801 node3801Labels := by
    have ha : raw2487 = raw2488 := by apply Matrix.ext; unfold raw2487 raw2488; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5406 = raw2488Labels := by decide +kernel
    rw [ha, hj, canonical2488 B hB]
  have hc1 : mixedMoment B raw2487 (Fin.cases (1 : Fin 2) singletonSmall5406) =
      mixedMoment B node3812 node3812Labels := by
    have ha : raw2487 = raw2489 := by apply Matrix.ext; unfold raw2487 raw2489; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5406 = raw2489Labels := by decide +kernel
    rw [ha, hj, canonical2489 B hB]
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

theorem singleton5447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5447 node5447Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4025 node4025Labels + mixedMoment B node3909 node3909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2547 singletonSmall5447
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5447) = raw2547Labels := by decide +kernel
  rw [hl, canonical2547 B hB] at h
  have hc0 : mixedMoment B raw2547 (Fin.cases (0 : Fin 2) singletonSmall5447) =
      mixedMoment B node4025 node4025Labels := by
    have ha : raw2547 = raw2548 := by apply Matrix.ext; unfold raw2547 raw2548; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5447 = raw2548Labels := by decide +kernel
    rw [ha, hj, canonical2548 B hB]
  have hc1 : mixedMoment B raw2547 (Fin.cases (1 : Fin 2) singletonSmall5447) =
      mixedMoment B node3909 node3909Labels := by
    have ha : raw2547 = raw2549 := by apply Matrix.ext; unfold raw2547 raw2549; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5447 = raw2549Labels := by decide +kernel
    rw [ha, hj, canonical2549 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem zero5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = 0 := by
  exact mixedMoment_alpha B hF node5471 node5471Labels 1 permutation200
    (by decide +kernel)

theorem zero5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = 0 := by
  exact mixedMoment_alpha B hF node5481 node5481Labels 2 permutation158
    (by decide +kernel)

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

theorem sound2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2567 node2567Labels = Sparse.eval nodeValue2567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2567) = mixedMoment B node2567 node2567Labels := rfl
  simpa [nodeValue2567, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2858 node2858Labels = Sparse.eval nodeValue2858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2858) = mixedMoment B node2858 node2858Labels := rfl
  simpa [nodeValue2858, Sparse.eval] using hc.symm

theorem sound2859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2859 node2859Labels = Sparse.eval nodeValue2859 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2859) = mixedMoment B node2859 node2859Labels := rfl
  simpa [nodeValue2859, Sparse.eval] using hc.symm

theorem sound2864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2864 node2864Labels = Sparse.eval nodeValue2864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2864) = mixedMoment B node2864 node2864Labels := rfl
  simpa [nodeValue2864, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3030 node3030Labels = Sparse.eval nodeValue3030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3030) = mixedMoment B node3030 node3030Labels := rfl
  simpa [nodeValue3030, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3176 node3176Labels = Sparse.eval nodeValue3176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3176) = mixedMoment B node3176 node3176Labels := rfl
  simpa [nodeValue3176, Sparse.eval] using hc.symm

theorem sound3179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3179 node3179Labels = Sparse.eval nodeValue3179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3179) = mixedMoment B node3179 node3179Labels := rfl
  simpa [nodeValue3179, Sparse.eval] using hc.symm

theorem sound3199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3199 node3199Labels = Sparse.eval nodeValue3199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3199) = mixedMoment B node3199 node3199Labels := rfl
  simpa [nodeValue3199, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3685 node3685Labels = Sparse.eval nodeValue3685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3685) = mixedMoment B node3685 node3685Labels := rfl
  simpa [nodeValue3685, Sparse.eval] using hc.symm

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3724 node3724Labels = Sparse.eval nodeValue3724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3724) = mixedMoment B node3724 node3724Labels := rfl
  simpa [nodeValue3724, Sparse.eval] using hc.symm

theorem sound3731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3731 node3731Labels = Sparse.eval nodeValue3731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3731) = mixedMoment B node3731 node3731Labels := rfl
  simpa [nodeValue3731, Sparse.eval] using hc.symm

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

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

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3827 node3827Labels = Sparse.eval nodeValue3827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3827) = mixedMoment B node3827 node3827Labels := rfl
  simpa [nodeValue3827, Sparse.eval] using hc.symm

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

theorem sound3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3846 node3846Labels = Sparse.eval nodeValue3846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3846) = mixedMoment B node3846 node3846Labels := rfl
  simpa [nodeValue3846, Sparse.eval] using hc.symm

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3867 node3867Labels = Sparse.eval nodeValue3867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3867) = mixedMoment B node3867 node3867Labels := rfl
  simpa [nodeValue3867, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = 0 := by
  exact mixedMoment_alpha B hF node3953 node3953Labels 1 permutation200
    (by decide +kernel)

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

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

theorem sound3935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3935 node3935Labels = Sparse.eval nodeValue3935 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3935) = mixedMoment B node3935 node3935Labels := rfl
  simpa [nodeValue3935, Sparse.eval] using hc.symm

theorem sound3947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3947 node3947Labels = Sparse.eval nodeValue3947 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3947) = mixedMoment B node3947 node3947Labels := rfl
  simpa [nodeValue3947, Sparse.eval] using hc.symm

theorem sound3949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3949 node3949Labels = Sparse.eval nodeValue3949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3949) = mixedMoment B node3949 node3949Labels := rfl
  simpa [nodeValue3949, Sparse.eval] using hc.symm

theorem sound3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = Sparse.eval nodeValue3953 (mixedVector B) := by
  simpa only [nodeValue3953, Sparse.eval_nil] using zero3953 B _hB _hF

theorem sound3954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3954 node3954Labels = Sparse.eval nodeValue3954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3954) = mixedMoment B node3954 node3954Labels := rfl
  simpa [nodeValue3954, Sparse.eval] using hc.symm

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = 0 := by
  exact mixedMoment_alpha B hF node4008 node4008Labels 1 permutation213
    (by decide +kernel)

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

theorem sound3972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3972 node3972Labels = Sparse.eval nodeValue3972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3972) = mixedMoment B node3972 node3972Labels := rfl
  simpa [nodeValue3972, Sparse.eval] using hc.symm

theorem sound4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = Sparse.eval nodeValue4008 (mixedVector B) := by
  simpa only [nodeValue4008, Sparse.eval_nil] using zero4008 B _hB _hF

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

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

theorem sound4046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4046 node4046Labels = Sparse.eval nodeValue4046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4046) = mixedMoment B node4046 node4046Labels := rfl
  simpa [nodeValue4046, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem sound4791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4791 node4791Labels = Sparse.eval nodeValue4791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4791) = mixedMoment B node4791 node4791Labels := rfl
  simpa [nodeValue4791, Sparse.eval] using hc.symm

theorem sound4795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4795 node4795Labels = Sparse.eval nodeValue4795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4795) = mixedMoment B node4795 node4795Labels := rfl
  simpa [nodeValue4795, Sparse.eval] using hc.symm

theorem sound4799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4799 node4799Labels = Sparse.eval nodeValue4799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4799) = mixedMoment B node4799 node4799Labels := rfl
  simpa [nodeValue4799, Sparse.eval] using hc.symm

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

theorem sound4863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4863 node4863Labels = Sparse.eval nodeValue4863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4863) = mixedMoment B node4863 node4863Labels := rfl
  simpa [nodeValue4863, Sparse.eval] using hc.symm

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

theorem sound4992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4992 node4992Labels = Sparse.eval nodeValue4992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4992) = mixedMoment B node4992 node4992Labels := rfl
  simpa [nodeValue4992, Sparse.eval] using hc.symm

theorem sound4993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4993 node4993Labels = Sparse.eval nodeValue4993 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4993) = mixedMoment B node4993 node4993Labels := rfl
  simpa [nodeValue4993, Sparse.eval] using hc.symm

theorem sound4999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4999 node4999Labels = Sparse.eval nodeValue4999 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4999) = mixedMoment B node4999 node4999Labels := rfl
  simpa [nodeValue4999, Sparse.eval] using hc.symm

theorem sound5004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5004 node5004Labels = Sparse.eval nodeValue5004 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5004) = mixedMoment B node5004 node5004Labels := rfl
  simpa [nodeValue5004, Sparse.eval] using hc.symm

theorem sound5005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5005 node5005Labels = Sparse.eval nodeValue5005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5005) = mixedMoment B node5005 node5005Labels := rfl
  simpa [nodeValue5005, Sparse.eval] using hc.symm

theorem sound5011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5011 node5011Labels = Sparse.eval nodeValue5011 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5011) = mixedMoment B node5011 node5011Labels := rfl
  simpa [nodeValue5011, Sparse.eval] using hc.symm

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

theorem sound5145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5145 node5145Labels = Sparse.eval nodeValue5145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5145) = mixedMoment B node5145 node5145Labels := rfl
  simpa [nodeValue5145, Sparse.eval] using hc.symm

theorem sound5181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5181 node5181Labels = Sparse.eval nodeValue5181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5181) = mixedMoment B node5181 node5181Labels := rfl
  simpa [nodeValue5181, Sparse.eval] using hc.symm

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

theorem sound5184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5184 node5184Labels = Sparse.eval nodeValue5184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5184) = mixedMoment B node5184 node5184Labels := rfl
  simpa [nodeValue5184, Sparse.eval] using hc.symm

theorem sound5243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5243 node5243Labels = Sparse.eval nodeValue5243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5243) = mixedMoment B node5243 node5243Labels := rfl
  simpa [nodeValue5243, Sparse.eval] using hc.symm

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

theorem sound5251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5251 node5251Labels = Sparse.eval nodeValue5251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5251) = mixedMoment B node5251 node5251Labels := rfl
  simpa [nodeValue5251, Sparse.eval] using hc.symm

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5282 node5282Labels = Sparse.eval nodeValue5282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5282) = mixedMoment B node5282 node5282Labels := rfl
  simpa [nodeValue5282, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5348 node5348Labels = Sparse.eval nodeValue5348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5348) = mixedMoment B node5348 node5348Labels := rfl
  simpa [nodeValue5348, Sparse.eval] using hc.symm

theorem sound5350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5350 node5350Labels = Sparse.eval nodeValue5350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5350) = mixedMoment B node5350 node5350Labels := rfl
  simpa [nodeValue5350, Sparse.eval] using hc.symm

theorem sound5354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5354 node5354Labels = Sparse.eval nodeValue5354 (mixedVector B) := by
  have h := singleton5354 B _hB
  rw [sound3692 B _hB _hF, sound3769 B _hB _hF] at h
  norm_num [nodeValue5354, nodeValue3692, nodeValue3769, Sparse.eval] at h ⊢
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

theorem sound5379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5379 node5379Labels = Sparse.eval nodeValue5379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5379) = mixedMoment B node5379 node5379Labels := rfl
  simpa [nodeValue5379, Sparse.eval] using hc.symm

theorem sound5383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5383 node5383Labels = Sparse.eval nodeValue5383 (mixedVector B) := by
  have h := singleton5383 B _hB
  rw [sound3731 B _hB _hF, sound3867 B _hB _hF] at h
  norm_num [nodeValue5383, nodeValue3731, nodeValue3867, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5414 node5414Labels = Sparse.eval nodeValue5414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5414) = mixedMoment B node5414 node5414Labels := rfl
  simpa [nodeValue5414, Sparse.eval] using hc.symm

theorem sound5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5421 node5421Labels = Sparse.eval nodeValue5421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5421) = mixedMoment B node5421 node5421Labels := rfl
  simpa [nodeValue5421, Sparse.eval] using hc.symm

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

theorem sound5446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5446 node5446Labels = Sparse.eval nodeValue5446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5446) = mixedMoment B node5446 node5446Labels := rfl
  simpa [nodeValue5446, Sparse.eval] using hc.symm

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5470 node5470Labels = Sparse.eval nodeValue5470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5470) = mixedMoment B node5470 node5470Labels := rfl
  simpa [nodeValue5470, Sparse.eval] using hc.symm

theorem sound5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = Sparse.eval nodeValue5471 (mixedVector B) := by
  simpa only [nodeValue5471, Sparse.eval_nil] using zero5471 B _hB _hF

theorem sound5472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5472 node5472Labels = Sparse.eval nodeValue5472 (mixedVector B) := by
  have h := singleton5472 B _hB
  rw [sound3957 B _hB _hF] at h
  norm_num [nodeValue5472, nodeValue3957, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources29
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq935 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm935 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA935 + difference 0 1) (sourceB935 + difference 1 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA935 + difference 0 1) (sourceB935 + difference 1 0) sourceC935) = raw15465 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15465; decide +kernel
    rw [ha]
    exact (canonical15465 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA935 + difference 0 2) (sourceB935 + difference 2 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA935 + difference 0 2) (sourceB935 + difference 2 0) sourceC935) = raw15466 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15466; decide +kernel
    rw [ha]
    exact (canonical15466 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA935 + difference 0 3) (sourceB935 + difference 3 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA935 + difference 0 3) (sourceB935 + difference 3 0) sourceC935) = raw15467 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15467; decide +kernel
    rw [ha]
    exact (canonical15467 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA935 + difference 0 4) (sourceB935 + difference 4 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA935 + difference 0 4) (sourceB935 + difference 4 0) sourceC935) = raw15468 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15468; decide +kernel
    rw [ha]
    exact (canonical15468 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA935 + difference 0 5) (sourceB935 + difference 5 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA935 + difference 0 5) (sourceB935 + difference 5 0) sourceC935) = raw15469 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15469; decide +kernel
    rw [ha]
    exact (canonical15469 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA935 + difference 1 0) (sourceB935 + difference 0 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA935 + difference 1 0) (sourceB935 + difference 0 1) sourceC935) = raw15470 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15470; decide +kernel
    rw [ha]
    exact (canonical15470 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA935 + difference 1 2) (sourceB935 + difference 2 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA935 + difference 1 2) (sourceB935 + difference 2 1) sourceC935) = raw8803 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8803; decide +kernel
    rw [ha]
    exact (canonical8803 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA935 + difference 1 3) (sourceB935 + difference 3 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA935 + difference 1 3) (sourceB935 + difference 3 1) sourceC935) = raw8804 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8804; decide +kernel
    rw [ha]
    exact (canonical8804 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA935 + difference 1 4) (sourceB935 + difference 4 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA935 + difference 1 4) (sourceB935 + difference 4 1) sourceC935) = raw8805 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8805; decide +kernel
    rw [ha]
    exact (canonical8805 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA935 + difference 1 5) (sourceB935 + difference 5 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA935 + difference 1 5) (sourceB935 + difference 5 1) sourceC935) = raw8806 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8806; decide +kernel
    rw [ha]
    exact (canonical8806 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA935 + difference 2 0) (sourceB935 + difference 0 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA935 + difference 2 0) (sourceB935 + difference 0 2) sourceC935) = raw8813 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8813; decide +kernel
    rw [ha]
    exact (canonical8813 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA935 + difference 2 1) (sourceB935 + difference 1 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA935 + difference 2 1) (sourceB935 + difference 1 2) sourceC935) = raw15471 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15471; decide +kernel
    rw [ha]
    exact (canonical15471 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA935 + difference 2 3) (sourceB935 + difference 3 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA935 + difference 2 3) (sourceB935 + difference 3 2) sourceC935) = raw15472 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15472; decide +kernel
    rw [ha]
    exact (canonical15472 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA935 + difference 2 4) (sourceB935 + difference 4 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA935 + difference 2 4) (sourceB935 + difference 4 2) sourceC935) = raw15473 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15473; decide +kernel
    rw [ha]
    exact (canonical15473 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA935 + difference 2 5) (sourceB935 + difference 5 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA935 + difference 2 5) (sourceB935 + difference 5 2) sourceC935) = raw15474 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15474; decide +kernel
    rw [ha]
    exact (canonical15474 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA935 + difference 3 0) (sourceB935 + difference 0 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA935 + difference 3 0) (sourceB935 + difference 0 3) sourceC935) = raw8818 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8818; decide +kernel
    rw [ha]
    exact (canonical8818 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA935 + difference 3 1) (sourceB935 + difference 1 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA935 + difference 3 1) (sourceB935 + difference 1 3) sourceC935) = raw15475 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15475; decide +kernel
    rw [ha]
    exact (canonical15475 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA935 + difference 3 2) (sourceB935 + difference 2 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA935 + difference 3 2) (sourceB935 + difference 2 3) sourceC935) = raw15476 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15476; decide +kernel
    rw [ha]
    exact (canonical15476 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA935 + difference 3 4) (sourceB935 + difference 4 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA935 + difference 3 4) (sourceB935 + difference 4 3) sourceC935) = raw15477 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15477; decide +kernel
    rw [ha]
    exact (canonical15477 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA935 + difference 3 5) (sourceB935 + difference 5 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA935 + difference 3 5) (sourceB935 + difference 5 3) sourceC935) = raw15478 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15478; decide +kernel
    rw [ha]
    exact (canonical15478 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA935 + difference 4 0) (sourceB935 + difference 0 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5011) := by
    have ha : (tripleCharges (sourceA935 + difference 4 0) (sourceB935 + difference 0 4) sourceC935) = raw8823 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8823; decide +kernel
    rw [ha]
    exact (canonical8823 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA935 + difference 4 1) (sourceB935 + difference 1 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5004) := by
    have ha : (tripleCharges (sourceA935 + difference 4 1) (sourceB935 + difference 1 4) sourceC935) = raw15479 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15479; decide +kernel
    rw [ha]
    exact (canonical15479 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA935 + difference 4 2) (sourceB935 + difference 2 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA935 + difference 4 2) (sourceB935 + difference 2 4) sourceC935) = raw15480 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15480; decide +kernel
    rw [ha]
    exact (canonical15480 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA935 + difference 4 3) (sourceB935 + difference 3 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA935 + difference 4 3) (sourceB935 + difference 3 4) sourceC935) = raw15481 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15481; decide +kernel
    rw [ha]
    exact (canonical15481 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA935 + difference 4 5) (sourceB935 + difference 5 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA935 + difference 4 5) (sourceB935 + difference 5 4) sourceC935) = raw15482 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15482; decide +kernel
    rw [ha]
    exact (canonical15482 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA935 + difference 5 0) (sourceB935 + difference 0 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4992) := by
    have ha : (tripleCharges (sourceA935 + difference 5 0) (sourceB935 + difference 0 5) sourceC935) = raw8828 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8828; decide +kernel
    rw [ha]
    exact (canonical8828 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA935 + difference 5 1) (sourceB935 + difference 1 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4993) := by
    have ha : (tripleCharges (sourceA935 + difference 5 1) (sourceB935 + difference 1 5) sourceC935) = raw15483 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15483; decide +kernel
    rw [ha]
    exact (canonical15483 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA935 + difference 5 2) (sourceB935 + difference 2 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA935 + difference 5 2) (sourceB935 + difference 2 5) sourceC935) = raw15484 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15484; decide +kernel
    rw [ha]
    exact (canonical15484 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA935 + difference 5 3) (sourceB935 + difference 3 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA935 + difference 5 3) (sourceB935 + difference 3 5) sourceC935) = raw15485 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15485; decide +kernel
    rw [ha]
    exact (canonical15485 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA935 + difference 5 4) (sourceB935 + difference 4 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA935 + difference 5 4) (sourceB935 + difference 4 5) sourceC935) = raw15486 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15486; decide +kernel
    rw [ha]
    exact (canonical15486 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA935 sourceB935 sourceC935
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm935, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm938 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA938 + difference 0 0) (sourceB938 + difference 0 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA938 + difference 0 0) (sourceB938 + difference 0 0) sourceC938) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA938 + difference 0 1) (sourceB938 + difference 1 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA938 + difference 0 1) (sourceB938 + difference 1 0) sourceC938) = raw15531 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15531; decide +kernel
    rw [ha]
    exact (canonical15531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA938 + difference 0 2) (sourceB938 + difference 2 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA938 + difference 0 2) (sourceB938 + difference 2 0) sourceC938) = raw15532 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15532; decide +kernel
    rw [ha]
    exact (canonical15532 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA938 + difference 0 3) (sourceB938 + difference 3 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA938 + difference 0 3) (sourceB938 + difference 3 0) sourceC938) = raw15533 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15533; decide +kernel
    rw [ha]
    exact (canonical15533 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA938 + difference 0 4) (sourceB938 + difference 4 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA938 + difference 0 4) (sourceB938 + difference 4 0) sourceC938) = raw15534 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15534; decide +kernel
    rw [ha]
    exact (canonical15534 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA938 + difference 0 5) (sourceB938 + difference 5 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA938 + difference 0 5) (sourceB938 + difference 5 0) sourceC938) = raw15535 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15535; decide +kernel
    rw [ha]
    exact (canonical15535 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA938 + sourceB938) sourceC938) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA938 + sourceB938) sourceC938) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA938 sourceB938 sourceC938 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA938 sourceB938 sourceC938
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm938, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq940 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm940 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA940 + difference 2 0) (sourceB940 + difference 0 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA940 + difference 2 0) (sourceB940 + difference 0 2) sourceC940) = raw8904 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw8904; decide +kernel
    rw [ha]
    exact (canonical8904 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA940 + difference 2 1) (sourceB940 + difference 1 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA940 + difference 2 1) (sourceB940 + difference 1 2) sourceC940) = raw15536 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw15536; decide +kernel
    rw [ha]
    exact (canonical15536 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA940 + difference 2 2) (sourceB940 + difference 2 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA940 + difference 2 2) (sourceB940 + difference 2 2) sourceC940) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA940 + difference 2 3) (sourceB940 + difference 3 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA940 + difference 2 3) (sourceB940 + difference 3 2) sourceC940) = raw15540 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw15540; decide +kernel
    rw [ha]
    exact (canonical15540 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA940 + difference 2 4) (sourceB940 + difference 4 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA940 + difference 2 4) (sourceB940 + difference 4 2) sourceC940) = raw15541 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw15541; decide +kernel
    rw [ha]
    exact (canonical15541 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA940 + difference 2 5) (sourceB940 + difference 5 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA940 + difference 2 5) (sourceB940 + difference 5 2) sourceC940) = raw15542 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw15542; decide +kernel
    rw [ha]
    exact (canonical15542 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA940 + sourceB940) sourceC940) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA940 + sourceB940) sourceC940) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA940 sourceB940 sourceC940 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA940 sourceB940 sourceC940
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm940, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm941 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA941 + difference 0 1) (sourceB941 + difference 1 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA941 + difference 0 1) (sourceB941 + difference 1 0) sourceC941) = raw15543 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15543; decide +kernel
    rw [ha]
    exact (canonical15543 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA941 + difference 0 2) (sourceB941 + difference 2 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA941 + difference 0 2) (sourceB941 + difference 2 0) sourceC941) = raw15544 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15544; decide +kernel
    rw [ha]
    exact (canonical15544 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA941 + difference 0 3) (sourceB941 + difference 3 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA941 + difference 0 3) (sourceB941 + difference 3 0) sourceC941) = raw15545 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15545; decide +kernel
    rw [ha]
    exact (canonical15545 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA941 + difference 0 4) (sourceB941 + difference 4 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA941 + difference 0 4) (sourceB941 + difference 4 0) sourceC941) = raw15546 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15546; decide +kernel
    rw [ha]
    exact (canonical15546 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA941 + difference 0 5) (sourceB941 + difference 5 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA941 + difference 0 5) (sourceB941 + difference 5 0) sourceC941) = raw15547 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15547; decide +kernel
    rw [ha]
    exact (canonical15547 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA941 + difference 1 0) (sourceB941 + difference 0 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA941 + difference 1 0) (sourceB941 + difference 0 1) sourceC941) = raw15548 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15548; decide +kernel
    rw [ha]
    exact (canonical15548 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA941 + difference 1 2) (sourceB941 + difference 2 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA941 + difference 1 2) (sourceB941 + difference 2 1) sourceC941) = raw15549 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15549; decide +kernel
    rw [ha]
    exact (canonical15549 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA941 + difference 1 3) (sourceB941 + difference 3 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA941 + difference 1 3) (sourceB941 + difference 3 1) sourceC941) = raw15550 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15550; decide +kernel
    rw [ha]
    exact (canonical15550 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA941 + difference 1 4) (sourceB941 + difference 4 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA941 + difference 1 4) (sourceB941 + difference 4 1) sourceC941) = raw15551 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15551; decide +kernel
    rw [ha]
    exact (canonical15551 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA941 + difference 1 5) (sourceB941 + difference 5 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA941 + difference 1 5) (sourceB941 + difference 5 1) sourceC941) = raw15552 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15552; decide +kernel
    rw [ha]
    exact (canonical15552 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA941 + difference 2 0) (sourceB941 + difference 0 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA941 + difference 2 0) (sourceB941 + difference 0 2) sourceC941) = raw15553 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15553; decide +kernel
    rw [ha]
    exact (canonical15553 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA941 + difference 2 1) (sourceB941 + difference 1 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA941 + difference 2 1) (sourceB941 + difference 1 2) sourceC941) = raw15554 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15554; decide +kernel
    rw [ha]
    exact (canonical15554 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA941 + difference 2 3) (sourceB941 + difference 3 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA941 + difference 2 3) (sourceB941 + difference 3 2) sourceC941) = raw15555 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15555; decide +kernel
    rw [ha]
    exact (canonical15555 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA941 + difference 2 4) (sourceB941 + difference 4 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA941 + difference 2 4) (sourceB941 + difference 4 2) sourceC941) = raw15556 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15556; decide +kernel
    rw [ha]
    exact (canonical15556 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA941 + difference 2 5) (sourceB941 + difference 5 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA941 + difference 2 5) (sourceB941 + difference 5 2) sourceC941) = raw15557 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15557; decide +kernel
    rw [ha]
    exact (canonical15557 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA941 + difference 3 0) (sourceB941 + difference 0 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA941 + difference 3 0) (sourceB941 + difference 0 3) sourceC941) = raw15558 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15558; decide +kernel
    rw [ha]
    exact (canonical15558 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA941 + difference 3 1) (sourceB941 + difference 1 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA941 + difference 3 1) (sourceB941 + difference 1 3) sourceC941) = raw15559 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15559; decide +kernel
    rw [ha]
    exact (canonical15559 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA941 + difference 3 2) (sourceB941 + difference 2 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA941 + difference 3 2) (sourceB941 + difference 2 3) sourceC941) = raw15560 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15560; decide +kernel
    rw [ha]
    exact (canonical15560 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA941 + difference 3 4) (sourceB941 + difference 4 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA941 + difference 3 4) (sourceB941 + difference 4 3) sourceC941) = raw15561 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15561; decide +kernel
    rw [ha]
    exact (canonical15561 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA941 + difference 3 5) (sourceB941 + difference 5 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA941 + difference 3 5) (sourceB941 + difference 5 3) sourceC941) = raw15562 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15562; decide +kernel
    rw [ha]
    exact (canonical15562 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA941 + difference 4 0) (sourceB941 + difference 0 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA941 + difference 4 0) (sourceB941 + difference 0 4) sourceC941) = raw15563 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15563; decide +kernel
    rw [ha]
    exact (canonical15563 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA941 + difference 4 1) (sourceB941 + difference 1 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA941 + difference 4 1) (sourceB941 + difference 1 4) sourceC941) = raw15564 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15564; decide +kernel
    rw [ha]
    exact (canonical15564 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA941 + difference 4 2) (sourceB941 + difference 2 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA941 + difference 4 2) (sourceB941 + difference 2 4) sourceC941) = raw15565 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15565; decide +kernel
    rw [ha]
    exact (canonical15565 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA941 + difference 4 3) (sourceB941 + difference 3 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA941 + difference 4 3) (sourceB941 + difference 3 4) sourceC941) = raw15566 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15566; decide +kernel
    rw [ha]
    exact (canonical15566 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA941 + difference 4 5) (sourceB941 + difference 5 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA941 + difference 4 5) (sourceB941 + difference 5 4) sourceC941) = raw15567 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15567; decide +kernel
    rw [ha]
    exact (canonical15567 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA941 + difference 5 0) (sourceB941 + difference 0 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4791) := by
    have ha : (tripleCharges (sourceA941 + difference 5 0) (sourceB941 + difference 0 5) sourceC941) = raw15568 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15568; decide +kernel
    rw [ha]
    exact (canonical15568 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA941 + difference 5 1) (sourceB941 + difference 1 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5181) := by
    have ha : (tripleCharges (sourceA941 + difference 5 1) (sourceB941 + difference 1 5) sourceC941) = raw15569 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15569; decide +kernel
    rw [ha]
    exact (canonical15569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA941 + difference 5 2) (sourceB941 + difference 2 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA941 + difference 5 2) (sourceB941 + difference 2 5) sourceC941) = raw15570 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15570; decide +kernel
    rw [ha]
    exact (canonical15570 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA941 + difference 5 3) (sourceB941 + difference 3 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA941 + difference 5 3) (sourceB941 + difference 3 5) sourceC941) = raw15571 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15571; decide +kernel
    rw [ha]
    exact (canonical15571 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA941 + difference 5 4) (sourceB941 + difference 4 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA941 + difference 5 4) (sourceB941 + difference 4 5) sourceC941) = raw15572 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15572; decide +kernel
    rw [ha]
    exact (canonical15572 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA941 sourceB941 sourceC941
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm941, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq944 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm944 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA944 + difference 0 0) (sourceB944 + difference 0 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA944 + difference 0 0) (sourceB944 + difference 0 0) sourceC944) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA944 + difference 0 1) (sourceB944 + difference 1 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA944 + difference 0 1) (sourceB944 + difference 1 0) sourceC944) = raw15634 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15634; decide +kernel
    rw [ha]
    exact (canonical15634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA944 + difference 0 2) (sourceB944 + difference 2 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA944 + difference 0 2) (sourceB944 + difference 2 0) sourceC944) = raw15635 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15635; decide +kernel
    rw [ha]
    exact (canonical15635 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA944 + difference 0 3) (sourceB944 + difference 3 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA944 + difference 0 3) (sourceB944 + difference 3 0) sourceC944) = raw15636 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15636; decide +kernel
    rw [ha]
    exact (canonical15636 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA944 + difference 0 4) (sourceB944 + difference 4 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA944 + difference 0 4) (sourceB944 + difference 4 0) sourceC944) = raw15637 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15637; decide +kernel
    rw [ha]
    exact (canonical15637 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA944 + difference 0 5) (sourceB944 + difference 5 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4046) := by
    have ha : (tripleCharges (sourceA944 + difference 0 5) (sourceB944 + difference 5 0) sourceC944) = raw15638 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15638; decide +kernel
    rw [ha]
    exact (canonical15638 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA944 + sourceB944) sourceC944) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA944 + sourceB944) sourceC944) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA944 sourceB944 sourceC944 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA944 sourceB944 sourceC944
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm944, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq945 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm945 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA945 + difference 0 0) (sourceB945 + difference 0 0) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA945 + difference 0 0) (sourceB945 + difference 0 0) sourceC945) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA945 + difference 1 0) (sourceB945 + difference 0 1) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA945 + difference 1 0) (sourceB945 + difference 0 1) sourceC945) = raw15640 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15640; decide +kernel
    rw [ha]
    exact (canonical15640 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA945 + difference 2 0) (sourceB945 + difference 0 2) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3176) := by
    have ha : (tripleCharges (sourceA945 + difference 2 0) (sourceB945 + difference 0 2) sourceC945) = raw15641 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15641; decide +kernel
    rw [ha]
    exact (canonical15641 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA945 + difference 3 0) (sourceB945 + difference 0 3) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3176) := by
    have ha : (tripleCharges (sourceA945 + difference 3 0) (sourceB945 + difference 0 3) sourceC945) = raw15642 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15642; decide +kernel
    rw [ha]
    exact (canonical15642 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA945 + difference 4 0) (sourceB945 + difference 0 4) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA945 + difference 4 0) (sourceB945 + difference 0 4) sourceC945) = raw15643 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15643; decide +kernel
    rw [ha]
    exact (canonical15643 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA945 + difference 5 0) (sourceB945 + difference 0 5) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2858) := by
    have ha : (tripleCharges (sourceA945 + difference 5 0) (sourceB945 + difference 0 5) sourceC945) = raw15644 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15644; decide +kernel
    rw [ha]
    exact (canonical15644 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA945 + sourceB945) sourceC945) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA945 + sourceB945) sourceC945) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA945 sourceB945 sourceC945 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA945 sourceB945 sourceC945
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm945, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm946 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA946 + difference 1 0) (sourceB946 + difference 0 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA946 + difference 1 0) (sourceB946 + difference 0 1) sourceC946) = raw15640 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15640; decide +kernel
    rw [ha]
    exact (canonical15640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA946 + difference 1 1) (sourceB946 + difference 1 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA946 + difference 1 1) (sourceB946 + difference 1 1) sourceC946) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA946 + difference 1 2) (sourceB946 + difference 2 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA946 + difference 1 2) (sourceB946 + difference 2 1) sourceC946) = raw15645 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15645; decide +kernel
    rw [ha]
    exact (canonical15645 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA946 + difference 1 3) (sourceB946 + difference 3 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA946 + difference 1 3) (sourceB946 + difference 3 1) sourceC946) = raw15646 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15646; decide +kernel
    rw [ha]
    exact (canonical15646 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA946 + difference 1 4) (sourceB946 + difference 4 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3731) := by
    have ha : (tripleCharges (sourceA946 + difference 1 4) (sourceB946 + difference 4 1) sourceC946) = raw15647 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15647; decide +kernel
    rw [ha]
    exact (canonical15647 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA946 + difference 1 5) (sourceB946 + difference 5 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA946 + difference 1 5) (sourceB946 + difference 5 1) sourceC946) = raw15648 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15648; decide +kernel
    rw [ha]
    exact (canonical15648 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA946 + sourceB946) sourceC946) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA946 + sourceB946) sourceC946) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA946 sourceB946 sourceC946 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA946 sourceB946 sourceC946
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm946, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm947 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA947 + difference 0 1) (sourceB947 + difference 1 0) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA947 + difference 0 1) (sourceB947 + difference 1 0) sourceC947) = raw15634 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15634; decide +kernel
    rw [ha]
    exact (canonical15634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA947 + difference 1 1) (sourceB947 + difference 1 1) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA947 + difference 1 1) (sourceB947 + difference 1 1) sourceC947) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA947 + difference 2 1) (sourceB947 + difference 1 2) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3935) := by
    have ha : (tripleCharges (sourceA947 + difference 2 1) (sourceB947 + difference 1 2) sourceC947) = raw15649 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15649; decide +kernel
    rw [ha]
    exact (canonical15649 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA947 + difference 3 1) (sourceB947 + difference 1 3) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3935) := by
    have ha : (tripleCharges (sourceA947 + difference 3 1) (sourceB947 + difference 1 3) sourceC947) = raw15650 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15650; decide +kernel
    rw [ha]
    exact (canonical15650 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA947 + difference 4 1) (sourceB947 + difference 1 4) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA947 + difference 4 1) (sourceB947 + difference 1 4) sourceC947) = raw15651 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15651; decide +kernel
    rw [ha]
    exact (canonical15651 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA947 + difference 5 1) (sourceB947 + difference 1 5) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2859) := by
    have ha : (tripleCharges (sourceA947 + difference 5 1) (sourceB947 + difference 1 5) sourceC947) = raw15652 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15652; decide +kernel
    rw [ha]
    exact (canonical15652 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA947 + sourceB947) sourceC947) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA947 + sourceB947) sourceC947) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA947 sourceB947 sourceC947 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA947 sourceB947 sourceC947
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm947, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm948 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA948 + difference 2 0) (sourceB948 + difference 0 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3176) := by
    have ha : (tripleCharges (sourceA948 + difference 2 0) (sourceB948 + difference 0 2) sourceC948) = raw15641 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15641; decide +kernel
    rw [ha]
    exact (canonical15641 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA948 + difference 2 1) (sourceB948 + difference 1 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3935) := by
    have ha : (tripleCharges (sourceA948 + difference 2 1) (sourceB948 + difference 1 2) sourceC948) = raw15649 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15649; decide +kernel
    rw [ha]
    exact (canonical15649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA948 + difference 2 2) (sourceB948 + difference 2 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA948 + difference 2 2) (sourceB948 + difference 2 2) sourceC948) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA948 + difference 2 3) (sourceB948 + difference 3 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA948 + difference 2 3) (sourceB948 + difference 3 2) sourceC948) = raw15653 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15653; decide +kernel
    rw [ha]
    exact (canonical15653 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA948 + difference 2 4) (sourceB948 + difference 4 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA948 + difference 2 4) (sourceB948 + difference 4 2) sourceC948) = raw15654 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15654; decide +kernel
    rw [ha]
    exact (canonical15654 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA948 + difference 2 5) (sourceB948 + difference 5 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA948 + difference 2 5) (sourceB948 + difference 5 2) sourceC948) = raw15655 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15655; decide +kernel
    rw [ha]
    exact (canonical15655 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA948 + sourceB948) sourceC948) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA948 + sourceB948) sourceC948) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA948 sourceB948 sourceC948 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA948 sourceB948 sourceC948
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm948, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm949 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA949 + difference 0 2) (sourceB949 + difference 2 0) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA949 + difference 0 2) (sourceB949 + difference 2 0) sourceC949) = raw15635 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15635; decide +kernel
    rw [ha]
    exact (canonical15635 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA949 + difference 1 2) (sourceB949 + difference 2 1) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA949 + difference 1 2) (sourceB949 + difference 2 1) sourceC949) = raw15645 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15645; decide +kernel
    rw [ha]
    exact (canonical15645 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA949 + difference 2 2) (sourceB949 + difference 2 2) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA949 + difference 2 2) (sourceB949 + difference 2 2) sourceC949) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA949 + difference 3 2) (sourceB949 + difference 2 3) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA949 + difference 3 2) (sourceB949 + difference 2 3) sourceC949) = raw15656 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15656; decide +kernel
    rw [ha]
    exact (canonical15656 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA949 + difference 4 2) (sourceB949 + difference 2 4) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA949 + difference 4 2) (sourceB949 + difference 2 4) sourceC949) = raw15657 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15657; decide +kernel
    rw [ha]
    exact (canonical15657 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA949 + difference 5 2) (sourceB949 + difference 2 5) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA949 + difference 5 2) (sourceB949 + difference 2 5) sourceC949) = raw15658 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15658; decide +kernel
    rw [ha]
    exact (canonical15658 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA949 + sourceB949) sourceC949) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA949 + sourceB949) sourceC949) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA949 sourceB949 sourceC949 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA949 sourceB949 sourceC949
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm949, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm950 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA950 + difference 4 0) (sourceB950 + difference 0 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA950 + difference 4 0) (sourceB950 + difference 0 4) sourceC950) = raw15643 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15643; decide +kernel
    rw [ha]
    exact (canonical15643 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA950 + difference 4 1) (sourceB950 + difference 1 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA950 + difference 4 1) (sourceB950 + difference 1 4) sourceC950) = raw15651 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15651; decide +kernel
    rw [ha]
    exact (canonical15651 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA950 + difference 4 2) (sourceB950 + difference 2 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA950 + difference 4 2) (sourceB950 + difference 2 4) sourceC950) = raw15657 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15657; decide +kernel
    rw [ha]
    exact (canonical15657 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA950 + difference 4 3) (sourceB950 + difference 3 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA950 + difference 4 3) (sourceB950 + difference 3 4) sourceC950) = raw15659 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15659; decide +kernel
    rw [ha]
    exact (canonical15659 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA950 + difference 4 4) (sourceB950 + difference 4 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA950 + difference 4 4) (sourceB950 + difference 4 4) sourceC950) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA950 + difference 4 5) (sourceB950 + difference 5 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA950 + difference 4 5) (sourceB950 + difference 5 4) sourceC950) = raw15660 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15660; decide +kernel
    rw [ha]
    exact (canonical15660 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA950 + sourceB950) sourceC950) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA950 + sourceB950) sourceC950) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA950 sourceB950 sourceC950 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA950 sourceB950 sourceC950
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm950, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq951 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm951 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA951 + difference 0 4) (sourceB951 + difference 4 0) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA951 + difference 0 4) (sourceB951 + difference 4 0) sourceC951) = raw15637 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15637; decide +kernel
    rw [ha]
    exact (canonical15637 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA951 + difference 1 4) (sourceB951 + difference 4 1) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3731) := by
    have ha : (tripleCharges (sourceA951 + difference 1 4) (sourceB951 + difference 4 1) sourceC951) = raw15647 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15647; decide +kernel
    rw [ha]
    exact (canonical15647 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA951 + difference 2 4) (sourceB951 + difference 4 2) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA951 + difference 2 4) (sourceB951 + difference 4 2) sourceC951) = raw15654 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15654; decide +kernel
    rw [ha]
    exact (canonical15654 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA951 + difference 3 4) (sourceB951 + difference 4 3) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA951 + difference 3 4) (sourceB951 + difference 4 3) sourceC951) = raw15661 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15661; decide +kernel
    rw [ha]
    exact (canonical15661 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA951 + difference 4 4) (sourceB951 + difference 4 4) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA951 + difference 4 4) (sourceB951 + difference 4 4) sourceC951) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA951 + difference 5 4) (sourceB951 + difference 4 5) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA951 + difference 5 4) (sourceB951 + difference 4 5) sourceC951) = raw15662 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15662; decide +kernel
    rw [ha]
    exact (canonical15662 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA951 + sourceB951) sourceC951) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA951 + sourceB951) sourceC951) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA951 sourceB951 sourceC951 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA951 sourceB951 sourceC951
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm951, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck816 : Integer.Sparse.reindex keyMap MixedData.row816 = numericRow816 := by decide +kernel

theorem numericCheck816 (x : Master → ℝ) : Integer.Sparse.eval numericRow816 x =
    (17280 : ℝ) * reducedSource816 x := by
  norm_num [numericRow816, reducedSource816, Integer.Sparse.eval, Sparse.eval, nodeValue4992, nodeValue4993, nodeValue4999, nodeValue5004, nodeValue5005, nodeValue5011, nodeValue5145, nodeValue5251, nodeValue5265, nodeValue5282, nodeValue5379, nodeValue5414, nodeValue5421, nodeValue5424, nodeValue5431, nodeValue5439, nodeValue5446, nodeValue5450, nodeValue5470, nodeValue5472, nodeValue5481]
  ring

theorem reindexCheck818 : Integer.Sparse.reindex keyMap MixedData.row818 = numericRow818 := by decide +kernel

theorem numericCheck818 (x : Master → ℝ) : Integer.Sparse.eval numericRow818 x =
    (4320 : ℝ) * reducedSource818 x := by
  norm_num [numericRow818, reducedSource818, Integer.Sparse.eval, Sparse.eval, nodeValue2389, nodeValue2390, nodeValue2396, nodeValue2730, nodeValue3345, nodeValue3346, nodeValue3350, nodeValue3539, nodeValue3562, nodeValue3580, nodeValue3819, nodeValue3832, nodeValue3843, nodeValue3858, nodeValue3873, nodeValue3875, nodeValue3884, nodeValue3887, nodeValue3947, nodeValue3991, nodeValue4002]
  ring

theorem reindexCheck819 : Integer.Sparse.reindex keyMap MixedData.row819 = numericRow819 := by decide +kernel

theorem numericCheck819 (x : Master → ℝ) : Integer.Sparse.eval numericRow819 x =
    (1 : ℝ) * reducedSource819 x := by
  norm_num [numericRow819, reducedSource819, Integer.Sparse.eval, Sparse.eval, nodeValue3846, nodeValue3947, nodeValue3949, nodeValue3957, nodeValue4008, nodeValue4091]

theorem reindexCheck820 : Integer.Sparse.reindex keyMap MixedData.row820 = numericRow820 := by decide +kernel

theorem numericCheck820 (x : Master → ℝ) : Integer.Sparse.eval numericRow820 x =
    (1 : ℝ) * reducedSource820 x := by
  norm_num [numericRow820, reducedSource820, Integer.Sparse.eval, Sparse.eval, nodeValue2567, nodeValue3724, nodeValue3827, nodeValue3838, nodeValue3846, nodeValue3849, nodeValue4091]

theorem reindexCheck821 : Integer.Sparse.reindex keyMap MixedData.row821 = numericRow821 := by decide +kernel

theorem numericCheck821 (x : Master → ℝ) : Integer.Sparse.eval numericRow821 x =
    (17280 : ℝ) * reducedSource821 x := by
  norm_num [numericRow821, reducedSource821, Integer.Sparse.eval, Sparse.eval, nodeValue4791, nodeValue4795, nodeValue4799, nodeValue4863, nodeValue5181, nodeValue5184, nodeValue5243, nodeValue5348, nodeValue5350, nodeValue5354, nodeValue5379, nodeValue5383, nodeValue5406, nodeValue5414, nodeValue5429, nodeValue5430, nodeValue5431, nodeValue5447, nodeValue5471, nodeValue5472, nodeValue5482]
  ring

theorem reindexCheck824 : Integer.Sparse.reindex keyMap MixedData.row824 = numericRow824 := by decide +kernel

theorem numericCheck824 (x : Master → ℝ) : Integer.Sparse.eval numericRow824 x =
    (1 : ℝ) * reducedSource824 x := by
  norm_num [numericRow824, reducedSource824, Integer.Sparse.eval, Sparse.eval, nodeValue3849, nodeValue3953, nodeValue3954, nodeValue3957, nodeValue4046, nodeValue4091]

theorem reindexCheck825 : Integer.Sparse.reindex keyMap MixedData.row825 = numericRow825 := by decide +kernel

theorem numericCheck825 (x : Master → ℝ) : Integer.Sparse.eval numericRow825 x =
    (1 : ℝ) * reducedSource825 x := by
  norm_num [numericRow825, reducedSource825, Integer.Sparse.eval, Sparse.eval, nodeValue2858, nodeValue3176, nodeValue3179, nodeValue3199, nodeValue3954, nodeValue4091]

theorem reindexCheck826 : Integer.Sparse.reindex keyMap MixedData.row826 = numericRow826 := by decide +kernel

theorem numericCheck826 (x : Master → ℝ) : Integer.Sparse.eval numericRow826 x =
    (1 : ℝ) * reducedSource826 x := by
  norm_num [numericRow826, reducedSource826, Integer.Sparse.eval, Sparse.eval, nodeValue3179, nodeValue3731, nodeValue3954, nodeValue4025, nodeValue4091]

theorem reindexCheck827 : Integer.Sparse.reindex keyMap MixedData.row827 = numericRow827 := by decide +kernel

theorem numericCheck827 (x : Master → ℝ) : Integer.Sparse.eval numericRow827 x =
    (1 : ℝ) * reducedSource827 x := by
  norm_num [numericRow827, reducedSource827, Integer.Sparse.eval, Sparse.eval, nodeValue2859, nodeValue3685, nodeValue3935, nodeValue3953, nodeValue3954, nodeValue4091]

theorem reindexCheck828 : Integer.Sparse.reindex keyMap MixedData.row828 = numericRow828 := by decide +kernel

theorem numericCheck828 (x : Master → ℝ) : Integer.Sparse.eval numericRow828 x =
    (1 : ℝ) * reducedSource828 x := by
  norm_num [numericRow828, reducedSource828, Integer.Sparse.eval, Sparse.eval, nodeValue3176, nodeValue3724, nodeValue3935, nodeValue3949, nodeValue3954, nodeValue3972, nodeValue4091]

theorem reindexCheck829 : Integer.Sparse.reindex keyMap MixedData.row829 = numericRow829 := by decide +kernel

theorem numericCheck829 (x : Master → ℝ) : Integer.Sparse.eval numericRow829 x =
    (1 : ℝ) * reducedSource829 x := by
  norm_num [numericRow829, reducedSource829, Integer.Sparse.eval, Sparse.eval, nodeValue2864, nodeValue3692, nodeValue3949, nodeValue3954, nodeValue3957, nodeValue4091]

theorem reindexCheck830 : Integer.Sparse.reindex keyMap MixedData.row830 = numericRow830 := by decide +kernel

theorem numericCheck830 (x : Master → ℝ) : Integer.Sparse.eval numericRow830 x =
    (1 : ℝ) * reducedSource830 x := by
  norm_num [numericRow830, reducedSource830, Integer.Sparse.eval, Sparse.eval, nodeValue3199, nodeValue3685, nodeValue3692, nodeValue3801, nodeValue3954, nodeValue4091]

theorem reindexCheck831 : Integer.Sparse.reindex keyMap MixedData.row831 = numericRow831 := by decide +kernel

theorem numericCheck831 (x : Master → ℝ) : Integer.Sparse.eval numericRow831 x =
    (1 : ℝ) * reducedSource831 x := by
  norm_num [numericRow831, reducedSource831, Integer.Sparse.eval, Sparse.eval, nodeValue3030, nodeValue3724, nodeValue3731, nodeValue3849, nodeValue3954, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource816 (mixedVector B) = 0 := by
  have h4992 : mixedVector B (Sum.inr 4992) = Sparse.eval nodeValue4992 (mixedVector B) := by
    change mixedMoment B node4992 node4992Labels = _
    exact sound4992 B hB hF
  have h4993 : mixedVector B (Sum.inr 4993) = Sparse.eval nodeValue4993 (mixedVector B) := by
    change mixedMoment B node4993 node4993Labels = _
    exact sound4993 B hB hF
  have h4999 : mixedVector B (Sum.inr 4999) = Sparse.eval nodeValue4999 (mixedVector B) := by
    change mixedMoment B node4999 node4999Labels = _
    exact sound4999 B hB hF
  have h5004 : mixedVector B (Sum.inr 5004) = Sparse.eval nodeValue5004 (mixedVector B) := by
    change mixedMoment B node5004 node5004Labels = _
    exact sound5004 B hB hF
  have h5005 : mixedVector B (Sum.inr 5005) = Sparse.eval nodeValue5005 (mixedVector B) := by
    change mixedMoment B node5005 node5005Labels = _
    exact sound5005 B hB hF
  have h5011 : mixedVector B (Sum.inr 5011) = Sparse.eval nodeValue5011 (mixedVector B) := by
    change mixedMoment B node5011 node5011Labels = _
    exact sound5011 B hB hF
  have h5145 : mixedVector B (Sum.inr 5145) = Sparse.eval nodeValue5145 (mixedVector B) := by
    change mixedMoment B node5145 node5145Labels = _
    exact sound5145 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5470 : mixedVector B (Sum.inr 5470) = Sparse.eval nodeValue5470 (mixedVector B) := by
    change mixedMoment B node5470 node5470Labels = _
    exact sound5470 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  simpa only [sourceForm935, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4992, h4993, h4999, h5004, h5005, h5011, h5145, h5251, h5265, h5282, h5379, h5414, h5421, h5424, h5431, h5439, h5446, h5450, h5470, h5472, h5481, reducedSource816] using sourceEq935 B hB

theorem rowSound816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row816 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck816, numericCheck816, reducedZero816 B hB hF, mul_zero]

theorem rowSound818 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row818 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck818, numericCheck818, reducedZero818_e B hB hF, mul_zero]

theorem reducedZero819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource819 (mixedVector B) = 0 := by
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3947 : mixedVector B (Sum.inr 3947) = Sparse.eval nodeValue3947 (mixedVector B) := by
    change mixedMoment B node3947 node3947Labels = _
    exact sound3947 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4008 : mixedVector B (Sum.inr 4008) = Sparse.eval nodeValue4008 (mixedVector B) := by
    change mixedMoment B node4008 node4008Labels = _
    exact sound4008 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm938, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3846, h3947, h3949, h3957, h4008, h4091, reducedSource819] using sourceEq938 B hB

theorem rowSound819 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row819 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck819, numericCheck819, reducedZero819 B hB hF, mul_zero]

theorem reducedZero820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource820 (mixedVector B) = 0 := by
  have h2567 : mixedVector B (Sum.inr 2567) = Sparse.eval nodeValue2567 (mixedVector B) := by
    change mixedMoment B node2567 node2567Labels = _
    exact sound2567 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3827 : mixedVector B (Sum.inr 3827) = Sparse.eval nodeValue3827 (mixedVector B) := by
    change mixedMoment B node3827 node3827Labels = _
    exact sound3827 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm940, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2567, h3724, h3827, h3838, h3846, h3849, h4091, reducedSource820] using sourceEq940 B hB

theorem rowSound820 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row820 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck820, numericCheck820, reducedZero820 B hB hF, mul_zero]

theorem reducedZero821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource821 (mixedVector B) = 0 := by
  have h4791 : mixedVector B (Sum.inr 4791) = Sparse.eval nodeValue4791 (mixedVector B) := by
    change mixedMoment B node4791 node4791Labels = _
    exact sound4791 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4799 : mixedVector B (Sum.inr 4799) = Sparse.eval nodeValue4799 (mixedVector B) := by
    change mixedMoment B node4799 node4799Labels = _
    exact sound4799 B hB hF
  have h4863 : mixedVector B (Sum.inr 4863) = Sparse.eval nodeValue4863 (mixedVector B) := by
    change mixedMoment B node4863 node4863Labels = _
    exact sound4863 B hB hF
  have h5181 : mixedVector B (Sum.inr 5181) = Sparse.eval nodeValue5181 (mixedVector B) := by
    change mixedMoment B node5181 node5181Labels = _
    exact sound5181 B hB hF
  have h5184 : mixedVector B (Sum.inr 5184) = Sparse.eval nodeValue5184 (mixedVector B) := by
    change mixedMoment B node5184 node5184Labels = _
    exact sound5184 B hB hF
  have h5243 : mixedVector B (Sum.inr 5243) = Sparse.eval nodeValue5243 (mixedVector B) := by
    change mixedMoment B node5243 node5243Labels = _
    exact sound5243 B hB hF
  have h5348 : mixedVector B (Sum.inr 5348) = Sparse.eval nodeValue5348 (mixedVector B) := by
    change mixedMoment B node5348 node5348Labels = _
    exact sound5348 B hB hF
  have h5350 : mixedVector B (Sum.inr 5350) = Sparse.eval nodeValue5350 (mixedVector B) := by
    change mixedMoment B node5350 node5350Labels = _
    exact sound5350 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5383 : mixedVector B (Sum.inr 5383) = Sparse.eval nodeValue5383 (mixedVector B) := by
    change mixedMoment B node5383 node5383Labels = _
    exact sound5383 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5471 : mixedVector B (Sum.inr 5471) = Sparse.eval nodeValue5471 (mixedVector B) := by
    change mixedMoment B node5471 node5471Labels = _
    exact sound5471 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  simpa only [sourceForm941, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4791, h4795, h4799, h4863, h5181, h5184, h5243, h5348, h5350, h5354, h5379, h5383, h5406, h5414, h5429, h5430, h5431, h5447, h5471, h5472, h5482, reducedSource821] using sourceEq941 B hB

theorem rowSound821 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row821 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck821, numericCheck821, reducedZero821 B hB hF, mul_zero]

theorem reducedZero824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource824 (mixedVector B) = 0 := by
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4046 : mixedVector B (Sum.inr 4046) = Sparse.eval nodeValue4046 (mixedVector B) := by
    change mixedMoment B node4046 node4046Labels = _
    exact sound4046 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm944, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3849, h3953, h3954, h3957, h4046, h4091, reducedSource824] using sourceEq944 B hB

theorem rowSound824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row824 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck824, numericCheck824, reducedZero824 B hB hF, mul_zero]

theorem reducedZero825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource825 (mixedVector B) = 0 := by
  have h2858 : mixedVector B (Sum.inr 2858) = Sparse.eval nodeValue2858 (mixedVector B) := by
    change mixedMoment B node2858 node2858Labels = _
    exact sound2858 B hB hF
  have h3176 : mixedVector B (Sum.inr 3176) = Sparse.eval nodeValue3176 (mixedVector B) := by
    change mixedMoment B node3176 node3176Labels = _
    exact sound3176 B hB hF
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm945, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2858, h3176, h3179, h3199, h3954, h4091, reducedSource825] using sourceEq945 B hB

theorem rowSound825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row825 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck825, numericCheck825, reducedZero825 B hB hF, mul_zero]

theorem reducedZero826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource826 (mixedVector B) = 0 := by
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3731 : mixedVector B (Sum.inr 3731) = Sparse.eval nodeValue3731 (mixedVector B) := by
    change mixedMoment B node3731 node3731Labels = _
    exact sound3731 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4025 : mixedVector B (Sum.inr 4025) = Sparse.eval nodeValue4025 (mixedVector B) := by
    change mixedMoment B node4025 node4025Labels = _
    exact sound4025 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm946, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3179, h3731, h3954, h4025, h4091, reducedSource826] using sourceEq946 B hB

theorem rowSound826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row826 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck826, numericCheck826, reducedZero826 B hB hF, mul_zero]

theorem reducedZero827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource827 (mixedVector B) = 0 := by
  have h2859 : mixedVector B (Sum.inr 2859) = Sparse.eval nodeValue2859 (mixedVector B) := by
    change mixedMoment B node2859 node2859Labels = _
    exact sound2859 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3935 : mixedVector B (Sum.inr 3935) = Sparse.eval nodeValue3935 (mixedVector B) := by
    change mixedMoment B node3935 node3935Labels = _
    exact sound3935 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm947, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2859, h3685, h3935, h3953, h3954, h4091, reducedSource827] using sourceEq947 B hB

theorem rowSound827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row827 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck827, numericCheck827, reducedZero827 B hB hF, mul_zero]

theorem reducedZero828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource828 (mixedVector B) = 0 := by
  have h3176 : mixedVector B (Sum.inr 3176) = Sparse.eval nodeValue3176 (mixedVector B) := by
    change mixedMoment B node3176 node3176Labels = _
    exact sound3176 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3935 : mixedVector B (Sum.inr 3935) = Sparse.eval nodeValue3935 (mixedVector B) := by
    change mixedMoment B node3935 node3935Labels = _
    exact sound3935 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm948, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3176, h3724, h3935, h3949, h3954, h3972, h4091, reducedSource828] using sourceEq948 B hB

theorem rowSound828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row828 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck828, numericCheck828, reducedZero828 B hB hF, mul_zero]

theorem reducedZero829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource829 (mixedVector B) = 0 := by
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm949, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2864, h3692, h3949, h3954, h3957, h4091, reducedSource829] using sourceEq949 B hB

theorem rowSound829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row829 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck829, numericCheck829, reducedZero829 B hB hF, mul_zero]

theorem reducedZero830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource830 (mixedVector B) = 0 := by
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3692 : mixedVector B (Sum.inr 3692) = Sparse.eval nodeValue3692 (mixedVector B) := by
    change mixedMoment B node3692 node3692Labels = _
    exact sound3692 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm950, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3199, h3685, h3692, h3801, h3954, h4091, reducedSource830] using sourceEq950 B hB

theorem rowSound830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row830 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck830, numericCheck830, reducedZero830 B hB hF, mul_zero]

theorem reducedZero831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource831 (mixedVector B) = 0 := by
  have h3030 : mixedVector B (Sum.inr 3030) = Sparse.eval nodeValue3030 (mixedVector B) := by
    change mixedMoment B node3030 node3030Labels = _
    exact sound3030 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3731 : mixedVector B (Sum.inr 3731) = Sparse.eval nodeValue3731 (mixedVector B) := by
    change mixedMoment B node3731 node3731Labels = _
    exact sound3731 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3954 : mixedVector B (Sum.inr 3954) = Sparse.eval nodeValue3954 (mixedVector B) := by
    change mixedMoment B node3954 node3954Labels = _
    exact sound3954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm951, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3030, h3724, h3731, h3849, h3954, h4091, reducedSource831] using sourceEq951 B hB

theorem rowSound831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row831 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck831, numericCheck831, reducedZero831 B hB hF, mul_zero]

theorem sourceRowsAt816 : MixedData.sourceRows (816 : Fin 2425) =
    MixedData.row816 := by decide +kernel

theorem sourceRowsAt817 : MixedData.sourceRows (817 : Fin 2425) =
    MixedData.row817 := by decide +kernel

theorem sourceRowsAt818 : MixedData.sourceRows (818 : Fin 2425) =
    MixedData.row818 := by decide +kernel

theorem sourceRowsAt819 : MixedData.sourceRows (819 : Fin 2425) =
    MixedData.row819 := by decide +kernel

theorem sourceRowsAt820 : MixedData.sourceRows (820 : Fin 2425) =
    MixedData.row820 := by decide +kernel

theorem sourceRowsAt821 : MixedData.sourceRows (821 : Fin 2425) =
    MixedData.row821 := by decide +kernel

theorem sourceRowsAt822 : MixedData.sourceRows (822 : Fin 2425) =
    MixedData.row822 := by decide +kernel

theorem sourceRowsAt823 : MixedData.sourceRows (823 : Fin 2425) =
    MixedData.row823 := by decide +kernel

theorem sourceRowsAt824 : MixedData.sourceRows (824 : Fin 2425) =
    MixedData.row824 := by decide +kernel

theorem sourceRowsAt825 : MixedData.sourceRows (825 : Fin 2425) =
    MixedData.row825 := by decide +kernel

theorem sourceRowsAt826 : MixedData.sourceRows (826 : Fin 2425) =
    MixedData.row826 := by decide +kernel

theorem sourceRowsAt827 : MixedData.sourceRows (827 : Fin 2425) =
    MixedData.row827 := by decide +kernel

theorem sourceRowsAt828 : MixedData.sourceRows (828 : Fin 2425) =
    MixedData.row828 := by decide +kernel

theorem sourceRowsAt829 : MixedData.sourceRows (829 : Fin 2425) =
    MixedData.row829 := by decide +kernel

theorem sourceRowsAt830 : MixedData.sourceRows (830 : Fin 2425) =
    MixedData.row830 := by decide +kernel

theorem sourceRowsAt831 : MixedData.sourceRows (831 : Fin 2425) =
    MixedData.row831 := by decide +kernel

theorem chunkSound51_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 51) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 816 ∨ k.val = 817 ∨ k.val = 818 ∨ k.val = 819 ∨ k.val = 820 ∨ k.val = 821 ∨ k.val = 822 ∨ k.val = 823 ∨ k.val = 824 ∨ k.val = 825 ∨ k.val = 826 ∨ k.val = 827 ∨ k.val = 828 ∨ k.val = 829 ∨ k.val = 830 ∨ k.val = 831 := by omega
  rcases heq with h816 | h817 | h818 | h819 | h820 | h821 | h822 | h823 | h824 | h825 | h826 | h827 | h828 | h829 | h830 | h831
  · have he : k = (816 : Fin 2425) := Fin.ext h816
    subst k
    rw [sourceRowsAt816]
    exact rowSound816 B hB hF
  · have he : k = (817 : Fin 2425) := Fin.ext h817
    subst k
    rw [sourceRowsAt817]
    exact rowSound817_e B hB hF
  · have he : k = (818 : Fin 2425) := Fin.ext h818
    subst k
    rw [sourceRowsAt818]
    exact rowSound818 B hB hF
  · have he : k = (819 : Fin 2425) := Fin.ext h819
    subst k
    rw [sourceRowsAt819]
    exact rowSound819 B hB hF
  · have he : k = (820 : Fin 2425) := Fin.ext h820
    subst k
    rw [sourceRowsAt820]
    exact rowSound820 B hB hF
  · have he : k = (821 : Fin 2425) := Fin.ext h821
    subst k
    rw [sourceRowsAt821]
    exact rowSound821 B hB hF
  · have he : k = (822 : Fin 2425) := Fin.ext h822
    subst k
    rw [sourceRowsAt822]
    exact rowSound822_e B hB hF
  · have he : k = (823 : Fin 2425) := Fin.ext h823
    subst k
    rw [sourceRowsAt823]
    exact rowSound823_e B hB hF
  · have he : k = (824 : Fin 2425) := Fin.ext h824
    subst k
    rw [sourceRowsAt824]
    exact rowSound824 B hB hF
  · have he : k = (825 : Fin 2425) := Fin.ext h825
    subst k
    rw [sourceRowsAt825]
    exact rowSound825 B hB hF
  · have he : k = (826 : Fin 2425) := Fin.ext h826
    subst k
    rw [sourceRowsAt826]
    exact rowSound826 B hB hF
  · have he : k = (827 : Fin 2425) := Fin.ext h827
    subst k
    rw [sourceRowsAt827]
    exact rowSound827 B hB hF
  · have he : k = (828 : Fin 2425) := Fin.ext h828
    subst k
    rw [sourceRowsAt828]
    exact rowSound828 B hB hF
  · have he : k = (829 : Fin 2425) := Fin.ext h829
    subst k
    rw [sourceRowsAt829]
    exact rowSound829 B hB hF
  · have he : k = (830 : Fin 2425) := Fin.ext h830
    subst k
    rw [sourceRowsAt830]
    exact rowSound830 B hB hF
  · have he : k = (831 : Fin 2425) := Fin.ext h831
    subst k
    rw [sourceRowsAt831]
    exact rowSound831 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e_oai
