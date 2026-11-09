-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:16.738204+00:00
-- url     : https://prove2.me/submissions/85f58904-a4a7-45ab-921e-a4e5cad7f828

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2594_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2766_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1492_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1493_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1293 raw1293Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw1293 raw1293Labels = mixedMoment B raw1293step0 raw1293step0Labels := by
      have ha : raw1293step0 = (fun i j => raw1293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1293step0 raw1293; decide +kernel
      have hl : raw1293step0Labels = raw1293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1293 raw1293Labels permutation32 permutation4
    mixedMoment B raw1293step0 raw1293step0Labels = mixedMoment B raw1293step1 raw1293step1Labels := by
      have ha : raw1293step1 = raw1293step0 := by apply Matrix.ext; unfold raw1293step1 raw1293step0; decide +kernel
      have hl : raw1293step0Labels = labelEmbedding7 ∘ raw1293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1293step0 raw1293step0Labels raw1293step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1294 raw1294Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw1294 raw1294Labels = mixedMoment B raw1294step0 raw1294step0Labels := by
      have ha : raw1294step0 = (fun i j => raw1294 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1294step0 raw1294; decide +kernel
      have hl : raw1294step0Labels = raw1294Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1294 raw1294Labels permutation32 permutation4
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1295 raw1295Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw1295 raw1295Labels = mixedMoment B raw1295step0 raw1295step0Labels := by
      have ha : raw1295step0 = (fun i j => raw1295 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1295step0 raw1295; decide +kernel
      have hl : raw1295step0Labels = raw1295Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1295 raw1295Labels permutation32 permutation6
    mixedMoment B raw1295step0 raw1295step0Labels = mixedMoment B raw1295step1 raw1295step1Labels := by
      have ha : raw1295step1 = -raw1295step0 := by apply Matrix.ext; change ∀ i j, raw1295step1 i j = -(raw1295step0 i j); unfold raw1295step1 raw1295step0; decide +kernel
      have hl : raw1295step1Labels = raw1295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1295step1 raw1295step1Labels = mixedMoment B raw1295step2 raw1295step2Labels := by
      have ha : raw1295step2 = raw1295step1 := by apply Matrix.ext; unfold raw1295step2 raw1295step1; decide +kernel
      have hl : raw1295step1Labels = labelEmbedding1 ∘ raw1295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1295step1 raw1295step1Labels raw1295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19876 raw19876Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw19876 raw19876Labels = mixedMoment B raw19876step0 raw19876step0Labels := by
      have hz : ∀ j, raw19876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19876step0 = (fun i j => raw19876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19876step0 raw19876; decide +kernel
      have hl : raw19876step0Labels = raw19876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19876 raw19876Labels permutation434 hz
    mixedMoment B raw19876step0 raw19876step0Labels = mixedMoment B raw19876step1 raw19876step1Labels := by
      have hz : ∀ j, raw19876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19876step1 = (fun i j => raw19876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19876step1 raw19876step0; decide +kernel
      have hl : raw19876step1Labels = raw19876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19876step0 raw19876step0Labels permutation80 hz
    mixedMoment B raw19876step1 raw19876step1Labels = mixedMoment B raw19876step2 raw19876step2Labels := by
      have ha : raw19876step2 = (fun i j => raw19876step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19876step2 raw19876step1; decide +kernel
      have hl : raw19876step2Labels = raw19876step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19876step1 raw19876step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

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

theorem canonical21461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21461 raw21461Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21461 raw21461Labels = mixedMoment B raw21461step0 raw21461step0Labels := by
      have hz : ∀ j, raw21461 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21461step0 = (fun i j => raw21461 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21461step0 raw21461; decide +kernel
      have hl : raw21461step0Labels = raw21461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461 raw21461Labels permutation520 hz
    mixedMoment B raw21461step0 raw21461step0Labels = mixedMoment B raw21461step1 raw21461step1Labels := by
      have hz : ∀ j, raw21461step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21461step1 = (fun i j => raw21461step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21461step1 raw21461step0; decide +kernel
      have hl : raw21461step1Labels = raw21461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step0 raw21461step0Labels permutation104 hz
    mixedMoment B raw21461step1 raw21461step1Labels = mixedMoment B raw21461step2 raw21461step2Labels := by
      have hz : ∀ j, raw21461step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21461step2 = (fun i j => raw21461step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21461step2 raw21461step1; decide +kernel
      have hl : raw21461step2Labels = raw21461step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step1 raw21461step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical21468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21468 raw21468Labels = mixedMoment B node943 node943Labels := by
  calc
    mixedMoment B raw21468 raw21468Labels = mixedMoment B raw21468step0 raw21468step0Labels := by
      have hz : ∀ j, raw21468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21468step0 = (fun i j => raw21468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21468step0 raw21468; decide +kernel
      have hl : raw21468step0Labels = raw21468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21468 raw21468Labels permutation346 hz
    _ = mixedMoment B node943 node943Labels := by rfl

theorem canonical21473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21473 raw21473Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw21473 raw21473Labels = mixedMoment B raw21473step0 raw21473step0Labels := by
      have hz : ∀ j, raw21473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21473step0 = (fun i j => raw21473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21473step0 raw21473; decide +kernel
      have hl : raw21473step0Labels = raw21473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21473 raw21473Labels permutation434 hz
    _ = mixedMoment B node1040 node1040Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21567 raw21567Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw21567 raw21567Labels = mixedMoment B raw21567step0 raw21567step0Labels := by
      have hz : ∀ j, raw21567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21567step0 = (fun i j => raw21567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21567step0 raw21567; decide +kernel
      have hl : raw21567step0Labels = raw21567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21567 raw21567Labels permutation434 hz
    mixedMoment B raw21567step0 raw21567step0Labels = mixedMoment B raw21567step1 raw21567step1Labels := by
      have hz : ∀ j, raw21567step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21567step1 = (fun i j => raw21567step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21567step1 raw21567step0; decide +kernel
      have hl : raw21567step1Labels = raw21567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21567step0 raw21567step0Labels permutation80 hz
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical21573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21573 raw21573Labels = mixedMoment B node1033 node1033Labels := by
  calc
    mixedMoment B raw21573 raw21573Labels = mixedMoment B raw21573step0 raw21573step0Labels := by
      have hz : ∀ j, raw21573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21573step0 = (fun i j => raw21573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21573step0 raw21573; decide +kernel
      have hl : raw21573step0Labels = raw21573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21573 raw21573Labels permutation346 hz
    mixedMoment B raw21573step0 raw21573step0Labels = mixedMoment B raw21573step1 raw21573step1Labels := by
      have ha : raw21573step1 = (fun i j => raw21573step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21573step1 raw21573step0; decide +kernel
      have hl : raw21573step1Labels = raw21573step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21573step0 raw21573step0Labels permutation34 permutation2
    _ = mixedMoment B node1033 node1033Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23799 raw23799Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23799 raw23799Labels = mixedMoment B raw23799step0 raw23799step0Labels := by
      have hz : ∀ j, raw23799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23799step0 = (fun i j => raw23799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23799step0 raw23799; decide +kernel
      have hl : raw23799step0Labels = raw23799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799 raw23799Labels permutation346 hz
    mixedMoment B raw23799step0 raw23799step0Labels = mixedMoment B raw23799step1 raw23799step1Labels := by
      have hz : ∀ j, raw23799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23799step1 = (fun i j => raw23799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23799step1 raw23799step0; decide +kernel
      have hl : raw23799step1Labels = raw23799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799step0 raw23799step0Labels permutation56 hz
    mixedMoment B raw23799step1 raw23799step1Labels = mixedMoment B raw23799step2 raw23799step2Labels := by
      have ha : raw23799step2 = -raw23799step1 := by apply Matrix.ext; change ∀ i j, raw23799step2 i j = -(raw23799step1 i j); unfold raw23799step2 raw23799step1; decide +kernel
      have hl : raw23799step2Labels = raw23799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

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

theorem canonical25350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25350 raw25350Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw25350 raw25350Labels = mixedMoment B raw25350step0 raw25350step0Labels := by
      have hz : ∀ j, raw25350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25350step0 = (fun i j => raw25350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25350step0 raw25350; decide +kernel
      have hl : raw25350step0Labels = raw25350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25350 raw25350Labels permutation346 hz
    mixedMoment B raw25350step0 raw25350step0Labels = mixedMoment B raw25350step1 raw25350step1Labels := by
      have ha : raw25350step1 = (fun i j => raw25350step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25350step1 raw25350step0; decide +kernel
      have hl : raw25350step1Labels = raw25350step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25350step0 raw25350step0Labels permutation44 permutation4
    mixedMoment B raw25350step1 raw25350step1Labels = mixedMoment B raw25350step2 raw25350step2Labels := by
      have ha : raw25350step2 = -raw25350step1 := by apply Matrix.ext; change ∀ i j, raw25350step2 i j = -(raw25350step1 i j); unfold raw25350step2 raw25350step1; decide +kernel
      have hl : raw25350step2Labels = raw25350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node806 node806Labels := by rfl

theorem canonical25413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25413 raw25413Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw25413 raw25413Labels = mixedMoment B raw25413step0 raw25413step0Labels := by
      have hz : ∀ j, raw25413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25413step0 = (fun i j => raw25413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25413step0 raw25413; decide +kernel
      have hl : raw25413step0Labels = raw25413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25413 raw25413Labels permutation346 hz
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical25415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25415 raw25415Labels = mixedMoment B node577 node577Labels := by
  calc
    _ = mixedMoment B node577 node577Labels := by rfl

theorem canonical25421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25421 raw25421Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw25421 raw25421Labels = mixedMoment B raw25421step0 raw25421step0Labels := by
      have hz : ∀ j, raw25421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25421step0 = (fun i j => raw25421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25421step0 raw25421; decide +kernel
      have hl : raw25421step0Labels = raw25421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25421 raw25421Labels permutation346 hz
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical25422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25422 raw25422Labels = mixedMoment B node941 node941Labels := by
  calc
    _ = mixedMoment B node941 node941Labels := by rfl

theorem canonical25423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25423 raw25423Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw25423 raw25423Labels = mixedMoment B raw25423step0 raw25423step0Labels := by
      have hz : ∀ j, raw25423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25423step0 = (fun i j => raw25423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25423step0 raw25423; decide +kernel
      have hl : raw25423step0Labels = raw25423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25423 raw25423Labels permutation346 hz
    mixedMoment B raw25423step0 raw25423step0Labels = mixedMoment B raw25423step1 raw25423step1Labels := by
      have ha : raw25423step1 = (fun i j => raw25423step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25423step1 raw25423step0; decide +kernel
      have hl : raw25423step1Labels = raw25423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25423step0 raw25423step0Labels permutation34 permutation2
    _ = mixedMoment B node946 node946Labels := by rfl

theorem canonical25424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25424 raw25424Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw25424 raw25424Labels = mixedMoment B raw25424step0 raw25424step0Labels := by
      have hz : ∀ j, raw25424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25424step0 = (fun i j => raw25424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25424step0 raw25424; decide +kernel
      have hl : raw25424step0Labels = raw25424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25424 raw25424Labels permutation346 hz
    _ = mixedMoment B node946 node946Labels := by rfl

theorem canonical25425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25425 raw25425Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw25425 raw25425Labels = mixedMoment B raw25425step0 raw25425step0Labels := by
      have hz : ∀ j, raw25425 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25425step0 = (fun i j => raw25425 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25425step0 raw25425; decide +kernel
      have hl : raw25425step0Labels = raw25425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25425 raw25425Labels permutation520 hz
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical25426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25426 raw25426Labels = mixedMoment B node1038 node1038Labels := by
  calc
    _ = mixedMoment B node1038 node1038Labels := by rfl

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

theorem canonical25428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25428 raw25428Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw25428 raw25428Labels = mixedMoment B raw25428step0 raw25428step0Labels := by
      have hz : ∀ j, raw25428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25428step0 = (fun i j => raw25428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25428step0 raw25428; decide +kernel
      have hl : raw25428step0Labels = raw25428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25428 raw25428Labels permutation346 hz
    mixedMoment B raw25428step0 raw25428step0Labels = mixedMoment B raw25428step1 raw25428step1Labels := by
      have ha : raw25428step1 = (fun i j => raw25428step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25428step1 raw25428step0; decide +kernel
      have hl : raw25428step1Labels = raw25428step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25428step0 raw25428step0Labels permutation40 permutation3
    mixedMoment B raw25428step1 raw25428step1Labels = mixedMoment B raw25428step2 raw25428step2Labels := by
      have ha : raw25428step2 = raw25428step1 := by apply Matrix.ext; unfold raw25428step2 raw25428step1; decide +kernel
      have hl : raw25428step1Labels = labelEmbedding6 ∘ raw25428step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25428step1 raw25428step1Labels raw25428step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

theorem canonical25429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25429 raw25429Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw25429 raw25429Labels = mixedMoment B raw25429step0 raw25429step0Labels := by
      have ha : raw25429step0 = (fun i j => raw25429 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25429step0 raw25429; decide +kernel
      have hl : raw25429step0Labels = raw25429Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25429 raw25429Labels permutation184 permutation3
    mixedMoment B raw25429step0 raw25429step0Labels = mixedMoment B raw25429step1 raw25429step1Labels := by
      have ha : raw25429step1 = raw25429step0 := by apply Matrix.ext; unfold raw25429step1 raw25429step0; decide +kernel
      have hl : raw25429step0Labels = labelEmbedding6 ∘ raw25429step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25429step0 raw25429step0Labels raw25429step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

theorem canonical25430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25430 raw25430Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw25430 raw25430Labels = mixedMoment B raw25430step0 raw25430step0Labels := by
      have hz : ∀ j, raw25430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25430step0 = (fun i j => raw25430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25430step0 raw25430; decide +kernel
      have hl : raw25430step0Labels = raw25430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25430 raw25430Labels permutation346 hz
    mixedMoment B raw25430step0 raw25430step0Labels = mixedMoment B raw25430step1 raw25430step1Labels := by
      have ha : raw25430step1 = (fun i j => raw25430step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25430step1 raw25430step0; decide +kernel
      have hl : raw25430step1Labels = raw25430step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25430step0 raw25430step0Labels permutation46 permutation3
    mixedMoment B raw25430step1 raw25430step1Labels = mixedMoment B raw25430step2 raw25430step2Labels := by
      have ha : raw25430step2 = raw25430step1 := by apply Matrix.ext; unfold raw25430step2 raw25430step1; decide +kernel
      have hl : raw25430step1Labels = labelEmbedding6 ∘ raw25430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25430step1 raw25430step1Labels raw25430step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical25431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25431 raw25431Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25431 raw25431Labels = mixedMoment B raw25431step0 raw25431step0Labels := by
      have hz : ∀ j, raw25431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25431step0 = (fun i j => raw25431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25431step0 raw25431; decide +kernel
      have hl : raw25431step0Labels = raw25431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25431 raw25431Labels permutation346 hz
    mixedMoment B raw25431step0 raw25431step0Labels = mixedMoment B raw25431step1 raw25431step1Labels := by
      have ha : raw25431step1 = (fun i j => raw25431step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25431step1 raw25431step0; decide +kernel
      have hl : raw25431step1Labels = raw25431step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25431step0 raw25431step0Labels permutation41 permutation3
    mixedMoment B raw25431step1 raw25431step1Labels = mixedMoment B raw25431step2 raw25431step2Labels := by
      have ha : raw25431step2 = raw25431step1 := by apply Matrix.ext; unfold raw25431step2 raw25431step1; decide +kernel
      have hl : raw25431step1Labels = labelEmbedding6 ∘ raw25431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25431step1 raw25431step1Labels raw25431step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical25432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25432 raw25432Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw25432 raw25432Labels = mixedMoment B raw25432step0 raw25432step0Labels := by
      have ha : raw25432step0 = (fun i j => raw25432 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25432step0 raw25432; decide +kernel
      have hl : raw25432step0Labels = raw25432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25432 raw25432Labels permutation160 permutation3
    mixedMoment B raw25432step0 raw25432step0Labels = mixedMoment B raw25432step1 raw25432step1Labels := by
      have ha : raw25432step1 = raw25432step0 := by apply Matrix.ext; unfold raw25432step1 raw25432step0; decide +kernel
      have hl : raw25432step0Labels = labelEmbedding6 ∘ raw25432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25432step0 raw25432step0Labels raw25432step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

theorem canonical25433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25433 raw25433Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25433 raw25433Labels = mixedMoment B raw25433step0 raw25433step0Labels := by
      have ha : raw25433step0 = (fun i j => raw25433 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25433step0 raw25433; decide +kernel
      have hl : raw25433step0Labels = raw25433Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25433 raw25433Labels permutation160 permutation3
    mixedMoment B raw25433step0 raw25433step0Labels = mixedMoment B raw25433step1 raw25433step1Labels := by
      have ha : raw25433step1 = raw25433step0 := by apply Matrix.ext; unfold raw25433step1 raw25433step0; decide +kernel
      have hl : raw25433step0Labels = labelEmbedding6 ∘ raw25433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25433step0 raw25433step0Labels raw25433step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical25434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25434 raw25434Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw25434 raw25434Labels = mixedMoment B raw25434step0 raw25434step0Labels := by
      have ha : raw25434step0 = (fun i j => raw25434 (permutation226 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25434step0 raw25434; decide +kernel
      have hl : raw25434step0Labels = raw25434Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25434 raw25434Labels permutation226 permutation3
    mixedMoment B raw25434step0 raw25434step0Labels = mixedMoment B raw25434step1 raw25434step1Labels := by
      have ha : raw25434step1 = raw25434step0 := by apply Matrix.ext; unfold raw25434step1 raw25434step0; decide +kernel
      have hl : raw25434step0Labels = labelEmbedding6 ∘ raw25434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25434step0 raw25434step0Labels raw25434step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

theorem canonical25435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25435 raw25435Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw25435 raw25435Labels = mixedMoment B raw25435step0 raw25435step0Labels := by
      have ha : raw25435step0 = (fun i j => raw25435 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25435step0 raw25435; decide +kernel
      have hl : raw25435step0Labels = raw25435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25435 raw25435Labels permutation160 permutation3
    mixedMoment B raw25435step0 raw25435step0Labels = mixedMoment B raw25435step1 raw25435step1Labels := by
      have ha : raw25435step1 = raw25435step0 := by apply Matrix.ext; unfold raw25435step1 raw25435step0; decide +kernel
      have hl : raw25435step0Labels = labelEmbedding6 ∘ raw25435step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25435step0 raw25435step0Labels raw25435step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical25436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25436 raw25436Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw25436 raw25436Labels = mixedMoment B raw25436step0 raw25436step0Labels := by
      have hz : ∀ j, raw25436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25436step0 = (fun i j => raw25436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25436step0 raw25436; decide +kernel
      have hl : raw25436step0Labels = raw25436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25436 raw25436Labels permutation346 hz
    mixedMoment B raw25436step0 raw25436step0Labels = mixedMoment B raw25436step1 raw25436step1Labels := by
      have ha : raw25436step1 = (fun i j => raw25436step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25436step1 raw25436step0; decide +kernel
      have hl : raw25436step1Labels = raw25436step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25436step0 raw25436step0Labels permutation34 permutation3
    mixedMoment B raw25436step1 raw25436step1Labels = mixedMoment B raw25436step2 raw25436step2Labels := by
      have ha : raw25436step2 = raw25436step1 := by apply Matrix.ext; unfold raw25436step2 raw25436step1; decide +kernel
      have hl : raw25436step1Labels = labelEmbedding6 ∘ raw25436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25436step1 raw25436step1Labels raw25436step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

theorem canonical25437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25437 raw25437Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25437 raw25437Labels = mixedMoment B raw25437step0 raw25437step0Labels := by
      have hz : ∀ j, raw25437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25437step0 = (fun i j => raw25437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25437step0 raw25437; decide +kernel
      have hl : raw25437step0Labels = raw25437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25437 raw25437Labels permutation346 hz
    mixedMoment B raw25437step0 raw25437step0Labels = mixedMoment B raw25437step1 raw25437step1Labels := by
      have ha : raw25437step1 = (fun i j => raw25437step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25437step1 raw25437step0; decide +kernel
      have hl : raw25437step1Labels = raw25437step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25437step0 raw25437step0Labels permutation34 permutation3
    mixedMoment B raw25437step1 raw25437step1Labels = mixedMoment B raw25437step2 raw25437step2Labels := by
      have ha : raw25437step2 = raw25437step1 := by apply Matrix.ext; unfold raw25437step2 raw25437step1; decide +kernel
      have hl : raw25437step1Labels = labelEmbedding6 ∘ raw25437step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25437step1 raw25437step1Labels raw25437step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical25438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25438 raw25438Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw25438 raw25438Labels = mixedMoment B raw25438step0 raw25438step0Labels := by
      have ha : raw25438step0 = (fun i j => raw25438 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25438step0 raw25438; decide +kernel
      have hl : raw25438step0Labels = raw25438Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25438 raw25438Labels permutation178 permutation3
    mixedMoment B raw25438step0 raw25438step0Labels = mixedMoment B raw25438step1 raw25438step1Labels := by
      have ha : raw25438step1 = raw25438step0 := by apply Matrix.ext; unfold raw25438step1 raw25438step0; decide +kernel
      have hl : raw25438step0Labels = labelEmbedding6 ∘ raw25438step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25438step0 raw25438step0Labels raw25438step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

theorem canonical25439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25439 raw25439Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw25439 raw25439Labels = mixedMoment B raw25439step0 raw25439step0Labels := by
      have hz : ∀ j, raw25439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25439step0 = (fun i j => raw25439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25439step0 raw25439; decide +kernel
      have hl : raw25439step0Labels = raw25439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25439 raw25439Labels permutation346 hz
    mixedMoment B raw25439step0 raw25439step0Labels = mixedMoment B raw25439step1 raw25439step1Labels := by
      have ha : raw25439step1 = (fun i j => raw25439step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25439step1 raw25439step0; decide +kernel
      have hl : raw25439step1Labels = raw25439step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25439step0 raw25439step0Labels permutation44 permutation3
    mixedMoment B raw25439step1 raw25439step1Labels = mixedMoment B raw25439step2 raw25439step2Labels := by
      have ha : raw25439step2 = raw25439step1 := by apply Matrix.ext; unfold raw25439step2 raw25439step1; decide +kernel
      have hl : raw25439step1Labels = labelEmbedding6 ∘ raw25439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25439step1 raw25439step1Labels raw25439step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

theorem canonical25440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25440 raw25440Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25440 raw25440Labels = mixedMoment B raw25440step0 raw25440step0Labels := by
      have hz : ∀ j, raw25440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25440step0 = (fun i j => raw25440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25440step0 raw25440; decide +kernel
      have hl : raw25440step0Labels = raw25440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25440 raw25440Labels permutation346 hz
    mixedMoment B raw25440step0 raw25440step0Labels = mixedMoment B raw25440step1 raw25440step1Labels := by
      have ha : raw25440step1 = (fun i j => raw25440step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25440step1 raw25440step0; decide +kernel
      have hl : raw25440step1Labels = raw25440step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25440step0 raw25440step0Labels permutation35 permutation3
    mixedMoment B raw25440step1 raw25440step1Labels = mixedMoment B raw25440step2 raw25440step2Labels := by
      have ha : raw25440step2 = raw25440step1 := by apply Matrix.ext; unfold raw25440step2 raw25440step1; decide +kernel
      have hl : raw25440step1Labels = labelEmbedding6 ∘ raw25440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25440step1 raw25440step1Labels raw25440step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25441 raw25441Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw25441 raw25441Labels = mixedMoment B raw25441step0 raw25441step0Labels := by
      have hz : ∀ j, raw25441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25441step0 = (fun i j => raw25441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25441step0 raw25441; decide +kernel
      have hl : raw25441step0Labels = raw25441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25441 raw25441Labels permutation346 hz
    mixedMoment B raw25441step0 raw25441step0Labels = mixedMoment B raw25441step1 raw25441step1Labels := by
      have ha : raw25441step1 = (fun i j => raw25441step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25441step1 raw25441step0; decide +kernel
      have hl : raw25441step1Labels = raw25441step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25441step0 raw25441step0Labels permutation32 permutation3
    mixedMoment B raw25441step1 raw25441step1Labels = mixedMoment B raw25441step2 raw25441step2Labels := by
      have ha : raw25441step2 = raw25441step1 := by apply Matrix.ext; unfold raw25441step2 raw25441step1; decide +kernel
      have hl : raw25441step1Labels = labelEmbedding6 ∘ raw25441step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25441step1 raw25441step1Labels raw25441step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

theorem canonical25442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25442 raw25442Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25442 raw25442Labels = mixedMoment B raw25442step0 raw25442step0Labels := by
      have hz : ∀ j, raw25442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25442step0 = (fun i j => raw25442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25442step0 raw25442; decide +kernel
      have hl : raw25442step0Labels = raw25442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25442 raw25442Labels permutation346 hz
    mixedMoment B raw25442step0 raw25442step0Labels = mixedMoment B raw25442step1 raw25442step1Labels := by
      have ha : raw25442step1 = (fun i j => raw25442step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25442step1 raw25442step0; decide +kernel
      have hl : raw25442step1Labels = raw25442step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25442step0 raw25442step0Labels permutation32 permutation3
    mixedMoment B raw25442step1 raw25442step1Labels = mixedMoment B raw25442step2 raw25442step2Labels := by
      have ha : raw25442step2 = raw25442step1 := by apply Matrix.ext; unfold raw25442step2 raw25442step1; decide +kernel
      have hl : raw25442step1Labels = labelEmbedding6 ∘ raw25442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25442step1 raw25442step1Labels raw25442step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical25443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25443 raw25443Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw25443 raw25443Labels = mixedMoment B raw25443step0 raw25443step0Labels := by
      have ha : raw25443step0 = (fun i j => raw25443 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25443step0 raw25443; decide +kernel
      have hl : raw25443step0Labels = raw25443Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25443 raw25443Labels permutation176 permutation3
    mixedMoment B raw25443step0 raw25443step0Labels = mixedMoment B raw25443step1 raw25443step1Labels := by
      have ha : raw25443step1 = raw25443step0 := by apply Matrix.ext; unfold raw25443step1 raw25443step0; decide +kernel
      have hl : raw25443step0Labels = labelEmbedding6 ∘ raw25443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25443step0 raw25443step0Labels raw25443step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

theorem canonical25444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25444 raw25444Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25444 raw25444Labels = mixedMoment B raw25444step0 raw25444step0Labels := by
      have hz : ∀ j, raw25444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25444step0 = (fun i j => raw25444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25444step0 raw25444; decide +kernel
      have hl : raw25444step0Labels = raw25444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25444 raw25444Labels permutation346 hz
    mixedMoment B raw25444step0 raw25444step0Labels = mixedMoment B raw25444step1 raw25444step1Labels := by
      have ha : raw25444step1 = (fun i j => raw25444step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25444step1 raw25444step0; decide +kernel
      have hl : raw25444step1Labels = raw25444step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25444step0 raw25444step0Labels permutation33 permutation3
    mixedMoment B raw25444step1 raw25444step1Labels = mixedMoment B raw25444step2 raw25444step2Labels := by
      have ha : raw25444step2 = raw25444step1 := by apply Matrix.ext; unfold raw25444step2 raw25444step1; decide +kernel
      have hl : raw25444step1Labels = labelEmbedding6 ∘ raw25444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25444step1 raw25444step1Labels raw25444step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25445 raw25445Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw25445 raw25445Labels = mixedMoment B raw25445step0 raw25445step0Labels := by
      have hz : ∀ j, raw25445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25445step0 = (fun i j => raw25445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25445step0 raw25445; decide +kernel
      have hl : raw25445step0Labels = raw25445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25445 raw25445Labels permutation346 hz
    mixedMoment B raw25445step0 raw25445step0Labels = mixedMoment B raw25445step1 raw25445step1Labels := by
      have ha : raw25445step1 = (fun i j => raw25445step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25445step1 raw25445step0; decide +kernel
      have hl : raw25445step1Labels = raw25445step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25445step0 raw25445step0Labels permutation32 permutation3
    mixedMoment B raw25445step1 raw25445step1Labels = mixedMoment B raw25445step2 raw25445step2Labels := by
      have ha : raw25445step2 = raw25445step1 := by apply Matrix.ext; unfold raw25445step2 raw25445step1; decide +kernel
      have hl : raw25445step1Labels = labelEmbedding6 ∘ raw25445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25445step1 raw25445step1Labels raw25445step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4099 node4099Labels := by rfl

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

theorem canonical25447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25447 raw25447Labels = mixedMoment B node4286 node4286Labels := by
  calc
    mixedMoment B raw25447 raw25447Labels = mixedMoment B raw25447step0 raw25447step0Labels := by
      have ha : raw25447step0 = (fun i j => raw25447 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25447step0 raw25447; decide +kernel
      have hl : raw25447step0Labels = raw25447Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25447 raw25447Labels permutation176 permutation3
    mixedMoment B raw25447step0 raw25447step0Labels = mixedMoment B raw25447step1 raw25447step1Labels := by
      have ha : raw25447step1 = raw25447step0 := by apply Matrix.ext; unfold raw25447step1 raw25447step0; decide +kernel
      have hl : raw25447step0Labels = labelEmbedding6 ∘ raw25447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25447step0 raw25447step0Labels raw25447step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4286 node4286Labels := by rfl

theorem canonical25448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25448 raw25448Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw25448 raw25448Labels = mixedMoment B raw25448step0 raw25448step0Labels := by
      have hz : ∀ j, raw25448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25448step0 = (fun i j => raw25448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25448step0 raw25448; decide +kernel
      have hl : raw25448step0Labels = raw25448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25448 raw25448Labels permutation346 hz
    mixedMoment B raw25448step0 raw25448step0Labels = mixedMoment B raw25448step1 raw25448step1Labels := by
      have ha : raw25448step1 = (fun i j => raw25448step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25448step1 raw25448step0; decide +kernel
      have hl : raw25448step1Labels = raw25448step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25448step0 raw25448step0Labels permutation44 permutation3
    mixedMoment B raw25448step1 raw25448step1Labels = mixedMoment B raw25448step2 raw25448step2Labels := by
      have ha : raw25448step2 = raw25448step1 := by apply Matrix.ext; unfold raw25448step2 raw25448step1; decide +kernel
      have hl : raw25448step1Labels = labelEmbedding6 ∘ raw25448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25448step1 raw25448step1Labels raw25448step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

theorem canonical25449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25449 raw25449Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw25449 raw25449Labels = mixedMoment B raw25449step0 raw25449step0Labels := by
      have hz : ∀ j, raw25449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25449step0 = (fun i j => raw25449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25449step0 raw25449; decide +kernel
      have hl : raw25449step0Labels = raw25449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25449 raw25449Labels permutation346 hz
    mixedMoment B raw25449step0 raw25449step0Labels = mixedMoment B raw25449step1 raw25449step1Labels := by
      have ha : raw25449step1 = (fun i j => raw25449step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25449step1 raw25449step0; decide +kernel
      have hl : raw25449step1Labels = raw25449step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25449step0 raw25449step0Labels permutation38 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical25450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25450 raw25450Labels = mixedMoment B node552 node552Labels := by
  calc
    mixedMoment B raw25450 raw25450Labels = mixedMoment B raw25450step0 raw25450step0Labels := by
      have hz : ∀ j, raw25450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25450step0 = (fun i j => raw25450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25450step0 raw25450; decide +kernel
      have hl : raw25450step0Labels = raw25450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25450 raw25450Labels permutation346 hz
    mixedMoment B raw25450step0 raw25450step0Labels = mixedMoment B raw25450step1 raw25450step1Labels := by
      have ha : raw25450step1 = (fun i j => raw25450step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25450step1 raw25450step0; decide +kernel
      have hl : raw25450step1Labels = raw25450step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25450step0 raw25450step0Labels permutation40 permutation3
    _ = mixedMoment B node552 node552Labels := by rfl

theorem canonical25451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25451 raw25451Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw25451 raw25451Labels = mixedMoment B raw25451step0 raw25451step0Labels := by
      have ha : raw25451step0 = (fun i j => raw25451 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25451step0 raw25451; decide +kernel
      have hl : raw25451step0Labels = raw25451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25451 raw25451Labels permutation184 permutation3
    _ = mixedMoment B node876 node876Labels := by rfl

theorem canonical25452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25452 raw25452Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw25452 raw25452Labels = mixedMoment B raw25452step0 raw25452step0Labels := by
      have hz : ∀ j, raw25452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25452step0 = (fun i j => raw25452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25452step0 raw25452; decide +kernel
      have hl : raw25452step0Labels = raw25452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25452 raw25452Labels permutation346 hz
    mixedMoment B raw25452step0 raw25452step0Labels = mixedMoment B raw25452step1 raw25452step1Labels := by
      have ha : raw25452step1 = (fun i j => raw25452step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25452step1 raw25452step0; decide +kernel
      have hl : raw25452step1Labels = raw25452step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25452step0 raw25452step0Labels permutation46 permutation3
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical25453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25453 raw25453Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25453 raw25453Labels = mixedMoment B raw25453step0 raw25453step0Labels := by
      have hz : ∀ j, raw25453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25453step0 = (fun i j => raw25453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25453step0 raw25453; decide +kernel
      have hl : raw25453step0Labels = raw25453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25453 raw25453Labels permutation346 hz
    mixedMoment B raw25453step0 raw25453step0Labels = mixedMoment B raw25453step1 raw25453step1Labels := by
      have ha : raw25453step1 = (fun i j => raw25453step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25453step1 raw25453step0; decide +kernel
      have hl : raw25453step1Labels = raw25453step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25453step0 raw25453step0Labels permutation41 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical25454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25454 raw25454Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw25454 raw25454Labels = mixedMoment B raw25454step0 raw25454step0Labels := by
      have ha : raw25454step0 = (fun i j => raw25454 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25454step0 raw25454; decide +kernel
      have hl : raw25454step0Labels = raw25454Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25454 raw25454Labels permutation160 permutation3
    _ = mixedMoment B node535 node535Labels := by rfl

theorem canonical25455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25455 raw25455Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw25455 raw25455Labels = mixedMoment B raw25455step0 raw25455step0Labels := by
      have ha : raw25455step0 = (fun i j => raw25455 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25455step0 raw25455; decide +kernel
      have hl : raw25455step0Labels = raw25455Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25455 raw25455Labels permutation160 permutation3
    _ = mixedMoment B node919 node919Labels := by rfl

theorem canonical25456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25456 raw25456Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw25456 raw25456Labels = mixedMoment B raw25456step0 raw25456step0Labels := by
      have ha : raw25456step0 = (fun i j => raw25456 (permutation226 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25456step0 raw25456; decide +kernel
      have hl : raw25456step0Labels = raw25456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25456 raw25456Labels permutation226 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical25457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25457 raw25457Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw25457 raw25457Labels = mixedMoment B raw25457step0 raw25457step0Labels := by
      have ha : raw25457step0 = (fun i j => raw25457 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25457step0 raw25457; decide +kernel
      have hl : raw25457step0Labels = raw25457Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25457 raw25457Labels permutation160 permutation3
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical25458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25458 raw25458Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw25458 raw25458Labels = mixedMoment B raw25458step0 raw25458step0Labels := by
      have hz : ∀ j, raw25458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25458step0 = (fun i j => raw25458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25458step0 raw25458; decide +kernel
      have hl : raw25458step0Labels = raw25458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25458 raw25458Labels permutation346 hz
    mixedMoment B raw25458step0 raw25458step0Labels = mixedMoment B raw25458step1 raw25458step1Labels := by
      have ha : raw25458step1 = (fun i j => raw25458step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25458step1 raw25458step0; decide +kernel
      have hl : raw25458step1Labels = raw25458step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25458step0 raw25458step0Labels permutation34 permutation3
    _ = mixedMoment B node539 node539Labels := by rfl

theorem canonical25459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25459 raw25459Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw25459 raw25459Labels = mixedMoment B raw25459step0 raw25459step0Labels := by
      have hz : ∀ j, raw25459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25459step0 = (fun i j => raw25459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25459step0 raw25459; decide +kernel
      have hl : raw25459step0Labels = raw25459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25459 raw25459Labels permutation346 hz
    mixedMoment B raw25459step0 raw25459step0Labels = mixedMoment B raw25459step1 raw25459step1Labels := by
      have ha : raw25459step1 = (fun i j => raw25459step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25459step1 raw25459step0; decide +kernel
      have hl : raw25459step1Labels = raw25459step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25459step0 raw25459step0Labels permutation34 permutation3
    _ = mixedMoment B node927 node927Labels := by rfl

theorem canonical25460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25460 raw25460Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw25460 raw25460Labels = mixedMoment B raw25460step0 raw25460step0Labels := by
      have ha : raw25460step0 = (fun i j => raw25460 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25460step0 raw25460; decide +kernel
      have hl : raw25460step0Labels = raw25460Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25460 raw25460Labels permutation178 permutation3
    _ = mixedMoment B node866 node866Labels := by rfl

theorem canonical25461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25461 raw25461Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw25461 raw25461Labels = mixedMoment B raw25461step0 raw25461step0Labels := by
      have hz : ∀ j, raw25461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25461step0 = (fun i j => raw25461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25461step0 raw25461; decide +kernel
      have hl : raw25461step0Labels = raw25461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25461 raw25461Labels permutation346 hz
    mixedMoment B raw25461step0 raw25461step0Labels = mixedMoment B raw25461step1 raw25461step1Labels := by
      have ha : raw25461step1 = (fun i j => raw25461step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25461step1 raw25461step0; decide +kernel
      have hl : raw25461step1Labels = raw25461step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25461step0 raw25461step0Labels permutation44 permutation3
    _ = mixedMoment B node985 node985Labels := by rfl

theorem canonical25462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25462 raw25462Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25462 raw25462Labels = mixedMoment B raw25462step0 raw25462step0Labels := by
      have hz : ∀ j, raw25462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25462step0 = (fun i j => raw25462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25462step0 raw25462; decide +kernel
      have hl : raw25462step0Labels = raw25462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25462 raw25462Labels permutation346 hz
    mixedMoment B raw25462step0 raw25462step0Labels = mixedMoment B raw25462step1 raw25462step1Labels := by
      have ha : raw25462step1 = (fun i j => raw25462step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25462step1 raw25462step0; decide +kernel
      have hl : raw25462step1Labels = raw25462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25462step0 raw25462step0Labels permutation35 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical25463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25463 raw25463Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw25463 raw25463Labels = mixedMoment B raw25463step0 raw25463step0Labels := by
      have hz : ∀ j, raw25463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25463step0 = (fun i j => raw25463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25463step0 raw25463; decide +kernel
      have hl : raw25463step0Labels = raw25463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25463 raw25463Labels permutation346 hz
    mixedMoment B raw25463step0 raw25463step0Labels = mixedMoment B raw25463step1 raw25463step1Labels := by
      have ha : raw25463step1 = (fun i j => raw25463step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25463step1 raw25463step0; decide +kernel
      have hl : raw25463step1Labels = raw25463step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25463step0 raw25463step0Labels permutation32 permutation3
    _ = mixedMoment B node539 node539Labels := by rfl

theorem canonical25464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25464 raw25464Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw25464 raw25464Labels = mixedMoment B raw25464step0 raw25464step0Labels := by
      have hz : ∀ j, raw25464 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25464step0 = (fun i j => raw25464 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25464step0 raw25464; decide +kernel
      have hl : raw25464step0Labels = raw25464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25464 raw25464Labels permutation346 hz
    mixedMoment B raw25464step0 raw25464step0Labels = mixedMoment B raw25464step1 raw25464step1Labels := by
      have ha : raw25464step1 = (fun i j => raw25464step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25464step1 raw25464step0; decide +kernel
      have hl : raw25464step1Labels = raw25464step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25464step0 raw25464step0Labels permutation32 permutation3
    _ = mixedMoment B node927 node927Labels := by rfl

theorem canonical25465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25465 raw25465Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw25465 raw25465Labels = mixedMoment B raw25465step0 raw25465step0Labels := by
      have ha : raw25465step0 = (fun i j => raw25465 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25465step0 raw25465; decide +kernel
      have hl : raw25465step0Labels = raw25465Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25465 raw25465Labels permutation176 permutation3
    _ = mixedMoment B node866 node866Labels := by rfl

theorem canonical25466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25466 raw25466Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25466 raw25466Labels = mixedMoment B raw25466step0 raw25466step0Labels := by
      have hz : ∀ j, raw25466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25466step0 = (fun i j => raw25466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25466step0 raw25466; decide +kernel
      have hl : raw25466step0Labels = raw25466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25466 raw25466Labels permutation346 hz
    mixedMoment B raw25466step0 raw25466step0Labels = mixedMoment B raw25466step1 raw25466step1Labels := by
      have ha : raw25466step1 = (fun i j => raw25466step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25466step1 raw25466step0; decide +kernel
      have hl : raw25466step1Labels = raw25466step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25466step0 raw25466step0Labels permutation33 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical25467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25467 raw25467Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw25467 raw25467Labels = mixedMoment B raw25467step0 raw25467step0Labels := by
      have hz : ∀ j, raw25467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25467step0 = (fun i j => raw25467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25467step0 raw25467; decide +kernel
      have hl : raw25467step0Labels = raw25467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25467 raw25467Labels permutation346 hz
    mixedMoment B raw25467step0 raw25467step0Labels = mixedMoment B raw25467step1 raw25467step1Labels := by
      have ha : raw25467step1 = (fun i j => raw25467step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25467step1 raw25467step0; decide +kernel
      have hl : raw25467step1Labels = raw25467step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25467step0 raw25467step0Labels permutation32 permutation3
    _ = mixedMoment B node536 node536Labels := by rfl

theorem canonical25468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25468 raw25468Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw25468 raw25468Labels = mixedMoment B raw25468step0 raw25468step0Labels := by
      have hz : ∀ j, raw25468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25468step0 = (fun i j => raw25468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25468step0 raw25468; decide +kernel
      have hl : raw25468step0Labels = raw25468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25468 raw25468Labels permutation346 hz
    mixedMoment B raw25468step0 raw25468step0Labels = mixedMoment B raw25468step1 raw25468step1Labels := by
      have ha : raw25468step1 = (fun i j => raw25468step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25468step1 raw25468step0; decide +kernel
      have hl : raw25468step1Labels = raw25468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25468step0 raw25468step0Labels permutation32 permutation3
    _ = mixedMoment B node921 node921Labels := by rfl

theorem canonical25469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25469 raw25469Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw25469 raw25469Labels = mixedMoment B raw25469step0 raw25469step0Labels := by
      have ha : raw25469step0 = (fun i j => raw25469 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25469step0 raw25469; decide +kernel
      have hl : raw25469step0Labels = raw25469Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25469 raw25469Labels permutation176 permutation3
    _ = mixedMoment B node864 node864Labels := by rfl

theorem canonical25470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25470 raw25470Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw25470 raw25470Labels = mixedMoment B raw25470step0 raw25470step0Labels := by
      have hz : ∀ j, raw25470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25470step0 = (fun i j => raw25470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25470step0 raw25470; decide +kernel
      have hl : raw25470step0Labels = raw25470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25470 raw25470Labels permutation346 hz
    mixedMoment B raw25470step0 raw25470step0Labels = mixedMoment B raw25470step1 raw25470step1Labels := by
      have ha : raw25470step1 = (fun i j => raw25470step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25470step1 raw25470step0; decide +kernel
      have hl : raw25470step1Labels = raw25470step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25470step0 raw25470step0Labels permutation44 permutation3
    _ = mixedMoment B node979 node979Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25501 raw25501Labels = mixedMoment B node2099 node2099Labels := by
  calc
    mixedMoment B raw25501 raw25501Labels = mixedMoment B raw25501step0 raw25501step0Labels := by
      have hz : ∀ j, raw25501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25501step0 = (fun i j => raw25501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25501step0 raw25501; decide +kernel
      have hl : raw25501step0Labels = raw25501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25501 raw25501Labels permutation346 hz
    mixedMoment B raw25501step0 raw25501step0Labels = mixedMoment B raw25501step1 raw25501step1Labels := by
      have ha : raw25501step1 = (fun i j => raw25501step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25501step1 raw25501step0; decide +kernel
      have hl : raw25501step1Labels = raw25501step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25501step0 raw25501step0Labels permutation34 permutation2
    _ = mixedMoment B node2099 node2099Labels := by rfl

theorem canonical25502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25502 raw25502Labels = mixedMoment B node2015 node2015Labels := by
  calc
    mixedMoment B raw25502 raw25502Labels = mixedMoment B raw25502step0 raw25502step0Labels := by
      have ha : raw25502step0 = (fun i j => raw25502 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25502step0 raw25502; decide +kernel
      have hl : raw25502step0Labels = raw25502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25502 raw25502Labels permutation178 permutation2
    _ = mixedMoment B node2015 node2015Labels := by rfl

theorem canonical25503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25503 raw25503Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw25503 raw25503Labels = mixedMoment B raw25503step0 raw25503step0Labels := by
      have hz : ∀ j, raw25503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25503step0 = (fun i j => raw25503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25503step0 raw25503; decide +kernel
      have hl : raw25503step0Labels = raw25503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25503 raw25503Labels permutation346 hz
    mixedMoment B raw25503step0 raw25503step0Labels = mixedMoment B raw25503step1 raw25503step1Labels := by
      have ha : raw25503step1 = (fun i j => raw25503step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25503step1 raw25503step0; decide +kernel
      have hl : raw25503step1Labels = raw25503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25503step0 raw25503step0Labels permutation44 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical25504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25504 raw25504Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw25504 raw25504Labels = mixedMoment B raw25504step0 raw25504step0Labels := by
      have hz : ∀ j, raw25504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25504step0 = (fun i j => raw25504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25504step0 raw25504; decide +kernel
      have hl : raw25504step0Labels = raw25504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25504 raw25504Labels permutation346 hz
    mixedMoment B raw25504step0 raw25504step0Labels = mixedMoment B raw25504step1 raw25504step1Labels := by
      have ha : raw25504step1 = (fun i j => raw25504step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25504step1 raw25504step0; decide +kernel
      have hl : raw25504step1Labels = raw25504step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25504step0 raw25504step0Labels permutation34 permutation2
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical25505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25505 raw25505Labels = mixedMoment B node981 node981Labels := by
  calc
    mixedMoment B raw25505 raw25505Labels = mixedMoment B raw25505step0 raw25505step0Labels := by
      have ha : raw25505step0 = (fun i j => raw25505 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25505step0 raw25505; decide +kernel
      have hl : raw25505step0Labels = raw25505Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25505 raw25505Labels permutation178 permutation2
    _ = mixedMoment B node981 node981Labels := by rfl

theorem canonical25506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25506 raw25506Labels = mixedMoment B node2078 node2078Labels := by
  calc
    mixedMoment B raw25506 raw25506Labels = mixedMoment B raw25506step0 raw25506step0Labels := by
      have ha : raw25506step0 = (fun i j => raw25506 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25506step0 raw25506; decide +kernel
      have hl : raw25506step0Labels = raw25506Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25506 raw25506Labels permutation154 permutation2
    _ = mixedMoment B node2078 node2078Labels := by rfl

theorem canonical25507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25507 raw25507Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw25507 raw25507Labels = mixedMoment B raw25507step0 raw25507step0Labels := by
      have ha : raw25507step0 = (fun i j => raw25507 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25507step0 raw25507; decide +kernel
      have hl : raw25507step0Labels = raw25507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25507 raw25507Labels permutation178 permutation2
    _ = mixedMoment B node1913 node1913Labels := by rfl

theorem canonical25508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25508 raw25508Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw25508 raw25508Labels = mixedMoment B raw25508step0 raw25508step0Labels := by
      have ha : raw25508step0 = (fun i j => raw25508 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25508step0 raw25508; decide +kernel
      have hl : raw25508step0Labels = raw25508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25508 raw25508Labels permutation176 permutation2
    _ = mixedMoment B node2196 node2196Labels := by rfl

theorem canonical25509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25509 raw25509Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw25509 raw25509Labels = mixedMoment B raw25509step0 raw25509step0Labels := by
      have ha : raw25509step0 = (fun i j => raw25509 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25509step0 raw25509; decide +kernel
      have hl : raw25509step0Labels = raw25509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25509 raw25509Labels permutation178 permutation2
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical25510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25510 raw25510Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25510 raw25510Labels = mixedMoment B raw25510step0 raw25510step0Labels := by
      have ha : raw25510step0 = (fun i j => raw25510 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25510step0 raw25510; decide +kernel
      have hl : raw25510step0Labels = raw25510Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25510 raw25510Labels permutation181 permutation2
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical25511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25511 raw25511Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25511 raw25511Labels = mixedMoment B raw25511step0 raw25511step0Labels := by
      have hz : ∀ j, raw25511 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw25511step0 = (fun i j => raw25511 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw25511step0 raw25511; decide +kernel
      have hl : raw25511step0Labels = raw25511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25511 raw25511Labels permutation590 hz
    mixedMoment B raw25511step0 raw25511step0Labels = mixedMoment B raw25511step1 raw25511step1Labels := by
      have ha : raw25511step1 = (fun i j => raw25511step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25511step1 raw25511step0; decide +kernel
      have hl : raw25511step1Labels = raw25511step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25511step0 raw25511step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical25512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25512 raw25512Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw25512 raw25512Labels = mixedMoment B raw25512step0 raw25512step0Labels := by
      have ha : raw25512step0 = (fun i j => raw25512 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25512step0 raw25512; decide +kernel
      have hl : raw25512step0Labels = raw25512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25512 raw25512Labels permutation195 permutation2
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical25513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25513 raw25513Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw25513 raw25513Labels = mixedMoment B raw25513step0 raw25513step0Labels := by
      have ha : raw25513step0 = (fun i j => raw25513 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25513step0 raw25513; decide +kernel
      have hl : raw25513step0Labels = raw25513Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25513 raw25513Labels permutation157 permutation2
    _ = mixedMoment B node1032 node1032Labels := by rfl

theorem canonical25514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25514 raw25514Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw25514 raw25514Labels = mixedMoment B raw25514step0 raw25514step0Labels := by
      have ha : raw25514step0 = (fun i j => raw25514 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25514step0 raw25514; decide +kernel
      have hl : raw25514step0Labels = raw25514Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25514 raw25514Labels permutation181 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical25515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25515 raw25515Labels = mixedMoment B node978 node978Labels := by
  calc
    mixedMoment B raw25515 raw25515Labels = mixedMoment B raw25515step0 raw25515step0Labels := by
      have ha : raw25515step0 = (fun i j => raw25515 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25515step0 raw25515; decide +kernel
      have hl : raw25515step0Labels = raw25515Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25515 raw25515Labels permutation180 permutation2
    _ = mixedMoment B node978 node978Labels := by rfl

theorem canonical25516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25516 raw25516Labels = mixedMoment B node978 node978Labels := by
  calc
    mixedMoment B raw25516 raw25516Labels = mixedMoment B raw25516step0 raw25516step0Labels := by
      have ha : raw25516step0 = (fun i j => raw25516 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25516step0 raw25516; decide +kernel
      have hl : raw25516step0Labels = raw25516Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25516 raw25516Labels permutation178 permutation2
    _ = mixedMoment B node978 node978Labels := by rfl

theorem canonical25517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25517 raw25517Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw25517 raw25517Labels = mixedMoment B raw25517step0 raw25517step0Labels := by
      have ha : raw25517step0 = (fun i j => raw25517 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25517step0 raw25517; decide +kernel
      have hl : raw25517step0Labels = raw25517Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25517 raw25517Labels permutation154 permutation2
    _ = mixedMoment B node2076 node2076Labels := by rfl

theorem canonical25518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25518 raw25518Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw25518 raw25518Labels = mixedMoment B raw25518step0 raw25518step0Labels := by
      have ha : raw25518step0 = (fun i j => raw25518 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25518step0 raw25518; decide +kernel
      have hl : raw25518step0Labels = raw25518Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25518 raw25518Labels permutation178 permutation2
    _ = mixedMoment B node1909 node1909Labels := by rfl

theorem canonical25519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25519 raw25519Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw25519 raw25519Labels = mixedMoment B raw25519step0 raw25519step0Labels := by
      have ha : raw25519step0 = (fun i j => raw25519 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25519step0 raw25519; decide +kernel
      have hl : raw25519step0Labels = raw25519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25519 raw25519Labels permutation176 permutation2
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical25520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25520 raw25520Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw25520 raw25520Labels = mixedMoment B raw25520step0 raw25520step0Labels := by
      have hz : ∀ j, raw25520 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25520step0 = (fun i j => raw25520 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25520step0 raw25520; decide +kernel
      have hl : raw25520step0Labels = raw25520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25520 raw25520Labels permutation520 hz
    mixedMoment B raw25520step0 raw25520step0Labels = mixedMoment B raw25520step1 raw25520step1Labels := by
      have ha : raw25520step1 = (fun i j => raw25520step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25520step1 raw25520step0; decide +kernel
      have hl : raw25520step1Labels = raw25520step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25520step0 raw25520step0Labels permutation38 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical25521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25521 raw25521Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25521 raw25521Labels = mixedMoment B raw25521step0 raw25521step0Labels := by
      have ha : raw25521step0 = (fun i j => raw25521 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25521step0 raw25521; decide +kernel
      have hl : raw25521step0Labels = raw25521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25521 raw25521Labels permutation179 permutation2
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical25522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25522 raw25522Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25522 raw25522Labels = mixedMoment B raw25522step0 raw25522step0Labels := by
      have hz : ∀ j, raw25522 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25522step0 = (fun i j => raw25522 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25522step0 raw25522; decide +kernel
      have hl : raw25522step0Labels = raw25522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25522 raw25522Labels permutation520 hz
    mixedMoment B raw25522step0 raw25522step0Labels = mixedMoment B raw25522step1 raw25522step1Labels := by
      have ha : raw25522step1 = (fun i j => raw25522step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25522step1 raw25522step0; decide +kernel
      have hl : raw25522step1Labels = raw25522step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25522step0 raw25522step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical25523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25523 raw25523Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25523 raw25523Labels = mixedMoment B raw25523step0 raw25523step0Labels := by
      have ha : raw25523step0 = (fun i j => raw25523 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25523step0 raw25523; decide +kernel
      have hl : raw25523step0Labels = raw25523Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25523 raw25523Labels permutation176 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical25524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25524 raw25524Labels = mixedMoment B node2077 node2077Labels := by
  calc
    _ = mixedMoment B node2077 node2077Labels := by rfl

theorem canonical25525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25525 raw25525Labels = mixedMoment B node1912 node1912Labels := by
  calc
    mixedMoment B raw25525 raw25525Labels = mixedMoment B raw25525step0 raw25525step0Labels := by
      have ha : raw25525step0 = (fun i j => raw25525 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25525step0 raw25525; decide +kernel
      have hl : raw25525step0Labels = raw25525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25525 raw25525Labels permutation176 permutation2
    _ = mixedMoment B node1912 node1912Labels := by rfl

theorem canonical25526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25526 raw25526Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw25526 raw25526Labels = mixedMoment B raw25526step0 raw25526step0Labels := by
      have ha : raw25526step0 = (fun i j => raw25526 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25526step0 raw25526; decide +kernel
      have hl : raw25526step0Labels = raw25526Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25526 raw25526Labels permutation176 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical25527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25527 raw25527Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw25527 raw25527Labels = mixedMoment B raw25527step0 raw25527step0Labels := by
      have ha : raw25527step0 = (fun i j => raw25527 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25527step0 raw25527; decide +kernel
      have hl : raw25527step0Labels = raw25527Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25527 raw25527Labels permutation178 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical25528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25528 raw25528Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw25528 raw25528Labels = mixedMoment B raw25528step0 raw25528step0Labels := by
      have ha : raw25528step0 = (fun i j => raw25528 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25528step0 raw25528; decide +kernel
      have hl : raw25528step0Labels = raw25528Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25528 raw25528Labels permutation176 permutation2
    _ = mixedMoment B node2204 node2204Labels := by rfl

theorem canonical25529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25529 raw25529Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw25529 raw25529Labels = mixedMoment B raw25529step0 raw25529step0Labels := by
      have ha : raw25529step0 = (fun i j => raw25529 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25529step0 raw25529; decide +kernel
      have hl : raw25529step0Labels = raw25529Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25529 raw25529Labels permutation176 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical25534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25534 raw25534Labels = mixedMoment B node1003 node1003Labels := by
  calc
    mixedMoment B raw25534 raw25534Labels = mixedMoment B raw25534step0 raw25534step0Labels := by
      have ha : raw25534step0 = (fun i j => raw25534 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25534step0 raw25534; decide +kernel
      have hl : raw25534step0Labels = raw25534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25534 raw25534Labels permutation176 permutation2
    _ = mixedMoment B node1003 node1003Labels := by rfl

theorem canonical25538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25538 raw25538Labels = mixedMoment B node1034 node1034Labels := by
  calc
    _ = mixedMoment B node1034 node1034Labels := by rfl

theorem canonical25539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25539 raw25539Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25539 raw25539Labels = mixedMoment B raw25539step0 raw25539step0Labels := by
      have ha : raw25539step0 = (fun i j => raw25539 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25539step0 raw25539; decide +kernel
      have hl : raw25539step0Labels = raw25539Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25539 raw25539Labels permutation179 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical25540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25540 raw25540Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25540 raw25540Labels = mixedMoment B raw25540step0 raw25540step0Labels := by
      have ha : raw25540step0 = (fun i j => raw25540 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25540step0 raw25540; decide +kernel
      have hl : raw25540step0Labels = raw25540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25540 raw25540Labels permutation177 permutation2
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical25546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25546 raw25546Labels = mixedMoment B node712 node712Labels := by
  calc
    mixedMoment B raw25546 raw25546Labels = mixedMoment B raw25546step0 raw25546step0Labels := by
      have ha : raw25546step0 = (fun i j => raw25546 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25546step0 raw25546; decide +kernel
      have hl : raw25546step0Labels = raw25546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25546 raw25546Labels permutation176 permutation4
    mixedMoment B raw25546step0 raw25546step0Labels = mixedMoment B raw25546step1 raw25546step1Labels := by
      have ha : raw25546step1 = -raw25546step0 := by apply Matrix.ext; change ∀ i j, raw25546step1 i j = -(raw25546step0 i j); unfold raw25546step1 raw25546step0; decide +kernel
      have hl : raw25546step1Labels = raw25546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node712 node712Labels := by rfl

theorem canonical25548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25548 raw25548Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw25548 raw25548Labels = mixedMoment B raw25548step0 raw25548step0Labels := by
      have ha : raw25548step0 = (fun i j => raw25548 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25548step0 raw25548; decide +kernel
      have hl : raw25548step0Labels = raw25548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25548 raw25548Labels permutation188 permutation4
    mixedMoment B raw25548step0 raw25548step0Labels = mixedMoment B raw25548step1 raw25548step1Labels := by
      have ha : raw25548step1 = -raw25548step0 := by apply Matrix.ext; change ∀ i j, raw25548step1 i j = -(raw25548step0 i j); unfold raw25548step1 raw25548step0; decide +kernel
      have hl : raw25548step1Labels = raw25548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

theorem canonical25549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25549 raw25549Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw25549 raw25549Labels = mixedMoment B raw25549step0 raw25549step0Labels := by
      have ha : raw25549step0 = (fun i j => raw25549 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25549step0 raw25549; decide +kernel
      have hl : raw25549step0Labels = raw25549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25549 raw25549Labels permutation178 permutation2
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical25550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25550 raw25550Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw25550 raw25550Labels = mixedMoment B raw25550step0 raw25550step0Labels := by
      have ha : raw25550step0 = (fun i j => raw25550 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25550step0 raw25550; decide +kernel
      have hl : raw25550step0Labels = raw25550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25550 raw25550Labels permutation154 permutation2
    _ = mixedMoment B node2075 node2075Labels := by rfl

theorem canonical25551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25551 raw25551Labels = mixedMoment B node1908 node1908Labels := by
  calc
    mixedMoment B raw25551 raw25551Labels = mixedMoment B raw25551step0 raw25551step0Labels := by
      have ha : raw25551step0 = (fun i j => raw25551 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25551step0 raw25551; decide +kernel
      have hl : raw25551step0Labels = raw25551Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25551 raw25551Labels permutation178 permutation2
    _ = mixedMoment B node1908 node1908Labels := by rfl

theorem canonical25552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25552 raw25552Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw25552 raw25552Labels = mixedMoment B raw25552step0 raw25552step0Labels := by
      have ha : raw25552step0 = (fun i j => raw25552 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25552step0 raw25552; decide +kernel
      have hl : raw25552step0Labels = raw25552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25552 raw25552Labels permutation176 permutation2
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical25553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25553 raw25553Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw25553 raw25553Labels = mixedMoment B raw25553step0 raw25553step0Labels := by
      have hz : ∀ j, raw25553 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25553step0 = (fun i j => raw25553 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25553step0 raw25553; decide +kernel
      have hl : raw25553step0Labels = raw25553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25553 raw25553Labels permutation520 hz
    mixedMoment B raw25553step0 raw25553step0Labels = mixedMoment B raw25553step1 raw25553step1Labels := by
      have ha : raw25553step1 = (fun i j => raw25553step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25553step1 raw25553step0; decide +kernel
      have hl : raw25553step1Labels = raw25553step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25553step0 raw25553step0Labels permutation38 permutation2
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical25554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25554 raw25554Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25554 raw25554Labels = mixedMoment B raw25554step0 raw25554step0Labels := by
      have ha : raw25554step0 = (fun i j => raw25554 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25554step0 raw25554; decide +kernel
      have hl : raw25554step0Labels = raw25554Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25554 raw25554Labels permutation178 permutation2
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical25555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25555 raw25555Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25555 raw25555Labels = mixedMoment B raw25555step0 raw25555step0Labels := by
      have hz : ∀ j, raw25555 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25555step0 = (fun i j => raw25555 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25555step0 raw25555; decide +kernel
      have hl : raw25555step0Labels = raw25555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25555 raw25555Labels permutation520 hz
    mixedMoment B raw25555step0 raw25555step0Labels = mixedMoment B raw25555step1 raw25555step1Labels := by
      have ha : raw25555step1 = (fun i j => raw25555step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25555step1 raw25555step0; decide +kernel
      have hl : raw25555step1Labels = raw25555step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25555step0 raw25555step0Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical25557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25557 raw25557Labels = mixedMoment B node878 node878Labels := by
  calc
    mixedMoment B raw25557 raw25557Labels = mixedMoment B raw25557step0 raw25557step0Labels := by
      have ha : raw25557step0 = (fun i j => raw25557 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25557step0 raw25557; decide +kernel
      have hl : raw25557step0Labels = raw25557Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25557 raw25557Labels permutation188 permutation2
    _ = mixedMoment B node878 node878Labels := by rfl

theorem canonical25561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25561 raw25561Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw25561 raw25561Labels = mixedMoment B raw25561step0 raw25561step0Labels := by
      have ha : raw25561step0 = (fun i j => raw25561 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25561step0 raw25561; decide +kernel
      have hl : raw25561step0Labels = raw25561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25561 raw25561Labels permutation178 permutation2
    _ = mixedMoment B node866 node866Labels := by rfl

theorem canonical25562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25562 raw25562Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw25562 raw25562Labels = mixedMoment B raw25562step0 raw25562step0Labels := by
      have ha : raw25562step0 = (fun i j => raw25562 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25562step0 raw25562; decide +kernel
      have hl : raw25562step0Labels = raw25562Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25562 raw25562Labels permutation176 permutation2
    _ = mixedMoment B node869 node869Labels := by rfl

theorem canonical25563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25563 raw25563Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw25563 raw25563Labels = mixedMoment B raw25563step0 raw25563step0Labels := by
      have ha : raw25563step0 = (fun i j => raw25563 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25563step0 raw25563; decide +kernel
      have hl : raw25563step0Labels = raw25563Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25563 raw25563Labels permutation178 permutation2
    _ = mixedMoment B node865 node865Labels := by rfl

theorem canonical25564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25564 raw25564Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw25564 raw25564Labels = mixedMoment B raw25564step0 raw25564step0Labels := by
      have ha : raw25564step0 = (fun i j => raw25564 (permutation190 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25564step0 raw25564; decide +kernel
      have hl : raw25564step0Labels = raw25564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25564 raw25564Labels permutation190 permutation4
    mixedMoment B raw25564step0 raw25564step0Labels = mixedMoment B raw25564step1 raw25564step1Labels := by
      have ha : raw25564step1 = -raw25564step0 := by apply Matrix.ext; change ∀ i j, raw25564step1 i j = -(raw25564step0 i j); unfold raw25564step1 raw25564step0; decide +kernel
      have hl : raw25564step1Labels = raw25564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node703 node703Labels := by rfl

theorem canonical25565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25565 raw25565Labels = mixedMoment B node700 node700Labels := by
  calc
    mixedMoment B raw25565 raw25565Labels = mixedMoment B raw25565step0 raw25565step0Labels := by
      have ha : raw25565step0 = (fun i j => raw25565 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25565step0 raw25565; decide +kernel
      have hl : raw25565step0Labels = raw25565Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25565 raw25565Labels permutation188 permutation4
    mixedMoment B raw25565step0 raw25565step0Labels = mixedMoment B raw25565step1 raw25565step1Labels := by
      have ha : raw25565step1 = -raw25565step0 := by apply Matrix.ext; change ∀ i j, raw25565step1 i j = -(raw25565step0 i j); unfold raw25565step1 raw25565step0; decide +kernel
      have hl : raw25565step1Labels = raw25565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node700 node700Labels := by rfl

theorem canonical25566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25566 raw25566Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw25566 raw25566Labels = mixedMoment B raw25566step0 raw25566step0Labels := by
      have ha : raw25566step0 = (fun i j => raw25566 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25566step0 raw25566; decide +kernel
      have hl : raw25566step0Labels = raw25566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25566 raw25566Labels permutation188 permutation4
    mixedMoment B raw25566step0 raw25566step0Labels = mixedMoment B raw25566step1 raw25566step1Labels := by
      have ha : raw25566step1 = -raw25566step0 := by apply Matrix.ext; change ∀ i j, raw25566step1 i j = -(raw25566step0 i j); unfold raw25566step1 raw25566step0; decide +kernel
      have hl : raw25566step1Labels = raw25566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node699 node699Labels := by rfl

theorem canonical25567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25567 raw25567Labels = mixedMoment B node976 node976Labels := by
  calc
    mixedMoment B raw25567 raw25567Labels = mixedMoment B raw25567step0 raw25567step0Labels := by
      have ha : raw25567step0 = (fun i j => raw25567 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25567step0 raw25567; decide +kernel
      have hl : raw25567step0Labels = raw25567Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25567 raw25567Labels permutation176 permutation2
    _ = mixedMoment B node976 node976Labels := by rfl

theorem canonical25568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25568 raw25568Labels = mixedMoment B node2074 node2074Labels := by
  calc
    _ = mixedMoment B node2074 node2074Labels := by rfl

theorem canonical25569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25569 raw25569Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw25569 raw25569Labels = mixedMoment B raw25569step0 raw25569step0Labels := by
      have ha : raw25569step0 = (fun i j => raw25569 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25569step0 raw25569; decide +kernel
      have hl : raw25569step0Labels = raw25569Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25569 raw25569Labels permutation176 permutation2
    _ = mixedMoment B node1907 node1907Labels := by rfl

theorem canonical25570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25570 raw25570Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw25570 raw25570Labels = mixedMoment B raw25570step0 raw25570step0Labels := by
      have hz : ∀ j, raw25570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25570step0 = (fun i j => raw25570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25570step0 raw25570; decide +kernel
      have hl : raw25570step0Labels = raw25570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25570 raw25570Labels permutation434 hz
    mixedMoment B raw25570step0 raw25570step0Labels = mixedMoment B raw25570step1 raw25570step1Labels := by
      have ha : raw25570step1 = (fun i j => raw25570step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25570step1 raw25570step0; decide +kernel
      have hl : raw25570step1Labels = raw25570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25570step0 raw25570step0Labels permutation38 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical25571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25571 raw25571Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw25571 raw25571Labels = mixedMoment B raw25571step0 raw25571step0Labels := by
      have hz : ∀ j, raw25571 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25571step0 = (fun i j => raw25571 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25571step0 raw25571; decide +kernel
      have hl : raw25571step0Labels = raw25571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25571 raw25571Labels permutation520 hz
    mixedMoment B raw25571step0 raw25571step0Labels = mixedMoment B raw25571step1 raw25571step1Labels := by
      have ha : raw25571step1 = (fun i j => raw25571step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25571step1 raw25571step0; decide +kernel
      have hl : raw25571step1Labels = raw25571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25571step0 raw25571step0Labels permutation38 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical25572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25572 raw25572Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw25572 raw25572Labels = mixedMoment B raw25572step0 raw25572step0Labels := by
      have ha : raw25572step0 = (fun i j => raw25572 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25572step0 raw25572; decide +kernel
      have hl : raw25572step0Labels = raw25572Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25572 raw25572Labels permutation176 permutation2
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical25573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25573 raw25573Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw25573 raw25573Labels = mixedMoment B raw25573step0 raw25573step0Labels := by
      have hz : ∀ j, raw25573 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25573step0 = (fun i j => raw25573 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25573step0 raw25573; decide +kernel
      have hl : raw25573step0Labels = raw25573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25573 raw25573Labels permutation520 hz
    mixedMoment B raw25573step0 raw25573step0Labels = mixedMoment B raw25573step1 raw25573step1Labels := by
      have hz : ∀ j, raw25573step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw25573step1 = (fun i j => raw25573step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw25573step1 raw25573step0; decide +kernel
      have hl : raw25573step1Labels = raw25573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25573step0 raw25573step0Labels permutation104 hz
    mixedMoment B raw25573step1 raw25573step1Labels = mixedMoment B raw25573step2 raw25573step2Labels := by
      have ha : raw25573step2 = (fun i j => raw25573step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25573step2 raw25573step1; decide +kernel
      have hl : raw25573step2Labels = raw25573step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25573step1 raw25573step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

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

theorem canonical666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw666 raw666Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw666 raw666Labels = mixedMoment B raw666step0 raw666step0Labels := by
      have ha : raw666step0 = (fun i j => raw666 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw666step0 raw666; decide +kernel
      have hl : raw666step0Labels = raw666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw666 raw666Labels permutation152 permutation4
    mixedMoment B raw666step0 raw666step0Labels = mixedMoment B raw666step1 raw666step1Labels := by
      have ha : raw666step1 = raw666step0 := by apply Matrix.ext; unfold raw666step1 raw666step0; decide +kernel
      have hl : raw666step0Labels = labelEmbedding7 ∘ raw666step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw666step0 raw666step0Labels raw666step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

theorem canonical667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw667 raw667Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw667 raw667Labels = mixedMoment B raw667step0 raw667step0Labels := by
      have ha : raw667step0 = (fun i j => raw667 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw667step0 raw667; decide +kernel
      have hl : raw667step0Labels = raw667Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw667 raw667Labels permutation152 permutation4
    _ = mixedMoment B node535 node535Labels := by rfl

theorem canonical668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw668 raw668Labels = mixedMoment B node656 node656Labels := by
  calc
    mixedMoment B raw668 raw668Labels = mixedMoment B raw668step0 raw668step0Labels := by
      have ha : raw668step0 = (fun i j => raw668 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw668step0 raw668; decide +kernel
      have hl : raw668step0Labels = raw668Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw668 raw668Labels permutation182 permutation6
    mixedMoment B raw668step0 raw668step0Labels = mixedMoment B raw668step1 raw668step1Labels := by
      have ha : raw668step1 = -raw668step0 := by apply Matrix.ext; change ∀ i j, raw668step1 i j = -(raw668step0 i j); unfold raw668step1 raw668step0; decide +kernel
      have hl : raw668step1Labels = raw668step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw668step1 raw668step1Labels = mixedMoment B raw668step2 raw668step2Labels := by
      have ha : raw668step2 = raw668step1 := by apply Matrix.ext; unfold raw668step2 raw668step1; decide +kernel
      have hl : raw668step1Labels = labelEmbedding1 ∘ raw668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw668step1 raw668step1Labels raw668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node656 node656Labels := by rfl

theorem canonical669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw669 raw669Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw669 raw669Labels = mixedMoment B raw669step0 raw669step0Labels := by
      have ha : raw669step0 = (fun i j => raw669 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw669step0 raw669; decide +kernel
      have hl : raw669step0Labels = raw669Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw669 raw669Labels permutation32 permutation4
    mixedMoment B raw669step0 raw669step0Labels = mixedMoment B raw669step1 raw669step1Labels := by
      have ha : raw669step1 = raw669step0 := by apply Matrix.ext; unfold raw669step1 raw669step0; decide +kernel
      have hl : raw669step0Labels = labelEmbedding7 ∘ raw669step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw669step0 raw669step0Labels raw669step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4099 node4099Labels := by rfl

theorem canonical670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw670 raw670Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw670 raw670Labels = mixedMoment B raw670step0 raw670step0Labels := by
      have ha : raw670step0 = (fun i j => raw670 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw670step0 raw670; decide +kernel
      have hl : raw670step0Labels = raw670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw670 raw670Labels permutation32 permutation4
    _ = mixedMoment B node536 node536Labels := by rfl

theorem canonical671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw671 raw671Labels = mixedMoment B node657 node657Labels := by
  calc
    mixedMoment B raw671 raw671Labels = mixedMoment B raw671step0 raw671step0Labels := by
      have ha : raw671step0 = (fun i j => raw671 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw671step0 raw671; decide +kernel
      have hl : raw671step0Labels = raw671Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw671 raw671Labels permutation40 permutation6
    mixedMoment B raw671step0 raw671step0Labels = mixedMoment B raw671step1 raw671step1Labels := by
      have ha : raw671step1 = -raw671step0 := by apply Matrix.ext; change ∀ i j, raw671step1 i j = -(raw671step0 i j); unfold raw671step1 raw671step0; decide +kernel
      have hl : raw671step1Labels = raw671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw671step1 raw671step1Labels = mixedMoment B raw671step2 raw671step2Labels := by
      have ha : raw671step2 = raw671step1 := by apply Matrix.ext; unfold raw671step2 raw671step1; decide +kernel
      have hl : raw671step1Labels = labelEmbedding1 ∘ raw671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw671step1 raw671step1Labels raw671step2Labels labelEmbedding1 hl
    _ = mixedMoment B node657 node657Labels := by rfl

theorem canonical678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw678 raw678Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw678 raw678Labels = mixedMoment B raw678step0 raw678step0Labels := by
      have ha : raw678step0 = (fun i j => raw678 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw678step0 raw678; decide +kernel
      have hl : raw678step0Labels = raw678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw678 raw678Labels permutation32 permutation4
    mixedMoment B raw678step0 raw678step0Labels = mixedMoment B raw678step1 raw678step1Labels := by
      have ha : raw678step1 = raw678step0 := by apply Matrix.ext; unfold raw678step1 raw678step0; decide +kernel
      have hl : raw678step0Labels = labelEmbedding7 ∘ raw678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw678step0 raw678step0Labels raw678step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

theorem canonical679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw679 raw679Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw679 raw679Labels = mixedMoment B raw679step0 raw679step0Labels := by
      have ha : raw679step0 = (fun i j => raw679 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw679step0 raw679; decide +kernel
      have hl : raw679step0Labels = raw679Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw679 raw679Labels permutation32 permutation4
    _ = mixedMoment B node539 node539Labels := by rfl

theorem canonical680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw680 raw680Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw680 raw680Labels = mixedMoment B raw680step0 raw680step0Labels := by
      have ha : raw680step0 = (fun i j => raw680 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw680step0 raw680; decide +kernel
      have hl : raw680step0Labels = raw680Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw680 raw680Labels permutation38 permutation6
    mixedMoment B raw680step0 raw680step0Labels = mixedMoment B raw680step1 raw680step1Labels := by
      have ha : raw680step1 = -raw680step0 := by apply Matrix.ext; change ∀ i j, raw680step1 i j = -(raw680step0 i j); unfold raw680step1 raw680step0; decide +kernel
      have hl : raw680step1Labels = raw680step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw680step1 raw680step1Labels = mixedMoment B raw680step2 raw680step2Labels := by
      have ha : raw680step2 = raw680step1 := by apply Matrix.ext; unfold raw680step2 raw680step1; decide +kernel
      have hl : raw680step1Labels = labelEmbedding1 ∘ raw680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw680step1 raw680step1Labels raw680step2Labels labelEmbedding1 hl
    _ = mixedMoment B node664 node664Labels := by rfl

theorem canonical717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw717 raw717Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw717 raw717Labels = mixedMoment B raw717step0 raw717step0Labels := by
      have ha : raw717step0 = (fun i j => raw717 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw717step0 raw717; decide +kernel
      have hl : raw717step0Labels = raw717Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw717 raw717Labels permutation32 permutation4
    mixedMoment B raw717step0 raw717step0Labels = mixedMoment B raw717step1 raw717step1Labels := by
      have ha : raw717step1 = raw717step0 := by apply Matrix.ext; unfold raw717step1 raw717step0; decide +kernel
      have hl : raw717step0Labels = labelEmbedding7 ∘ raw717step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw717step0 raw717step0Labels raw717step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

theorem canonical718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw718 raw718Labels = mixedMoment B node552 node552Labels := by
  calc
    mixedMoment B raw718 raw718Labels = mixedMoment B raw718step0 raw718step0Labels := by
      have ha : raw718step0 = (fun i j => raw718 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw718step0 raw718; decide +kernel
      have hl : raw718step0Labels = raw718Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw718 raw718Labels permutation32 permutation4
    _ = mixedMoment B node552 node552Labels := by rfl

theorem canonical719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw719 raw719Labels = mixedMoment B node660 node660Labels := by
  calc
    mixedMoment B raw719 raw719Labels = mixedMoment B raw719step0 raw719step0Labels := by
      have ha : raw719step0 = (fun i j => raw719 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw719step0 raw719; decide +kernel
      have hl : raw719step0Labels = raw719Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw719 raw719Labels permutation32 permutation6
    mixedMoment B raw719step0 raw719step0Labels = mixedMoment B raw719step1 raw719step1Labels := by
      have ha : raw719step1 = -raw719step0 := by apply Matrix.ext; change ∀ i j, raw719step1 i j = -(raw719step0 i j); unfold raw719step1 raw719step0; decide +kernel
      have hl : raw719step1Labels = raw719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw719step1 raw719step1Labels = mixedMoment B raw719step2 raw719step2Labels := by
      have ha : raw719step2 = raw719step1 := by apply Matrix.ext; unfold raw719step2 raw719step1; decide +kernel
      have hl : raw719step1Labels = labelEmbedding1 ∘ raw719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw719step1 raw719step1Labels raw719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node660 node660Labels := by rfl

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

theorem canonical1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1020 raw1020Labels = mixedMoment B node4286 node4286Labels := by
  calc
    mixedMoment B raw1020 raw1020Labels = mixedMoment B raw1020step0 raw1020step0Labels := by
      have ha : raw1020step0 = (fun i j => raw1020 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1020step0 raw1020; decide +kernel
      have hl : raw1020step0Labels = raw1020Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1020 raw1020Labels permutation152 permutation4
    mixedMoment B raw1020step0 raw1020step0Labels = mixedMoment B raw1020step1 raw1020step1Labels := by
      have ha : raw1020step1 = raw1020step0 := by apply Matrix.ext; unfold raw1020step1 raw1020step0; decide +kernel
      have hl : raw1020step0Labels = labelEmbedding7 ∘ raw1020step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1020step0 raw1020step0Labels raw1020step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4286 node4286Labels := by rfl

theorem canonical1021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1021 raw1021Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw1021 raw1021Labels = mixedMoment B raw1021step0 raw1021step0Labels := by
      have ha : raw1021step0 = (fun i j => raw1021 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1021step0 raw1021; decide +kernel
      have hl : raw1021step0Labels = raw1021Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1021 raw1021Labels permutation152 permutation4
    _ = mixedMoment B node864 node864Labels := by rfl

theorem canonical1022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1022 raw1022Labels = mixedMoment B node1550 node1550Labels := by
  calc
    mixedMoment B raw1022 raw1022Labels = mixedMoment B raw1022step0 raw1022step0Labels := by
      have ha : raw1022step0 = (fun i j => raw1022 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1022step0 raw1022; decide +kernel
      have hl : raw1022step0Labels = raw1022Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1022 raw1022Labels permutation160 permutation6
    mixedMoment B raw1022step0 raw1022step0Labels = mixedMoment B raw1022step1 raw1022step1Labels := by
      have ha : raw1022step1 = -raw1022step0 := by apply Matrix.ext; change ∀ i j, raw1022step1 i j = -(raw1022step0 i j); unfold raw1022step1 raw1022step0; decide +kernel
      have hl : raw1022step1Labels = raw1022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1022step1 raw1022step1Labels = mixedMoment B raw1022step2 raw1022step2Labels := by
      have ha : raw1022step2 = raw1022step1 := by apply Matrix.ext; unfold raw1022step2 raw1022step1; decide +kernel
      have hl : raw1022step1Labels = labelEmbedding1 ∘ raw1022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1022step1 raw1022step1Labels raw1022step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1550 node1550Labels := by rfl

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

theorem canonical10120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10120 raw10120Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw10120 raw10120Labels = mixedMoment B raw10120step0 raw10120step0Labels := by
      have hz : ∀ j, raw10120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10120step0 = (fun i j => raw10120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10120step0 raw10120; decide +kernel
      have hl : raw10120step0Labels = raw10120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10120 raw10120Labels permutation346 hz
    mixedMoment B raw10120step0 raw10120step0Labels = mixedMoment B raw10120step1 raw10120step1Labels := by
      have ha : raw10120step1 = (fun i j => raw10120step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10120step1 raw10120step0; decide +kernel
      have hl : raw10120step1Labels = raw10120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10120step0 raw10120step0Labels permutation40 permutation3
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical10125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10125 raw10125Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw10125 raw10125Labels = mixedMoment B raw10125step0 raw10125step0Labels := by
      have ha : raw10125step0 = (fun i j => raw10125 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10125step0 raw10125; decide +kernel
      have hl : raw10125step0Labels = raw10125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10125 raw10125Labels permutation202 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical10131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10131 raw10131Labels = mixedMoment B node2594 node2594Labels := by
  calc
    mixedMoment B raw10131 raw10131Labels = mixedMoment B raw10131step0 raw10131step0Labels := by
      have hz : ∀ j, raw10131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10131step0 = (fun i j => raw10131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10131step0 raw10131; decide +kernel
      have hl : raw10131step0Labels = raw10131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10131 raw10131Labels permutation346 hz
    mixedMoment B raw10131step0 raw10131step0Labels = mixedMoment B raw10131step1 raw10131step1Labels := by
      have ha : raw10131step1 = (fun i j => raw10131step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10131step1 raw10131step0; decide +kernel
      have hl : raw10131step1Labels = raw10131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10131step0 raw10131step0Labels permutation32 permutation3
    _ = mixedMoment B node2594 node2594Labels := by rfl

theorem canonical10132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10132 raw10132Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw10132 raw10132Labels = mixedMoment B raw10132step0 raw10132step0Labels := by
      have ha : raw10132step0 = (fun i j => raw10132 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10132step0 raw10132; decide +kernel
      have hl : raw10132step0Labels = raw10132Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10132 raw10132Labels permutation176 permutation3
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical10133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10133 raw10133Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10133 raw10133Labels = mixedMoment B raw10133step0 raw10133step0Labels := by
      have hz : ∀ j, raw10133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10133step0 = (fun i j => raw10133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10133step0 raw10133; decide +kernel
      have hl : raw10133step0Labels = raw10133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10133 raw10133Labels permutation346 hz
    mixedMoment B raw10133step0 raw10133step0Labels = mixedMoment B raw10133step1 raw10133step1Labels := by
      have ha : raw10133step1 = (fun i j => raw10133step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10133step1 raw10133step0; decide +kernel
      have hl : raw10133step1Labels = raw10133step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10133step0 raw10133step0Labels permutation44 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical10134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10134 raw10134Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw10134 raw10134Labels = mixedMoment B raw10134step0 raw10134step0Labels := by
      have hz : ∀ j, raw10134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10134step0 = (fun i j => raw10134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10134step0 raw10134; decide +kernel
      have hl : raw10134step0Labels = raw10134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10134 raw10134Labels permutation346 hz
    mixedMoment B raw10134step0 raw10134step0Labels = mixedMoment B raw10134step1 raw10134step1Labels := by
      have ha : raw10134step1 = (fun i j => raw10134step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10134step1 raw10134step0; decide +kernel
      have hl : raw10134step1Labels = raw10134step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10134step0 raw10134step0Labels permutation32 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

theorem canonical10135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10135 raw10135Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw10135 raw10135Labels = mixedMoment B raw10135step0 raw10135step0Labels := by
      have hz : ∀ j, raw10135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10135step0 = (fun i j => raw10135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10135step0 raw10135; decide +kernel
      have hl : raw10135step0Labels = raw10135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10135 raw10135Labels permutation346 hz
    mixedMoment B raw10135step0 raw10135step0Labels = mixedMoment B raw10135step1 raw10135step1Labels := by
      have ha : raw10135step1 = (fun i j => raw10135step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10135step1 raw10135step0; decide +kernel
      have hl : raw10135step1Labels = raw10135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10135step0 raw10135step0Labels permutation38 permutation3
    _ = mixedMoment B node985 node985Labels := by rfl

theorem canonical10140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10140 raw10140Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw10140 raw10140Labels = mixedMoment B raw10140step0 raw10140step0Labels := by
      have hz : ∀ j, raw10140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10140step0 = (fun i j => raw10140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10140step0 raw10140; decide +kernel
      have hl : raw10140step0Labels = raw10140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10140 raw10140Labels permutation346 hz
    mixedMoment B raw10140step0 raw10140step0Labels = mixedMoment B raw10140step1 raw10140step1Labels := by
      have ha : raw10140step1 = (fun i j => raw10140step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10140step1 raw10140step0; decide +kernel
      have hl : raw10140step1Labels = raw10140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10140step0 raw10140step0Labels permutation38 permutation3
    _ = mixedMoment B node979 node979Labels := by rfl

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

theorem canonical1026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1026 raw1026Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw1026 raw1026Labels = mixedMoment B raw1026step0 raw1026step0Labels := by
      have ha : raw1026step0 = (fun i j => raw1026 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1026step0 raw1026; decide +kernel
      have hl : raw1026step0Labels = raw1026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1026 raw1026Labels permutation152 permutation4
    mixedMoment B raw1026step0 raw1026step0Labels = mixedMoment B raw1026step1 raw1026step1Labels := by
      have ha : raw1026step1 = raw1026step0 := by apply Matrix.ext; unfold raw1026step1 raw1026step0; decide +kernel
      have hl : raw1026step0Labels = labelEmbedding7 ∘ raw1026step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1026step0 raw1026step0Labels raw1026step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

theorem canonical1027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1027 raw1027Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw1027 raw1027Labels = mixedMoment B raw1027step0 raw1027step0Labels := by
      have ha : raw1027step0 = (fun i j => raw1027 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1027step0 raw1027; decide +kernel
      have hl : raw1027step0Labels = raw1027Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1027 raw1027Labels permutation152 permutation4
    _ = mixedMoment B node866 node866Labels := by rfl

theorem canonical1028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1028 raw1028Labels = mixedMoment B node1554 node1554Labels := by
  calc
    mixedMoment B raw1028 raw1028Labels = mixedMoment B raw1028step0 raw1028step0Labels := by
      have ha : raw1028step0 = (fun i j => raw1028 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1028step0 raw1028; decide +kernel
      have hl : raw1028step0Labels = raw1028Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1028 raw1028Labels permutation158 permutation6
    mixedMoment B raw1028step0 raw1028step0Labels = mixedMoment B raw1028step1 raw1028step1Labels := by
      have ha : raw1028step1 = -raw1028step0 := by apply Matrix.ext; change ∀ i j, raw1028step1 i j = -(raw1028step0 i j); unfold raw1028step1 raw1028step0; decide +kernel
      have hl : raw1028step1Labels = raw1028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1028step1 raw1028step1Labels = mixedMoment B raw1028step2 raw1028step2Labels := by
      have ha : raw1028step2 = raw1028step1 := by apply Matrix.ext; unfold raw1028step2 raw1028step1; decide +kernel
      have hl : raw1028step1Labels = labelEmbedding1 ∘ raw1028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1028step1 raw1028step1Labels raw1028step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1554 node1554Labels := by rfl

theorem canonical1056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1056 raw1056Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw1056 raw1056Labels = mixedMoment B raw1056step0 raw1056step0Labels := by
      have ha : raw1056step0 = (fun i j => raw1056 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1056step0 raw1056; decide +kernel
      have hl : raw1056step0Labels = raw1056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1056 raw1056Labels permutation152 permutation4
    mixedMoment B raw1056step0 raw1056step0Labels = mixedMoment B raw1056step1 raw1056step1Labels := by
      have ha : raw1056step1 = raw1056step0 := by apply Matrix.ext; unfold raw1056step1 raw1056step0; decide +kernel
      have hl : raw1056step0Labels = labelEmbedding7 ∘ raw1056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1056step0 raw1056step0Labels raw1056step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

theorem canonical1057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1057 raw1057Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw1057 raw1057Labels = mixedMoment B raw1057step0 raw1057step0Labels := by
      have ha : raw1057step0 = (fun i j => raw1057 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1057step0 raw1057; decide +kernel
      have hl : raw1057step0Labels = raw1057Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1057 raw1057Labels permutation152 permutation4
    _ = mixedMoment B node876 node876Labels := by rfl

theorem canonical1058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1058 raw1058Labels = mixedMoment B node1552 node1552Labels := by
  calc
    mixedMoment B raw1058 raw1058Labels = mixedMoment B raw1058step0 raw1058step0Labels := by
      have ha : raw1058step0 = (fun i j => raw1058 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1058step0 raw1058; decide +kernel
      have hl : raw1058step0Labels = raw1058Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1058 raw1058Labels permutation152 permutation6
    mixedMoment B raw1058step0 raw1058step0Labels = mixedMoment B raw1058step1 raw1058step1Labels := by
      have ha : raw1058step1 = -raw1058step0 := by apply Matrix.ext; change ∀ i j, raw1058step1 i j = -(raw1058step0 i j); unfold raw1058step1 raw1058step0; decide +kernel
      have hl : raw1058step1Labels = raw1058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1058step1 raw1058step1Labels = mixedMoment B raw1058step2 raw1058step2Labels := by
      have ha : raw1058step2 = raw1058step1 := by apply Matrix.ext; unfold raw1058step2 raw1058step1; decide +kernel
      have hl : raw1058step1Labels = labelEmbedding1 ∘ raw1058step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1058step1 raw1058step1Labels raw1058step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1552 node1552Labels := by rfl

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

theorem canonical1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1134 raw1134Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw1134 raw1134Labels = mixedMoment B raw1134step0 raw1134step0Labels := by
      have ha : raw1134step0 = (fun i j => raw1134 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1134step0 raw1134; decide +kernel
      have hl : raw1134step0Labels = raw1134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1134 raw1134Labels permutation32 permutation4
    mixedMoment B raw1134step0 raw1134step0Labels = mixedMoment B raw1134step1 raw1134step1Labels := by
      have ha : raw1134step1 = raw1134step0 := by apply Matrix.ext; unfold raw1134step1 raw1134step0; decide +kernel
      have hl : raw1134step0Labels = labelEmbedding7 ∘ raw1134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1134step0 raw1134step0Labels raw1134step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1135 raw1135Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw1135 raw1135Labels = mixedMoment B raw1135step0 raw1135step0Labels := by
      have ha : raw1135step0 = (fun i j => raw1135 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1135step0 raw1135; decide +kernel
      have hl : raw1135step0Labels = raw1135Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1135 raw1135Labels permutation32 permutation4
    _ = mixedMoment B node927 node927Labels := by rfl

theorem canonical1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1136 raw1136Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw1136 raw1136Labels = mixedMoment B raw1136step0 raw1136step0Labels := by
      have ha : raw1136step0 = (fun i j => raw1136 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1136step0 raw1136; decide +kernel
      have hl : raw1136step0Labels = raw1136Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1136 raw1136Labels permutation32 permutation6
    mixedMoment B raw1136step0 raw1136step0Labels = mixedMoment B raw1136step1 raw1136step1Labels := by
      have ha : raw1136step1 = -raw1136step0 := by apply Matrix.ext; change ∀ i j, raw1136step1 i j = -(raw1136step0 i j); unfold raw1136step1 raw1136step0; decide +kernel
      have hl : raw1136step1Labels = raw1136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1136step1 raw1136step1Labels = mixedMoment B raw1136step2 raw1136step2Labels := by
      have ha : raw1136step2 = raw1136step1 := by apply Matrix.ext; unfold raw1136step2 raw1136step1; decide +kernel
      have hl : raw1136step1Labels = labelEmbedding1 ∘ raw1136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1136step1 raw1136step1Labels raw1136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

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

theorem canonical1254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1254 raw1254Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw1254 raw1254Labels = mixedMoment B raw1254step0 raw1254step0Labels := by
      have ha : raw1254step0 = (fun i j => raw1254 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1254step0 raw1254; decide +kernel
      have hl : raw1254step0Labels = raw1254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1254 raw1254Labels permutation152 permutation4
    mixedMoment B raw1254step0 raw1254step0Labels = mixedMoment B raw1254step1 raw1254step1Labels := by
      have ha : raw1254step1 = raw1254step0 := by apply Matrix.ext; unfold raw1254step1 raw1254step0; decide +kernel
      have hl : raw1254step0Labels = labelEmbedding7 ∘ raw1254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1254step0 raw1254step0Labels raw1254step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical1255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1255 raw1255Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw1255 raw1255Labels = mixedMoment B raw1255step0 raw1255step0Labels := by
      have ha : raw1255step0 = (fun i j => raw1255 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1255step0 raw1255; decide +kernel
      have hl : raw1255step0Labels = raw1255Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1255 raw1255Labels permutation152 permutation4
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical1256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1256 raw1256Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw1256 raw1256Labels = mixedMoment B raw1256step0 raw1256step0Labels := by
      have ha : raw1256step0 = (fun i j => raw1256 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1256step0 raw1256; decide +kernel
      have hl : raw1256step0Labels = raw1256Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1256 raw1256Labels permutation182 permutation6
    mixedMoment B raw1256step0 raw1256step0Labels = mixedMoment B raw1256step1 raw1256step1Labels := by
      have ha : raw1256step1 = -raw1256step0 := by apply Matrix.ext; change ∀ i j, raw1256step1 i j = -(raw1256step0 i j); unfold raw1256step1 raw1256step0; decide +kernel
      have hl : raw1256step1Labels = raw1256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1256step1 raw1256step1Labels = mixedMoment B raw1256step2 raw1256step2Labels := by
      have ha : raw1256step2 = raw1256step1 := by apply Matrix.ext; unfold raw1256step2 raw1256step1; decide +kernel
      have hl : raw1256step1Labels = labelEmbedding1 ∘ raw1256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1256step1 raw1256step1Labels raw1256step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4098 node4098Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node535 node535Labels + mixedMoment B node656 node656Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw666 singletonSmall4098
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4098) = raw666Labels := by decide +kernel
  rw [hl, canonical666 B hB] at h
  have hc0 : mixedMoment B raw666 (Fin.cases (0 : Fin 2) singletonSmall4098) =
      mixedMoment B node535 node535Labels := by
    have ha : raw666 = raw667 := by apply Matrix.ext; unfold raw666 raw667; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4098 = raw667Labels := by decide +kernel
    rw [ha, hj, canonical667 B hB]
  have hc1 : mixedMoment B raw666 (Fin.cases (1 : Fin 2) singletonSmall4098) =
      mixedMoment B node656 node656Labels := by
    have ha : raw666 = raw668 := by apply Matrix.ext; unfold raw666 raw668; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4098 = raw668Labels := by decide +kernel
    rw [ha, hj, canonical668 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4099 node4099Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node536 node536Labels + mixedMoment B node657 node657Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw669 singletonSmall4099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4099) = raw669Labels := by decide +kernel
  rw [hl, canonical669 B hB] at h
  have hc0 : mixedMoment B raw669 (Fin.cases (0 : Fin 2) singletonSmall4099) =
      mixedMoment B node536 node536Labels := by
    have ha : raw669 = raw670 := by apply Matrix.ext; unfold raw669 raw670; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4099 = raw670Labels := by decide +kernel
    rw [ha, hj, canonical670 B hB]
  have hc1 : mixedMoment B raw669 (Fin.cases (1 : Fin 2) singletonSmall4099) =
      mixedMoment B node657 node657Labels := by
    have ha : raw669 = raw671 := by apply Matrix.ext; unfold raw669 raw671; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4099 = raw671Labels := by decide +kernel
    rw [ha, hj, canonical671 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4102 node4102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node539 node539Labels + mixedMoment B node664 node664Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw678 singletonSmall4102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4102) = raw678Labels := by decide +kernel
  rw [hl, canonical678 B hB] at h
  have hc0 : mixedMoment B raw678 (Fin.cases (0 : Fin 2) singletonSmall4102) =
      mixedMoment B node539 node539Labels := by
    have ha : raw678 = raw679 := by apply Matrix.ext; unfold raw678 raw679; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4102 = raw679Labels := by decide +kernel
    rw [ha, hj, canonical679 B hB]
  have hc1 : mixedMoment B raw678 (Fin.cases (1 : Fin 2) singletonSmall4102) =
      mixedMoment B node664 node664Labels := by
    have ha : raw678 = raw680 := by apply Matrix.ext; unfold raw678 raw680; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4102 = raw680Labels := by decide +kernel
    rw [ha, hj, canonical680 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4115 node4115Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node552 node552Labels + mixedMoment B node660 node660Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw717 singletonSmall4115
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4115) = raw717Labels := by decide +kernel
  rw [hl, canonical717 B hB] at h
  have hc0 : mixedMoment B raw717 (Fin.cases (0 : Fin 2) singletonSmall4115) =
      mixedMoment B node552 node552Labels := by
    have ha : raw717 = raw718 := by apply Matrix.ext; unfold raw717 raw718; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4115 = raw718Labels := by decide +kernel
    rw [ha, hj, canonical718 B hB]
  have hc1 : mixedMoment B raw717 (Fin.cases (1 : Fin 2) singletonSmall4115) =
      mixedMoment B node660 node660Labels := by
    have ha : raw717 = raw719 := by apply Matrix.ext; unfold raw717 raw719; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4115 = raw719Labels := by decide +kernel
    rw [ha, hj, canonical719 B hB]
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

theorem singleton4286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4286 node4286Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node864 node864Labels + mixedMoment B node1550 node1550Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1020 singletonSmall4286
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4286) = raw1020Labels := by decide +kernel
  rw [hl, canonical1020 B hB] at h
  have hc0 : mixedMoment B raw1020 (Fin.cases (0 : Fin 2) singletonSmall4286) =
      mixedMoment B node864 node864Labels := by
    have ha : raw1020 = raw1021 := by apply Matrix.ext; unfold raw1020 raw1021; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4286 = raw1021Labels := by decide +kernel
    rw [ha, hj, canonical1021 B hB]
  have hc1 : mixedMoment B raw1020 (Fin.cases (1 : Fin 2) singletonSmall4286) =
      mixedMoment B node1550 node1550Labels := by
    have ha : raw1020 = raw1022 := by apply Matrix.ext; unfold raw1020 raw1022; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4286 = raw1022Labels := by decide +kernel
    rw [ha, hj, canonical1022 B hB]
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

theorem singleton4288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4288 node4288Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node866 node866Labels + mixedMoment B node1554 node1554Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1026 singletonSmall4288
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4288) = raw1026Labels := by decide +kernel
  rw [hl, canonical1026 B hB] at h
  have hc0 : mixedMoment B raw1026 (Fin.cases (0 : Fin 2) singletonSmall4288) =
      mixedMoment B node866 node866Labels := by
    have ha : raw1026 = raw1027 := by apply Matrix.ext; unfold raw1026 raw1027; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4288 = raw1027Labels := by decide +kernel
    rw [ha, hj, canonical1027 B hB]
  have hc1 : mixedMoment B raw1026 (Fin.cases (1 : Fin 2) singletonSmall4288) =
      mixedMoment B node1554 node1554Labels := by
    have ha : raw1026 = raw1028 := by apply Matrix.ext; unfold raw1026 raw1028; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4288 = raw1028Labels := by decide +kernel
    rw [ha, hj, canonical1028 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4298 node4298Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node876 node876Labels + mixedMoment B node1552 node1552Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1056 singletonSmall4298
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4298) = raw1056Labels := by decide +kernel
  rw [hl, canonical1056 B hB] at h
  have hc0 : mixedMoment B raw1056 (Fin.cases (0 : Fin 2) singletonSmall4298) =
      mixedMoment B node876 node876Labels := by
    have ha : raw1056 = raw1057 := by apply Matrix.ext; unfold raw1056 raw1057; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4298 = raw1057Labels := by decide +kernel
    rw [ha, hj, canonical1057 B hB]
  have hc1 : mixedMoment B raw1056 (Fin.cases (1 : Fin 2) singletonSmall4298) =
      mixedMoment B node1552 node1552Labels := by
    have ha : raw1056 = raw1058 := by apply Matrix.ext; unfold raw1056 raw1058; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4298 = raw1058Labels := by decide +kernel
    rw [ha, hj, canonical1058 B hB]
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

theorem singleton4349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4349 node4349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node927 node927Labels + mixedMoment B node1675 node1675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1134 singletonSmall4349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4349) = raw1134Labels := by decide +kernel
  rw [hl, canonical1134 B hB] at h
  have hc0 : mixedMoment B raw1134 (Fin.cases (0 : Fin 2) singletonSmall4349) =
      mixedMoment B node927 node927Labels := by
    have ha : raw1134 = raw1135 := by apply Matrix.ext; unfold raw1134 raw1135; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4349 = raw1135Labels := by decide +kernel
    rw [ha, hj, canonical1135 B hB]
  have hc1 : mixedMoment B raw1134 (Fin.cases (1 : Fin 2) singletonSmall4349) =
      mixedMoment B node1675 node1675Labels := by
    have ha : raw1134 = raw1136 := by apply Matrix.ext; unfold raw1134 raw1136; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4349 = raw1136Labels := by decide +kernel
    rw [ha, hj, canonical1136 B hB]
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

theorem singleton4456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4456 node4456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1039 node1039Labels + mixedMoment B node1706 node1706Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1254 singletonSmall4456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4456) = raw1254Labels := by decide +kernel
  rw [hl, canonical1254 B hB] at h
  have hc0 : mixedMoment B raw1254 (Fin.cases (0 : Fin 2) singletonSmall4456) =
      mixedMoment B node1039 node1039Labels := by
    have ha : raw1254 = raw1255 := by apply Matrix.ext; unfold raw1254 raw1255; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4456 = raw1255Labels := by decide +kernel
    rw [ha, hj, canonical1255 B hB]
  have hc1 : mixedMoment B raw1254 (Fin.cases (1 : Fin 2) singletonSmall4456) =
      mixedMoment B node1706 node1706Labels := by
    have ha : raw1254 = raw1256 := by apply Matrix.ext; unfold raw1254 raw1256; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4456 = raw1256Labels := by decide +kernel
    rw [ha, hj, canonical1256 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4495 node4495Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1079 node1079Labels + mixedMoment B node1708 node1708Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1293 singletonSmall4495
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4495) = raw1293Labels := by decide +kernel
  rw [hl, canonical1293 B hB] at h
  have hc0 : mixedMoment B raw1293 (Fin.cases (0 : Fin 2) singletonSmall4495) =
      mixedMoment B node1079 node1079Labels := by
    have ha : raw1293 = raw1294 := by apply Matrix.ext; unfold raw1293 raw1294; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4495 = raw1294Labels := by decide +kernel
    rw [ha, hj, canonical1294 B hB]
  have hc1 : mixedMoment B raw1293 (Fin.cases (1 : Fin 2) singletonSmall4495) =
      mixedMoment B node1708 node1708Labels := by
    have ha : raw1293 = raw1295 := by apply Matrix.ext; unfold raw1293 raw1295; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4495 = raw1295Labels := by decide +kernel
    rw [ha, hj, canonical1295 B hB]
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

theorem sound656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node656 node656Labels = Sparse.eval nodeValue656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 656) = mixedMoment B node656 node656Labels := rfl
  simpa [nodeValue656, Sparse.eval] using hc.symm

theorem sound657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node657 node657Labels = Sparse.eval nodeValue657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 657) = mixedMoment B node657 node657Labels := rfl
  simpa [nodeValue657, Sparse.eval] using hc.symm

theorem sound660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node660 node660Labels = Sparse.eval nodeValue660 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 660) = mixedMoment B node660 node660Labels := rfl
  simpa [nodeValue660, Sparse.eval] using hc.symm

theorem sound664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node664 node664Labels = Sparse.eval nodeValue664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 664) = mixedMoment B node664 node664Labels := rfl
  simpa [nodeValue664, Sparse.eval] using hc.symm

theorem sound699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node699 node699Labels = Sparse.eval nodeValue699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 699) = mixedMoment B node699 node699Labels := rfl
  simpa [nodeValue699, Sparse.eval] using hc.symm

theorem sound700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node700 node700Labels = Sparse.eval nodeValue700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 700) = mixedMoment B node700 node700Labels := rfl
  simpa [nodeValue700, Sparse.eval] using hc.symm

theorem sound703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node703 node703Labels = Sparse.eval nodeValue703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 703) = mixedMoment B node703 node703Labels := rfl
  simpa [nodeValue703, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node712 node712Labels = 0 := by
  exact mixedMoment_order_one B hB node712 node712Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node712 node712Labels = Sparse.eval nodeValue712 (mixedVector B) := by
  simpa only [nodeValue712, Sparse.eval_nil] using zero712 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node806 node806Labels = 0 := by
  exact mixedMoment_order_one B hB node806 node806Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node806 node806Labels = Sparse.eval nodeValue806 (mixedVector B) := by
  simpa only [nodeValue806, Sparse.eval_nil] using zero806 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero878 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node878 node878Labels = 0 := by
  exact mixedMoment_order_one B hB node878 node878Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node864 node864Labels = Sparse.eval nodeValue864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 864) = mixedMoment B node864 node864Labels := rfl
  simpa [nodeValue864, Sparse.eval] using hc.symm

theorem sound865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node865 node865Labels = Sparse.eval nodeValue865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 865) = mixedMoment B node865 node865Labels := rfl
  simpa [nodeValue865, Sparse.eval] using hc.symm

theorem sound866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node866 node866Labels = Sparse.eval nodeValue866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 866) = mixedMoment B node866 node866Labels := rfl
  simpa [nodeValue866, Sparse.eval] using hc.symm

theorem sound869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node869 node869Labels = Sparse.eval nodeValue869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 869) = mixedMoment B node869 node869Labels := rfl
  simpa [nodeValue869, Sparse.eval] using hc.symm

theorem sound876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node876 node876Labels = Sparse.eval nodeValue876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 876) = mixedMoment B node876 node876Labels := rfl
  simpa [nodeValue876, Sparse.eval] using hc.symm

theorem sound878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node878 node878Labels = Sparse.eval nodeValue878 (mixedVector B) := by
  simpa only [nodeValue878, Sparse.eval_nil] using zero878 B _hB _hF

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

theorem sound919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node919 node919Labels = Sparse.eval nodeValue919 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 919) = mixedMoment B node919 node919Labels := rfl
  simpa [nodeValue919, Sparse.eval] using hc.symm

theorem sound921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node921 node921Labels = Sparse.eval nodeValue921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 921) = mixedMoment B node921 node921Labels := rfl
  simpa [nodeValue921, Sparse.eval] using hc.symm

theorem sound927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node927 node927Labels = Sparse.eval nodeValue927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 927) = mixedMoment B node927 node927Labels := rfl
  simpa [nodeValue927, Sparse.eval] using hc.symm

theorem sound941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node941 node941Labels = Sparse.eval nodeValue941 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 941) = mixedMoment B node941 node941Labels := rfl
  simpa [nodeValue941, Sparse.eval] using hc.symm

theorem sound943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node943 node943Labels = Sparse.eval nodeValue943 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 943) = mixedMoment B node943 node943Labels := rfl
  simpa [nodeValue943, Sparse.eval] using hc.symm

theorem sound946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node946 node946Labels = Sparse.eval nodeValue946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 946) = mixedMoment B node946 node946Labels := rfl
  simpa [nodeValue946, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node976 node976Labels = 0 := by
  exact mixedMoment_alpha B hF node976 node976Labels 1 permutation203
    (by decide +kernel)

theorem zero978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node978 node978Labels = 0 := by
  exact mixedMoment_alpha B hF node978 node978Labels 1 permutation202
    (by decide +kernel)

theorem zero1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1003 node1003Labels = 0 := by
  exact mixedMoment_order_one B hB node1003 node1003Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node976 node976Labels = Sparse.eval nodeValue976 (mixedVector B) := by
  simpa only [nodeValue976, Sparse.eval_nil] using zero976 B _hB _hF

theorem sound977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node977 node977Labels = Sparse.eval nodeValue977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 977) = mixedMoment B node977 node977Labels := rfl
  simpa [nodeValue977, Sparse.eval] using hc.symm

theorem sound978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node978 node978Labels = Sparse.eval nodeValue978 (mixedVector B) := by
  simpa only [nodeValue978, Sparse.eval_nil] using zero978 B _hB _hF

theorem sound979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node979 node979Labels = Sparse.eval nodeValue979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 979) = mixedMoment B node979 node979Labels := rfl
  simpa [nodeValue979, Sparse.eval] using hc.symm

theorem sound980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node980 node980Labels = Sparse.eval nodeValue980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 980) = mixedMoment B node980 node980Labels := rfl
  simpa [nodeValue980, Sparse.eval] using hc.symm

theorem sound981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node981 node981Labels = Sparse.eval nodeValue981 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 981) = mixedMoment B node981 node981Labels := rfl
  simpa [nodeValue981, Sparse.eval] using hc.symm

theorem sound985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node985 node985Labels = Sparse.eval nodeValue985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 985) = mixedMoment B node985 node985Labels := rfl
  simpa [nodeValue985, Sparse.eval] using hc.symm

theorem sound998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node998 node998Labels = Sparse.eval nodeValue998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 998) = mixedMoment B node998 node998Labels := rfl
  simpa [nodeValue998, Sparse.eval] using hc.symm

theorem sound1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1000 node1000Labels = Sparse.eval nodeValue1000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1000) = mixedMoment B node1000 node1000Labels := rfl
  simpa [nodeValue1000, Sparse.eval] using hc.symm

theorem sound1003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1003 node1003Labels = Sparse.eval nodeValue1003 (mixedVector B) := by
  simpa only [nodeValue1003, Sparse.eval_nil] using zero1003 B _hB _hF

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

theorem zero1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1038 node1038Labels = 0 := by
  exact mixedMoment_alpha B hF node1038 node1038Labels 1 permutation161
    (by decide +kernel)

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

theorem sound1032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1032 node1032Labels = Sparse.eval nodeValue1032 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1032) = mixedMoment B node1032 node1032Labels := rfl
  simpa [nodeValue1032, Sparse.eval] using hc.symm

theorem sound1033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1033 node1033Labels = Sparse.eval nodeValue1033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1033) = mixedMoment B node1033 node1033Labels := rfl
  simpa [nodeValue1033, Sparse.eval] using hc.symm

theorem sound1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1034 node1034Labels = Sparse.eval nodeValue1034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1034) = mixedMoment B node1034 node1034Labels := rfl
  simpa [nodeValue1034, Sparse.eval] using hc.symm

theorem sound1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1038 node1038Labels = Sparse.eval nodeValue1038 (mixedVector B) := by
  simpa only [nodeValue1038, Sparse.eval_nil] using zero1038 B _hB _hF

theorem sound1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1039 node1039Labels = Sparse.eval nodeValue1039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1039) = mixedMoment B node1039 node1039Labels := rfl
  simpa [nodeValue1039, Sparse.eval] using hc.symm

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

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

theorem sound1550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1550 node1550Labels = Sparse.eval nodeValue1550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1550) = mixedMoment B node1550 node1550Labels := rfl
  simpa [nodeValue1550, Sparse.eval] using hc.symm

theorem sound1552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1552 node1552Labels = Sparse.eval nodeValue1552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1552) = mixedMoment B node1552 node1552Labels := rfl
  simpa [nodeValue1552, Sparse.eval] using hc.symm

theorem sound1554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1554 node1554Labels = Sparse.eval nodeValue1554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1554) = mixedMoment B node1554 node1554Labels := rfl
  simpa [nodeValue1554, Sparse.eval] using hc.symm

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

theorem sound1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1664 node1664Labels = Sparse.eval nodeValue1664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1664) = mixedMoment B node1664 node1664Labels := rfl
  simpa [nodeValue1664, Sparse.eval] using hc.symm

theorem sound1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1666 node1666Labels = Sparse.eval nodeValue1666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1666) = mixedMoment B node1666 node1666Labels := rfl
  simpa [nodeValue1666, Sparse.eval] using hc.symm

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

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

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1908 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1908 node1908Labels = 0 := by
  exact mixedMoment_order_one B hB node1908 node1908Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1912 node1912Labels = 0 := by
  exact mixedMoment_order_one B hB node1912 node1912Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1907 node1907Labels = Sparse.eval nodeValue1907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1907) = mixedMoment B node1907 node1907Labels := rfl
  simpa [nodeValue1907, Sparse.eval] using hc.symm

theorem sound1908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1908 node1908Labels = Sparse.eval nodeValue1908 (mixedVector B) := by
  simpa only [nodeValue1908, Sparse.eval_nil] using zero1908 B _hB _hF

theorem sound1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1909 node1909Labels = Sparse.eval nodeValue1909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1909) = mixedMoment B node1909 node1909Labels := rfl
  simpa [nodeValue1909, Sparse.eval] using hc.symm

theorem sound1912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1912 node1912Labels = Sparse.eval nodeValue1912 (mixedVector B) := by
  simpa only [nodeValue1912, Sparse.eval_nil] using zero1912 B _hB _hF

theorem sound1913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1913 node1913Labels = Sparse.eval nodeValue1913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1913) = mixedMoment B node1913 node1913Labels := rfl
  simpa [nodeValue1913, Sparse.eval] using hc.symm

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

theorem sound2015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2015 node2015Labels = Sparse.eval nodeValue2015 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2015) = mixedMoment B node2015 node2015Labels := rfl
  simpa [nodeValue2015, Sparse.eval] using hc.symm

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

theorem sound2074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2074 node2074Labels = Sparse.eval nodeValue2074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2074) = mixedMoment B node2074 node2074Labels := rfl
  simpa [nodeValue2074, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2076 node2076Labels = Sparse.eval nodeValue2076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2076) = mixedMoment B node2076 node2076Labels := rfl
  simpa [nodeValue2076, Sparse.eval] using hc.symm

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

theorem sound2078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2078 node2078Labels = Sparse.eval nodeValue2078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2078) = mixedMoment B node2078 node2078Labels := rfl
  simpa [nodeValue2078, Sparse.eval] using hc.symm

theorem sound2099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2099 node2099Labels = Sparse.eval nodeValue2099 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2099) = mixedMoment B node2099 node2099Labels := rfl
  simpa [nodeValue2099, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = 0 := by
  exact mixedMoment_order_one B hB node2204 node2204Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = 0 := by
  exact mixedMoment_order_one B hB node2205 node2205Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2192 node2192Labels = Sparse.eval nodeValue2192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2192) = mixedMoment B node2192 node2192Labels := rfl
  simpa [nodeValue2192, Sparse.eval] using hc.symm

theorem sound2195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2195 node2195Labels = Sparse.eval nodeValue2195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2195) = mixedMoment B node2195 node2195Labels := rfl
  simpa [nodeValue2195, Sparse.eval] using hc.symm

theorem sound2196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2196 node2196Labels = Sparse.eval nodeValue2196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2196) = mixedMoment B node2196 node2196Labels := rfl
  simpa [nodeValue2196, Sparse.eval] using hc.symm

theorem sound2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2201 node2201Labels = Sparse.eval nodeValue2201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2201) = mixedMoment B node2201 node2201Labels := rfl
  simpa [nodeValue2201, Sparse.eval] using hc.symm

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

theorem sound2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = Sparse.eval nodeValue2204 (mixedVector B) := by
  simpa only [nodeValue2204, Sparse.eval_nil] using zero2204 B _hB _hF

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

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

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

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

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

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

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

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

theorem sound535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node535 node535Labels = Sparse.eval nodeValue535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 535) = mixedMoment B node535 node535Labels := rfl
  simpa [nodeValue535, Sparse.eval] using hc.symm

theorem sound536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node536 node536Labels = Sparse.eval nodeValue536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 536) = mixedMoment B node536 node536Labels := rfl
  simpa [nodeValue536, Sparse.eval] using hc.symm

theorem sound539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node539 node539Labels = Sparse.eval nodeValue539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 539) = mixedMoment B node539 node539Labels := rfl
  simpa [nodeValue539, Sparse.eval] using hc.symm

theorem sound552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node552 node552Labels = Sparse.eval nodeValue552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 552) = mixedMoment B node552 node552Labels := rfl
  simpa [nodeValue552, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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

theorem sound577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node577 node577Labels = Sparse.eval nodeValue577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 577) = mixedMoment B node577 node577Labels := rfl
  simpa [nodeValue577, Sparse.eval] using hc.symm

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

theorem sound4098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4098 node4098Labels = Sparse.eval nodeValue4098 (mixedVector B) := by
  have h := singleton4098 B _hB
  rw [sound535 B _hB _hF, sound656 B _hB _hF] at h
  norm_num [nodeValue4098, nodeValue535, nodeValue656, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4099 node4099Labels = Sparse.eval nodeValue4099 (mixedVector B) := by
  have h := singleton4099 B _hB
  rw [sound536 B _hB _hF, sound657 B _hB _hF] at h
  norm_num [nodeValue4099, nodeValue536, nodeValue657, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4102 node4102Labels = Sparse.eval nodeValue4102 (mixedVector B) := by
  have h := singleton4102 B _hB
  rw [sound539 B _hB _hF, sound664 B _hB _hF] at h
  norm_num [nodeValue4102, nodeValue539, nodeValue664, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4115 node4115Labels = Sparse.eval nodeValue4115 (mixedVector B) := by
  have h := singleton4115 B _hB
  rw [sound552 B _hB _hF, sound660 B _hB _hF] at h
  norm_num [nodeValue4115, nodeValue552, nodeValue660, Sparse.eval] at h ⊢
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

theorem sound4286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4286 node4286Labels = Sparse.eval nodeValue4286 (mixedVector B) := by
  have h := singleton4286 B _hB
  rw [sound864 B _hB _hF, sound1550 B _hB _hF] at h
  norm_num [nodeValue4286, nodeValue864, nodeValue1550, Sparse.eval] at h ⊢
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

theorem sound4288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4288 node4288Labels = Sparse.eval nodeValue4288 (mixedVector B) := by
  have h := singleton4288 B _hB
  rw [sound866 B _hB _hF, sound1554 B _hB _hF] at h
  norm_num [nodeValue4288, nodeValue866, nodeValue1554, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4298 node4298Labels = Sparse.eval nodeValue4298 (mixedVector B) := by
  have h := singleton4298 B _hB
  rw [sound876 B _hB _hF, sound1552 B _hB _hF] at h
  norm_num [nodeValue4298, nodeValue876, nodeValue1552, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4341 node4341Labels = Sparse.eval nodeValue4341 (mixedVector B) := by
  have h := singleton4341 B _hB
  rw [sound919 B _hB _hF, sound1664 B _hB _hF] at h
  norm_num [nodeValue4341, nodeValue919, nodeValue1664, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4343 node4343Labels = Sparse.eval nodeValue4343 (mixedVector B) := by
  have h := singleton4343 B _hB
  rw [sound921 B _hB _hF, sound1666 B _hB _hF] at h
  norm_num [nodeValue4343, nodeValue921, nodeValue1666, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4349 node4349Labels = Sparse.eval nodeValue4349 (mixedVector B) := by
  have h := singleton4349 B _hB
  rw [sound927 B _hB _hF, sound1675 B _hB _hF] at h
  norm_num [nodeValue4349, nodeValue927, nodeValue1675, Sparse.eval] at h ⊢
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

theorem sound4456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4456 node4456Labels = Sparse.eval nodeValue4456 (mixedVector B) := by
  have h := singleton4456 B _hB
  rw [sound1039 B _hB _hF, sound1706 B _hB _hF] at h
  norm_num [nodeValue4456, nodeValue1039, nodeValue1706, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
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

theorem sound4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4495 node4495Labels = Sparse.eval nodeValue4495 (mixedVector B) := by
  have h := singleton4495 B _hB
  rw [sound1079 B _hB _hF, sound1708 B _hB _hF] at h
  norm_num [nodeValue4495, nodeValue1079, nodeValue1708, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources54
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1743 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1743 + difference 0 1) (sourceB1743 + difference 1 0) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA1743 + difference 0 1) (sourceB1743 + difference 1 0) sourceC1743) = raw25421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25421; decide +kernel
    rw [ha]
    exact (canonical25421 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1743 + difference 1 1) (sourceB1743 + difference 1 1) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1743 + difference 1 1) (sourceB1743 + difference 1 1) sourceC1743) = raw25413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25413; decide +kernel
    rw [ha]
    exact (canonical25413 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1743 + difference 2 1) (sourceB1743 + difference 1 2) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 941) := by
    have ha : (tripleCharges (sourceA1743 + difference 2 1) (sourceB1743 + difference 1 2) sourceC1743) = raw25422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25422; decide +kernel
    rw [ha]
    exact (canonical25422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1743 + difference 3 1) (sourceB1743 + difference 1 3) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1743 + difference 3 1) (sourceB1743 + difference 1 3) sourceC1743) = raw25423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25423; decide +kernel
    rw [ha]
    exact (canonical25423 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1743 + difference 4 1) (sourceB1743 + difference 1 4) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1743 + difference 4 1) (sourceB1743 + difference 1 4) sourceC1743) = raw25424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25424; decide +kernel
    rw [ha]
    exact (canonical25424 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1743 + difference 5 1) (sourceB1743 + difference 1 5) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA1743 + difference 5 1) (sourceB1743 + difference 1 5) sourceC1743) = raw21468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw21468; decide +kernel
    rw [ha]
    exact (canonical21468 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1743 + sourceB1743) sourceC1743) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1743 + sourceB1743) sourceC1743) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1743 sourceB1743 sourceC1743 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1743 sourceB1743 sourceC1743
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1743, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1744 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 0) (sourceB1744 + difference 0 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 577) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 0) (sourceB1744 + difference 0 2) sourceC1744) = raw25415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25415; decide +kernel
    rw [ha]
    exact (canonical25415 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 1) (sourceB1744 + difference 1 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 941) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 1) (sourceB1744 + difference 1 2) sourceC1744) = raw25422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25422; decide +kernel
    rw [ha]
    exact (canonical25422 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 2) (sourceB1744 + difference 2 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 2) (sourceB1744 + difference 2 2) sourceC1744) = raw25413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25413; decide +kernel
    rw [ha]
    exact (canonical25413 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 3) (sourceB1744 + difference 3 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 3) (sourceB1744 + difference 3 2) sourceC1744) = raw21473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw21473; decide +kernel
    rw [ha]
    exact (canonical21473 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 4) (sourceB1744 + difference 4 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 4) (sourceB1744 + difference 4 2) sourceC1744) = raw25425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25425; decide +kernel
    rw [ha]
    exact (canonical25425 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 5) (sourceB1744 + difference 5 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 5) (sourceB1744 + difference 5 2) sourceC1744) = raw25426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25426; decide +kernel
    rw [ha]
    exact (canonical25426 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1744 + sourceB1744) sourceC1744) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1744 + sourceB1744) sourceC1744) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1744 sourceB1744 sourceC1744 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1744 sourceB1744 sourceC1744
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1744, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1745 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 1) (sourceB1745 + difference 1 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 1) (sourceB1745 + difference 1 0) sourceC1745) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 2) (sourceB1745 + difference 2 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 2) (sourceB1745 + difference 2 0) sourceC1745) = raw10102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10102; decide +kernel
    rw [ha]
    exact (canonical10102 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 3) (sourceB1745 + difference 3 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 3) (sourceB1745 + difference 3 0) sourceC1745) = raw25427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25427; decide +kernel
    rw [ha]
    exact (canonical25427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 4) (sourceB1745 + difference 4 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 4) (sourceB1745 + difference 4 0) sourceC1745) = raw10103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10103; decide +kernel
    rw [ha]
    exact (canonical10103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 5) (sourceB1745 + difference 5 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 5) (sourceB1745 + difference 5 0) sourceC1745) = raw10104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10104; decide +kernel
    rw [ha]
    exact (canonical10104 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 0) (sourceB1745 + difference 0 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4115) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 0) (sourceB1745 + difference 0 1) sourceC1745) = raw25428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25428; decide +kernel
    rw [ha]
    exact (canonical25428 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 2) (sourceB1745 + difference 2 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4298) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 2) (sourceB1745 + difference 2 1) sourceC1745) = raw25429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25429; decide +kernel
    rw [ha]
    exact (canonical25429 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 3) (sourceB1745 + difference 3 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 3) (sourceB1745 + difference 3 1) sourceC1745) = raw10090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10090; decide +kernel
    rw [ha]
    exact (canonical10090 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 4) (sourceB1745 + difference 4 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 4) (sourceB1745 + difference 4 1) sourceC1745) = raw25430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25430; decide +kernel
    rw [ha]
    exact (canonical25430 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 5) (sourceB1745 + difference 5 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 5) (sourceB1745 + difference 5 1) sourceC1745) = raw25431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25431; decide +kernel
    rw [ha]
    exact (canonical25431 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 0) (sourceB1745 + difference 0 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4098) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 0) (sourceB1745 + difference 0 2) sourceC1745) = raw25432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25432; decide +kernel
    rw [ha]
    exact (canonical25432 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 1) (sourceB1745 + difference 1 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 1) (sourceB1745 + difference 1 2) sourceC1745) = raw25433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25433; decide +kernel
    rw [ha]
    exact (canonical25433 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 3) (sourceB1745 + difference 3 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 3) (sourceB1745 + difference 3 2) sourceC1745) = raw10095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10095; decide +kernel
    rw [ha]
    exact (canonical10095 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 4) (sourceB1745 + difference 4 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 4) (sourceB1745 + difference 4 2) sourceC1745) = raw25434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25434; decide +kernel
    rw [ha]
    exact (canonical25434 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 5) (sourceB1745 + difference 5 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 5) (sourceB1745 + difference 5 2) sourceC1745) = raw25435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25435; decide +kernel
    rw [ha]
    exact (canonical25435 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 0) (sourceB1745 + difference 0 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 0) (sourceB1745 + difference 0 3) sourceC1745) = raw25436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25436; decide +kernel
    rw [ha]
    exact (canonical25436 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 1) (sourceB1745 + difference 1 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 1) (sourceB1745 + difference 1 3) sourceC1745) = raw25437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25437; decide +kernel
    rw [ha]
    exact (canonical25437 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 2) (sourceB1745 + difference 2 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 2) (sourceB1745 + difference 2 3) sourceC1745) = raw25438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25438; decide +kernel
    rw [ha]
    exact (canonical25438 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 4) (sourceB1745 + difference 4 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 4) (sourceB1745 + difference 4 3) sourceC1745) = raw25439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25439; decide +kernel
    rw [ha]
    exact (canonical25439 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 5) (sourceB1745 + difference 5 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 5) (sourceB1745 + difference 5 3) sourceC1745) = raw25440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25440; decide +kernel
    rw [ha]
    exact (canonical25440 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 0) (sourceB1745 + difference 0 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 0) (sourceB1745 + difference 0 4) sourceC1745) = raw25441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25441; decide +kernel
    rw [ha]
    exact (canonical25441 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 1) (sourceB1745 + difference 1 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 1) (sourceB1745 + difference 1 4) sourceC1745) = raw25442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25442; decide +kernel
    rw [ha]
    exact (canonical25442 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 2) (sourceB1745 + difference 2 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 2) (sourceB1745 + difference 2 4) sourceC1745) = raw25443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25443; decide +kernel
    rw [ha]
    exact (canonical25443 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 3) (sourceB1745 + difference 3 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 3) (sourceB1745 + difference 3 4) sourceC1745) = raw10105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10105; decide +kernel
    rw [ha]
    exact (canonical10105 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 5) (sourceB1745 + difference 5 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 5) (sourceB1745 + difference 5 4) sourceC1745) = raw25444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25444; decide +kernel
    rw [ha]
    exact (canonical25444 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 0) (sourceB1745 + difference 0 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4099) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 0) (sourceB1745 + difference 0 5) sourceC1745) = raw25445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25445; decide +kernel
    rw [ha]
    exact (canonical25445 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 1) (sourceB1745 + difference 1 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 1) (sourceB1745 + difference 1 5) sourceC1745) = raw25446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25446; decide +kernel
    rw [ha]
    exact (canonical25446 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 2) (sourceB1745 + difference 2 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4286) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 2) (sourceB1745 + difference 2 5) sourceC1745) = raw25447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25447; decide +kernel
    rw [ha]
    exact (canonical25447 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 3) (sourceB1745 + difference 3 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 3) (sourceB1745 + difference 3 5) sourceC1745) = raw10110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10110; decide +kernel
    rw [ha]
    exact (canonical10110 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 4) (sourceB1745 + difference 4 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 4) (sourceB1745 + difference 4 5) sourceC1745) = raw25448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25448; decide +kernel
    rw [ha]
    exact (canonical25448 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1745 sourceB1745 sourceC1745
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1745, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1746 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 1) (sourceB1746 + difference 1 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 1) (sourceB1746 + difference 1 0) sourceC1746) = raw10131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10131; decide +kernel
    rw [ha]
    exact (canonical10131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 2) (sourceB1746 + difference 2 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 2) (sourceB1746 + difference 2 0) sourceC1746) = raw10132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10132; decide +kernel
    rw [ha]
    exact (canonical10132 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 3) (sourceB1746 + difference 3 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 3) (sourceB1746 + difference 3 0) sourceC1746) = raw25449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25449; decide +kernel
    rw [ha]
    exact (canonical25449 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 4) (sourceB1746 + difference 4 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 4) (sourceB1746 + difference 4 0) sourceC1746) = raw10133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10133; decide +kernel
    rw [ha]
    exact (canonical10133 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 5) (sourceB1746 + difference 5 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 5) (sourceB1746 + difference 5 0) sourceC1746) = raw10134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10134; decide +kernel
    rw [ha]
    exact (canonical10134 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 0) (sourceB1746 + difference 0 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 552) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 0) (sourceB1746 + difference 0 1) sourceC1746) = raw25450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25450; decide +kernel
    rw [ha]
    exact (canonical25450 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 2) (sourceB1746 + difference 2 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 876) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 2) (sourceB1746 + difference 2 1) sourceC1746) = raw25451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25451; decide +kernel
    rw [ha]
    exact (canonical25451 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 3) (sourceB1746 + difference 3 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 3) (sourceB1746 + difference 3 1) sourceC1746) = raw10120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10120; decide +kernel
    rw [ha]
    exact (canonical10120 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 4) (sourceB1746 + difference 4 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 4) (sourceB1746 + difference 4 1) sourceC1746) = raw25452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25452; decide +kernel
    rw [ha]
    exact (canonical25452 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 5) (sourceB1746 + difference 5 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 5) (sourceB1746 + difference 5 1) sourceC1746) = raw25453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25453; decide +kernel
    rw [ha]
    exact (canonical25453 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 0) (sourceB1746 + difference 0 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 535) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 0) (sourceB1746 + difference 0 2) sourceC1746) = raw25454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25454; decide +kernel
    rw [ha]
    exact (canonical25454 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 1) (sourceB1746 + difference 1 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 1) (sourceB1746 + difference 1 2) sourceC1746) = raw25455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25455; decide +kernel
    rw [ha]
    exact (canonical25455 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 3) (sourceB1746 + difference 3 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 3) (sourceB1746 + difference 3 2) sourceC1746) = raw10125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10125; decide +kernel
    rw [ha]
    exact (canonical10125 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 4) (sourceB1746 + difference 4 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 4) (sourceB1746 + difference 4 2) sourceC1746) = raw25456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25456; decide +kernel
    rw [ha]
    exact (canonical25456 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 5) (sourceB1746 + difference 5 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 5) (sourceB1746 + difference 5 2) sourceC1746) = raw25457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25457; decide +kernel
    rw [ha]
    exact (canonical25457 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 0) (sourceB1746 + difference 0 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 0) (sourceB1746 + difference 0 3) sourceC1746) = raw25458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25458; decide +kernel
    rw [ha]
    exact (canonical25458 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 1) (sourceB1746 + difference 1 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 1) (sourceB1746 + difference 1 3) sourceC1746) = raw25459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25459; decide +kernel
    rw [ha]
    exact (canonical25459 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 2) (sourceB1746 + difference 2 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 2) (sourceB1746 + difference 2 3) sourceC1746) = raw25460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25460; decide +kernel
    rw [ha]
    exact (canonical25460 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 4) (sourceB1746 + difference 4 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 4) (sourceB1746 + difference 4 3) sourceC1746) = raw25461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25461; decide +kernel
    rw [ha]
    exact (canonical25461 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 5) (sourceB1746 + difference 5 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 5) (sourceB1746 + difference 5 3) sourceC1746) = raw25462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25462; decide +kernel
    rw [ha]
    exact (canonical25462 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 0) (sourceB1746 + difference 0 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 0) (sourceB1746 + difference 0 4) sourceC1746) = raw25463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25463; decide +kernel
    rw [ha]
    exact (canonical25463 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 1) (sourceB1746 + difference 1 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 1) (sourceB1746 + difference 1 4) sourceC1746) = raw25464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25464; decide +kernel
    rw [ha]
    exact (canonical25464 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 2) (sourceB1746 + difference 2 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 2) (sourceB1746 + difference 2 4) sourceC1746) = raw25465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25465; decide +kernel
    rw [ha]
    exact (canonical25465 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 3) (sourceB1746 + difference 3 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 3) (sourceB1746 + difference 3 4) sourceC1746) = raw10135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10135; decide +kernel
    rw [ha]
    exact (canonical10135 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 5) (sourceB1746 + difference 5 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 5) (sourceB1746 + difference 5 4) sourceC1746) = raw25466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25466; decide +kernel
    rw [ha]
    exact (canonical25466 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 0) (sourceB1746 + difference 0 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 536) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 0) (sourceB1746 + difference 0 5) sourceC1746) = raw25467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25467; decide +kernel
    rw [ha]
    exact (canonical25467 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 1) (sourceB1746 + difference 1 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 921) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 1) (sourceB1746 + difference 1 5) sourceC1746) = raw25468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25468; decide +kernel
    rw [ha]
    exact (canonical25468 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 2) (sourceB1746 + difference 2 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 864) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 2) (sourceB1746 + difference 2 5) sourceC1746) = raw25469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25469; decide +kernel
    rw [ha]
    exact (canonical25469 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 3) (sourceB1746 + difference 3 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 3) (sourceB1746 + difference 3 5) sourceC1746) = raw10140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10140; decide +kernel
    rw [ha]
    exact (canonical10140 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 4) (sourceB1746 + difference 4 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 4) (sourceB1746 + difference 4 5) sourceC1746) = raw25470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25470; decide +kernel
    rw [ha]
    exact (canonical25470 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1746 sourceB1746 sourceC1746
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1746, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1749 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 0) (sourceB1749 + difference 0 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 0) (sourceB1749 + difference 0 0) sourceC1749) = raw21573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw21573; decide +kernel
    rw [ha]
    exact (canonical21573 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 1) (sourceB1749 + difference 1 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2099) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 1) (sourceB1749 + difference 1 0) sourceC1749) = raw25501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw25501; decide +kernel
    rw [ha]
    exact (canonical25501 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 2) (sourceB1749 + difference 2 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2015) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 2) (sourceB1749 + difference 2 0) sourceC1749) = raw25502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw25502; decide +kernel
    rw [ha]
    exact (canonical25502 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 3) (sourceB1749 + difference 3 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 3) (sourceB1749 + difference 3 0) sourceC1749) = raw21567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw21567; decide +kernel
    rw [ha]
    exact (canonical21567 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 4) (sourceB1749 + difference 4 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 4) (sourceB1749 + difference 4 0) sourceC1749) = raw25503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw25503; decide +kernel
    rw [ha]
    exact (canonical25503 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 5) (sourceB1749 + difference 5 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 5) (sourceB1749 + difference 5 0) sourceC1749) = raw25504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw25504; decide +kernel
    rw [ha]
    exact (canonical25504 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1749 + sourceB1749) sourceC1749) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1749 + sourceB1749) sourceC1749) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1749 sourceB1749 sourceC1749 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1749 sourceB1749 sourceC1749
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1749, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1750 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 0) (sourceB1750 + difference 0 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 0) (sourceB1750 + difference 0 0) sourceC1750) = raw25505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25505; decide +kernel
    rw [ha]
    exact (canonical25505 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 1) (sourceB1750 + difference 1 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2078) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 1) (sourceB1750 + difference 1 0) sourceC1750) = raw25506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25506; decide +kernel
    rw [ha]
    exact (canonical25506 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 2) (sourceB1750 + difference 2 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 2) (sourceB1750 + difference 2 0) sourceC1750) = raw25507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25507; decide +kernel
    rw [ha]
    exact (canonical25507 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 3) (sourceB1750 + difference 3 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 3) (sourceB1750 + difference 3 0) sourceC1750) = raw25508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25508; decide +kernel
    rw [ha]
    exact (canonical25508 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 4) (sourceB1750 + difference 4 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 4) (sourceB1750 + difference 4 0) sourceC1750) = raw25509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25509; decide +kernel
    rw [ha]
    exact (canonical25509 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 5) (sourceB1750 + difference 5 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 5) (sourceB1750 + difference 5 0) sourceC1750) = raw25510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25510; decide +kernel
    rw [ha]
    exact (canonical25510 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1750 + sourceB1750) sourceC1750) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1750 + sourceB1750) sourceC1750) = raw25511 := by
      apply Matrix.ext; unfold doubleCharges sourceA1750 sourceB1750 sourceC1750 raw25511; decide +kernel
    rw [ha]
    exact (canonical25511 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1750 sourceB1750 sourceC1750
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1750, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1751 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1751 + difference 0 5) (sourceB1751 + difference 5 0) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1751 + difference 0 5) (sourceB1751 + difference 5 0) sourceC1751) = raw25510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25510; decide +kernel
    rw [ha]
    exact (canonical25510 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1751 + difference 1 5) (sourceB1751 + difference 5 1) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1751 + difference 1 5) (sourceB1751 + difference 5 1) sourceC1751) = raw25512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25512; decide +kernel
    rw [ha]
    exact (canonical25512 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1751 + difference 2 5) (sourceB1751 + difference 5 2) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA1751 + difference 2 5) (sourceB1751 + difference 5 2) sourceC1751) = raw25513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25513; decide +kernel
    rw [ha]
    exact (canonical25513 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1751 + difference 3 5) (sourceB1751 + difference 5 3) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1751 + difference 3 5) (sourceB1751 + difference 5 3) sourceC1751) = raw25514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25514; decide +kernel
    rw [ha]
    exact (canonical25514 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1751 + difference 4 5) (sourceB1751 + difference 5 4) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 978) := by
    have ha : (tripleCharges (sourceA1751 + difference 4 5) (sourceB1751 + difference 5 4) sourceC1751) = raw25515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25515; decide +kernel
    rw [ha]
    exact (canonical25515 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1751 + difference 5 5) (sourceB1751 + difference 5 5) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA1751 + difference 5 5) (sourceB1751 + difference 5 5) sourceC1751) = raw25505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25505; decide +kernel
    rw [ha]
    exact (canonical25505 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1751 + sourceB1751) sourceC1751) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1751 + sourceB1751) sourceC1751) = raw25511 := by
      apply Matrix.ext; unfold doubleCharges sourceA1751 sourceB1751 sourceC1751 raw25511; decide +kernel
    rw [ha]
    exact (canonical25511 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1751 sourceB1751 sourceC1751
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1751, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1752 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 0) (sourceB1752 + difference 0 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 978) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 0) (sourceB1752 + difference 0 0) sourceC1752) = raw25516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25516; decide +kernel
    rw [ha]
    exact (canonical25516 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 1) (sourceB1752 + difference 1 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 1) (sourceB1752 + difference 1 0) sourceC1752) = raw25517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25517; decide +kernel
    rw [ha]
    exact (canonical25517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 2) (sourceB1752 + difference 2 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1909) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 2) (sourceB1752 + difference 2 0) sourceC1752) = raw25518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25518; decide +kernel
    rw [ha]
    exact (canonical25518 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 3) (sourceB1752 + difference 3 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 3) (sourceB1752 + difference 3 0) sourceC1752) = raw25519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25519; decide +kernel
    rw [ha]
    exact (canonical25519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 4) (sourceB1752 + difference 4 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 4) (sourceB1752 + difference 4 0) sourceC1752) = raw25520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25520; decide +kernel
    rw [ha]
    exact (canonical25520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 5) (sourceB1752 + difference 5 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 5) (sourceB1752 + difference 5 0) sourceC1752) = raw25521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25521; decide +kernel
    rw [ha]
    exact (canonical25521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1752 + sourceB1752) sourceC1752) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1752 + sourceB1752) sourceC1752) = raw25522 := by
      apply Matrix.ext; unfold doubleCharges sourceA1752 sourceB1752 sourceC1752 raw25522; decide +kernel
    rw [ha]
    exact (canonical25522 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1752 sourceB1752 sourceC1752
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1752, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1753 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 0) (sourceB1753 + difference 0 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 0) (sourceB1753 + difference 0 0) sourceC1753) = raw25523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25523; decide +kernel
    rw [ha]
    exact (canonical25523 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 1) (sourceB1753 + difference 1 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 1) (sourceB1753 + difference 1 0) sourceC1753) = raw25524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25524; decide +kernel
    rw [ha]
    exact (canonical25524 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 2) (sourceB1753 + difference 2 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 2) (sourceB1753 + difference 2 0) sourceC1753) = raw25525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25525; decide +kernel
    rw [ha]
    exact (canonical25525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 3) (sourceB1753 + difference 3 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 3) (sourceB1753 + difference 3 0) sourceC1753) = raw25526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25526; decide +kernel
    rw [ha]
    exact (canonical25526 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 4) (sourceB1753 + difference 4 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 4) (sourceB1753 + difference 4 0) sourceC1753) = raw25527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25527; decide +kernel
    rw [ha]
    exact (canonical25527 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 5) (sourceB1753 + difference 5 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 5) (sourceB1753 + difference 5 0) sourceC1753) = raw25528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25528; decide +kernel
    rw [ha]
    exact (canonical25528 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1753 + sourceB1753) sourceC1753) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1753 + sourceB1753) sourceC1753) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA1753 sourceB1753 sourceC1753 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1753 sourceB1753 sourceC1753
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1753, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1756 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1756 + difference 0 5) (sourceB1756 + difference 5 0) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA1756 + difference 0 5) (sourceB1756 + difference 5 0) sourceC1756) = raw25528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25528; decide +kernel
    rw [ha]
    exact (canonical25528 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1756 + difference 1 5) (sourceB1756 + difference 5 1) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1003) := by
    have ha : (tripleCharges (sourceA1756 + difference 1 5) (sourceB1756 + difference 5 1) sourceC1756) = raw25534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25534; decide +kernel
    rw [ha]
    exact (canonical25534 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1756 + difference 2 5) (sourceB1756 + difference 5 2) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1756 + difference 2 5) (sourceB1756 + difference 5 2) sourceC1756) = raw25538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25538; decide +kernel
    rw [ha]
    exact (canonical25538 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1756 + difference 3 5) (sourceB1756 + difference 5 3) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1756 + difference 3 5) (sourceB1756 + difference 5 3) sourceC1756) = raw25539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25539; decide +kernel
    rw [ha]
    exact (canonical25539 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1756 + difference 4 5) (sourceB1756 + difference 5 4) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1756 + difference 4 5) (sourceB1756 + difference 5 4) sourceC1756) = raw25540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25540; decide +kernel
    rw [ha]
    exact (canonical25540 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1756 + difference 5 5) (sourceB1756 + difference 5 5) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1756 + difference 5 5) (sourceB1756 + difference 5 5) sourceC1756) = raw25523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25523; decide +kernel
    rw [ha]
    exact (canonical25523 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1756 + sourceB1756) sourceC1756) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1756 + sourceB1756) sourceC1756) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA1756 sourceB1756 sourceC1756 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1756 sourceB1756 sourceC1756
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1756, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1759 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 0) (sourceB1759 + difference 0 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 0) (sourceB1759 + difference 0 0) sourceC1759) = raw25549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25549; decide +kernel
    rw [ha]
    exact (canonical25549 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 1) (sourceB1759 + difference 1 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 1) (sourceB1759 + difference 1 0) sourceC1759) = raw25550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25550; decide +kernel
    rw [ha]
    exact (canonical25550 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 2) (sourceB1759 + difference 2 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1908) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 2) (sourceB1759 + difference 2 0) sourceC1759) = raw25551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25551; decide +kernel
    rw [ha]
    exact (canonical25551 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 3) (sourceB1759 + difference 3 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 3) (sourceB1759 + difference 3 0) sourceC1759) = raw25552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25552; decide +kernel
    rw [ha]
    exact (canonical25552 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 4) (sourceB1759 + difference 4 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 4) (sourceB1759 + difference 4 0) sourceC1759) = raw25553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25553; decide +kernel
    rw [ha]
    exact (canonical25553 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 5) (sourceB1759 + difference 5 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 5) (sourceB1759 + difference 5 0) sourceC1759) = raw25554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25554; decide +kernel
    rw [ha]
    exact (canonical25554 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1759 + sourceB1759) sourceC1759) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1759 + sourceB1759) sourceC1759) = raw25555 := by
      apply Matrix.ext; unfold doubleCharges sourceA1759 sourceB1759 sourceC1759 raw25555; decide +kernel
    rw [ha]
    exact (canonical25555 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1759 sourceB1759 sourceC1759
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1759, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources55
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1761 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1761 + difference 0 2) (sourceB1761 + difference 2 0) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1908) := by
    have ha : (tripleCharges (sourceA1761 + difference 0 2) (sourceB1761 + difference 2 0) sourceC1761) = raw25551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25551; decide +kernel
    rw [ha]
    exact (canonical25551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1761 + difference 1 2) (sourceB1761 + difference 2 1) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 878) := by
    have ha : (tripleCharges (sourceA1761 + difference 1 2) (sourceB1761 + difference 2 1) sourceC1761) = raw25557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25557; decide +kernel
    rw [ha]
    exact (canonical25557 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1761 + difference 2 2) (sourceB1761 + difference 2 2) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1761 + difference 2 2) (sourceB1761 + difference 2 2) sourceC1761) = raw25549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25549; decide +kernel
    rw [ha]
    exact (canonical25549 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1761 + difference 3 2) (sourceB1761 + difference 2 3) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1761 + difference 3 2) (sourceB1761 + difference 2 3) sourceC1761) = raw25561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25561; decide +kernel
    rw [ha]
    exact (canonical25561 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1761 + difference 4 2) (sourceB1761 + difference 2 4) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA1761 + difference 4 2) (sourceB1761 + difference 2 4) sourceC1761) = raw25562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25562; decide +kernel
    rw [ha]
    exact (canonical25562 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1761 + difference 5 2) (sourceB1761 + difference 2 5) sourceC1761) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA1761 + difference 5 2) (sourceB1761 + difference 2 5) sourceC1761) = raw25563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1761 sourceB1761 sourceC1761 difference raw25563; decide +kernel
    rw [ha]
    exact (canonical25563 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1761 + sourceB1761) sourceC1761) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1761 + sourceB1761) sourceC1761) = raw25555 := by
      apply Matrix.ext; unfold doubleCharges sourceA1761 sourceB1761 sourceC1761 raw25555; decide +kernel
    rw [ha]
    exact (canonical25555 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1761 sourceB1761 sourceC1761
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1761, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1762 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1762 + difference 0 0) (sourceB1762 + difference 0 0) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1762 + difference 0 0) (sourceB1762 + difference 0 0) sourceC1762) = raw25548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25548; decide +kernel
    rw [ha]
    exact (canonical25548 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1762 + difference 1 0) (sourceB1762 + difference 0 1) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 703) := by
    have ha : (tripleCharges (sourceA1762 + difference 1 0) (sourceB1762 + difference 0 1) sourceC1762) = raw25564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25564; decide +kernel
    rw [ha]
    exact (canonical25564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1762 + difference 2 0) (sourceB1762 + difference 0 2) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1762 + difference 2 0) (sourceB1762 + difference 0 2) sourceC1762) = raw25350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25350; decide +kernel
    rw [ha]
    exact (canonical25350 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1762 + difference 3 0) (sourceB1762 + difference 0 3) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 700) := by
    have ha : (tripleCharges (sourceA1762 + difference 3 0) (sourceB1762 + difference 0 3) sourceC1762) = raw25565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25565; decide +kernel
    rw [ha]
    exact (canonical25565 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1762 + difference 4 0) (sourceB1762 + difference 0 4) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 712) := by
    have ha : (tripleCharges (sourceA1762 + difference 4 0) (sourceB1762 + difference 0 4) sourceC1762) = raw25546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25546; decide +kernel
    rw [ha]
    exact (canonical25546 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1762 + difference 5 0) (sourceB1762 + difference 0 5) sourceC1762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 699) := by
    have ha : (tripleCharges (sourceA1762 + difference 5 0) (sourceB1762 + difference 0 5) sourceC1762) = raw25566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1762 sourceB1762 sourceC1762 difference raw25566; decide +kernel
    rw [ha]
    exact (canonical25566 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1762 + sourceB1762) sourceC1762) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1762 + sourceB1762) sourceC1762) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1762 sourceB1762 sourceC1762 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1762 sourceB1762 sourceC1762
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1762, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1763 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 0) (sourceB1763 + difference 0 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 976) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 0) (sourceB1763 + difference 0 0) sourceC1763) = raw25567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25567; decide +kernel
    rw [ha]
    exact (canonical25567 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 1) (sourceB1763 + difference 1 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2074) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 1) (sourceB1763 + difference 1 0) sourceC1763) = raw25568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25568; decide +kernel
    rw [ha]
    exact (canonical25568 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 2) (sourceB1763 + difference 2 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1907) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 2) (sourceB1763 + difference 2 0) sourceC1763) = raw25569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25569; decide +kernel
    rw [ha]
    exact (canonical25569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 3) (sourceB1763 + difference 3 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 3) (sourceB1763 + difference 3 0) sourceC1763) = raw25570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25570; decide +kernel
    rw [ha]
    exact (canonical25570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 4) (sourceB1763 + difference 4 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 4) (sourceB1763 + difference 4 0) sourceC1763) = raw25571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25571; decide +kernel
    rw [ha]
    exact (canonical25571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1763 + difference 0 5) (sourceB1763 + difference 5 0) sourceC1763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1763 + difference 0 5) (sourceB1763 + difference 5 0) sourceC1763) = raw25572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1763 sourceB1763 sourceC1763 difference raw25572; decide +kernel
    rw [ha]
    exact (canonical25572 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1763 + sourceB1763) sourceC1763) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1763 + sourceB1763) sourceC1763) = raw25573 := by
      apply Matrix.ext; unfold doubleCharges sourceA1763 sourceB1763 sourceC1763 raw25573; decide +kernel
    rw [ha]
    exact (canonical25573 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1763 sourceB1763 sourceC1763
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1763, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1488 : Integer.Sparse.reindex keyMap MixedData.row1488 = numericRow1488 := by decide +kernel

theorem numericCheck1488 (x : Master → ℝ) : Integer.Sparse.eval numericRow1488 x =
    (1 : ℝ) * reducedSource1488 x := by
  norm_num [numericRow1488, reducedSource1488, Integer.Sparse.eval, Sparse.eval, nodeValue941, nodeValue943, nodeValue946, nodeValue1040, nodeValue2106, nodeValue4084]

theorem reindexCheck1489 : Integer.Sparse.reindex keyMap MixedData.row1489 = numericRow1489 := by decide +kernel

theorem numericCheck1489 (x : Master → ℝ) : Integer.Sparse.eval numericRow1489 x =
    (1 : ℝ) * reducedSource1489 x := by
  norm_num [numericRow1489, reducedSource1489, Integer.Sparse.eval, Sparse.eval, nodeValue577, nodeValue941, nodeValue1038, nodeValue1040, nodeValue4084]

theorem reindexCheck1490 : Integer.Sparse.reindex keyMap MixedData.row1490 = numericRow1490 := by decide +kernel

theorem numericCheck1490 (x : Master → ℝ) : Integer.Sparse.eval numericRow1490 x =
    (3456 : ℝ) * reducedSource1490 x := by
  norm_num [numericRow1490, reducedSource1490, Integer.Sparse.eval, Sparse.eval, nodeValue4098, nodeValue4099, nodeValue4102, nodeValue4115, nodeValue4286, nodeValue4288, nodeValue4298, nodeValue4341, nodeValue4343, nodeValue4349, nodeValue4396, nodeValue4398, nodeValue4404, nodeValue4419, nodeValue4456, nodeValue4458, nodeValue4495, nodeValue5072, nodeValue5168, nodeValue5258, nodeValue5292] <;> ring

theorem reindexCheck1491 : Integer.Sparse.reindex keyMap MixedData.row1491 = numericRow1491 := by decide +kernel

theorem numericCheck1491 (x : Master → ℝ) : Integer.Sparse.eval numericRow1491 x =
    (864 : ℝ) * reducedSource1491 x := by
  norm_num [numericRow1491, reducedSource1491, Integer.Sparse.eval, Sparse.eval, nodeValue535, nodeValue536, nodeValue539, nodeValue552, nodeValue864, nodeValue866, nodeValue876, nodeValue919, nodeValue921, nodeValue927, nodeValue977, nodeValue979, nodeValue985, nodeValue1000, nodeValue1039, nodeValue1041, nodeValue1079, nodeValue2479, nodeValue2594, nodeValue2722, nodeValue2766] <;> ring

theorem reindexCheck1494 : Integer.Sparse.reindex keyMap MixedData.row1494 = numericRow1494 := by decide +kernel

theorem numericCheck1494 (x : Master → ℝ) : Integer.Sparse.eval numericRow1494 x =
    (1 : ℝ) * reducedSource1494 x := by
  norm_num [numericRow1494, reducedSource1494, Integer.Sparse.eval, Sparse.eval, nodeValue1033, nodeValue2015, nodeValue2099, nodeValue2203, nodeValue2259, nodeValue2261, nodeValue4081]

theorem reindexCheck1495 : Integer.Sparse.reindex keyMap MixedData.row1495 = numericRow1495 := by decide +kernel

theorem numericCheck1495 (x : Master → ℝ) : Integer.Sparse.eval numericRow1495 x =
    (1 : ℝ) * reducedSource1495 x := by
  norm_num [numericRow1495, reducedSource1495, Integer.Sparse.eval, Sparse.eval, nodeValue981, nodeValue1913, nodeValue2078, nodeValue2192, nodeValue2196, nodeValue2202, nodeValue4080]

theorem reindexCheck1496 : Integer.Sparse.reindex keyMap MixedData.row1496 = numericRow1496 := by decide +kernel

theorem numericCheck1496 (x : Master → ℝ) : Integer.Sparse.eval numericRow1496 x =
    (1 : ℝ) * reducedSource1496 x := by
  norm_num [numericRow1496, reducedSource1496, Integer.Sparse.eval, Sparse.eval, nodeValue977, nodeValue978, nodeValue981, nodeValue998, nodeValue1032, nodeValue2202, nodeValue4080]

theorem reindexCheck1497 : Integer.Sparse.reindex keyMap MixedData.row1497 = numericRow1497 := by decide +kernel

theorem numericCheck1497 (x : Master → ℝ) : Integer.Sparse.eval numericRow1497 x =
    (1 : ℝ) * reducedSource1497 x := by
  norm_num [numericRow1497, reducedSource1497, Integer.Sparse.eval, Sparse.eval, nodeValue978, nodeValue1909, nodeValue2076, nodeValue2195, nodeValue2202, nodeValue2206, nodeValue4080]

theorem reindexCheck1498 : Integer.Sparse.reindex keyMap MixedData.row1498 = numericRow1498 := by decide +kernel

theorem numericCheck1498 (x : Master → ℝ) : Integer.Sparse.eval numericRow1498 x =
    (1 : ℝ) * reducedSource1498 x := by
  norm_num [numericRow1498, reducedSource1498, Integer.Sparse.eval, Sparse.eval, nodeValue980, nodeValue1912, nodeValue2077, nodeValue2191, nodeValue2204, nodeValue4079]

theorem reindexCheck1499 : Integer.Sparse.reindex keyMap MixedData.row1499 = numericRow1499 := by decide +kernel

theorem numericCheck1499 (x : Master → ℝ) : Integer.Sparse.eval numericRow1499 x =
    (1 : ℝ) * reducedSource1499 x := by
  norm_num [numericRow1499, reducedSource1499, Integer.Sparse.eval, Sparse.eval, nodeValue980, nodeValue1003, nodeValue1034, nodeValue2204, nodeValue4079]

theorem reindexCheck1500 : Integer.Sparse.reindex keyMap MixedData.row1500 = numericRow1500 := by decide +kernel

theorem numericCheck1500 (x : Master → ℝ) : Integer.Sparse.eval numericRow1500 x =
    (1 : ℝ) * reducedSource1500 x := by
  norm_num [numericRow1500, reducedSource1500, Integer.Sparse.eval, Sparse.eval, nodeValue977, nodeValue1908, nodeValue2075, nodeValue2190, nodeValue2202, nodeValue2205, nodeValue4080]

theorem reindexCheck1501 : Integer.Sparse.reindex keyMap MixedData.row1501 = numericRow1501 := by decide +kernel

theorem numericCheck1501 (x : Master → ℝ) : Integer.Sparse.eval numericRow1501 x =
    (1 : ℝ) * reducedSource1501 x := by
  norm_num [numericRow1501, reducedSource1501, Integer.Sparse.eval, Sparse.eval, nodeValue865, nodeValue866, nodeValue869, nodeValue878, nodeValue977, nodeValue1908, nodeValue4080]

theorem reindexCheck1502 : Integer.Sparse.reindex keyMap MixedData.row1502 = numericRow1502 := by decide +kernel

theorem numericCheck1502 (x : Master → ℝ) : Integer.Sparse.eval numericRow1502 x =
    (1 : ℝ) * reducedSource1502 x := by
  norm_num [numericRow1502, reducedSource1502, Integer.Sparse.eval, Sparse.eval, nodeValue699, nodeValue700, nodeValue703, nodeValue712, nodeValue806, nodeValue1597, nodeValue4069]

theorem reindexCheck1503 : Integer.Sparse.reindex keyMap MixedData.row1503 = numericRow1503 := by decide +kernel

theorem numericCheck1503 (x : Master → ℝ) : Integer.Sparse.eval numericRow1503 x =
    (1 : ℝ) * reducedSource1503 x := by
  norm_num [numericRow1503, reducedSource1503, Integer.Sparse.eval, Sparse.eval, nodeValue976, nodeValue1907, nodeValue2074, nodeValue2201, nodeValue2203, nodeValue4081]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1488 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1488 (mixedVector B) = 0 := by
  have h941 : mixedVector B (Sum.inr 941) = Sparse.eval nodeValue941 (mixedVector B) := by
    change mixedMoment B node941 node941Labels = _
    exact sound941 B hB hF
  have h943 : mixedVector B (Sum.inr 943) = Sparse.eval nodeValue943 (mixedVector B) := by
    change mixedMoment B node943 node943Labels = _
    exact sound943 B hB hF
  have h946 : mixedVector B (Sum.inr 946) = Sparse.eval nodeValue946 (mixedVector B) := by
    change mixedMoment B node946 node946Labels = _
    exact sound946 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1743, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h941, h943, h946, h1040, h2106, h4084, reducedSource1488] using sourceEq1743 B hB

theorem rowSound1488 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1488 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1488, numericCheck1488, reducedZero1488 B hB hF, mul_zero]

theorem reducedZero1489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1489 (mixedVector B) = 0 := by
  have h577 : mixedVector B (Sum.inr 577) = Sparse.eval nodeValue577 (mixedVector B) := by
    change mixedMoment B node577 node577Labels = _
    exact sound577 B hB hF
  have h941 : mixedVector B (Sum.inr 941) = Sparse.eval nodeValue941 (mixedVector B) := by
    change mixedMoment B node941 node941Labels = _
    exact sound941 B hB hF
  have h1038 : mixedVector B (Sum.inr 1038) = Sparse.eval nodeValue1038 (mixedVector B) := by
    change mixedMoment B node1038 node1038Labels = _
    exact sound1038 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1744, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h577, h941, h1038, h1040, h4084, reducedSource1489] using sourceEq1744 B hB

theorem rowSound1489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1489 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1489, numericCheck1489, reducedZero1489 B hB hF, mul_zero]

theorem reducedZero1490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1490 (mixedVector B) = 0 := by
  have h4098 : mixedVector B (Sum.inr 4098) = Sparse.eval nodeValue4098 (mixedVector B) := by
    change mixedMoment B node4098 node4098Labels = _
    exact sound4098 B hB hF
  have h4099 : mixedVector B (Sum.inr 4099) = Sparse.eval nodeValue4099 (mixedVector B) := by
    change mixedMoment B node4099 node4099Labels = _
    exact sound4099 B hB hF
  have h4102 : mixedVector B (Sum.inr 4102) = Sparse.eval nodeValue4102 (mixedVector B) := by
    change mixedMoment B node4102 node4102Labels = _
    exact sound4102 B hB hF
  have h4115 : mixedVector B (Sum.inr 4115) = Sparse.eval nodeValue4115 (mixedVector B) := by
    change mixedMoment B node4115 node4115Labels = _
    exact sound4115 B hB hF
  have h4286 : mixedVector B (Sum.inr 4286) = Sparse.eval nodeValue4286 (mixedVector B) := by
    change mixedMoment B node4286 node4286Labels = _
    exact sound4286 B hB hF
  have h4288 : mixedVector B (Sum.inr 4288) = Sparse.eval nodeValue4288 (mixedVector B) := by
    change mixedMoment B node4288 node4288Labels = _
    exact sound4288 B hB hF
  have h4298 : mixedVector B (Sum.inr 4298) = Sparse.eval nodeValue4298 (mixedVector B) := by
    change mixedMoment B node4298 node4298Labels = _
    exact sound4298 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
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
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  simpa only [sourceForm1745, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4098, h4099, h4102, h4115, h4286, h4288, h4298, h4341, h4343, h4349, h4396, h4398, h4404, h4419, h4456, h4458, h4495, h5072, h5168, h5258, h5292, reducedSource1490] using sourceEq1745 B hB

theorem rowSound1490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1490 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1490, numericCheck1490, reducedZero1490 B hB hF, mul_zero]

theorem reducedZero1491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1491 (mixedVector B) = 0 := by
  have h535 : mixedVector B (Sum.inr 535) = Sparse.eval nodeValue535 (mixedVector B) := by
    change mixedMoment B node535 node535Labels = _
    exact sound535 B hB hF
  have h536 : mixedVector B (Sum.inr 536) = Sparse.eval nodeValue536 (mixedVector B) := by
    change mixedMoment B node536 node536Labels = _
    exact sound536 B hB hF
  have h539 : mixedVector B (Sum.inr 539) = Sparse.eval nodeValue539 (mixedVector B) := by
    change mixedMoment B node539 node539Labels = _
    exact sound539 B hB hF
  have h552 : mixedVector B (Sum.inr 552) = Sparse.eval nodeValue552 (mixedVector B) := by
    change mixedMoment B node552 node552Labels = _
    exact sound552 B hB hF
  have h864 : mixedVector B (Sum.inr 864) = Sparse.eval nodeValue864 (mixedVector B) := by
    change mixedMoment B node864 node864Labels = _
    exact sound864 B hB hF
  have h866 : mixedVector B (Sum.inr 866) = Sparse.eval nodeValue866 (mixedVector B) := by
    change mixedMoment B node866 node866Labels = _
    exact sound866 B hB hF
  have h876 : mixedVector B (Sum.inr 876) = Sparse.eval nodeValue876 (mixedVector B) := by
    change mixedMoment B node876 node876Labels = _
    exact sound876 B hB hF
  have h919 : mixedVector B (Sum.inr 919) = Sparse.eval nodeValue919 (mixedVector B) := by
    change mixedMoment B node919 node919Labels = _
    exact sound919 B hB hF
  have h921 : mixedVector B (Sum.inr 921) = Sparse.eval nodeValue921 (mixedVector B) := by
    change mixedMoment B node921 node921Labels = _
    exact sound921 B hB hF
  have h927 : mixedVector B (Sum.inr 927) = Sparse.eval nodeValue927 (mixedVector B) := by
    change mixedMoment B node927 node927Labels = _
    exact sound927 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2594 : mixedVector B (Sum.inr 2594) = Sparse.eval nodeValue2594 (mixedVector B) := by
    change mixedMoment B node2594 node2594Labels = _
    exact sound2594_e B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766_e B hB hF
  simpa only [sourceForm1746, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h535, h536, h539, h552, h864, h866, h876, h919, h921, h927, h977, h979, h985, h1000, h1039, h1041, h1079, h2479, h2594, h2722, h2766, reducedSource1491] using sourceEq1746 B hB

theorem rowSound1491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1491 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1491, numericCheck1491, reducedZero1491 B hB hF, mul_zero]

theorem reducedZero1494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1494 (mixedVector B) = 0 := by
  have h1033 : mixedVector B (Sum.inr 1033) = Sparse.eval nodeValue1033 (mixedVector B) := by
    change mixedMoment B node1033 node1033Labels = _
    exact sound1033 B hB hF
  have h2015 : mixedVector B (Sum.inr 2015) = Sparse.eval nodeValue2015 (mixedVector B) := by
    change mixedMoment B node2015 node2015Labels = _
    exact sound2015 B hB hF
  have h2099 : mixedVector B (Sum.inr 2099) = Sparse.eval nodeValue2099 (mixedVector B) := by
    change mixedMoment B node2099 node2099Labels = _
    exact sound2099 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1749, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1033, h2015, h2099, h2203, h2259, h2261, h4081, reducedSource1494] using sourceEq1749 B hB

theorem rowSound1494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1494 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1494, numericCheck1494, reducedZero1494 B hB hF, mul_zero]

theorem reducedZero1495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1495 (mixedVector B) = 0 := by
  have h981 : mixedVector B (Sum.inr 981) = Sparse.eval nodeValue981 (mixedVector B) := by
    change mixedMoment B node981 node981Labels = _
    exact sound981 B hB hF
  have h1913 : mixedVector B (Sum.inr 1913) = Sparse.eval nodeValue1913 (mixedVector B) := by
    change mixedMoment B node1913 node1913Labels = _
    exact sound1913 B hB hF
  have h2078 : mixedVector B (Sum.inr 2078) = Sparse.eval nodeValue2078 (mixedVector B) := by
    change mixedMoment B node2078 node2078Labels = _
    exact sound2078 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1750, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h981, h1913, h2078, h2192, h2196, h2202, h4080, reducedSource1495] using sourceEq1750 B hB

theorem rowSound1495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1495 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1495, numericCheck1495, reducedZero1495 B hB hF, mul_zero]

theorem reducedZero1496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1496 (mixedVector B) = 0 := by
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h978 : mixedVector B (Sum.inr 978) = Sparse.eval nodeValue978 (mixedVector B) := by
    change mixedMoment B node978 node978Labels = _
    exact sound978 B hB hF
  have h981 : mixedVector B (Sum.inr 981) = Sparse.eval nodeValue981 (mixedVector B) := by
    change mixedMoment B node981 node981Labels = _
    exact sound981 B hB hF
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1032 : mixedVector B (Sum.inr 1032) = Sparse.eval nodeValue1032 (mixedVector B) := by
    change mixedMoment B node1032 node1032Labels = _
    exact sound1032 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1751, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h977, h978, h981, h998, h1032, h2202, h4080, reducedSource1496] using sourceEq1751 B hB

theorem rowSound1496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1496 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1496, numericCheck1496, reducedZero1496 B hB hF, mul_zero]

theorem reducedZero1497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1497 (mixedVector B) = 0 := by
  have h978 : mixedVector B (Sum.inr 978) = Sparse.eval nodeValue978 (mixedVector B) := by
    change mixedMoment B node978 node978Labels = _
    exact sound978 B hB hF
  have h1909 : mixedVector B (Sum.inr 1909) = Sparse.eval nodeValue1909 (mixedVector B) := by
    change mixedMoment B node1909 node1909Labels = _
    exact sound1909 B hB hF
  have h2076 : mixedVector B (Sum.inr 2076) = Sparse.eval nodeValue2076 (mixedVector B) := by
    change mixedMoment B node2076 node2076Labels = _
    exact sound2076 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1752, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h978, h1909, h2076, h2195, h2202, h2206, h4080, reducedSource1497] using sourceEq1752 B hB

theorem rowSound1497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1497 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1497, numericCheck1497, reducedZero1497 B hB hF, mul_zero]

theorem reducedZero1498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1498 (mixedVector B) = 0 := by
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h1912 : mixedVector B (Sum.inr 1912) = Sparse.eval nodeValue1912 (mixedVector B) := by
    change mixedMoment B node1912 node1912Labels = _
    exact sound1912 B hB hF
  have h2077 : mixedVector B (Sum.inr 2077) = Sparse.eval nodeValue2077 (mixedVector B) := by
    change mixedMoment B node2077 node2077Labels = _
    exact sound2077 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1753, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h980, h1912, h2077, h2191, h2204, h4079, reducedSource1498] using sourceEq1753 B hB

theorem rowSound1498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1498 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1498, numericCheck1498, reducedZero1498 B hB hF, mul_zero]

theorem reducedZero1499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1499 (mixedVector B) = 0 := by
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h1003 : mixedVector B (Sum.inr 1003) = Sparse.eval nodeValue1003 (mixedVector B) := by
    change mixedMoment B node1003 node1003Labels = _
    exact sound1003 B hB hF
  have h1034 : mixedVector B (Sum.inr 1034) = Sparse.eval nodeValue1034 (mixedVector B) := by
    change mixedMoment B node1034 node1034Labels = _
    exact sound1034 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1756, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h980, h1003, h1034, h2204, h4079, reducedSource1499] using sourceEq1756 B hB

theorem rowSound1499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1499 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1499, numericCheck1499, reducedZero1499 B hB hF, mul_zero]

theorem reducedZero1500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1500 (mixedVector B) = 0 := by
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h1908 : mixedVector B (Sum.inr 1908) = Sparse.eval nodeValue1908 (mixedVector B) := by
    change mixedMoment B node1908 node1908Labels = _
    exact sound1908 B hB hF
  have h2075 : mixedVector B (Sum.inr 2075) = Sparse.eval nodeValue2075 (mixedVector B) := by
    change mixedMoment B node2075 node2075Labels = _
    exact sound2075 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1759, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h977, h1908, h2075, h2190, h2202, h2205, h4080, reducedSource1500] using sourceEq1759 B hB

theorem rowSound1500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1500 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1500, numericCheck1500, reducedZero1500 B hB hF, mul_zero]

theorem reducedZero1501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1501 (mixedVector B) = 0 := by
  have h865 : mixedVector B (Sum.inr 865) = Sparse.eval nodeValue865 (mixedVector B) := by
    change mixedMoment B node865 node865Labels = _
    exact sound865 B hB hF
  have h866 : mixedVector B (Sum.inr 866) = Sparse.eval nodeValue866 (mixedVector B) := by
    change mixedMoment B node866 node866Labels = _
    exact sound866 B hB hF
  have h869 : mixedVector B (Sum.inr 869) = Sparse.eval nodeValue869 (mixedVector B) := by
    change mixedMoment B node869 node869Labels = _
    exact sound869 B hB hF
  have h878 : mixedVector B (Sum.inr 878) = Sparse.eval nodeValue878 (mixedVector B) := by
    change mixedMoment B node878 node878Labels = _
    exact sound878 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h1908 : mixedVector B (Sum.inr 1908) = Sparse.eval nodeValue1908 (mixedVector B) := by
    change mixedMoment B node1908 node1908Labels = _
    exact sound1908 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1761, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h865, h866, h869, h878, h977, h1908, h4080, reducedSource1501] using sourceEq1761 B hB

theorem rowSound1501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1501 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1501, numericCheck1501, reducedZero1501 B hB hF, mul_zero]

theorem reducedZero1502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1502 (mixedVector B) = 0 := by
  have h699 : mixedVector B (Sum.inr 699) = Sparse.eval nodeValue699 (mixedVector B) := by
    change mixedMoment B node699 node699Labels = _
    exact sound699 B hB hF
  have h700 : mixedVector B (Sum.inr 700) = Sparse.eval nodeValue700 (mixedVector B) := by
    change mixedMoment B node700 node700Labels = _
    exact sound700 B hB hF
  have h703 : mixedVector B (Sum.inr 703) = Sparse.eval nodeValue703 (mixedVector B) := by
    change mixedMoment B node703 node703Labels = _
    exact sound703 B hB hF
  have h712 : mixedVector B (Sum.inr 712) = Sparse.eval nodeValue712 (mixedVector B) := by
    change mixedMoment B node712 node712Labels = _
    exact sound712 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h1597 : mixedVector B (Sum.inr 1597) = Sparse.eval nodeValue1597 (mixedVector B) := by
    change mixedMoment B node1597 node1597Labels = _
    exact sound1597 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1762, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h699, h700, h703, h712, h806, h1597, h4069, reducedSource1502] using sourceEq1762 B hB

theorem rowSound1502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1502 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1502, numericCheck1502, reducedZero1502 B hB hF, mul_zero]

theorem reducedZero1503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1503 (mixedVector B) = 0 := by
  have h976 : mixedVector B (Sum.inr 976) = Sparse.eval nodeValue976 (mixedVector B) := by
    change mixedMoment B node976 node976Labels = _
    exact sound976 B hB hF
  have h1907 : mixedVector B (Sum.inr 1907) = Sparse.eval nodeValue1907 (mixedVector B) := by
    change mixedMoment B node1907 node1907Labels = _
    exact sound1907 B hB hF
  have h2074 : mixedVector B (Sum.inr 2074) = Sparse.eval nodeValue2074 (mixedVector B) := by
    change mixedMoment B node2074 node2074Labels = _
    exact sound2074 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1763, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h976, h1907, h2074, h2201, h2203, h4081, reducedSource1503] using sourceEq1763 B hB

theorem rowSound1503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1503 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1503, numericCheck1503, reducedZero1503 B hB hF, mul_zero]

theorem sourceRowsAt1488 : MixedData.sourceRows (1488 : Fin 2425) =
    MixedData.row1488 := by decide +kernel

theorem sourceRowsAt1489 : MixedData.sourceRows (1489 : Fin 2425) =
    MixedData.row1489 := by decide +kernel

theorem sourceRowsAt1490 : MixedData.sourceRows (1490 : Fin 2425) =
    MixedData.row1490 := by decide +kernel

theorem sourceRowsAt1491 : MixedData.sourceRows (1491 : Fin 2425) =
    MixedData.row1491 := by decide +kernel

theorem sourceRowsAt1492 : MixedData.sourceRows (1492 : Fin 2425) =
    MixedData.row1492 := by decide +kernel

theorem sourceRowsAt1493 : MixedData.sourceRows (1493 : Fin 2425) =
    MixedData.row1493 := by decide +kernel

theorem sourceRowsAt1494 : MixedData.sourceRows (1494 : Fin 2425) =
    MixedData.row1494 := by decide +kernel

theorem sourceRowsAt1495 : MixedData.sourceRows (1495 : Fin 2425) =
    MixedData.row1495 := by decide +kernel

theorem sourceRowsAt1496 : MixedData.sourceRows (1496 : Fin 2425) =
    MixedData.row1496 := by decide +kernel

theorem sourceRowsAt1497 : MixedData.sourceRows (1497 : Fin 2425) =
    MixedData.row1497 := by decide +kernel

theorem sourceRowsAt1498 : MixedData.sourceRows (1498 : Fin 2425) =
    MixedData.row1498 := by decide +kernel

theorem sourceRowsAt1499 : MixedData.sourceRows (1499 : Fin 2425) =
    MixedData.row1499 := by decide +kernel

theorem sourceRowsAt1500 : MixedData.sourceRows (1500 : Fin 2425) =
    MixedData.row1500 := by decide +kernel

theorem sourceRowsAt1501 : MixedData.sourceRows (1501 : Fin 2425) =
    MixedData.row1501 := by decide +kernel

theorem sourceRowsAt1502 : MixedData.sourceRows (1502 : Fin 2425) =
    MixedData.row1502 := by decide +kernel

theorem sourceRowsAt1503 : MixedData.sourceRows (1503 : Fin 2425) =
    MixedData.row1503 := by decide +kernel

theorem chunkSound93_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 93) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1488 ∨ k.val = 1489 ∨ k.val = 1490 ∨ k.val = 1491 ∨ k.val = 1492 ∨ k.val = 1493 ∨ k.val = 1494 ∨ k.val = 1495 ∨ k.val = 1496 ∨ k.val = 1497 ∨ k.val = 1498 ∨ k.val = 1499 ∨ k.val = 1500 ∨ k.val = 1501 ∨ k.val = 1502 ∨ k.val = 1503 := by omega
  rcases heq with h1488 | h1489 | h1490 | h1491 | h1492 | h1493 | h1494 | h1495 | h1496 | h1497 | h1498 | h1499 | h1500 | h1501 | h1502 | h1503
  · have he : k = (1488 : Fin 2425) := Fin.ext h1488
    subst k
    rw [sourceRowsAt1488]
    exact rowSound1488 B hB hF
  · have he : k = (1489 : Fin 2425) := Fin.ext h1489
    subst k
    rw [sourceRowsAt1489]
    exact rowSound1489 B hB hF
  · have he : k = (1490 : Fin 2425) := Fin.ext h1490
    subst k
    rw [sourceRowsAt1490]
    exact rowSound1490 B hB hF
  · have he : k = (1491 : Fin 2425) := Fin.ext h1491
    subst k
    rw [sourceRowsAt1491]
    exact rowSound1491 B hB hF
  · have he : k = (1492 : Fin 2425) := Fin.ext h1492
    subst k
    rw [sourceRowsAt1492]
    exact rowSound1492_e B hB hF
  · have he : k = (1493 : Fin 2425) := Fin.ext h1493
    subst k
    rw [sourceRowsAt1493]
    exact rowSound1493_e B hB hF
  · have he : k = (1494 : Fin 2425) := Fin.ext h1494
    subst k
    rw [sourceRowsAt1494]
    exact rowSound1494 B hB hF
  · have he : k = (1495 : Fin 2425) := Fin.ext h1495
    subst k
    rw [sourceRowsAt1495]
    exact rowSound1495 B hB hF
  · have he : k = (1496 : Fin 2425) := Fin.ext h1496
    subst k
    rw [sourceRowsAt1496]
    exact rowSound1496 B hB hF
  · have he : k = (1497 : Fin 2425) := Fin.ext h1497
    subst k
    rw [sourceRowsAt1497]
    exact rowSound1497 B hB hF
  · have he : k = (1498 : Fin 2425) := Fin.ext h1498
    subst k
    rw [sourceRowsAt1498]
    exact rowSound1498 B hB hF
  · have he : k = (1499 : Fin 2425) := Fin.ext h1499
    subst k
    rw [sourceRowsAt1499]
    exact rowSound1499 B hB hF
  · have he : k = (1500 : Fin 2425) := Fin.ext h1500
    subst k
    rw [sourceRowsAt1500]
    exact rowSound1500 B hB hF
  · have he : k = (1501 : Fin 2425) := Fin.ext h1501
    subst k
    rw [sourceRowsAt1501]
    exact rowSound1501 B hB hF
  · have he : k = (1502 : Fin 2425) := Fin.ext h1502
    subst k
    rw [sourceRowsAt1502]
    exact rowSound1502 B hB hF
  · have he : k = (1503 : Fin 2425) := Fin.ext h1503
    subst k
    rw [sourceRowsAt1503]
    exact rowSound1503 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound93_e_oai
