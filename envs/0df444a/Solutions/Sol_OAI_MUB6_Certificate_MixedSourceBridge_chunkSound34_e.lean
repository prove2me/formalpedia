-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:25:19.092115+00:00
-- url     : https://prove2.me/submissions/2a8eddb2-c459-423e-baff-c9e6794bde5a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound545_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound546_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound547_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound548_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound551_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound552_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound553_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound554_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound555_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound558_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1740 raw1740Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw1740 raw1740Labels = mixedMoment B raw1740step0 raw1740step0Labels := by
      have ha : raw1740step0 = (fun i j => raw1740 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1740step0 raw1740; decide +kernel
      have hl : raw1740step0Labels = raw1740Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1740 raw1740Labels permutation152 permutation4
    mixedMoment B raw1740step0 raw1740step0Labels = mixedMoment B raw1740step1 raw1740step1Labels := by
      have ha : raw1740step1 = raw1740step0 := by apply Matrix.ext; unfold raw1740step1 raw1740step0; decide +kernel
      have hl : raw1740step0Labels = labelEmbedding7 ∘ raw1740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1740step0 raw1740step0Labels raw1740step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1741 raw1741Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw1741 raw1741Labels = mixedMoment B raw1741step0 raw1741step0Labels := by
      have ha : raw1741step0 = (fun i j => raw1741 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1741step0 raw1741; decide +kernel
      have hl : raw1741step0Labels = raw1741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1741 raw1741Labels permutation152 permutation4
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1742 raw1742Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw1742 raw1742Labels = mixedMoment B raw1742step0 raw1742step0Labels := by
      have ha : raw1742step0 = (fun i j => raw1742 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1742step0 raw1742; decide +kernel
      have hl : raw1742step0Labels = raw1742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1742 raw1742Labels permutation170 permutation6
    mixedMoment B raw1742step0 raw1742step0Labels = mixedMoment B raw1742step1 raw1742step1Labels := by
      have ha : raw1742step1 = -raw1742step0 := by apply Matrix.ext; change ∀ i j, raw1742step1 i j = -(raw1742step0 i j); unfold raw1742step1 raw1742step0; decide +kernel
      have hl : raw1742step1Labels = raw1742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1742step1 raw1742step1Labels = mixedMoment B raw1742step2 raw1742step2Labels := by
      have ha : raw1742step2 = raw1742step1 := by apply Matrix.ext; unfold raw1742step2 raw1742step1; decide +kernel
      have hl : raw1742step1Labels = labelEmbedding1 ∘ raw1742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1742step1 raw1742step1Labels raw1742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

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

theorem canonical1800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1800 raw1800Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw1800 raw1800Labels = mixedMoment B raw1800step0 raw1800step0Labels := by
      have ha : raw1800step0 = (fun i j => raw1800 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1800step0 raw1800; decide +kernel
      have hl : raw1800step0Labels = raw1800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1800 raw1800Labels permutation32 permutation4
    mixedMoment B raw1800step0 raw1800step0Labels = mixedMoment B raw1800step1 raw1800step1Labels := by
      have ha : raw1800step1 = raw1800step0 := by apply Matrix.ext; unfold raw1800step1 raw1800step0; decide +kernel
      have hl : raw1800step0Labels = labelEmbedding7 ∘ raw1800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1800step0 raw1800step0Labels raw1800step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1801 raw1801Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw1801 raw1801Labels = mixedMoment B raw1801step0 raw1801step0Labels := by
      have ha : raw1801step0 = (fun i j => raw1801 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1801step0 raw1801; decide +kernel
      have hl : raw1801step0Labels = raw1801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1801 raw1801Labels permutation32 permutation4
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1802 raw1802Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw1802 raw1802Labels = mixedMoment B raw1802step0 raw1802step0Labels := by
      have ha : raw1802step0 = (fun i j => raw1802 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1802step0 raw1802; decide +kernel
      have hl : raw1802step0Labels = raw1802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1802 raw1802Labels permutation50 permutation6
    mixedMoment B raw1802step0 raw1802step0Labels = mixedMoment B raw1802step1 raw1802step1Labels := by
      have ha : raw1802step1 = -raw1802step0 := by apply Matrix.ext; change ∀ i j, raw1802step1 i j = -(raw1802step0 i j); unfold raw1802step1 raw1802step0; decide +kernel
      have hl : raw1802step1Labels = raw1802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1802step1 raw1802step1Labels = mixedMoment B raw1802step2 raw1802step2Labels := by
      have ha : raw1802step2 = raw1802step1 := by apply Matrix.ext; unfold raw1802step2 raw1802step1; decide +kernel
      have hl : raw1802step1Labels = labelEmbedding1 ∘ raw1802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1802step1 raw1802step1Labels raw1802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

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

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

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

theorem canonical2310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2310 raw2310Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2310 raw2310Labels = mixedMoment B raw2310step0 raw2310step0Labels := by
      have ha : raw2310step0 = (fun i j => raw2310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2310step0 raw2310; decide +kernel
      have hl : raw2310step0Labels = raw2310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2310 raw2310Labels permutation32 permutation5
    mixedMoment B raw2310step0 raw2310step0Labels = mixedMoment B raw2310step1 raw2310step1Labels := by
      have ha : raw2310step1 = raw2310step0 := by apply Matrix.ext; unfold raw2310step1 raw2310step0; decide +kernel
      have hl : raw2310step0Labels = labelEmbedding8 ∘ raw2310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2310step0 raw2310step0Labels raw2310step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical2311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2311 raw2311Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw2311 raw2311Labels = mixedMoment B raw2311step0 raw2311step0Labels := by
      have ha : raw2311step0 = (fun i j => raw2311 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2311step0 raw2311; decide +kernel
      have hl : raw2311step0Labels = raw2311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2311 raw2311Labels permutation32 permutation4
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical2312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2312 raw2312Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw2312 raw2312Labels = mixedMoment B raw2312step0 raw2312step0Labels := by
      have ha : raw2312step0 = (fun i j => raw2312 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2312step0 raw2312; decide +kernel
      have hl : raw2312step0Labels = raw2312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2312 raw2312Labels permutation41 permutation3
    mixedMoment B raw2312step0 raw2312step0Labels = mixedMoment B raw2312step1 raw2312step1Labels := by
      have ha : raw2312step1 = -raw2312step0 := by apply Matrix.ext; change ∀ i j, raw2312step1 i j = -(raw2312step0 i j); unfold raw2312step1 raw2312step0; decide +kernel
      have hl : raw2312step1Labels = raw2312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2312step1 raw2312step1Labels = mixedMoment B raw2312step2 raw2312step2Labels := by
      have ha : raw2312step2 = raw2312step1 := by apply Matrix.ext; unfold raw2312step2 raw2312step1; decide +kernel
      have hl : raw2312step1Labels = labelEmbedding1 ∘ raw2312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2312step1 raw2312step1Labels raw2312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10762 raw10762Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw10762 raw10762Labels = mixedMoment B raw10762step0 raw10762step0Labels := by
      have hz : ∀ j, raw10762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10762step0 = (fun i j => raw10762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10762step0 raw10762; decide +kernel
      have hl : raw10762step0Labels = raw10762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10762 raw10762Labels permutation434 hz
    mixedMoment B raw10762step0 raw10762step0Labels = mixedMoment B raw10762step1 raw10762step1Labels := by
      have hz : ∀ j, raw10762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10762step1 = (fun i j => raw10762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10762step1 raw10762step0; decide +kernel
      have hl : raw10762step1Labels = raw10762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10762step0 raw10762step0Labels permutation80 hz
    mixedMoment B raw10762step1 raw10762step1Labels = mixedMoment B raw10762step2 raw10762step2Labels := by
      have ha : raw10762step2 = (fun i j => raw10762step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10762step2 raw10762step1; decide +kernel
      have hl : raw10762step2Labels = raw10762step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10762step1 raw10762step1Labels permutation10 permutation2
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical10763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10763 raw10763Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw10763 raw10763Labels = mixedMoment B raw10763step0 raw10763step0Labels := by
      have hz : ∀ j, raw10763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10763step0 = (fun i j => raw10763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10763step0 raw10763; decide +kernel
      have hl : raw10763step0Labels = raw10763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10763 raw10763Labels permutation434 hz
    mixedMoment B raw10763step0 raw10763step0Labels = mixedMoment B raw10763step1 raw10763step1Labels := by
      have hz : ∀ j, raw10763step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10763step1 = (fun i j => raw10763step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10763step1 raw10763step0; decide +kernel
      have hl : raw10763step1Labels = raw10763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10763step0 raw10763step0Labels permutation80 hz
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical10764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10764 raw10764Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw10764 raw10764Labels = mixedMoment B raw10764step0 raw10764step0Labels := by
      have hz : ∀ j, raw10764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10764step0 = (fun i j => raw10764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10764step0 raw10764; decide +kernel
      have hl : raw10764step0Labels = raw10764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10764 raw10764Labels permutation434 hz
    mixedMoment B raw10764step0 raw10764step0Labels = mixedMoment B raw10764step1 raw10764step1Labels := by
      have ha : raw10764step1 = (fun i j => raw10764step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10764step1 raw10764step0; decide +kernel
      have hl : raw10764step1Labels = raw10764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10764step0 raw10764step0Labels permutation40 permutation2
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical10765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10765 raw10765Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw10765 raw10765Labels = mixedMoment B raw10765step0 raw10765step0Labels := by
      have hz : ∀ j, raw10765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10765step0 = (fun i j => raw10765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10765step0 raw10765; decide +kernel
      have hl : raw10765step0Labels = raw10765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10765 raw10765Labels permutation346 hz
    mixedMoment B raw10765step0 raw10765step0Labels = mixedMoment B raw10765step1 raw10765step1Labels := by
      have ha : raw10765step1 = (fun i j => raw10765step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10765step1 raw10765step0; decide +kernel
      have hl : raw10765step1Labels = raw10765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10765step0 raw10765step0Labels permutation40 permutation2
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical10766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10766 raw10766Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw10766 raw10766Labels = mixedMoment B raw10766step0 raw10766step0Labels := by
      have hz : ∀ j, raw10766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10766step0 = (fun i j => raw10766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10766step0 raw10766; decide +kernel
      have hl : raw10766step0Labels = raw10766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10766 raw10766Labels permutation434 hz
    mixedMoment B raw10766step0 raw10766step0Labels = mixedMoment B raw10766step1 raw10766step1Labels := by
      have hz : ∀ j, raw10766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10766step1 = (fun i j => raw10766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10766step1 raw10766step0; decide +kernel
      have hl : raw10766step1Labels = raw10766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10766step0 raw10766step0Labels permutation80 hz
    mixedMoment B raw10766step1 raw10766step1Labels = mixedMoment B raw10766step2 raw10766step2Labels := by
      have ha : raw10766step2 = (fun i j => raw10766step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10766step2 raw10766step1; decide +kernel
      have hl : raw10766step2Labels = raw10766step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10766step1 raw10766step1Labels permutation10 permutation2
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical10767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10767 raw10767Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw10767 raw10767Labels = mixedMoment B raw10767step0 raw10767step0Labels := by
      have hz : ∀ j, raw10767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10767step0 = (fun i j => raw10767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10767step0 raw10767; decide +kernel
      have hl : raw10767step0Labels = raw10767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10767 raw10767Labels permutation434 hz
    mixedMoment B raw10767step0 raw10767step0Labels = mixedMoment B raw10767step1 raw10767step1Labels := by
      have hz : ∀ j, raw10767step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10767step1 = (fun i j => raw10767step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10767step1 raw10767step0; decide +kernel
      have hl : raw10767step1Labels = raw10767step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10767step0 raw10767step0Labels permutation80 hz
    mixedMoment B raw10767step1 raw10767step1Labels = mixedMoment B raw10767step2 raw10767step2Labels := by
      have ha : raw10767step2 = (fun i j => raw10767step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10767step2 raw10767step1; decide +kernel
      have hl : raw10767step2Labels = raw10767step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10767step1 raw10767step1Labels permutation13 permutation2
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical10768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10768 raw10768Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw10768 raw10768Labels = mixedMoment B raw10768step0 raw10768step0Labels := by
      have hz : ∀ j, raw10768 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw10768step0 = (fun i j => raw10768 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw10768step0 raw10768; decide +kernel
      have hl : raw10768step0Labels = raw10768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10768 raw10768Labels permutation590 hz
    mixedMoment B raw10768step0 raw10768step0Labels = mixedMoment B raw10768step1 raw10768step1Labels := by
      have hz : ∀ j, raw10768step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10768step1 = (fun i j => raw10768step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10768step1 raw10768step0; decide +kernel
      have hl : raw10768step1Labels = raw10768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10768step0 raw10768step0Labels permutation104 hz
    mixedMoment B raw10768step1 raw10768step1Labels = mixedMoment B raw10768step2 raw10768step2Labels := by
      have hz : ∀ j, raw10768step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10768step2 = (fun i j => raw10768step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10768step2 raw10768step1; decide +kernel
      have hl : raw10768step2Labels = raw10768step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10768step1 raw10768step1Labels permutation20 hz
    mixedMoment B raw10768step2 raw10768step2Labels = mixedMoment B raw10768step3 raw10768step3Labels := by
      have ha : raw10768step3 = (fun i j => raw10768step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10768step3 raw10768step2; decide +kernel
      have hl : raw10768step3Labels = raw10768step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10768step2 raw10768step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10889 raw10889Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw10889 raw10889Labels = mixedMoment B raw10889step0 raw10889step0Labels := by
      have hz : ∀ j, raw10889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10889step0 = (fun i j => raw10889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10889step0 raw10889; decide +kernel
      have hl : raw10889step0Labels = raw10889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10889 raw10889Labels permutation434 hz
    mixedMoment B raw10889step0 raw10889step0Labels = mixedMoment B raw10889step1 raw10889step1Labels := by
      have hz : ∀ j, raw10889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10889step1 = (fun i j => raw10889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10889step1 raw10889step0; decide +kernel
      have hl : raw10889step1Labels = raw10889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10889step0 raw10889step0Labels permutation80 hz
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical10890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10890 raw10890Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw10890 raw10890Labels = mixedMoment B raw10890step0 raw10890step0Labels := by
      have hz : ∀ j, raw10890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10890step0 = (fun i j => raw10890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10890step0 raw10890; decide +kernel
      have hl : raw10890step0Labels = raw10890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10890 raw10890Labels permutation434 hz
    mixedMoment B raw10890step0 raw10890step0Labels = mixedMoment B raw10890step1 raw10890step1Labels := by
      have hz : ∀ j, raw10890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10890step1 = (fun i j => raw10890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10890step1 raw10890step0; decide +kernel
      have hl : raw10890step1Labels = raw10890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10890step0 raw10890step0Labels permutation80 hz
    mixedMoment B raw10890step1 raw10890step1Labels = mixedMoment B raw10890step2 raw10890step2Labels := by
      have ha : raw10890step2 = (fun i j => raw10890step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10890step2 raw10890step1; decide +kernel
      have hl : raw10890step2Labels = raw10890step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10890step1 raw10890step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical10891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10891 raw10891Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw10891 raw10891Labels = mixedMoment B raw10891step0 raw10891step0Labels := by
      have hz : ∀ j, raw10891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10891step0 = (fun i j => raw10891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10891step0 raw10891; decide +kernel
      have hl : raw10891step0Labels = raw10891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10891 raw10891Labels permutation434 hz
    _ = mixedMoment B node1057 node1057Labels := by rfl

theorem canonical10892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10892 raw10892Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw10892 raw10892Labels = mixedMoment B raw10892step0 raw10892step0Labels := by
      have hz : ∀ j, raw10892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10892step0 = (fun i j => raw10892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10892step0 raw10892; decide +kernel
      have hl : raw10892step0Labels = raw10892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10892 raw10892Labels permutation346 hz
    _ = mixedMoment B node1057 node1057Labels := by rfl

theorem canonical10893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10893 raw10893Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw10893 raw10893Labels = mixedMoment B raw10893step0 raw10893step0Labels := by
      have hz : ∀ j, raw10893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10893step0 = (fun i j => raw10893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10893step0 raw10893; decide +kernel
      have hl : raw10893step0Labels = raw10893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10893 raw10893Labels permutation434 hz
    mixedMoment B raw10893step0 raw10893step0Labels = mixedMoment B raw10893step1 raw10893step1Labels := by
      have hz : ∀ j, raw10893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10893step1 = (fun i j => raw10893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10893step1 raw10893step0; decide +kernel
      have hl : raw10893step1Labels = raw10893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10893step0 raw10893step0Labels permutation80 hz
    _ = mixedMoment B node1063 node1063Labels := by rfl

theorem canonical10894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10894 raw10894Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw10894 raw10894Labels = mixedMoment B raw10894step0 raw10894step0Labels := by
      have hz : ∀ j, raw10894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10894step0 = (fun i j => raw10894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10894step0 raw10894; decide +kernel
      have hl : raw10894step0Labels = raw10894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10894 raw10894Labels permutation434 hz
    mixedMoment B raw10894step0 raw10894step0Labels = mixedMoment B raw10894step1 raw10894step1Labels := by
      have hz : ∀ j, raw10894step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10894step1 = (fun i j => raw10894step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10894step1 raw10894step0; decide +kernel
      have hl : raw10894step1Labels = raw10894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10894step0 raw10894step0Labels permutation80 hz
    _ = mixedMoment B node1059 node1059Labels := by rfl

theorem canonical10895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10895 raw10895Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw10895 raw10895Labels = mixedMoment B raw10895step0 raw10895step0Labels := by
      have hz : ∀ j, raw10895 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10895step0 = (fun i j => raw10895 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10895step0 raw10895; decide +kernel
      have hl : raw10895step0Labels = raw10895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10895 raw10895Labels permutation520 hz
    mixedMoment B raw10895step0 raw10895step0Labels = mixedMoment B raw10895step1 raw10895step1Labels := by
      have hz : ∀ j, raw10895step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10895step1 = (fun i j => raw10895step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10895step1 raw10895step0; decide +kernel
      have hl : raw10895step1Labels = raw10895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10895step0 raw10895step0Labels permutation104 hz
    mixedMoment B raw10895step1 raw10895step1Labels = mixedMoment B raw10895step2 raw10895step2Labels := by
      have hz : ∀ j, raw10895step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10895step2 = (fun i j => raw10895step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10895step2 raw10895step1; decide +kernel
      have hl : raw10895step2Labels = raw10895step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10895step1 raw10895step1Labels permutation20 hz
    mixedMoment B raw10895step2 raw10895step2Labels = mixedMoment B raw10895step3 raw10895step3Labels := by
      have ha : raw10895step3 = (fun i j => raw10895step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10895step3 raw10895step2; decide +kernel
      have hl : raw10895step3Labels = raw10895step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10895step2 raw10895step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical10896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10896 raw10896Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw10896 raw10896Labels = mixedMoment B raw10896step0 raw10896step0Labels := by
      have hz : ∀ j, raw10896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10896step0 = (fun i j => raw10896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10896step0 raw10896; decide +kernel
      have hl : raw10896step0Labels = raw10896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10896 raw10896Labels permutation434 hz
    mixedMoment B raw10896step0 raw10896step0Labels = mixedMoment B raw10896step1 raw10896step1Labels := by
      have ha : raw10896step1 = (fun i j => raw10896step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10896step1 raw10896step0; decide +kernel
      have hl : raw10896step1Labels = raw10896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10896step0 raw10896step0Labels permutation40 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical10897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10897 raw10897Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw10897 raw10897Labels = mixedMoment B raw10897step0 raw10897step0Labels := by
      have hz : ∀ j, raw10897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10897step0 = (fun i j => raw10897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10897step0 raw10897; decide +kernel
      have hl : raw10897step0Labels = raw10897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10897 raw10897Labels permutation346 hz
    mixedMoment B raw10897step0 raw10897step0Labels = mixedMoment B raw10897step1 raw10897step1Labels := by
      have ha : raw10897step1 = (fun i j => raw10897step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10897step1 raw10897step0; decide +kernel
      have hl : raw10897step1Labels = raw10897step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10897step0 raw10897step0Labels permutation40 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical10898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10898 raw10898Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw10898 raw10898Labels = mixedMoment B raw10898step0 raw10898step0Labels := by
      have hz : ∀ j, raw10898 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10898step0 = (fun i j => raw10898 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10898step0 raw10898; decide +kernel
      have hl : raw10898step0Labels = raw10898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10898 raw10898Labels permutation520 hz
    mixedMoment B raw10898step0 raw10898step0Labels = mixedMoment B raw10898step1 raw10898step1Labels := by
      have hz : ∀ j, raw10898step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10898step1 = (fun i j => raw10898step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10898step1 raw10898step0; decide +kernel
      have hl : raw10898step1Labels = raw10898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10898step0 raw10898step0Labels permutation104 hz
    mixedMoment B raw10898step1 raw10898step1Labels = mixedMoment B raw10898step2 raw10898step2Labels := by
      have hz : ∀ j, raw10898step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10898step2 = (fun i j => raw10898step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10898step2 raw10898step1; decide +kernel
      have hl : raw10898step2Labels = raw10898step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10898step1 raw10898step1Labels permutation20 hz
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical10899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10899 raw10899Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw10899 raw10899Labels = mixedMoment B raw10899step0 raw10899step0Labels := by
      have hz : ∀ j, raw10899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10899step0 = (fun i j => raw10899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10899step0 raw10899; decide +kernel
      have hl : raw10899step0Labels = raw10899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10899 raw10899Labels permutation434 hz
    mixedMoment B raw10899step0 raw10899step0Labels = mixedMoment B raw10899step1 raw10899step1Labels := by
      have hz : ∀ j, raw10899step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10899step1 = (fun i j => raw10899step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10899step1 raw10899step0; decide +kernel
      have hl : raw10899step1Labels = raw10899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10899step0 raw10899step0Labels permutation80 hz
    mixedMoment B raw10899step1 raw10899step1Labels = mixedMoment B raw10899step2 raw10899step2Labels := by
      have ha : raw10899step2 = (fun i j => raw10899step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10899step2 raw10899step1; decide +kernel
      have hl : raw10899step2Labels = raw10899step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10899step1 raw10899step1Labels permutation11 permutation2
    _ = mixedMoment B node2291 node2291Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11014 raw11014Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw11014 raw11014Labels = mixedMoment B raw11014step0 raw11014step0Labels := by
      have hz : ∀ j, raw11014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11014step0 = (fun i j => raw11014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11014step0 raw11014; decide +kernel
      have hl : raw11014step0Labels = raw11014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11014 raw11014Labels permutation434 hz
    mixedMoment B raw11014step0 raw11014step0Labels = mixedMoment B raw11014step1 raw11014step1Labels := by
      have hz : ∀ j, raw11014step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11014step1 = (fun i j => raw11014step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11014step1 raw11014step0; decide +kernel
      have hl : raw11014step1Labels = raw11014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11014step0 raw11014step0Labels permutation80 hz
    mixedMoment B raw11014step1 raw11014step1Labels = mixedMoment B raw11014step2 raw11014step2Labels := by
      have ha : raw11014step2 = (fun i j => raw11014step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11014step2 raw11014step1; decide +kernel
      have hl : raw11014step2Labels = raw11014step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11014step1 raw11014step1Labels permutation11 permutation4
    mixedMoment B raw11014step2 raw11014step2Labels = mixedMoment B raw11014step3 raw11014step3Labels := by
      have ha : raw11014step3 = -raw11014step2 := by apply Matrix.ext; change ∀ i j, raw11014step3 i j = -(raw11014step2 i j); unfold raw11014step3 raw11014step2; decide +kernel
      have hl : raw11014step3Labels = raw11014step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical11015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11015 raw11015Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw11015 raw11015Labels = mixedMoment B raw11015step0 raw11015step0Labels := by
      have hz : ∀ j, raw11015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11015step0 = (fun i j => raw11015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11015step0 raw11015; decide +kernel
      have hl : raw11015step0Labels = raw11015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11015 raw11015Labels permutation434 hz
    mixedMoment B raw11015step0 raw11015step0Labels = mixedMoment B raw11015step1 raw11015step1Labels := by
      have hz : ∀ j, raw11015step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11015step1 = (fun i j => raw11015step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11015step1 raw11015step0; decide +kernel
      have hl : raw11015step1Labels = raw11015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11015step0 raw11015step0Labels permutation80 hz
    mixedMoment B raw11015step1 raw11015step1Labels = mixedMoment B raw11015step2 raw11015step2Labels := by
      have ha : raw11015step2 = (fun i j => raw11015step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11015step2 raw11015step1; decide +kernel
      have hl : raw11015step2Labels = raw11015step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11015step1 raw11015step1Labels permutation11 permutation4
    mixedMoment B raw11015step2 raw11015step2Labels = mixedMoment B raw11015step3 raw11015step3Labels := by
      have ha : raw11015step3 = -raw11015step2 := by apply Matrix.ext; change ∀ i j, raw11015step3 i j = -(raw11015step2 i j); unfold raw11015step3 raw11015step2; decide +kernel
      have hl : raw11015step3Labels = raw11015step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1047 node1047Labels := by rfl

theorem canonical11016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11016 raw11016Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw11016 raw11016Labels = mixedMoment B raw11016step0 raw11016step0Labels := by
      have hz : ∀ j, raw11016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11016step0 = (fun i j => raw11016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11016step0 raw11016; decide +kernel
      have hl : raw11016step0Labels = raw11016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11016 raw11016Labels permutation434 hz
    mixedMoment B raw11016step0 raw11016step0Labels = mixedMoment B raw11016step1 raw11016step1Labels := by
      have ha : raw11016step1 = (fun i j => raw11016step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11016step1 raw11016step0; decide +kernel
      have hl : raw11016step1Labels = raw11016step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11016step0 raw11016step0Labels permutation47 permutation4
    mixedMoment B raw11016step1 raw11016step1Labels = mixedMoment B raw11016step2 raw11016step2Labels := by
      have ha : raw11016step2 = -raw11016step1 := by apply Matrix.ext; change ∀ i j, raw11016step2 i j = -(raw11016step1 i j); unfold raw11016step2 raw11016step1; decide +kernel
      have hl : raw11016step2Labels = raw11016step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1042 node1042Labels := by rfl

theorem canonical11017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11017 raw11017Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw11017 raw11017Labels = mixedMoment B raw11017step0 raw11017step0Labels := by
      have hz : ∀ j, raw11017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11017step0 = (fun i j => raw11017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11017step0 raw11017; decide +kernel
      have hl : raw11017step0Labels = raw11017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11017 raw11017Labels permutation346 hz
    mixedMoment B raw11017step0 raw11017step0Labels = mixedMoment B raw11017step1 raw11017step1Labels := by
      have ha : raw11017step1 = (fun i j => raw11017step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11017step1 raw11017step0; decide +kernel
      have hl : raw11017step1Labels = raw11017step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11017step0 raw11017step0Labels permutation47 permutation4
    mixedMoment B raw11017step1 raw11017step1Labels = mixedMoment B raw11017step2 raw11017step2Labels := by
      have ha : raw11017step2 = -raw11017step1 := by apply Matrix.ext; change ∀ i j, raw11017step2 i j = -(raw11017step1 i j); unfold raw11017step2 raw11017step1; decide +kernel
      have hl : raw11017step2Labels = raw11017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1042 node1042Labels := by rfl

theorem canonical11018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11018 raw11018Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw11018 raw11018Labels = mixedMoment B raw11018step0 raw11018step0Labels := by
      have hz : ∀ j, raw11018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11018step0 = (fun i j => raw11018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11018step0 raw11018; decide +kernel
      have hl : raw11018step0Labels = raw11018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11018 raw11018Labels permutation434 hz
    mixedMoment B raw11018step0 raw11018step0Labels = mixedMoment B raw11018step1 raw11018step1Labels := by
      have hz : ∀ j, raw11018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11018step1 = (fun i j => raw11018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11018step1 raw11018step0; decide +kernel
      have hl : raw11018step1Labels = raw11018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11018step0 raw11018step0Labels permutation80 hz
    mixedMoment B raw11018step1 raw11018step1Labels = mixedMoment B raw11018step2 raw11018step2Labels := by
      have ha : raw11018step2 = (fun i j => raw11018step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11018step2 raw11018step1; decide +kernel
      have hl : raw11018step2Labels = raw11018step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11018step1 raw11018step1Labels permutation11 permutation4
    mixedMoment B raw11018step2 raw11018step2Labels = mixedMoment B raw11018step3 raw11018step3Labels := by
      have ha : raw11018step3 = -raw11018step2 := by apply Matrix.ext; change ∀ i j, raw11018step3 i j = -(raw11018step2 i j); unfold raw11018step3 raw11018step2; decide +kernel
      have hl : raw11018step3Labels = raw11018step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical11019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11019 raw11019Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw11019 raw11019Labels = mixedMoment B raw11019step0 raw11019step0Labels := by
      have hz : ∀ j, raw11019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11019step0 = (fun i j => raw11019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11019step0 raw11019; decide +kernel
      have hl : raw11019step0Labels = raw11019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11019 raw11019Labels permutation434 hz
    mixedMoment B raw11019step0 raw11019step0Labels = mixedMoment B raw11019step1 raw11019step1Labels := by
      have hz : ∀ j, raw11019step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11019step1 = (fun i j => raw11019step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11019step1 raw11019step0; decide +kernel
      have hl : raw11019step1Labels = raw11019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11019step0 raw11019step0Labels permutation80 hz
    mixedMoment B raw11019step1 raw11019step1Labels = mixedMoment B raw11019step2 raw11019step2Labels := by
      have ha : raw11019step2 = (fun i j => raw11019step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11019step2 raw11019step1; decide +kernel
      have hl : raw11019step2Labels = raw11019step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11019step1 raw11019step1Labels permutation10 permutation4
    mixedMoment B raw11019step2 raw11019step2Labels = mixedMoment B raw11019step3 raw11019step3Labels := by
      have ha : raw11019step3 = -raw11019step2 := by apply Matrix.ext; change ∀ i j, raw11019step3 i j = -(raw11019step2 i j); unfold raw11019step3 raw11019step2; decide +kernel
      have hl : raw11019step3Labels = raw11019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical11020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11020 raw11020Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw11020 raw11020Labels = mixedMoment B raw11020step0 raw11020step0Labels := by
      have hz : ∀ j, raw11020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11020step0 = (fun i j => raw11020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11020step0 raw11020; decide +kernel
      have hl : raw11020step0Labels = raw11020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11020 raw11020Labels permutation434 hz
    mixedMoment B raw11020step0 raw11020step0Labels = mixedMoment B raw11020step1 raw11020step1Labels := by
      have ha : raw11020step1 = (fun i j => raw11020step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11020step1 raw11020step0; decide +kernel
      have hl : raw11020step1Labels = raw11020step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11020step0 raw11020step0Labels permutation50 permutation7
    mixedMoment B raw11020step1 raw11020step1Labels = mixedMoment B raw11020step2 raw11020step2Labels := by
      have ha : raw11020step2 = -raw11020step1 := by apply Matrix.ext; change ∀ i j, raw11020step2 i j = -(raw11020step1 i j); unfold raw11020step2 raw11020step1; decide +kernel
      have hl : raw11020step2Labels = raw11020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11020step2 raw11020step2Labels = mixedMoment B raw11020step3 raw11020step3Labels := by
      have ha : raw11020step3 = raw11020step2 := by apply Matrix.ext; unfold raw11020step3 raw11020step2; decide +kernel
      have hl : raw11020step2Labels = labelEmbedding10 ∘ raw11020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11020step2 raw11020step2Labels raw11020step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical11021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11021 raw11021Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw11021 raw11021Labels = mixedMoment B raw11021step0 raw11021step0Labels := by
      have hz : ∀ j, raw11021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11021step0 = (fun i j => raw11021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11021step0 raw11021; decide +kernel
      have hl : raw11021step0Labels = raw11021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11021 raw11021Labels permutation434 hz
    mixedMoment B raw11021step0 raw11021step0Labels = mixedMoment B raw11021step1 raw11021step1Labels := by
      have ha : raw11021step1 = (fun i j => raw11021step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11021step1 raw11021step0; decide +kernel
      have hl : raw11021step1Labels = raw11021step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11021step0 raw11021step0Labels permutation52 permutation7
    mixedMoment B raw11021step1 raw11021step1Labels = mixedMoment B raw11021step2 raw11021step2Labels := by
      have ha : raw11021step2 = -raw11021step1 := by apply Matrix.ext; change ∀ i j, raw11021step2 i j = -(raw11021step1 i j); unfold raw11021step2 raw11021step1; decide +kernel
      have hl : raw11021step2Labels = raw11021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11021step2 raw11021step2Labels = mixedMoment B raw11021step3 raw11021step3Labels := by
      have ha : raw11021step3 = raw11021step2 := by apply Matrix.ext; unfold raw11021step3 raw11021step2; decide +kernel
      have hl : raw11021step2Labels = labelEmbedding10 ∘ raw11021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11021step2 raw11021step2Labels raw11021step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical11022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11022 raw11022Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11022 raw11022Labels = mixedMoment B raw11022step0 raw11022step0Labels := by
      have ha : raw11022step0 = (fun i j => raw11022 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11022step0 raw11022; decide +kernel
      have hl : raw11022step0Labels = raw11022Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11022 raw11022Labels permutation218 permutation7
    mixedMoment B raw11022step0 raw11022step0Labels = mixedMoment B raw11022step1 raw11022step1Labels := by
      have ha : raw11022step1 = -raw11022step0 := by apply Matrix.ext; change ∀ i j, raw11022step1 i j = -(raw11022step0 i j); unfold raw11022step1 raw11022step0; decide +kernel
      have hl : raw11022step1Labels = raw11022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11022step1 raw11022step1Labels = mixedMoment B raw11022step2 raw11022step2Labels := by
      have ha : raw11022step2 = raw11022step1 := by apply Matrix.ext; unfold raw11022step2 raw11022step1; decide +kernel
      have hl : raw11022step1Labels = labelEmbedding10 ∘ raw11022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11022step1 raw11022step1Labels raw11022step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical11023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11023 raw11023Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw11023 raw11023Labels = mixedMoment B raw11023step0 raw11023step0Labels := by
      have hz : ∀ j, raw11023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11023step0 = (fun i j => raw11023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11023step0 raw11023; decide +kernel
      have hl : raw11023step0Labels = raw11023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11023 raw11023Labels permutation434 hz
    mixedMoment B raw11023step0 raw11023step0Labels = mixedMoment B raw11023step1 raw11023step1Labels := by
      have ha : raw11023step1 = (fun i j => raw11023step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11023step1 raw11023step0; decide +kernel
      have hl : raw11023step1Labels = raw11023step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11023step0 raw11023step0Labels permutation50 permutation7
    mixedMoment B raw11023step1 raw11023step1Labels = mixedMoment B raw11023step2 raw11023step2Labels := by
      have ha : raw11023step2 = -raw11023step1 := by apply Matrix.ext; change ∀ i j, raw11023step2 i j = -(raw11023step1 i j); unfold raw11023step2 raw11023step1; decide +kernel
      have hl : raw11023step2Labels = raw11023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11023step2 raw11023step2Labels = mixedMoment B raw11023step3 raw11023step3Labels := by
      have ha : raw11023step3 = raw11023step2 := by apply Matrix.ext; unfold raw11023step3 raw11023step2; decide +kernel
      have hl : raw11023step2Labels = labelEmbedding10 ∘ raw11023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11023step2 raw11023step2Labels raw11023step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical11024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11024 raw11024Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw11024 raw11024Labels = mixedMoment B raw11024step0 raw11024step0Labels := by
      have hz : ∀ j, raw11024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11024step0 = (fun i j => raw11024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11024step0 raw11024; decide +kernel
      have hl : raw11024step0Labels = raw11024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11024 raw11024Labels permutation434 hz
    mixedMoment B raw11024step0 raw11024step0Labels = mixedMoment B raw11024step1 raw11024step1Labels := by
      have ha : raw11024step1 = (fun i j => raw11024step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11024step1 raw11024step0; decide +kernel
      have hl : raw11024step1Labels = raw11024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11024step0 raw11024step0Labels permutation50 permutation7
    mixedMoment B raw11024step1 raw11024step1Labels = mixedMoment B raw11024step2 raw11024step2Labels := by
      have ha : raw11024step2 = -raw11024step1 := by apply Matrix.ext; change ∀ i j, raw11024step2 i j = -(raw11024step1 i j); unfold raw11024step2 raw11024step1; decide +kernel
      have hl : raw11024step2Labels = raw11024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11024step2 raw11024step2Labels = mixedMoment B raw11024step3 raw11024step3Labels := by
      have ha : raw11024step3 = raw11024step2 := by apply Matrix.ext; unfold raw11024step3 raw11024step2; decide +kernel
      have hl : raw11024step2Labels = labelEmbedding10 ∘ raw11024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11024step2 raw11024step2Labels raw11024step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical11025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11025 raw11025Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw11025 raw11025Labels = mixedMoment B raw11025step0 raw11025step0Labels := by
      have hz : ∀ j, raw11025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11025step0 = (fun i j => raw11025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11025step0 raw11025; decide +kernel
      have hl : raw11025step0Labels = raw11025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11025 raw11025Labels permutation434 hz
    mixedMoment B raw11025step0 raw11025step0Labels = mixedMoment B raw11025step1 raw11025step1Labels := by
      have ha : raw11025step1 = (fun i j => raw11025step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11025step1 raw11025step0; decide +kernel
      have hl : raw11025step1Labels = raw11025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11025step0 raw11025step0Labels permutation38 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical11026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11026 raw11026Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw11026 raw11026Labels = mixedMoment B raw11026step0 raw11026step0Labels := by
      have hz : ∀ j, raw11026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11026step0 = (fun i j => raw11026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11026step0 raw11026; decide +kernel
      have hl : raw11026step0Labels = raw11026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11026 raw11026Labels permutation434 hz
    mixedMoment B raw11026step0 raw11026step0Labels = mixedMoment B raw11026step1 raw11026step1Labels := by
      have ha : raw11026step1 = (fun i j => raw11026step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11026step1 raw11026step0; decide +kernel
      have hl : raw11026step1Labels = raw11026step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11026step0 raw11026step0Labels permutation38 permutation2
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical11027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11027 raw11027Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11027 raw11027Labels = mixedMoment B raw11027step0 raw11027step0Labels := by
      have ha : raw11027step0 = (fun i j => raw11027 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11027step0 raw11027; decide +kernel
      have hl : raw11027step0Labels = raw11027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11027 raw11027Labels permutation206 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical11028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11028 raw11028Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw11028 raw11028Labels = mixedMoment B raw11028step0 raw11028step0Labels := by
      have hz : ∀ j, raw11028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11028step0 = (fun i j => raw11028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11028step0 raw11028; decide +kernel
      have hl : raw11028step0Labels = raw11028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11028 raw11028Labels permutation434 hz
    mixedMoment B raw11028step0 raw11028step0Labels = mixedMoment B raw11028step1 raw11028step1Labels := by
      have ha : raw11028step1 = (fun i j => raw11028step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11028step1 raw11028step0; decide +kernel
      have hl : raw11028step1Labels = raw11028step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11028step0 raw11028step0Labels permutation40 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical11029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11029 raw11029Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw11029 raw11029Labels = mixedMoment B raw11029step0 raw11029step0Labels := by
      have hz : ∀ j, raw11029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11029step0 = (fun i j => raw11029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11029step0 raw11029; decide +kernel
      have hl : raw11029step0Labels = raw11029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11029 raw11029Labels permutation434 hz
    mixedMoment B raw11029step0 raw11029step0Labels = mixedMoment B raw11029step1 raw11029step1Labels := by
      have ha : raw11029step1 = (fun i j => raw11029step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11029step1 raw11029step0; decide +kernel
      have hl : raw11029step1Labels = raw11029step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11029step0 raw11029step0Labels permutation42 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical11030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11030 raw11030Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw11030 raw11030Labels = mixedMoment B raw11030step0 raw11030step0Labels := by
      have hz : ∀ j, raw11030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11030step0 = (fun i j => raw11030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11030step0 raw11030; decide +kernel
      have hl : raw11030step0Labels = raw11030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11030 raw11030Labels permutation434 hz
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical11031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11031 raw11031Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw11031 raw11031Labels = mixedMoment B raw11031step0 raw11031step0Labels := by
      have hz : ∀ j, raw11031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11031step0 = (fun i j => raw11031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11031step0 raw11031; decide +kernel
      have hl : raw11031step0Labels = raw11031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11031 raw11031Labels permutation434 hz
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical11032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11032 raw11032Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11032 raw11032Labels = mixedMoment B raw11032step0 raw11032step0Labels := by
      have ha : raw11032step0 = (fun i j => raw11032 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11032step0 raw11032; decide +kernel
      have hl : raw11032step0Labels = raw11032Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11032 raw11032Labels permutation200 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical11033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11033 raw11033Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw11033 raw11033Labels = mixedMoment B raw11033step0 raw11033step0Labels := by
      have hz : ∀ j, raw11033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11033step0 = (fun i j => raw11033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11033step0 raw11033; decide +kernel
      have hl : raw11033step0Labels = raw11033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11033 raw11033Labels permutation434 hz
    mixedMoment B raw11033step0 raw11033step0Labels = mixedMoment B raw11033step1 raw11033step1Labels := by
      have ha : raw11033step1 = (fun i j => raw11033step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11033step1 raw11033step0; decide +kernel
      have hl : raw11033step1Labels = raw11033step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11033step0 raw11033step0Labels permutation34 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical11034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11034 raw11034Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw11034 raw11034Labels = mixedMoment B raw11034step0 raw11034step0Labels := by
      have hz : ∀ j, raw11034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11034step0 = (fun i j => raw11034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11034step0 raw11034; decide +kernel
      have hl : raw11034step0Labels = raw11034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11034 raw11034Labels permutation434 hz
    mixedMoment B raw11034step0 raw11034step0Labels = mixedMoment B raw11034step1 raw11034step1Labels := by
      have ha : raw11034step1 = (fun i j => raw11034step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11034step1 raw11034step0; decide +kernel
      have hl : raw11034step1Labels = raw11034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11034step0 raw11034step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical11035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11035 raw11035Labels = mixedMoment B node4439 node4439Labels := by
  calc
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical11036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11036 raw11036Labels = mixedMoment B node4852 node4852Labels := by
  calc
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical11037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11037 raw11037Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw11037 raw11037Labels = mixedMoment B raw11037step0 raw11037step0Labels := by
      have ha : raw11037step0 = (fun i j => raw11037 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11037step0 raw11037; decide +kernel
      have hl : raw11037step0Labels = raw11037Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11037 raw11037Labels permutation176 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical11038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11038 raw11038Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw11038 raw11038Labels = mixedMoment B raw11038step0 raw11038step0Labels := by
      have ha : raw11038step0 = (fun i j => raw11038 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11038step0 raw11038; decide +kernel
      have hl : raw11038step0Labels = raw11038Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11038 raw11038Labels permutation154 permutation2
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical11039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11039 raw11039Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw11039 raw11039Labels = mixedMoment B raw11039step0 raw11039step0Labels := by
      have ha : raw11039step0 = (fun i j => raw11039 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11039step0 raw11039; decide +kernel
      have hl : raw11039step0Labels = raw11039Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11039 raw11039Labels permutation153 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical11040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11040 raw11040Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw11040 raw11040Labels = mixedMoment B raw11040step0 raw11040step0Labels := by
      have hz : ∀ j, raw11040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11040step0 = (fun i j => raw11040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11040step0 raw11040; decide +kernel
      have hl : raw11040step0Labels = raw11040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11040 raw11040Labels permutation434 hz
    mixedMoment B raw11040step0 raw11040step0Labels = mixedMoment B raw11040step1 raw11040step1Labels := by
      have ha : raw11040step1 = (fun i j => raw11040step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11040step1 raw11040step0; decide +kernel
      have hl : raw11040step1Labels = raw11040step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11040step0 raw11040step0Labels permutation33 permutation2
    _ = mixedMoment B node4444 node4444Labels := by rfl

theorem canonical11041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11041 raw11041Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw11041 raw11041Labels = mixedMoment B raw11041step0 raw11041step0Labels := by
      have hz : ∀ j, raw11041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11041step0 = (fun i j => raw11041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11041step0 raw11041; decide +kernel
      have hl : raw11041step0Labels = raw11041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11041 raw11041Labels permutation434 hz
    mixedMoment B raw11041step0 raw11041step0Labels = mixedMoment B raw11041step1 raw11041step1Labels := by
      have ha : raw11041step1 = (fun i j => raw11041step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11041step1 raw11041step0; decide +kernel
      have hl : raw11041step1Labels = raw11041step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11041step0 raw11041step0Labels permutation33 permutation2
    _ = mixedMoment B node4856 node4856Labels := by rfl

theorem canonical11042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11042 raw11042Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw11042 raw11042Labels = mixedMoment B raw11042step0 raw11042step0Labels := by
      have hz : ∀ j, raw11042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11042step0 = (fun i j => raw11042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11042step0 raw11042; decide +kernel
      have hl : raw11042step0Labels = raw11042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11042 raw11042Labels permutation434 hz
    mixedMoment B raw11042step0 raw11042step0Labels = mixedMoment B raw11042step1 raw11042step1Labels := by
      have ha : raw11042step1 = (fun i j => raw11042step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11042step1 raw11042step0; decide +kernel
      have hl : raw11042step1Labels = raw11042step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11042step0 raw11042step0Labels permutation39 permutation2
    _ = mixedMoment B node4856 node4856Labels := by rfl

theorem canonical11043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11043 raw11043Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw11043 raw11043Labels = mixedMoment B raw11043step0 raw11043step0Labels := by
      have ha : raw11043step0 = (fun i j => raw11043 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11043step0 raw11043; decide +kernel
      have hl : raw11043step0Labels = raw11043Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11043 raw11043Labels permutation201 permutation2
    _ = mixedMoment B node4795 node4795Labels := by rfl

theorem canonical11044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11044 raw11044Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11044 raw11044Labels = mixedMoment B raw11044step0 raw11044step0Labels := by
      have hz : ∀ j, raw11044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11044step0 = (fun i j => raw11044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11044step0 raw11044; decide +kernel
      have hl : raw11044step0Labels = raw11044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11044 raw11044Labels permutation434 hz
    mixedMoment B raw11044step0 raw11044step0Labels = mixedMoment B raw11044step1 raw11044step1Labels := by
      have ha : raw11044step1 = (fun i j => raw11044step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11044step1 raw11044step0; decide +kernel
      have hl : raw11044step1Labels = raw11044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11044step0 raw11044step0Labels permutation33 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11045 raw11045Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw11045 raw11045Labels = mixedMoment B raw11045step0 raw11045step0Labels := by
      have hz : ∀ j, raw11045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11045step0 = (fun i j => raw11045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11045step0 raw11045; decide +kernel
      have hl : raw11045step0Labels = raw11045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11045 raw11045Labels permutation434 hz
    _ = mixedMoment B node4442 node4442Labels := by rfl

theorem canonical11046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11046 raw11046Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw11046 raw11046Labels = mixedMoment B raw11046step0 raw11046step0Labels := by
      have hz : ∀ j, raw11046 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11046step0 = (fun i j => raw11046 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11046step0 raw11046; decide +kernel
      have hl : raw11046step0Labels = raw11046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11046 raw11046Labels permutation434 hz
    mixedMoment B raw11046step0 raw11046step0Labels = mixedMoment B raw11046step1 raw11046step1Labels := by
      have ha : raw11046step1 = (fun i j => raw11046step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11046step1 raw11046step0; decide +kernel
      have hl : raw11046step1Labels = raw11046step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11046step0 raw11046step0Labels permutation151 permutation3
    mixedMoment B raw11046step1 raw11046step1Labels = mixedMoment B raw11046step2 raw11046step2Labels := by
      have ha : raw11046step2 = -raw11046step1 := by apply Matrix.ext; change ∀ i j, raw11046step2 i j = -(raw11046step1 i j); unfold raw11046step2 raw11046step1; decide +kernel
      have hl : raw11046step2Labels = raw11046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11046step2 raw11046step2Labels = mixedMoment B raw11046step3 raw11046step3Labels := by
      have ha : raw11046step3 = raw11046step2 := by apply Matrix.ext; unfold raw11046step3 raw11046step2; decide +kernel
      have hl : raw11046step2Labels = labelEmbedding6 ∘ raw11046step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11046step2 raw11046step2Labels raw11046step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

theorem canonical11047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11047 raw11047Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw11047 raw11047Labels = mixedMoment B raw11047step0 raw11047step0Labels := by
      have hz : ∀ j, raw11047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11047step0 = (fun i j => raw11047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11047step0 raw11047; decide +kernel
      have hl : raw11047step0Labels = raw11047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11047 raw11047Labels permutation434 hz
    mixedMoment B raw11047step0 raw11047step0Labels = mixedMoment B raw11047step1 raw11047step1Labels := by
      have ha : raw11047step1 = (fun i j => raw11047step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11047step1 raw11047step0; decide +kernel
      have hl : raw11047step1Labels = raw11047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11047step0 raw11047step0Labels permutation149 permutation3
    mixedMoment B raw11047step1 raw11047step1Labels = mixedMoment B raw11047step2 raw11047step2Labels := by
      have ha : raw11047step2 = -raw11047step1 := by apply Matrix.ext; change ∀ i j, raw11047step2 i j = -(raw11047step1 i j); unfold raw11047step2 raw11047step1; decide +kernel
      have hl : raw11047step2Labels = raw11047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11047step2 raw11047step2Labels = mixedMoment B raw11047step3 raw11047step3Labels := by
      have ha : raw11047step3 = raw11047step2 := by apply Matrix.ext; unfold raw11047step3 raw11047step2; decide +kernel
      have hl : raw11047step2Labels = labelEmbedding6 ∘ raw11047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11047step2 raw11047step2Labels raw11047step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

theorem canonical11048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11048 raw11048Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw11048 raw11048Labels = mixedMoment B raw11048step0 raw11048step0Labels := by
      have ha : raw11048step0 = (fun i j => raw11048 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11048step0 raw11048; decide +kernel
      have hl : raw11048step0Labels = raw11048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11048 raw11048Labels permutation200 permutation2
    _ = mixedMoment B node4793 node4793Labels := by rfl

theorem canonical11049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11049 raw11049Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw11049 raw11049Labels = mixedMoment B raw11049step0 raw11049step0Labels := by
      have hz : ∀ j, raw11049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11049step0 = (fun i j => raw11049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11049step0 raw11049; decide +kernel
      have hl : raw11049step0Labels = raw11049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11049 raw11049Labels permutation434 hz
    _ = mixedMoment B node4886 node4886Labels := by rfl

theorem canonical11080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11080 raw11080Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw11080 raw11080Labels = mixedMoment B raw11080step0 raw11080step0Labels := by
      have hz : ∀ j, raw11080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11080step0 = (fun i j => raw11080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11080step0 raw11080; decide +kernel
      have hl : raw11080step0Labels = raw11080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11080 raw11080Labels permutation434 hz
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical11081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11081 raw11081Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11081 raw11081Labels = mixedMoment B raw11081step0 raw11081step0Labels := by
      have hz : ∀ j, raw11081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11081step0 = (fun i j => raw11081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11081step0 raw11081; decide +kernel
      have hl : raw11081step0Labels = raw11081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11081 raw11081Labels permutation434 hz
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical11082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11082 raw11082Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw11082 raw11082Labels = mixedMoment B raw11082step0 raw11082step0Labels := by
      have hz : ∀ j, raw11082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11082step0 = (fun i j => raw11082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11082step0 raw11082; decide +kernel
      have hl : raw11082step0Labels = raw11082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11082 raw11082Labels permutation434 hz
    mixedMoment B raw11082step0 raw11082step0Labels = mixedMoment B raw11082step1 raw11082step1Labels := by
      have ha : raw11082step1 = (fun i j => raw11082step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11082step1 raw11082step0; decide +kernel
      have hl : raw11082step1Labels = raw11082step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11082step0 raw11082step0Labels permutation38 permutation2
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical11083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11083 raw11083Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11083 raw11083Labels = mixedMoment B raw11083step0 raw11083step0Labels := by
      have ha : raw11083step0 = (fun i j => raw11083 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11083step0 raw11083; decide +kernel
      have hl : raw11083step0Labels = raw11083Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11083 raw11083Labels permutation200 permutation2
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical11084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11084 raw11084Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw11084 raw11084Labels = mixedMoment B raw11084step0 raw11084step0Labels := by
      have hz : ∀ j, raw11084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11084step0 = (fun i j => raw11084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11084step0 raw11084; decide +kernel
      have hl : raw11084step0Labels = raw11084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11084 raw11084Labels permutation434 hz
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical11085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11085 raw11085Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw11085 raw11085Labels = mixedMoment B raw11085step0 raw11085step0Labels := by
      have hz : ∀ j, raw11085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11085step0 = (fun i j => raw11085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11085step0 raw11085; decide +kernel
      have hl : raw11085step0Labels = raw11085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11085 raw11085Labels permutation434 hz
    mixedMoment B raw11085step0 raw11085step0Labels = mixedMoment B raw11085step1 raw11085step1Labels := by
      have ha : raw11085step1 = (fun i j => raw11085step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11085step1 raw11085step0; decide +kernel
      have hl : raw11085step1Labels = raw11085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11085step0 raw11085step0Labels permutation33 permutation2
    _ = mixedMoment B node3622 node3622Labels := by rfl

theorem canonical11086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11086 raw11086Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11086 raw11086Labels = mixedMoment B raw11086step0 raw11086step0Labels := by
      have hz : ∀ j, raw11086 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11086step0 = (fun i j => raw11086 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11086step0 raw11086; decide +kernel
      have hl : raw11086step0Labels = raw11086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086 raw11086Labels permutation590 hz
    mixedMoment B raw11086step0 raw11086step0Labels = mixedMoment B raw11086step1 raw11086step1Labels := by
      have hz : ∀ j, raw11086step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11086step1 = (fun i j => raw11086step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11086step1 raw11086step0; decide +kernel
      have hl : raw11086step1Labels = raw11086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086step0 raw11086step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

theorem canonical1266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1266 raw1266Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw1266 raw1266Labels = mixedMoment B raw1266step0 raw1266step0Labels := by
      have ha : raw1266step0 = (fun i j => raw1266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1266step0 raw1266; decide +kernel
      have hl : raw1266step0Labels = raw1266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1266 raw1266Labels permutation32 permutation4
    mixedMoment B raw1266step0 raw1266step0Labels = mixedMoment B raw1266step1 raw1266step1Labels := by
      have ha : raw1266step1 = raw1266step0 := by apply Matrix.ext; unfold raw1266step1 raw1266step0; decide +kernel
      have hl : raw1266step0Labels = labelEmbedding7 ∘ raw1266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1266step0 raw1266step0Labels raw1266step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical1267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1267 raw1267Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw1267 raw1267Labels = mixedMoment B raw1267step0 raw1267step0Labels := by
      have ha : raw1267step0 = (fun i j => raw1267 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1267step0 raw1267; decide +kernel
      have hl : raw1267step0Labels = raw1267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1267 raw1267Labels permutation32 permutation4
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1268 raw1268Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw1268 raw1268Labels = mixedMoment B raw1268step0 raw1268step0Labels := by
      have ha : raw1268step0 = (fun i j => raw1268 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1268step0 raw1268; decide +kernel
      have hl : raw1268step0Labels = raw1268Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1268 raw1268Labels permutation50 permutation6
    mixedMoment B raw1268step0 raw1268step0Labels = mixedMoment B raw1268step1 raw1268step1Labels := by
      have ha : raw1268step1 = -raw1268step0 := by apply Matrix.ext; change ∀ i j, raw1268step1 i j = -(raw1268step0 i j); unfold raw1268step1 raw1268step0; decide +kernel
      have hl : raw1268step1Labels = raw1268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1268step1 raw1268step1Labels = mixedMoment B raw1268step2 raw1268step2Labels := by
      have ha : raw1268step2 = raw1268step1 := by apply Matrix.ext; unfold raw1268step2 raw1268step1; decide +kernel
      have hl : raw1268step1Labels = labelEmbedding1 ∘ raw1268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1268step1 raw1268step1Labels raw1268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4461 node4461Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1044 node1044Labels + mixedMoment B node1737 node1737Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1266 singletonSmall4461
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4461) = raw1266Labels := by decide +kernel
  rw [hl, canonical1266 B hB] at h
  have hc0 : mixedMoment B raw1266 (Fin.cases (0 : Fin 2) singletonSmall4461) =
      mixedMoment B node1044 node1044Labels := by
    have ha : raw1266 = raw1267 := by apply Matrix.ext; unfold raw1266 raw1267; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4461 = raw1267Labels := by decide +kernel
    rw [ha, hj, canonical1267 B hB]
  have hc1 : mixedMoment B raw1266 (Fin.cases (1 : Fin 2) singletonSmall4461) =
      mixedMoment B node1737 node1737Labels := by
    have ha : raw1266 = raw1268 := by apply Matrix.ext; unfold raw1266 raw1268; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4461 = raw1268Labels := by decide +kernel
    rw [ha, hj, canonical1268 B hB]
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

theorem singleton4805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4805 node4805Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2023 node2023Labels + mixedMoment B node2214 node2214Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1740 singletonSmall4805
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4805) = raw1740Labels := by decide +kernel
  rw [hl, canonical1740 B hB] at h
  have hc0 : mixedMoment B raw1740 (Fin.cases (0 : Fin 2) singletonSmall4805) =
      mixedMoment B node2023 node2023Labels := by
    have ha : raw1740 = raw1741 := by apply Matrix.ext; unfold raw1740 raw1741; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4805 = raw1741Labels := by decide +kernel
    rw [ha, hj, canonical1741 B hB]
  have hc1 : mixedMoment B raw1740 (Fin.cases (1 : Fin 2) singletonSmall4805) =
      mixedMoment B node2214 node2214Labels := by
    have ha : raw1740 = raw1742 := by apply Matrix.ext; unfold raw1740 raw1742; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4805 = raw1742Labels := by decide +kernel
    rw [ha, hj, canonical1742 B hB]
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

theorem singleton4869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4869 node4869Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2110 node2110Labels + mixedMoment B node2275 node2275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1800 singletonSmall4869
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4869) = raw1800Labels := by decide +kernel
  rw [hl, canonical1800 B hB] at h
  have hc0 : mixedMoment B raw1800 (Fin.cases (0 : Fin 2) singletonSmall4869) =
      mixedMoment B node2110 node2110Labels := by
    have ha : raw1800 = raw1801 := by apply Matrix.ext; unfold raw1800 raw1801; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4869 = raw1801Labels := by decide +kernel
    rw [ha, hj, canonical1801 B hB]
  have hc1 : mixedMoment B raw1800 (Fin.cases (1 : Fin 2) singletonSmall4869) =
      mixedMoment B node2275 node2275Labels := by
    have ha : raw1800 = raw1802 := by apply Matrix.ext; unfold raw1800 raw1802; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4869 = raw1802Labels := by decide +kernel
    rw [ha, hj, canonical1802 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
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

theorem singleton5301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5301 node5301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3053 node3053Labels + mixedMoment B node3619 node3619Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2310 singletonSmall5301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5301) = raw2310Labels := by decide +kernel
  rw [hl, canonical2310 B hB] at h
  have hc0 : mixedMoment B raw2310 (Fin.cases (0 : Fin 2) singletonSmall5301) =
      mixedMoment B node3053 node3053Labels := by
    have ha : raw2310 = raw2311 := by apply Matrix.ext; unfold raw2310 raw2311; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5301 = raw2311Labels := by decide +kernel
    rw [ha, hj, canonical2311 B hB]
  have hc1 : mixedMoment B raw2310 (Fin.cases (1 : Fin 2) singletonSmall5301) =
      mixedMoment B node3619 node3619Labels := by
    have ha : raw2310 = raw2312 := by apply Matrix.ext; unfold raw2310 raw2312; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5301 = raw2312Labels := by decide +kernel
    rw [ha, hj, canonical2312 B hB]
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

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

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

theorem sound1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1042 node1042Labels = Sparse.eval nodeValue1042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1042) = mixedMoment B node1042 node1042Labels := rfl
  simpa [nodeValue1042, Sparse.eval] using hc.symm

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

theorem sound1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1047 node1047Labels = Sparse.eval nodeValue1047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1047) = mixedMoment B node1047 node1047Labels := rfl
  simpa [nodeValue1047, Sparse.eval] using hc.symm

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

theorem sound1057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1057 node1057Labels = Sparse.eval nodeValue1057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1057) = mixedMoment B node1057 node1057Labels := rfl
  simpa [nodeValue1057, Sparse.eval] using hc.symm

theorem sound1059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1059 node1059Labels = Sparse.eval nodeValue1059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1059) = mixedMoment B node1059 node1059Labels := rfl
  simpa [nodeValue1059, Sparse.eval] using hc.symm

theorem sound1063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1063 node1063Labels = Sparse.eval nodeValue1063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1063) = mixedMoment B node1063 node1063Labels := rfl
  simpa [nodeValue1063, Sparse.eval] using hc.symm

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

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

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = 0 := by
  exact mixedMoment_order_one B hB node2293 node2293Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

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

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3526 node3526Labels = Sparse.eval nodeValue3526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3526) = mixedMoment B node3526 node3526Labels := rfl
  simpa [nodeValue3526, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

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

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

theorem sound3622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3622 node3622Labels = Sparse.eval nodeValue3622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3622) = mixedMoment B node3622 node3622Labels := rfl
  simpa [nodeValue3622, Sparse.eval] using hc.symm

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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

theorem sound4439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4439 node4439Labels = Sparse.eval nodeValue4439 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4439) = mixedMoment B node4439 node4439Labels := rfl
  simpa [nodeValue4439, Sparse.eval] using hc.symm

theorem sound4442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4442 node4442Labels = Sparse.eval nodeValue4442 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4442) = mixedMoment B node4442 node4442Labels := rfl
  simpa [nodeValue4442, Sparse.eval] using hc.symm

theorem sound4444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4444 node4444Labels = Sparse.eval nodeValue4444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4444) = mixedMoment B node4444 node4444Labels := rfl
  simpa [nodeValue4444, Sparse.eval] using hc.symm

theorem sound4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4461 node4461Labels = Sparse.eval nodeValue4461 (mixedVector B) := by
  have h := singleton4461 B _hB
  rw [sound1044 B _hB _hF, sound1737 B _hB _hF] at h
  norm_num [nodeValue4461, nodeValue1044, nodeValue1737, Sparse.eval] at h ⊢
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

theorem sound4793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4793 node4793Labels = Sparse.eval nodeValue4793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4793) = mixedMoment B node4793 node4793Labels := rfl
  simpa [nodeValue4793, Sparse.eval] using hc.symm

theorem sound4795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4795 node4795Labels = Sparse.eval nodeValue4795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4795) = mixedMoment B node4795 node4795Labels := rfl
  simpa [nodeValue4795, Sparse.eval] using hc.symm

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

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4808 node4808Labels = Sparse.eval nodeValue4808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4808) = mixedMoment B node4808 node4808Labels := rfl
  simpa [nodeValue4808, Sparse.eval] using hc.symm

theorem sound4852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4852 node4852Labels = Sparse.eval nodeValue4852 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4852) = mixedMoment B node4852 node4852Labels := rfl
  simpa [nodeValue4852, Sparse.eval] using hc.symm

theorem sound4856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4856 node4856Labels = Sparse.eval nodeValue4856 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4856) = mixedMoment B node4856 node4856Labels := rfl
  simpa [nodeValue4856, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = 0 := by
  exact mixedMoment_order_one B hB node4893 node4893Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4885 node4885Labels = Sparse.eval nodeValue4885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4885) = mixedMoment B node4885 node4885Labels := rfl
  simpa [nodeValue4885, Sparse.eval] using hc.symm

theorem sound4886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4886 node4886Labels = Sparse.eval nodeValue4886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4886) = mixedMoment B node4886 node4886Labels := rfl
  simpa [nodeValue4886, Sparse.eval] using hc.symm

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

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = Sparse.eval nodeValue4893 (mixedVector B) := by
  simpa only [nodeValue4893, Sparse.eval_nil] using zero4893 B _hB _hF

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

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5299 node5299Labels = Sparse.eval nodeValue5299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5299) = mixedMoment B node5299 node5299Labels := rfl
  simpa [nodeValue5299, Sparse.eval] using hc.symm

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources19
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm635 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA635 + difference 1 0) (sourceB635 + difference 0 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA635 + difference 1 0) (sourceB635 + difference 0 1) sourceC635) = raw10762 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10762; decide +kernel
    rw [ha]
    exact (canonical10762 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA635 + difference 1 1) (sourceB635 + difference 1 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA635 + difference 1 1) (sourceB635 + difference 1 1) sourceC635) = raw10763 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10763; decide +kernel
    rw [ha]
    exact (canonical10763 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA635 + difference 1 2) (sourceB635 + difference 2 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA635 + difference 1 2) (sourceB635 + difference 2 1) sourceC635) = raw10764 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10764; decide +kernel
    rw [ha]
    exact (canonical10764 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA635 + difference 1 3) (sourceB635 + difference 3 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA635 + difference 1 3) (sourceB635 + difference 3 1) sourceC635) = raw10765 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10765; decide +kernel
    rw [ha]
    exact (canonical10765 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA635 + difference 1 4) (sourceB635 + difference 4 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA635 + difference 1 4) (sourceB635 + difference 4 1) sourceC635) = raw10766 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10766; decide +kernel
    rw [ha]
    exact (canonical10766 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA635 + difference 1 5) (sourceB635 + difference 5 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA635 + difference 1 5) (sourceB635 + difference 5 1) sourceC635) = raw10767 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10767; decide +kernel
    rw [ha]
    exact (canonical10767 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA635 + sourceB635) sourceC635) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA635 + sourceB635) sourceC635) = raw10768 := by
      apply Matrix.ext; unfold doubleCharges sourceA635 sourceB635 sourceC635 raw10768; decide +kernel
    rw [ha]
    exact (canonical10768 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA635 sourceB635 sourceC635
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm635, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

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

theorem sourceEq640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm640 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA640 + difference 0 0) (sourceB640 + difference 0 0) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA640 + difference 0 0) (sourceB640 + difference 0 0) sourceC640) = raw10889 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10889; decide +kernel
    rw [ha]
    exact (canonical10889 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA640 + difference 1 0) (sourceB640 + difference 0 1) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA640 + difference 1 0) (sourceB640 + difference 0 1) sourceC640) = raw10890 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10890; decide +kernel
    rw [ha]
    exact (canonical10890 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA640 + difference 2 0) (sourceB640 + difference 0 2) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA640 + difference 2 0) (sourceB640 + difference 0 2) sourceC640) = raw10891 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10891; decide +kernel
    rw [ha]
    exact (canonical10891 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA640 + difference 3 0) (sourceB640 + difference 0 3) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA640 + difference 3 0) (sourceB640 + difference 0 3) sourceC640) = raw10892 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10892; decide +kernel
    rw [ha]
    exact (canonical10892 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA640 + difference 4 0) (sourceB640 + difference 0 4) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA640 + difference 4 0) (sourceB640 + difference 0 4) sourceC640) = raw10893 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10893; decide +kernel
    rw [ha]
    exact (canonical10893 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA640 + difference 5 0) (sourceB640 + difference 0 5) sourceC640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA640 + difference 5 0) (sourceB640 + difference 0 5) sourceC640) = raw10894 := by
      apply Matrix.ext; unfold tripleCharges sourceA640 sourceB640 sourceC640 difference raw10894; decide +kernel
    rw [ha]
    exact (canonical10894 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA640 + sourceB640) sourceC640) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA640 + sourceB640) sourceC640) = raw10895 := by
      apply Matrix.ext; unfold doubleCharges sourceA640 sourceB640 sourceC640 raw10895; decide +kernel
    rw [ha]
    exact (canonical10895 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA640 sourceB640 sourceC640
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm640, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm641 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA641 + difference 1 0) (sourceB641 + difference 0 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA641 + difference 1 0) (sourceB641 + difference 0 1) sourceC641) = raw10890 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10890; decide +kernel
    rw [ha]
    exact (canonical10890 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA641 + difference 1 1) (sourceB641 + difference 1 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA641 + difference 1 1) (sourceB641 + difference 1 1) sourceC641) = raw10889 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10889; decide +kernel
    rw [ha]
    exact (canonical10889 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA641 + difference 1 2) (sourceB641 + difference 2 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA641 + difference 1 2) (sourceB641 + difference 2 1) sourceC641) = raw10896 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10896; decide +kernel
    rw [ha]
    exact (canonical10896 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA641 + difference 1 3) (sourceB641 + difference 3 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA641 + difference 1 3) (sourceB641 + difference 3 1) sourceC641) = raw10897 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10897; decide +kernel
    rw [ha]
    exact (canonical10897 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA641 + difference 1 4) (sourceB641 + difference 4 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA641 + difference 1 4) (sourceB641 + difference 4 1) sourceC641) = raw10898 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10898; decide +kernel
    rw [ha]
    exact (canonical10898 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA641 + difference 1 5) (sourceB641 + difference 5 1) sourceC641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA641 + difference 1 5) (sourceB641 + difference 5 1) sourceC641) = raw10899 := by
      apply Matrix.ext; unfold tripleCharges sourceA641 sourceB641 sourceC641 difference raw10899; decide +kernel
    rw [ha]
    exact (canonical10899 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA641 + sourceB641) sourceC641) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA641 + sourceB641) sourceC641) = raw10895 := by
      apply Matrix.ext; unfold doubleCharges sourceA641 sourceB641 sourceC641 raw10895; decide +kernel
    rw [ha]
    exact (canonical10895 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA641 sourceB641 sourceC641
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm641, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm647 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA647 + difference 0 0) (sourceB647 + difference 0 0) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA647 + difference 0 0) (sourceB647 + difference 0 0) sourceC647) = raw11014 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11014; decide +kernel
    rw [ha]
    exact (canonical11014 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA647 + difference 1 0) (sourceB647 + difference 0 1) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA647 + difference 1 0) (sourceB647 + difference 0 1) sourceC647) = raw11015 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11015; decide +kernel
    rw [ha]
    exact (canonical11015 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA647 + difference 2 0) (sourceB647 + difference 0 2) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA647 + difference 2 0) (sourceB647 + difference 0 2) sourceC647) = raw11016 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11016; decide +kernel
    rw [ha]
    exact (canonical11016 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA647 + difference 3 0) (sourceB647 + difference 0 3) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA647 + difference 3 0) (sourceB647 + difference 0 3) sourceC647) = raw11017 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11017; decide +kernel
    rw [ha]
    exact (canonical11017 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA647 + difference 4 0) (sourceB647 + difference 0 4) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA647 + difference 4 0) (sourceB647 + difference 0 4) sourceC647) = raw11018 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11018; decide +kernel
    rw [ha]
    exact (canonical11018 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA647 + difference 5 0) (sourceB647 + difference 0 5) sourceC647) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA647 + difference 5 0) (sourceB647 + difference 0 5) sourceC647) = raw11019 := by
      apply Matrix.ext; unfold tripleCharges sourceA647 sourceB647 sourceC647 difference raw11019; decide +kernel
    rw [ha]
    exact (canonical11019 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA647 + sourceB647) sourceC647) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA647 + sourceB647) sourceC647) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA647 sourceB647 sourceC647 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA647 sourceB647 sourceC647
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm647, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm648 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA648 + difference 0 1) (sourceB648 + difference 1 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA648 + difference 0 1) (sourceB648 + difference 1 0) sourceC648) = raw11020 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11020; decide +kernel
    rw [ha]
    exact (canonical11020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA648 + difference 0 2) (sourceB648 + difference 2 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA648 + difference 0 2) (sourceB648 + difference 2 0) sourceC648) = raw11021 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11021; decide +kernel
    rw [ha]
    exact (canonical11021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA648 + difference 0 3) (sourceB648 + difference 3 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA648 + difference 0 3) (sourceB648 + difference 3 0) sourceC648) = raw11022 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11022; decide +kernel
    rw [ha]
    exact (canonical11022 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA648 + difference 0 4) (sourceB648 + difference 4 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA648 + difference 0 4) (sourceB648 + difference 4 0) sourceC648) = raw11023 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11023; decide +kernel
    rw [ha]
    exact (canonical11023 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA648 + difference 0 5) (sourceB648 + difference 5 0) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA648 + difference 0 5) (sourceB648 + difference 5 0) sourceC648) = raw11024 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11024; decide +kernel
    rw [ha]
    exact (canonical11024 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA648 + difference 1 0) (sourceB648 + difference 0 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA648 + difference 1 0) (sourceB648 + difference 0 1) sourceC648) = raw11025 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11025; decide +kernel
    rw [ha]
    exact (canonical11025 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA648 + difference 1 2) (sourceB648 + difference 2 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA648 + difference 1 2) (sourceB648 + difference 2 1) sourceC648) = raw11026 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11026; decide +kernel
    rw [ha]
    exact (canonical11026 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA648 + difference 1 3) (sourceB648 + difference 3 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA648 + difference 1 3) (sourceB648 + difference 3 1) sourceC648) = raw11027 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11027; decide +kernel
    rw [ha]
    exact (canonical11027 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA648 + difference 1 4) (sourceB648 + difference 4 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA648 + difference 1 4) (sourceB648 + difference 4 1) sourceC648) = raw11028 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11028; decide +kernel
    rw [ha]
    exact (canonical11028 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA648 + difference 1 5) (sourceB648 + difference 5 1) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA648 + difference 1 5) (sourceB648 + difference 5 1) sourceC648) = raw11029 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11029; decide +kernel
    rw [ha]
    exact (canonical11029 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA648 + difference 2 0) (sourceB648 + difference 0 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA648 + difference 2 0) (sourceB648 + difference 0 2) sourceC648) = raw11030 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11030; decide +kernel
    rw [ha]
    exact (canonical11030 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA648 + difference 2 1) (sourceB648 + difference 1 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA648 + difference 2 1) (sourceB648 + difference 1 2) sourceC648) = raw11031 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11031; decide +kernel
    rw [ha]
    exact (canonical11031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA648 + difference 2 3) (sourceB648 + difference 3 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA648 + difference 2 3) (sourceB648 + difference 3 2) sourceC648) = raw11032 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11032; decide +kernel
    rw [ha]
    exact (canonical11032 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA648 + difference 2 4) (sourceB648 + difference 4 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA648 + difference 2 4) (sourceB648 + difference 4 2) sourceC648) = raw11033 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11033; decide +kernel
    rw [ha]
    exact (canonical11033 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA648 + difference 2 5) (sourceB648 + difference 5 2) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA648 + difference 2 5) (sourceB648 + difference 5 2) sourceC648) = raw11034 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11034; decide +kernel
    rw [ha]
    exact (canonical11034 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA648 + difference 3 0) (sourceB648 + difference 0 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA648 + difference 3 0) (sourceB648 + difference 0 3) sourceC648) = raw11035 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11035; decide +kernel
    rw [ha]
    exact (canonical11035 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA648 + difference 3 1) (sourceB648 + difference 1 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA648 + difference 3 1) (sourceB648 + difference 1 3) sourceC648) = raw11036 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11036; decide +kernel
    rw [ha]
    exact (canonical11036 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA648 + difference 3 2) (sourceB648 + difference 2 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA648 + difference 3 2) (sourceB648 + difference 2 3) sourceC648) = raw11037 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11037; decide +kernel
    rw [ha]
    exact (canonical11037 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA648 + difference 3 4) (sourceB648 + difference 4 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA648 + difference 3 4) (sourceB648 + difference 4 3) sourceC648) = raw11038 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11038; decide +kernel
    rw [ha]
    exact (canonical11038 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA648 + difference 3 5) (sourceB648 + difference 5 3) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA648 + difference 3 5) (sourceB648 + difference 5 3) sourceC648) = raw11039 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11039; decide +kernel
    rw [ha]
    exact (canonical11039 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA648 + difference 4 0) (sourceB648 + difference 0 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA648 + difference 4 0) (sourceB648 + difference 0 4) sourceC648) = raw11040 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11040; decide +kernel
    rw [ha]
    exact (canonical11040 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA648 + difference 4 1) (sourceB648 + difference 1 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA648 + difference 4 1) (sourceB648 + difference 1 4) sourceC648) = raw11041 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11041; decide +kernel
    rw [ha]
    exact (canonical11041 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA648 + difference 4 2) (sourceB648 + difference 2 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA648 + difference 4 2) (sourceB648 + difference 2 4) sourceC648) = raw11042 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11042; decide +kernel
    rw [ha]
    exact (canonical11042 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA648 + difference 4 3) (sourceB648 + difference 3 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA648 + difference 4 3) (sourceB648 + difference 3 4) sourceC648) = raw11043 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11043; decide +kernel
    rw [ha]
    exact (canonical11043 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA648 + difference 4 5) (sourceB648 + difference 5 4) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA648 + difference 4 5) (sourceB648 + difference 5 4) sourceC648) = raw11044 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11044; decide +kernel
    rw [ha]
    exact (canonical11044 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA648 + difference 5 0) (sourceB648 + difference 0 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA648 + difference 5 0) (sourceB648 + difference 0 5) sourceC648) = raw11045 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11045; decide +kernel
    rw [ha]
    exact (canonical11045 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA648 + difference 5 1) (sourceB648 + difference 1 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA648 + difference 5 1) (sourceB648 + difference 1 5) sourceC648) = raw11046 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11046; decide +kernel
    rw [ha]
    exact (canonical11046 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA648 + difference 5 2) (sourceB648 + difference 2 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA648 + difference 5 2) (sourceB648 + difference 2 5) sourceC648) = raw11047 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11047; decide +kernel
    rw [ha]
    exact (canonical11047 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA648 + difference 5 3) (sourceB648 + difference 3 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA648 + difference 5 3) (sourceB648 + difference 3 5) sourceC648) = raw11048 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11048; decide +kernel
    rw [ha]
    exact (canonical11048 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA648 + difference 5 4) (sourceB648 + difference 4 5) sourceC648) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA648 + difference 5 4) (sourceB648 + difference 4 5) sourceC648) = raw11049 := by
      apply Matrix.ext; unfold tripleCharges sourceA648 sourceB648 sourceC648 difference raw11049; decide +kernel
    rw [ha]
    exact (canonical11049 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA648 sourceB648 sourceC648
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm648, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm650 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA650 + difference 0 0) (sourceB650 + difference 0 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA650 + difference 0 0) (sourceB650 + difference 0 0) sourceC650) = raw11080 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11080; decide +kernel
    rw [ha]
    exact (canonical11080 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA650 + difference 0 1) (sourceB650 + difference 1 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA650 + difference 0 1) (sourceB650 + difference 1 0) sourceC650) = raw11081 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11081; decide +kernel
    rw [ha]
    exact (canonical11081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA650 + difference 0 2) (sourceB650 + difference 2 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA650 + difference 0 2) (sourceB650 + difference 2 0) sourceC650) = raw11082 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11082; decide +kernel
    rw [ha]
    exact (canonical11082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA650 + difference 0 3) (sourceB650 + difference 3 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA650 + difference 0 3) (sourceB650 + difference 3 0) sourceC650) = raw11083 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11083; decide +kernel
    rw [ha]
    exact (canonical11083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA650 + difference 0 4) (sourceB650 + difference 4 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA650 + difference 0 4) (sourceB650 + difference 4 0) sourceC650) = raw11084 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11084; decide +kernel
    rw [ha]
    exact (canonical11084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA650 + difference 0 5) (sourceB650 + difference 5 0) sourceC650) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA650 + difference 0 5) (sourceB650 + difference 5 0) sourceC650) = raw11085 := by
      apply Matrix.ext; unfold tripleCharges sourceA650 sourceB650 sourceC650 difference raw11085; decide +kernel
    rw [ha]
    exact (canonical11085 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA650 + sourceB650) sourceC650) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA650 + sourceB650) sourceC650) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA650 sourceB650 sourceC650 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA650 sourceB650 sourceC650
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm650, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck544 : Integer.Sparse.reindex keyMap MixedData.row544 = numericRow544 := by decide +kernel

theorem numericCheck544 (x : Master → ℝ) : Integer.Sparse.eval numericRow544 x =
    (1 : ℝ) * reducedSource544 x := by
  norm_num [numericRow544, reducedSource544, Integer.Sparse.eval, Sparse.eval, nodeValue1087, nodeValue2058, nodeValue2266, nodeValue2279, nodeValue2291, nodeValue4084]

theorem reindexCheck549 : Integer.Sparse.reindex keyMap MixedData.row549 = numericRow549 := by decide +kernel

theorem numericCheck549 (x : Master → ℝ) : Integer.Sparse.eval numericRow549 x =
    (1 : ℝ) * reducedSource549 x := by
  norm_num [numericRow549, reducedSource549, Integer.Sparse.eval, Sparse.eval, nodeValue1057, nodeValue1059, nodeValue1063, nodeValue1083, nodeValue2278, nodeValue4084]

theorem reindexCheck550 : Integer.Sparse.reindex keyMap MixedData.row550 = numericRow550 := by decide +kernel

theorem numericCheck550 (x : Master → ℝ) : Integer.Sparse.eval numericRow550 x =
    (1 : ℝ) * reducedSource550 x := by
  norm_num [numericRow550, reducedSource550, Integer.Sparse.eval, Sparse.eval, nodeValue1083, nodeValue2054, nodeValue2278, nodeValue2291, nodeValue2293, nodeValue4084]

theorem reindexCheck556 : Integer.Sparse.reindex keyMap MixedData.row556 = numericRow556 := by decide +kernel

theorem numericCheck556 (x : Master → ℝ) : Integer.Sparse.eval numericRow556 x =
    (1 : ℝ) * reducedSource556 x := by
  norm_num [numericRow556, reducedSource556, Integer.Sparse.eval, Sparse.eval, nodeValue1042, nodeValue1047, nodeValue1049, nodeValue1087, nodeValue2266, nodeValue4084]

theorem reindexCheck557 : Integer.Sparse.reindex keyMap MixedData.row557 = numericRow557 := by decide +kernel

theorem numericCheck557 (x : Master → ℝ) : Integer.Sparse.eval numericRow557 x =
    (17280 : ℝ) * reducedSource557 x := by
  norm_num [numericRow557, reducedSource557, Integer.Sparse.eval, Sparse.eval, nodeValue4439, nodeValue4442, nodeValue4444, nodeValue4461, nodeValue4793, nodeValue4795, nodeValue4805, nodeValue4808, nodeValue4852, nodeValue4856, nodeValue4869, nodeValue4885, nodeValue4886, nodeValue4887, nodeValue4888, nodeValue4889, nodeValue4893, nodeValue5265, nodeValue5292, nodeValue5299, nodeValue5301]
  ring

theorem reindexCheck559 : Integer.Sparse.reindex keyMap MixedData.row559 = numericRow559 := by decide +kernel

theorem numericCheck559 (x : Master → ℝ) : Integer.Sparse.eval numericRow559 x =
    (1 : ℝ) * reducedSource559 x := by
  norm_num [numericRow559, reducedSource559, Integer.Sparse.eval, Sparse.eval, nodeValue2245, nodeValue3526, nodeValue3573, nodeValue3619, nodeValue3622, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero544 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource544 (mixedVector B) = 0 := by
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm635, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1087, h2058, h2266, h2279, h2291, h4084, reducedSource544] using sourceEq635 B hB

theorem rowSound544 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row544 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck544, numericCheck544, reducedZero544 B hB hF, mul_zero]

theorem reducedZero549 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource549 (mixedVector B) = 0 := by
  have h1057 : mixedVector B (Sum.inr 1057) = Sparse.eval nodeValue1057 (mixedVector B) := by
    change mixedMoment B node1057 node1057Labels = _
    exact sound1057 B hB hF
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h1063 : mixedVector B (Sum.inr 1063) = Sparse.eval nodeValue1063 (mixedVector B) := by
    change mixedMoment B node1063 node1063Labels = _
    exact sound1063 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm640, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1057, h1059, h1063, h1083, h2278, h4084, reducedSource549] using sourceEq640 B hB

theorem rowSound549 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row549 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck549, numericCheck549, reducedZero549 B hB hF, mul_zero]

theorem reducedZero550 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource550 (mixedVector B) = 0 := by
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm641, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1083, h2054, h2278, h2291, h2293, h4084, reducedSource550] using sourceEq641 B hB

theorem rowSound550 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row550 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck550, numericCheck550, reducedZero550 B hB hF, mul_zero]

theorem reducedZero556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource556 (mixedVector B) = 0 := by
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm647, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1042, h1047, h1049, h1087, h2266, h4084, reducedSource556] using sourceEq647 B hB

theorem rowSound556 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row556 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck556, numericCheck556, reducedZero556 B hB hF, mul_zero]

theorem reducedZero557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource557 (mixedVector B) = 0 := by
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4444 : mixedVector B (Sum.inr 4444) = Sparse.eval nodeValue4444 (mixedVector B) := by
    change mixedMoment B node4444 node4444Labels = _
    exact sound4444 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4793 : mixedVector B (Sum.inr 4793) = Sparse.eval nodeValue4793 (mixedVector B) := by
    change mixedMoment B node4793 node4793Labels = _
    exact sound4793 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4808 : mixedVector B (Sum.inr 4808) = Sparse.eval nodeValue4808 (mixedVector B) := by
    change mixedMoment B node4808 node4808Labels = _
    exact sound4808 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h4856 : mixedVector B (Sum.inr 4856) = Sparse.eval nodeValue4856 (mixedVector B) := by
    change mixedMoment B node4856 node4856Labels = _
    exact sound4856 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h4886 : mixedVector B (Sum.inr 4886) = Sparse.eval nodeValue4886 (mixedVector B) := by
    change mixedMoment B node4886 node4886Labels = _
    exact sound4886 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  simpa only [sourceForm648, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4439, h4442, h4444, h4461, h4793, h4795, h4805, h4808, h4852, h4856, h4869, h4885, h4886, h4887, h4888, h4889, h4893, h5265, h5292, h5299, h5301, reducedSource557] using sourceEq648 B hB

theorem rowSound557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row557 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck557, numericCheck557, reducedZero557 B hB hF, mul_zero]

theorem reducedZero559 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource559 (mixedVector B) = 0 := by
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h3619 : mixedVector B (Sum.inr 3619) = Sparse.eval nodeValue3619 (mixedVector B) := by
    change mixedMoment B node3619 node3619Labels = _
    exact sound3619 B hB hF
  have h3622 : mixedVector B (Sum.inr 3622) = Sparse.eval nodeValue3622 (mixedVector B) := by
    change mixedMoment B node3622 node3622Labels = _
    exact sound3622 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm650, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2245, h3526, h3573, h3619, h3622, h4083, reducedSource559] using sourceEq650 B hB

theorem rowSound559 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row559 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck559, numericCheck559, reducedZero559 B hB hF, mul_zero]

theorem sourceRowsAt544 : MixedData.sourceRows (544 : Fin 2425) =
    MixedData.row544 := by decide +kernel

theorem sourceRowsAt545 : MixedData.sourceRows (545 : Fin 2425) =
    MixedData.row545 := by decide +kernel

theorem sourceRowsAt546 : MixedData.sourceRows (546 : Fin 2425) =
    MixedData.row546 := by decide +kernel

theorem sourceRowsAt547 : MixedData.sourceRows (547 : Fin 2425) =
    MixedData.row547 := by decide +kernel

theorem sourceRowsAt548 : MixedData.sourceRows (548 : Fin 2425) =
    MixedData.row548 := by decide +kernel

theorem sourceRowsAt549 : MixedData.sourceRows (549 : Fin 2425) =
    MixedData.row549 := by decide +kernel

theorem sourceRowsAt550 : MixedData.sourceRows (550 : Fin 2425) =
    MixedData.row550 := by decide +kernel

theorem sourceRowsAt551 : MixedData.sourceRows (551 : Fin 2425) =
    MixedData.row551 := by decide +kernel

theorem sourceRowsAt552 : MixedData.sourceRows (552 : Fin 2425) =
    MixedData.row552 := by decide +kernel

theorem sourceRowsAt553 : MixedData.sourceRows (553 : Fin 2425) =
    MixedData.row553 := by decide +kernel

theorem sourceRowsAt554 : MixedData.sourceRows (554 : Fin 2425) =
    MixedData.row554 := by decide +kernel

theorem sourceRowsAt555 : MixedData.sourceRows (555 : Fin 2425) =
    MixedData.row555 := by decide +kernel

theorem sourceRowsAt556 : MixedData.sourceRows (556 : Fin 2425) =
    MixedData.row556 := by decide +kernel

theorem sourceRowsAt557 : MixedData.sourceRows (557 : Fin 2425) =
    MixedData.row557 := by decide +kernel

theorem sourceRowsAt558 : MixedData.sourceRows (558 : Fin 2425) =
    MixedData.row558 := by decide +kernel

theorem sourceRowsAt559 : MixedData.sourceRows (559 : Fin 2425) =
    MixedData.row559 := by decide +kernel

theorem chunkSound34_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 34) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 544 ∨ k.val = 545 ∨ k.val = 546 ∨ k.val = 547 ∨ k.val = 548 ∨ k.val = 549 ∨ k.val = 550 ∨ k.val = 551 ∨ k.val = 552 ∨ k.val = 553 ∨ k.val = 554 ∨ k.val = 555 ∨ k.val = 556 ∨ k.val = 557 ∨ k.val = 558 ∨ k.val = 559 := by omega
  rcases heq with h544 | h545 | h546 | h547 | h548 | h549 | h550 | h551 | h552 | h553 | h554 | h555 | h556 | h557 | h558 | h559
  · have he : k = (544 : Fin 2425) := Fin.ext h544
    subst k
    rw [sourceRowsAt544]
    exact rowSound544 B hB hF
  · have he : k = (545 : Fin 2425) := Fin.ext h545
    subst k
    rw [sourceRowsAt545]
    exact rowSound545_e B hB hF
  · have he : k = (546 : Fin 2425) := Fin.ext h546
    subst k
    rw [sourceRowsAt546]
    exact rowSound546_e B hB hF
  · have he : k = (547 : Fin 2425) := Fin.ext h547
    subst k
    rw [sourceRowsAt547]
    exact rowSound547_e B hB hF
  · have he : k = (548 : Fin 2425) := Fin.ext h548
    subst k
    rw [sourceRowsAt548]
    exact rowSound548_e B hB hF
  · have he : k = (549 : Fin 2425) := Fin.ext h549
    subst k
    rw [sourceRowsAt549]
    exact rowSound549 B hB hF
  · have he : k = (550 : Fin 2425) := Fin.ext h550
    subst k
    rw [sourceRowsAt550]
    exact rowSound550 B hB hF
  · have he : k = (551 : Fin 2425) := Fin.ext h551
    subst k
    rw [sourceRowsAt551]
    exact rowSound551_e B hB hF
  · have he : k = (552 : Fin 2425) := Fin.ext h552
    subst k
    rw [sourceRowsAt552]
    exact rowSound552_e B hB hF
  · have he : k = (553 : Fin 2425) := Fin.ext h553
    subst k
    rw [sourceRowsAt553]
    exact rowSound553_e B hB hF
  · have he : k = (554 : Fin 2425) := Fin.ext h554
    subst k
    rw [sourceRowsAt554]
    exact rowSound554_e B hB hF
  · have he : k = (555 : Fin 2425) := Fin.ext h555
    subst k
    rw [sourceRowsAt555]
    exact rowSound555_e B hB hF
  · have he : k = (556 : Fin 2425) := Fin.ext h556
    subst k
    rw [sourceRowsAt556]
    exact rowSound556 B hB hF
  · have he : k = (557 : Fin 2425) := Fin.ext h557
    subst k
    rw [sourceRowsAt557]
    exact rowSound557 B hB hF
  · have he : k = (558 : Fin 2425) := Fin.ext h558
    subst k
    rw [sourceRowsAt558]
    exact rowSound558_e B hB hF
  · have he : k = (559 : Fin 2425) := Fin.ext h559
    subst k
    rw [sourceRowsAt559]
    exact rowSound559 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e_oai
