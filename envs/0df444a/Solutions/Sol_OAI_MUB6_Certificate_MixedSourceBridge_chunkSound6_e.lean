-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:45:40.222141+00:00
-- url     : https://prove2.me/submissions/52105c2f-584b-4dfb-9a3a-bd9a7ae60f0f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E112
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound109_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound110_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound111_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound97_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound99_e

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

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

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

theorem transition_reverse (b c : Basis) :
    transition c b = (transition b c).conjTranspose := by
  ext i j
  simp [transition, Matrix.conjTranspose_apply]

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

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem familyAverage_add (B : Fin 7 → Basis) (F G : CMatrix → ℝ) :
    familyAverage B (fun H => F H + G H) = familyAverage B F + familyAverage B G := by
  simp only [familyAverage, average_add]

theorem familyAverage_mul (B : Fin 7 → Basis) (c : ℝ) (F : CMatrix → ℝ) :
    familyAverage B (fun H => c * F H) = c * familyAverage B F := by
  simp only [familyAverage, average_mul]

theorem relativeMatrix_reverse (B : Fin 7 → Basis) (p : Fin 7 × Coord) :
    relativeMatrix B (reversePair p).1 (reversePair p).2 =
      (relativeMatrix B p.1 p.2).conjTranspose := by
  simp only [relativeMatrix, reversePair, Fin.succAbove_succAbove_predAbove]
  exact transition_reverse _ _

theorem familyAverage_transpose (B : Fin 7 → Basis) (F : CMatrix → ℝ)
    (hF : ∀ H, F (fun i j => conj (H i j)) = F H) :
    familyAverage B (fun H => F H.transpose) = familyAverage B F := by
  change (average (fun r : Fin 7 => average (fun s : Coord => F ((relativeMatrix B r s).transpose)))) =
    average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))
  rw [← average_prod (fun p : Fin 7 × Coord => F ((relativeMatrix B p.1 p.2).transpose)),
    ← average_prod (fun p : Fin 7 × Coord => F (relativeMatrix B p.1 p.2))]
  have h (p : Fin 7 × Coord) :
      F ((relativeMatrix B p.1 p.2).transpose) =
        F (relativeMatrix B (reversePair p).1 (reversePair p).2) := by
    rw [relativeMatrix_reverse]
    exact (hF ((relativeMatrix B p.1 p.2).transpose)).symm
  simp_rw [h]
  exact average_equiv reversePairEquiv (fun p => F (relativeMatrix B p.1 p.2))

theorem rowFourier_conjugate {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier (fun i j => conj (H i j)) ρ a = conj (rowFourier H ρ a) := by
  simp only [rowFourier, map_mul, map_sum, map_prod, map_zpow₀, map_inv₀, map_ofNat]

theorem unorientedRowProducts_conjugate {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    unorientedRowProducts (fun i j => conj (H i j)) A = unorientedRowProducts H A := by
  apply average_congr
  intro ρ
  simp only [rowFourier_conjugate, ← map_prod, Complex.conj_re]

theorem averagedRowProducts_split {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    averagedRowProducts H A =
      (1 / 2 : ℝ) * unorientedRowProducts H A +
        (1 / 2 : ℝ) * unorientedRowProducts H.transpose A := by
  have h (ρ : Fin p ↪ Coord) :
      ((∏ j, rowFourier H ρ (fun i => A i j)).re +
        (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (1 / 2 : ℝ) * (∏ j, rowFourier H ρ (fun i => A i j)).re +
        (1 / 2 : ℝ) * (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re := by ring
  simp only [averagedRowProducts, h, average_add, average_mul, unorientedRowProducts]

theorem familyAverage_averagedRowProducts {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    familyAverage B (fun H => averagedRowProducts H A) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  simp only [averagedRowProducts_split, familyAverage_add, familyAverage_mul]
  rw [familyAverage_transpose B (fun H => unorientedRowProducts H A)
    (fun H => unorientedRowProducts_conjugate H A)]
  ring

theorem mixedMoment_single_label {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) :
      average (fun τ : Fin 1 ↪ Coord =>
        (mixedIntegrand B A (fun _ => (0 : Fin 1)) r ρ τ).re) =
      average (fun s : Coord => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re) := by
    exact average_equiv singletonEmbeddingEquiv
      (fun s => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re)
  simp_rw [h]
  exact average_comm _

/-- Single-label mixed moments expand into the manuscript's transpose-averaged
pair moments with the exact falling-factorial weights. -/
theorem mixedMoment_single_label_partition {p n : ℕ} {P : Type*} [Fintype P]
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        familyPairMoment B (groupedColumns A (F.label s)) := by
  rw [mixedMoment_single_label, ← familyAverage_averagedRowProducts]
  unfold familyAverage
  simp_rw [averagedRowProducts_partition (relativeMatrix_isHadamard B hB _ _) A F cover,
    average_sum, average_mul]
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw284 raw284Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw284 raw284Labels = mixedMoment B raw284step0 raw284step0Labels := by
      have ha : raw284step0 = (fun i j => raw284 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw284step0 raw284; decide +kernel
      have hl : raw284step0Labels = raw284Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw284 raw284Labels permutation2 permutation5
    mixedMoment B raw284step0 raw284step0Labels = mixedMoment B raw284step1 raw284step1Labels := by
      have ha : raw284step1 = raw284step0 := by apply Matrix.ext; unfold raw284step1 raw284step0; decide +kernel
      have hl : raw284step0Labels = labelEmbedding1 ∘ raw284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw284step0 raw284step0Labels raw284step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw285 raw285Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw285 raw285Labels = mixedMoment B raw285step0 raw285step0Labels := by
      have ha : raw285step0 = (fun i j => raw285 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw285step0 raw285; decide +kernel
      have hl : raw285step0Labels = raw285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw285 raw285Labels permutation2 permutation5
    _ = mixedMoment B node420 node420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3721 raw3721Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3721 raw3721Labels = mixedMoment B raw3721step0 raw3721step0Labels := by
      have hz : ∀ j, raw3721 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3721step0 = (fun i j => raw3721 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3721step0 raw3721; decide +kernel
      have hl : raw3721step0Labels = raw3721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721 raw3721Labels permutation520 hz
    mixedMoment B raw3721step0 raw3721step0Labels = mixedMoment B raw3721step1 raw3721step1Labels := by
      have hz : ∀ j, raw3721step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3721step1 = (fun i j => raw3721step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3721step1 raw3721step0; decide +kernel
      have hl : raw3721step1Labels = raw3721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step0 raw3721step0Labels permutation104 hz
    mixedMoment B raw3721step1 raw3721step1Labels = mixedMoment B raw3721step2 raw3721step2Labels := by
      have hz : ∀ j, raw3721step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3721step2 = (fun i j => raw3721step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3721step2 raw3721step1; decide +kernel
      have hl : raw3721step2Labels = raw3721step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step1 raw3721step1Labels permutation20 hz
    mixedMoment B raw3721step2 raw3721step2Labels = mixedMoment B raw3721step3 raw3721step3Labels := by
      have hz : ∀ j, raw3721step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3721step3 = (fun i j => raw3721step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3721step3 raw3721step2; decide +kernel
      have hl : raw3721step3Labels = raw3721step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step2 raw3721step2Labels permutation4 hz
    mixedMoment B raw3721step3 raw3721step3Labels = mixedMoment B raw3721step4 raw3721step4Labels := by
      have ha : raw3721step4 = (fun i j => raw3721step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3721step4 raw3721step3; decide +kernel
      have hl : raw3721step4Labels = raw3721step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3721step3 raw3721step3Labels permutation1 permutation0
    _ = mixedMoment B node4085 node4085Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw404 raw404Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw404 raw404Labels = mixedMoment B raw404step0 raw404step0Labels := by
      have ha : raw404step0 = (fun i j => raw404 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw404step0 raw404; decide +kernel
      have hl : raw404step0Labels = raw404Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw404 raw404Labels permutation2 permutation5
    mixedMoment B raw404step0 raw404step0Labels = mixedMoment B raw404step1 raw404step1Labels := by
      have ha : raw404step1 = raw404step0 := by apply Matrix.ext; unfold raw404step1 raw404step0; decide +kernel
      have hl : raw404step0Labels = labelEmbedding1 ∘ raw404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw404step0 raw404step0Labels raw404step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

theorem canonical405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw405 raw405Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw405 raw405Labels = mixedMoment B raw405step0 raw405step0Labels := by
      have ha : raw405step0 = (fun i j => raw405 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw405step0 raw405; decide +kernel
      have hl : raw405step0Labels = raw405Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw405 raw405Labels permutation2 permutation4
    _ = mixedMoment B node420 node420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4091 raw4091Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw4091 raw4091Labels = mixedMoment B raw4091step0 raw4091step0Labels := by
      have hz : ∀ j, raw4091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4091step0 = (fun i j => raw4091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4091step0 raw4091; decide +kernel
      have hl : raw4091step0Labels = raw4091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091 raw4091Labels permutation434 hz
    mixedMoment B raw4091step0 raw4091step0Labels = mixedMoment B raw4091step1 raw4091step1Labels := by
      have hz : ∀ j, raw4091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4091step1 = (fun i j => raw4091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4091step1 raw4091step0; decide +kernel
      have hl : raw4091step1Labels = raw4091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091step0 raw4091step0Labels permutation80 hz
    mixedMoment B raw4091step1 raw4091step1Labels = mixedMoment B raw4091step2 raw4091step2Labels := by
      have hz : ∀ j, raw4091step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4091step2 = (fun i j => raw4091step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4091step2 raw4091step1; decide +kernel
      have hl : raw4091step2Labels = raw4091step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091step1 raw4091step1Labels permutation14 hz
    mixedMoment B raw4091step2 raw4091step2Labels = mixedMoment B raw4091step3 raw4091step3Labels := by
      have ha : raw4091step3 = (fun i j => raw4091step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4091step3 raw4091step2; decide +kernel
      have hl : raw4091step3Labels = raw4091step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4091step2 raw4091step2Labels permutation3 permutation4
    mixedMoment B raw4091step3 raw4091step3Labels = mixedMoment B raw4091step4 raw4091step4Labels := by
      have ha : raw4091step4 = -raw4091step3 := by apply Matrix.ext; change ∀ i j, raw4091step4 i j = -(raw4091step3 i j); unfold raw4091step4 raw4091step3; decide +kernel
      have hl : raw4091step4Labels = raw4091step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4097 raw4097Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw4097 raw4097Labels = mixedMoment B raw4097step0 raw4097step0Labels := by
      have hz : ∀ j, raw4097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4097step0 = (fun i j => raw4097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4097step0 raw4097; decide +kernel
      have hl : raw4097step0Labels = raw4097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097 raw4097Labels permutation434 hz
    mixedMoment B raw4097step0 raw4097step0Labels = mixedMoment B raw4097step1 raw4097step1Labels := by
      have hz : ∀ j, raw4097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4097step1 = (fun i j => raw4097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4097step1 raw4097step0; decide +kernel
      have hl : raw4097step1Labels = raw4097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097step0 raw4097step0Labels permutation80 hz
    mixedMoment B raw4097step1 raw4097step1Labels = mixedMoment B raw4097step2 raw4097step2Labels := by
      have hz : ∀ j, raw4097step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4097step2 = (fun i j => raw4097step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4097step2 raw4097step1; decide +kernel
      have hl : raw4097step2Labels = raw4097step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097step1 raw4097step1Labels permutation14 hz
    mixedMoment B raw4097step2 raw4097step2Labels = mixedMoment B raw4097step3 raw4097step3Labels := by
      have ha : raw4097step3 = (fun i j => raw4097step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4097step3 raw4097step2; decide +kernel
      have hl : raw4097step3Labels = raw4097step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4097step2 raw4097step2Labels permutation7 permutation2
    _ = mixedMoment B node3634 node3634Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4272 raw4272Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw4272 raw4272Labels = mixedMoment B raw4272step0 raw4272step0Labels := by
      have hz : ∀ j, raw4272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4272step0 = (fun i j => raw4272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4272step0 raw4272; decide +kernel
      have hl : raw4272step0Labels = raw4272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4272 raw4272Labels permutation346 hz
    mixedMoment B raw4272step0 raw4272step0Labels = mixedMoment B raw4272step1 raw4272step1Labels := by
      have hz : ∀ j, raw4272step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4272step1 = (fun i j => raw4272step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4272step1 raw4272step0; decide +kernel
      have hl : raw4272step1Labels = raw4272step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4272step0 raw4272step0Labels permutation56 hz
    mixedMoment B raw4272step1 raw4272step1Labels = mixedMoment B raw4272step2 raw4272step2Labels := by
      have ha : raw4272step2 = (fun i j => raw4272step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4272step2 raw4272step1; decide +kernel
      have hl : raw4272step2Labels = raw4272step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4272step1 raw4272step1Labels permutation8 permutation4
    mixedMoment B raw4272step2 raw4272step2Labels = mixedMoment B raw4272step3 raw4272step3Labels := by
      have ha : raw4272step3 = -raw4272step2 := by apply Matrix.ext; change ∀ i j, raw4272step3 i j = -(raw4272step2 i j); unfold raw4272step3 raw4272step2; decide +kernel
      have hl : raw4272step3Labels = raw4272step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2290 node2290Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4376 raw4376Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw4376 raw4376Labels = mixedMoment B raw4376step0 raw4376step0Labels := by
      have hz : ∀ j, raw4376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4376step0 = (fun i j => raw4376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4376step0 raw4376; decide +kernel
      have hl : raw4376step0Labels = raw4376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4376 raw4376Labels permutation434 hz
    mixedMoment B raw4376step0 raw4376step0Labels = mixedMoment B raw4376step1 raw4376step1Labels := by
      have hz : ∀ j, raw4376step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4376step1 = (fun i j => raw4376step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4376step1 raw4376step0; decide +kernel
      have hl : raw4376step1Labels = raw4376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4376step0 raw4376step0Labels permutation80 hz
    mixedMoment B raw4376step1 raw4376step1Labels = mixedMoment B raw4376step2 raw4376step2Labels := by
      have ha : raw4376step2 = (fun i j => raw4376step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4376step2 raw4376step1; decide +kernel
      have hl : raw4376step2Labels = raw4376step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4376step1 raw4376step1Labels permutation8 permutation4
    mixedMoment B raw4376step2 raw4376step2Labels = mixedMoment B raw4376step3 raw4376step3Labels := by
      have ha : raw4376step3 = -raw4376step2 := by apply Matrix.ext; change ∀ i j, raw4376step3 i j = -(raw4376step2 i j); unfold raw4376step3 raw4376step2; decide +kernel
      have hl : raw4376step3Labels = raw4376step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical4377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4377 raw4377Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw4377 raw4377Labels = mixedMoment B raw4377step0 raw4377step0Labels := by
      have hz : ∀ j, raw4377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4377step0 = (fun i j => raw4377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4377step0 raw4377; decide +kernel
      have hl : raw4377step0Labels = raw4377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4377 raw4377Labels permutation434 hz
    mixedMoment B raw4377step0 raw4377step0Labels = mixedMoment B raw4377step1 raw4377step1Labels := by
      have hz : ∀ j, raw4377step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4377step1 = (fun i j => raw4377step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4377step1 raw4377step0; decide +kernel
      have hl : raw4377step1Labels = raw4377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4377step0 raw4377step0Labels permutation56 hz
    mixedMoment B raw4377step1 raw4377step1Labels = mixedMoment B raw4377step2 raw4377step2Labels := by
      have ha : raw4377step2 = (fun i j => raw4377step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4377step2 raw4377step1; decide +kernel
      have hl : raw4377step2Labels = raw4377step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4377step1 raw4377step1Labels permutation8 permutation4
    mixedMoment B raw4377step2 raw4377step2Labels = mixedMoment B raw4377step3 raw4377step3Labels := by
      have ha : raw4377step3 = -raw4377step2 := by apply Matrix.ext; change ∀ i j, raw4377step3 i j = -(raw4377step2 i j); unfold raw4377step3 raw4377step2; decide +kernel
      have hl : raw4377step3Labels = raw4377step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2290 node2290Labels := by rfl

theorem canonical4378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4378 raw4378Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw4378 raw4378Labels = mixedMoment B raw4378step0 raw4378step0Labels := by
      have hz : ∀ j, raw4378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4378step0 = (fun i j => raw4378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4378step0 raw4378; decide +kernel
      have hl : raw4378step0Labels = raw4378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4378 raw4378Labels permutation434 hz
    mixedMoment B raw4378step0 raw4378step0Labels = mixedMoment B raw4378step1 raw4378step1Labels := by
      have hz : ∀ j, raw4378step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4378step1 = (fun i j => raw4378step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4378step1 raw4378step0; decide +kernel
      have hl : raw4378step1Labels = raw4378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4378step0 raw4378step0Labels permutation80 hz
    mixedMoment B raw4378step1 raw4378step1Labels = mixedMoment B raw4378step2 raw4378step2Labels := by
      have hz : ∀ j, raw4378step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4378step2 = (fun i j => raw4378step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4378step2 raw4378step1; decide +kernel
      have hl : raw4378step2Labels = raw4378step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4378step1 raw4378step1Labels permutation14 hz
    mixedMoment B raw4378step2 raw4378step2Labels = mixedMoment B raw4378step3 raw4378step3Labels := by
      have ha : raw4378step3 = (fun i j => raw4378step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4378step3 raw4378step2; decide +kernel
      have hl : raw4378step3Labels = raw4378step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4378step2 raw4378step2Labels permutation2 permutation4
    mixedMoment B raw4378step3 raw4378step3Labels = mixedMoment B raw4378step4 raw4378step4Labels := by
      have ha : raw4378step4 = -raw4378step3 := by apply Matrix.ext; change ∀ i j, raw4378step4 i j = -(raw4378step3 i j); unfold raw4378step4 raw4378step3; decide +kernel
      have hl : raw4378step4Labels = raw4378step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2292 node2292Labels := by rfl

theorem canonical4401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4401 raw4401Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw4401 raw4401Labels = mixedMoment B raw4401step0 raw4401step0Labels := by
      have hz : ∀ j, raw4401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4401step0 = (fun i j => raw4401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4401step0 raw4401; decide +kernel
      have hl : raw4401step0Labels = raw4401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4401 raw4401Labels permutation434 hz
    mixedMoment B raw4401step0 raw4401step0Labels = mixedMoment B raw4401step1 raw4401step1Labels := by
      have hz : ∀ j, raw4401step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4401step1 = (fun i j => raw4401step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4401step1 raw4401step0; decide +kernel
      have hl : raw4401step1Labels = raw4401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4401step0 raw4401step0Labels permutation80 hz
    mixedMoment B raw4401step1 raw4401step1Labels = mixedMoment B raw4401step2 raw4401step2Labels := by
      have ha : raw4401step2 = (fun i j => raw4401step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4401step2 raw4401step1; decide +kernel
      have hl : raw4401step2Labels = raw4401step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4401step1 raw4401step1Labels permutation31 permutation3
    mixedMoment B raw4401step2 raw4401step2Labels = mixedMoment B raw4401step3 raw4401step3Labels := by
      have ha : raw4401step3 = -raw4401step2 := by apply Matrix.ext; change ∀ i j, raw4401step3 i j = -(raw4401step2 i j); unfold raw4401step3 raw4401step2; decide +kernel
      have hl : raw4401step3Labels = raw4401step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical4402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4402 raw4402Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw4402 raw4402Labels = mixedMoment B raw4402step0 raw4402step0Labels := by
      have hz : ∀ j, raw4402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4402step0 = (fun i j => raw4402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4402step0 raw4402; decide +kernel
      have hl : raw4402step0Labels = raw4402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4402 raw4402Labels permutation434 hz
    mixedMoment B raw4402step0 raw4402step0Labels = mixedMoment B raw4402step1 raw4402step1Labels := by
      have hz : ∀ j, raw4402step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4402step1 = (fun i j => raw4402step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4402step1 raw4402step0; decide +kernel
      have hl : raw4402step1Labels = raw4402step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4402step0 raw4402step0Labels permutation56 hz
    mixedMoment B raw4402step1 raw4402step1Labels = mixedMoment B raw4402step2 raw4402step2Labels := by
      have ha : raw4402step2 = (fun i j => raw4402step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4402step2 raw4402step1; decide +kernel
      have hl : raw4402step2Labels = raw4402step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4402step1 raw4402step1Labels permutation31 permutation3
    mixedMoment B raw4402step2 raw4402step2Labels = mixedMoment B raw4402step3 raw4402step3Labels := by
      have ha : raw4402step3 = -raw4402step2 := by apply Matrix.ext; change ∀ i j, raw4402step3 i j = -(raw4402step2 i j); unfold raw4402step3 raw4402step2; decide +kernel
      have hl : raw4402step3Labels = raw4402step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical4403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4403 raw4403Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw4403 raw4403Labels = mixedMoment B raw4403step0 raw4403step0Labels := by
      have hz : ∀ j, raw4403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4403step0 = (fun i j => raw4403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4403step0 raw4403; decide +kernel
      have hl : raw4403step0Labels = raw4403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4403 raw4403Labels permutation346 hz
    mixedMoment B raw4403step0 raw4403step0Labels = mixedMoment B raw4403step1 raw4403step1Labels := by
      have hz : ∀ j, raw4403step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4403step1 = (fun i j => raw4403step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4403step1 raw4403step0; decide +kernel
      have hl : raw4403step1Labels = raw4403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4403step0 raw4403step0Labels permutation56 hz
    mixedMoment B raw4403step1 raw4403step1Labels = mixedMoment B raw4403step2 raw4403step2Labels := by
      have ha : raw4403step2 = (fun i j => raw4403step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4403step2 raw4403step1; decide +kernel
      have hl : raw4403step2Labels = raw4403step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4403step1 raw4403step1Labels permutation31 permutation3
    mixedMoment B raw4403step2 raw4403step2Labels = mixedMoment B raw4403step3 raw4403step3Labels := by
      have ha : raw4403step3 = -raw4403step2 := by apply Matrix.ext; change ∀ i j, raw4403step3 i j = -(raw4403step2 i j); unfold raw4403step3 raw4403step2; decide +kernel
      have hl : raw4403step3Labels = raw4403step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical4404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4404 raw4404Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw4404 raw4404Labels = mixedMoment B raw4404step0 raw4404step0Labels := by
      have hz : ∀ j, raw4404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4404step0 = (fun i j => raw4404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4404step0 raw4404; decide +kernel
      have hl : raw4404step0Labels = raw4404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4404 raw4404Labels permutation434 hz
    mixedMoment B raw4404step0 raw4404step0Labels = mixedMoment B raw4404step1 raw4404step1Labels := by
      have hz : ∀ j, raw4404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4404step1 = (fun i j => raw4404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4404step1 raw4404step0; decide +kernel
      have hl : raw4404step1Labels = raw4404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4404step0 raw4404step0Labels permutation80 hz
    mixedMoment B raw4404step1 raw4404step1Labels = mixedMoment B raw4404step2 raw4404step2Labels := by
      have hz : ∀ j, raw4404step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4404step2 = (fun i j => raw4404step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4404step2 raw4404step1; decide +kernel
      have hl : raw4404step2Labels = raw4404step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4404step1 raw4404step1Labels permutation14 hz
    mixedMoment B raw4404step2 raw4404step2Labels = mixedMoment B raw4404step3 raw4404step3Labels := by
      have ha : raw4404step3 = (fun i j => raw4404step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4404step3 raw4404step2; decide +kernel
      have hl : raw4404step3Labels = raw4404step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4404step2 raw4404step2Labels permutation7 permutation3
    mixedMoment B raw4404step3 raw4404step3Labels = mixedMoment B raw4404step4 raw4404step4Labels := by
      have ha : raw4404step4 = -raw4404step3 := by apply Matrix.ext; change ∀ i j, raw4404step4 i j = -(raw4404step3 i j); unfold raw4404step4 raw4404step3; decide +kernel
      have hl : raw4404step4Labels = raw4404step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical4405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4405 raw4405Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw4405 raw4405Labels = mixedMoment B raw4405step0 raw4405step0Labels := by
      have hz : ∀ j, raw4405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4405step0 = (fun i j => raw4405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4405step0 raw4405; decide +kernel
      have hl : raw4405step0Labels = raw4405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4405 raw4405Labels permutation434 hz
    mixedMoment B raw4405step0 raw4405step0Labels = mixedMoment B raw4405step1 raw4405step1Labels := by
      have hz : ∀ j, raw4405step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4405step1 = (fun i j => raw4405step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4405step1 raw4405step0; decide +kernel
      have hl : raw4405step1Labels = raw4405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4405step0 raw4405step0Labels permutation80 hz
    mixedMoment B raw4405step1 raw4405step1Labels = mixedMoment B raw4405step2 raw4405step2Labels := by
      have hz : ∀ j, raw4405step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4405step2 = (fun i j => raw4405step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4405step2 raw4405step1; decide +kernel
      have hl : raw4405step2Labels = raw4405step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4405step1 raw4405step1Labels permutation14 hz
    mixedMoment B raw4405step2 raw4405step2Labels = mixedMoment B raw4405step3 raw4405step3Labels := by
      have ha : raw4405step3 = (fun i j => raw4405step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4405step3 raw4405step2; decide +kernel
      have hl : raw4405step3Labels = raw4405step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4405step2 raw4405step2Labels permutation7 permutation3
    mixedMoment B raw4405step3 raw4405step3Labels = mixedMoment B raw4405step4 raw4405step4Labels := by
      have ha : raw4405step4 = -raw4405step3 := by apply Matrix.ext; change ∀ i j, raw4405step4 i j = -(raw4405step3 i j); unfold raw4405step4 raw4405step3; decide +kernel
      have hl : raw4405step4Labels = raw4405step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical4406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4406 raw4406Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw4406 raw4406Labels = mixedMoment B raw4406step0 raw4406step0Labels := by
      have hz : ∀ j, raw4406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4406step0 = (fun i j => raw4406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4406step0 raw4406; decide +kernel
      have hl : raw4406step0Labels = raw4406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4406 raw4406Labels permutation434 hz
    mixedMoment B raw4406step0 raw4406step0Labels = mixedMoment B raw4406step1 raw4406step1Labels := by
      have hz : ∀ j, raw4406step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4406step1 = (fun i j => raw4406step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4406step1 raw4406step0; decide +kernel
      have hl : raw4406step1Labels = raw4406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4406step0 raw4406step0Labels permutation80 hz
    mixedMoment B raw4406step1 raw4406step1Labels = mixedMoment B raw4406step2 raw4406step2Labels := by
      have ha : raw4406step2 = (fun i j => raw4406step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4406step2 raw4406step1; decide +kernel
      have hl : raw4406step2Labels = raw4406step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4406step1 raw4406step1Labels permutation10 permutation3
    _ = mixedMoment B node1190 node1190Labels := by rfl

theorem canonical4407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4407 raw4407Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4407 raw4407Labels = mixedMoment B raw4407step0 raw4407step0Labels := by
      have hz : ∀ j, raw4407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4407step0 = (fun i j => raw4407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4407step0 raw4407; decide +kernel
      have hl : raw4407step0Labels = raw4407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4407 raw4407Labels permutation434 hz
    mixedMoment B raw4407step0 raw4407step0Labels = mixedMoment B raw4407step1 raw4407step1Labels := by
      have ha : raw4407step1 = (fun i j => raw4407step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4407step1 raw4407step0; decide +kernel
      have hl : raw4407step1Labels = raw4407step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4407step0 raw4407step0Labels permutation139 permutation3
    mixedMoment B raw4407step1 raw4407step1Labels = mixedMoment B raw4407step2 raw4407step2Labels := by
      have ha : raw4407step2 = -raw4407step1 := by apply Matrix.ext; change ∀ i j, raw4407step2 i j = -(raw4407step1 i j); unfold raw4407step2 raw4407step1; decide +kernel
      have hl : raw4407step2Labels = raw4407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical4408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4408 raw4408Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4408 raw4408Labels = mixedMoment B raw4408step0 raw4408step0Labels := by
      have hz : ∀ j, raw4408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4408step0 = (fun i j => raw4408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4408step0 raw4408; decide +kernel
      have hl : raw4408step0Labels = raw4408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4408 raw4408Labels permutation346 hz
    mixedMoment B raw4408step0 raw4408step0Labels = mixedMoment B raw4408step1 raw4408step1Labels := by
      have ha : raw4408step1 = (fun i j => raw4408step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4408step1 raw4408step0; decide +kernel
      have hl : raw4408step1Labels = raw4408step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4408step0 raw4408step0Labels permutation139 permutation3
    mixedMoment B raw4408step1 raw4408step1Labels = mixedMoment B raw4408step2 raw4408step2Labels := by
      have ha : raw4408step2 = -raw4408step1 := by apply Matrix.ext; change ∀ i j, raw4408step2 i j = -(raw4408step1 i j); unfold raw4408step2 raw4408step1; decide +kernel
      have hl : raw4408step2Labels = raw4408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical4409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4409 raw4409Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw4409 raw4409Labels = mixedMoment B raw4409step0 raw4409step0Labels := by
      have hz : ∀ j, raw4409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4409step0 = (fun i j => raw4409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4409step0 raw4409; decide +kernel
      have hl : raw4409step0Labels = raw4409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4409 raw4409Labels permutation434 hz
    mixedMoment B raw4409step0 raw4409step0Labels = mixedMoment B raw4409step1 raw4409step1Labels := by
      have hz : ∀ j, raw4409step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4409step1 = (fun i j => raw4409step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4409step1 raw4409step0; decide +kernel
      have hl : raw4409step1Labels = raw4409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4409step0 raw4409step0Labels permutation80 hz
    mixedMoment B raw4409step1 raw4409step1Labels = mixedMoment B raw4409step2 raw4409step2Labels := by
      have ha : raw4409step2 = (fun i j => raw4409step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4409step2 raw4409step1; decide +kernel
      have hl : raw4409step2Labels = raw4409step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4409step1 raw4409step1Labels permutation29 permutation3
    mixedMoment B raw4409step2 raw4409step2Labels = mixedMoment B raw4409step3 raw4409step3Labels := by
      have ha : raw4409step3 = -raw4409step2 := by apply Matrix.ext; change ∀ i j, raw4409step3 i j = -(raw4409step2 i j); unfold raw4409step3 raw4409step2; decide +kernel
      have hl : raw4409step3Labels = raw4409step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1951 node1951Labels := by rfl

theorem canonical4410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4410 raw4410Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw4410 raw4410Labels = mixedMoment B raw4410step0 raw4410step0Labels := by
      have hz : ∀ j, raw4410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4410step0 = (fun i j => raw4410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4410step0 raw4410; decide +kernel
      have hl : raw4410step0Labels = raw4410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4410 raw4410Labels permutation434 hz
    mixedMoment B raw4410step0 raw4410step0Labels = mixedMoment B raw4410step1 raw4410step1Labels := by
      have hz : ∀ j, raw4410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4410step1 = (fun i j => raw4410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4410step1 raw4410step0; decide +kernel
      have hl : raw4410step1Labels = raw4410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4410step0 raw4410step0Labels permutation80 hz
    mixedMoment B raw4410step1 raw4410step1Labels = mixedMoment B raw4410step2 raw4410step2Labels := by
      have ha : raw4410step2 = (fun i j => raw4410step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4410step2 raw4410step1; decide +kernel
      have hl : raw4410step2Labels = raw4410step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4410step1 raw4410step1Labels permutation10 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical4411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4411 raw4411Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw4411 raw4411Labels = mixedMoment B raw4411step0 raw4411step0Labels := by
      have hz : ∀ j, raw4411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4411step0 = (fun i j => raw4411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4411step0 raw4411; decide +kernel
      have hl : raw4411step0Labels = raw4411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4411 raw4411Labels permutation434 hz
    mixedMoment B raw4411step0 raw4411step0Labels = mixedMoment B raw4411step1 raw4411step1Labels := by
      have hz : ∀ j, raw4411step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4411step1 = (fun i j => raw4411step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4411step1 raw4411step0; decide +kernel
      have hl : raw4411step1Labels = raw4411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4411step0 raw4411step0Labels permutation56 hz
    mixedMoment B raw4411step1 raw4411step1Labels = mixedMoment B raw4411step2 raw4411step2Labels := by
      have ha : raw4411step2 = (fun i j => raw4411step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4411step2 raw4411step1; decide +kernel
      have hl : raw4411step2Labels = raw4411step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4411step1 raw4411step1Labels permutation10 permutation3
    _ = mixedMoment B node1190 node1190Labels := by rfl

theorem canonical4412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4412 raw4412Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4412 raw4412Labels = mixedMoment B raw4412step0 raw4412step0Labels := by
      have hz : ∀ j, raw4412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4412step0 = (fun i j => raw4412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4412step0 raw4412; decide +kernel
      have hl : raw4412step0Labels = raw4412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4412 raw4412Labels permutation434 hz
    mixedMoment B raw4412step0 raw4412step0Labels = mixedMoment B raw4412step1 raw4412step1Labels := by
      have ha : raw4412step1 = (fun i j => raw4412step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4412step1 raw4412step0; decide +kernel
      have hl : raw4412step1Labels = raw4412step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4412step0 raw4412step0Labels permutation145 permutation3
    mixedMoment B raw4412step1 raw4412step1Labels = mixedMoment B raw4412step2 raw4412step2Labels := by
      have ha : raw4412step2 = -raw4412step1 := by apply Matrix.ext; change ∀ i j, raw4412step2 i j = -(raw4412step1 i j); unfold raw4412step2 raw4412step1; decide +kernel
      have hl : raw4412step2Labels = raw4412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical4413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4413 raw4413Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4413 raw4413Labels = mixedMoment B raw4413step0 raw4413step0Labels := by
      have hz : ∀ j, raw4413 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4413step0 = (fun i j => raw4413 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4413step0 raw4413; decide +kernel
      have hl : raw4413step0Labels = raw4413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4413 raw4413Labels permutation265 hz
    mixedMoment B raw4413step0 raw4413step0Labels = mixedMoment B raw4413step1 raw4413step1Labels := by
      have ha : raw4413step1 = (fun i j => raw4413step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4413step1 raw4413step0; decide +kernel
      have hl : raw4413step1Labels = raw4413step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4413step0 raw4413step0Labels permutation139 permutation3
    mixedMoment B raw4413step1 raw4413step1Labels = mixedMoment B raw4413step2 raw4413step2Labels := by
      have ha : raw4413step2 = -raw4413step1 := by apply Matrix.ext; change ∀ i j, raw4413step2 i j = -(raw4413step1 i j); unfold raw4413step2 raw4413step1; decide +kernel
      have hl : raw4413step2Labels = raw4413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical4414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4414 raw4414Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw4414 raw4414Labels = mixedMoment B raw4414step0 raw4414step0Labels := by
      have hz : ∀ j, raw4414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4414step0 = (fun i j => raw4414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4414step0 raw4414; decide +kernel
      have hl : raw4414step0Labels = raw4414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4414 raw4414Labels permutation434 hz
    mixedMoment B raw4414step0 raw4414step0Labels = mixedMoment B raw4414step1 raw4414step1Labels := by
      have hz : ∀ j, raw4414step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4414step1 = (fun i j => raw4414step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4414step1 raw4414step0; decide +kernel
      have hl : raw4414step1Labels = raw4414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4414step0 raw4414step0Labels permutation56 hz
    mixedMoment B raw4414step1 raw4414step1Labels = mixedMoment B raw4414step2 raw4414step2Labels := by
      have ha : raw4414step2 = (fun i j => raw4414step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4414step2 raw4414step1; decide +kernel
      have hl : raw4414step2Labels = raw4414step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4414step1 raw4414step1Labels permutation29 permutation3
    mixedMoment B raw4414step2 raw4414step2Labels = mixedMoment B raw4414step3 raw4414step3Labels := by
      have ha : raw4414step3 = -raw4414step2 := by apply Matrix.ext; change ∀ i j, raw4414step3 i j = -(raw4414step2 i j); unfold raw4414step3 raw4414step2; decide +kernel
      have hl : raw4414step3Labels = raw4414step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1951 node1951Labels := by rfl

theorem canonical4415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4415 raw4415Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw4415 raw4415Labels = mixedMoment B raw4415step0 raw4415step0Labels := by
      have hz : ∀ j, raw4415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4415step0 = (fun i j => raw4415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4415step0 raw4415; decide +kernel
      have hl : raw4415step0Labels = raw4415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4415 raw4415Labels permutation434 hz
    mixedMoment B raw4415step0 raw4415step0Labels = mixedMoment B raw4415step1 raw4415step1Labels := by
      have hz : ∀ j, raw4415step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4415step1 = (fun i j => raw4415step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4415step1 raw4415step0; decide +kernel
      have hl : raw4415step1Labels = raw4415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4415step0 raw4415step0Labels permutation56 hz
    mixedMoment B raw4415step1 raw4415step1Labels = mixedMoment B raw4415step2 raw4415step2Labels := by
      have ha : raw4415step2 = (fun i j => raw4415step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4415step2 raw4415step1; decide +kernel
      have hl : raw4415step2Labels = raw4415step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4415step1 raw4415step1Labels permutation10 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical4416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4416 raw4416Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw4416 raw4416Labels = mixedMoment B raw4416step0 raw4416step0Labels := by
      have hz : ∀ j, raw4416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4416step0 = (fun i j => raw4416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4416step0 raw4416; decide +kernel
      have hl : raw4416step0Labels = raw4416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4416 raw4416Labels permutation346 hz
    mixedMoment B raw4416step0 raw4416step0Labels = mixedMoment B raw4416step1 raw4416step1Labels := by
      have hz : ∀ j, raw4416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4416step1 = (fun i j => raw4416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4416step1 raw4416step0; decide +kernel
      have hl : raw4416step1Labels = raw4416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4416step0 raw4416step0Labels permutation56 hz
    mixedMoment B raw4416step1 raw4416step1Labels = mixedMoment B raw4416step2 raw4416step2Labels := by
      have ha : raw4416step2 = (fun i j => raw4416step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4416step2 raw4416step1; decide +kernel
      have hl : raw4416step2Labels = raw4416step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4416step1 raw4416step1Labels permutation10 permutation3
    _ = mixedMoment B node1190 node1190Labels := by rfl

theorem canonical4417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4417 raw4417Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4417 raw4417Labels = mixedMoment B raw4417step0 raw4417step0Labels := by
      have hz : ∀ j, raw4417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4417step0 = (fun i j => raw4417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4417step0 raw4417; decide +kernel
      have hl : raw4417step0Labels = raw4417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4417 raw4417Labels permutation346 hz
    mixedMoment B raw4417step0 raw4417step0Labels = mixedMoment B raw4417step1 raw4417step1Labels := by
      have ha : raw4417step1 = (fun i j => raw4417step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4417step1 raw4417step0; decide +kernel
      have hl : raw4417step1Labels = raw4417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4417step0 raw4417step0Labels permutation145 permutation3
    mixedMoment B raw4417step1 raw4417step1Labels = mixedMoment B raw4417step2 raw4417step2Labels := by
      have ha : raw4417step2 = -raw4417step1 := by apply Matrix.ext; change ∀ i j, raw4417step2 i j = -(raw4417step1 i j); unfold raw4417step2 raw4417step1; decide +kernel
      have hl : raw4417step2Labels = raw4417step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical4418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4418 raw4418Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw4418 raw4418Labels = mixedMoment B raw4418step0 raw4418step0Labels := by
      have hz : ∀ j, raw4418 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4418step0 = (fun i j => raw4418 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4418step0 raw4418; decide +kernel
      have hl : raw4418step0Labels = raw4418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4418 raw4418Labels permutation265 hz
    mixedMoment B raw4418step0 raw4418step0Labels = mixedMoment B raw4418step1 raw4418step1Labels := by
      have ha : raw4418step1 = (fun i j => raw4418step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4418step1 raw4418step0; decide +kernel
      have hl : raw4418step1Labels = raw4418step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4418step0 raw4418step0Labels permutation145 permutation3
    mixedMoment B raw4418step1 raw4418step1Labels = mixedMoment B raw4418step2 raw4418step2Labels := by
      have ha : raw4418step2 = -raw4418step1 := by apply Matrix.ext; change ∀ i j, raw4418step2 i j = -(raw4418step1 i j); unfold raw4418step2 raw4418step1; decide +kernel
      have hl : raw4418step2Labels = raw4418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical4419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4419 raw4419Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw4419 raw4419Labels = mixedMoment B raw4419step0 raw4419step0Labels := by
      have hz : ∀ j, raw4419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4419step0 = (fun i j => raw4419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4419step0 raw4419; decide +kernel
      have hl : raw4419step0Labels = raw4419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4419 raw4419Labels permutation346 hz
    mixedMoment B raw4419step0 raw4419step0Labels = mixedMoment B raw4419step1 raw4419step1Labels := by
      have hz : ∀ j, raw4419step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4419step1 = (fun i j => raw4419step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4419step1 raw4419step0; decide +kernel
      have hl : raw4419step1Labels = raw4419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4419step0 raw4419step0Labels permutation56 hz
    mixedMoment B raw4419step1 raw4419step1Labels = mixedMoment B raw4419step2 raw4419step2Labels := by
      have ha : raw4419step2 = (fun i j => raw4419step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4419step2 raw4419step1; decide +kernel
      have hl : raw4419step2Labels = raw4419step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4419step1 raw4419step1Labels permutation29 permutation3
    mixedMoment B raw4419step2 raw4419step2Labels = mixedMoment B raw4419step3 raw4419step3Labels := by
      have ha : raw4419step3 = -raw4419step2 := by apply Matrix.ext; change ∀ i j, raw4419step3 i j = -(raw4419step2 i j); unfold raw4419step3 raw4419step2; decide +kernel
      have hl : raw4419step3Labels = raw4419step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1951 node1951Labels := by rfl

theorem canonical4420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4420 raw4420Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw4420 raw4420Labels = mixedMoment B raw4420step0 raw4420step0Labels := by
      have hz : ∀ j, raw4420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4420step0 = (fun i j => raw4420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4420step0 raw4420; decide +kernel
      have hl : raw4420step0Labels = raw4420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4420 raw4420Labels permutation346 hz
    mixedMoment B raw4420step0 raw4420step0Labels = mixedMoment B raw4420step1 raw4420step1Labels := by
      have hz : ∀ j, raw4420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4420step1 = (fun i j => raw4420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4420step1 raw4420step0; decide +kernel
      have hl : raw4420step1Labels = raw4420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4420step0 raw4420step0Labels permutation56 hz
    mixedMoment B raw4420step1 raw4420step1Labels = mixedMoment B raw4420step2 raw4420step2Labels := by
      have ha : raw4420step2 = (fun i j => raw4420step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4420step2 raw4420step1; decide +kernel
      have hl : raw4420step2Labels = raw4420step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4420step1 raw4420step1Labels permutation10 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical4421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4421 raw4421Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw4421 raw4421Labels = mixedMoment B raw4421step0 raw4421step0Labels := by
      have hz : ∀ j, raw4421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4421step0 = (fun i j => raw4421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4421step0 raw4421; decide +kernel
      have hl : raw4421step0Labels = raw4421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4421 raw4421Labels permutation434 hz
    mixedMoment B raw4421step0 raw4421step0Labels = mixedMoment B raw4421step1 raw4421step1Labels := by
      have hz : ∀ j, raw4421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4421step1 = (fun i j => raw4421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4421step1 raw4421step0; decide +kernel
      have hl : raw4421step1Labels = raw4421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4421step0 raw4421step0Labels permutation80 hz
    mixedMoment B raw4421step1 raw4421step1Labels = mixedMoment B raw4421step2 raw4421step2Labels := by
      have hz : ∀ j, raw4421step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4421step2 = (fun i j => raw4421step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4421step2 raw4421step1; decide +kernel
      have hl : raw4421step2Labels = raw4421step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4421step1 raw4421step1Labels permutation14 hz
    mixedMoment B raw4421step2 raw4421step2Labels = mixedMoment B raw4421step3 raw4421step3Labels := by
      have ha : raw4421step3 = (fun i j => raw4421step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4421step3 raw4421step2; decide +kernel
      have hl : raw4421step3Labels = raw4421step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4421step2 raw4421step2Labels permutation2 permutation3
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical4422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4422 raw4422Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4422 raw4422Labels = mixedMoment B raw4422step0 raw4422step0Labels := by
      have hz : ∀ j, raw4422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4422step0 = (fun i j => raw4422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4422step0 raw4422; decide +kernel
      have hl : raw4422step0Labels = raw4422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4422 raw4422Labels permutation434 hz
    mixedMoment B raw4422step0 raw4422step0Labels = mixedMoment B raw4422step1 raw4422step1Labels := by
      have hz : ∀ j, raw4422step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4422step1 = (fun i j => raw4422step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4422step1 raw4422step0; decide +kernel
      have hl : raw4422step1Labels = raw4422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4422step0 raw4422step0Labels permutation80 hz
    mixedMoment B raw4422step1 raw4422step1Labels = mixedMoment B raw4422step2 raw4422step2Labels := by
      have ha : raw4422step2 = (fun i j => raw4422step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4422step2 raw4422step1; decide +kernel
      have hl : raw4422step2Labels = raw4422step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4422step1 raw4422step1Labels permutation31 permutation3
    mixedMoment B raw4422step2 raw4422step2Labels = mixedMoment B raw4422step3 raw4422step3Labels := by
      have ha : raw4422step3 = -raw4422step2 := by apply Matrix.ext; change ∀ i j, raw4422step3 i j = -(raw4422step2 i j); unfold raw4422step3 raw4422step2; decide +kernel
      have hl : raw4422step3Labels = raw4422step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical4423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4423 raw4423Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4423 raw4423Labels = mixedMoment B raw4423step0 raw4423step0Labels := by
      have hz : ∀ j, raw4423 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4423step0 = (fun i j => raw4423 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4423step0 raw4423; decide +kernel
      have hl : raw4423step0Labels = raw4423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4423 raw4423Labels permutation434 hz
    mixedMoment B raw4423step0 raw4423step0Labels = mixedMoment B raw4423step1 raw4423step1Labels := by
      have hz : ∀ j, raw4423step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4423step1 = (fun i j => raw4423step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4423step1 raw4423step0; decide +kernel
      have hl : raw4423step1Labels = raw4423step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4423step0 raw4423step0Labels permutation56 hz
    mixedMoment B raw4423step1 raw4423step1Labels = mixedMoment B raw4423step2 raw4423step2Labels := by
      have ha : raw4423step2 = (fun i j => raw4423step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4423step2 raw4423step1; decide +kernel
      have hl : raw4423step2Labels = raw4423step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4423step1 raw4423step1Labels permutation31 permutation3
    mixedMoment B raw4423step2 raw4423step2Labels = mixedMoment B raw4423step3 raw4423step3Labels := by
      have ha : raw4423step3 = -raw4423step2 := by apply Matrix.ext; change ∀ i j, raw4423step3 i j = -(raw4423step2 i j); unfold raw4423step3 raw4423step2; decide +kernel
      have hl : raw4423step3Labels = raw4423step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical4424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4424 raw4424Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4424 raw4424Labels = mixedMoment B raw4424step0 raw4424step0Labels := by
      have hz : ∀ j, raw4424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4424step0 = (fun i j => raw4424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4424step0 raw4424; decide +kernel
      have hl : raw4424step0Labels = raw4424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4424 raw4424Labels permutation346 hz
    mixedMoment B raw4424step0 raw4424step0Labels = mixedMoment B raw4424step1 raw4424step1Labels := by
      have hz : ∀ j, raw4424step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4424step1 = (fun i j => raw4424step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4424step1 raw4424step0; decide +kernel
      have hl : raw4424step1Labels = raw4424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4424step0 raw4424step0Labels permutation56 hz
    mixedMoment B raw4424step1 raw4424step1Labels = mixedMoment B raw4424step2 raw4424step2Labels := by
      have ha : raw4424step2 = (fun i j => raw4424step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4424step2 raw4424step1; decide +kernel
      have hl : raw4424step2Labels = raw4424step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4424step1 raw4424step1Labels permutation31 permutation3
    mixedMoment B raw4424step2 raw4424step2Labels = mixedMoment B raw4424step3 raw4424step3Labels := by
      have ha : raw4424step3 = -raw4424step2 := by apply Matrix.ext; change ∀ i j, raw4424step3 i j = -(raw4424step2 i j); unfold raw4424step3 raw4424step2; decide +kernel
      have hl : raw4424step3Labels = raw4424step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical4425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4425 raw4425Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw4425 raw4425Labels = mixedMoment B raw4425step0 raw4425step0Labels := by
      have hz : ∀ j, raw4425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4425step0 = (fun i j => raw4425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4425step0 raw4425; decide +kernel
      have hl : raw4425step0Labels = raw4425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4425 raw4425Labels permutation434 hz
    mixedMoment B raw4425step0 raw4425step0Labels = mixedMoment B raw4425step1 raw4425step1Labels := by
      have hz : ∀ j, raw4425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4425step1 = (fun i j => raw4425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4425step1 raw4425step0; decide +kernel
      have hl : raw4425step1Labels = raw4425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4425step0 raw4425step0Labels permutation80 hz
    mixedMoment B raw4425step1 raw4425step1Labels = mixedMoment B raw4425step2 raw4425step2Labels := by
      have hz : ∀ j, raw4425step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4425step2 = (fun i j => raw4425step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4425step2 raw4425step1; decide +kernel
      have hl : raw4425step2Labels = raw4425step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4425step1 raw4425step1Labels permutation14 hz
    mixedMoment B raw4425step2 raw4425step2Labels = mixedMoment B raw4425step3 raw4425step3Labels := by
      have ha : raw4425step3 = (fun i j => raw4425step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4425step3 raw4425step2; decide +kernel
      have hl : raw4425step3Labels = raw4425step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4425step2 raw4425step2Labels permutation2 permutation3
    _ = mixedMoment B node3121 node3121Labels := by rfl

theorem canonical4426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4426 raw4426Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw4426 raw4426Labels = mixedMoment B raw4426step0 raw4426step0Labels := by
      have hz : ∀ j, raw4426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4426step0 = (fun i j => raw4426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4426step0 raw4426; decide +kernel
      have hl : raw4426step0Labels = raw4426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4426 raw4426Labels permutation434 hz
    mixedMoment B raw4426step0 raw4426step0Labels = mixedMoment B raw4426step1 raw4426step1Labels := by
      have hz : ∀ j, raw4426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4426step1 = (fun i j => raw4426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4426step1 raw4426step0; decide +kernel
      have hl : raw4426step1Labels = raw4426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4426step0 raw4426step0Labels permutation80 hz
    mixedMoment B raw4426step1 raw4426step1Labels = mixedMoment B raw4426step2 raw4426step2Labels := by
      have hz : ∀ j, raw4426step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4426step2 = (fun i j => raw4426step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4426step2 raw4426step1; decide +kernel
      have hl : raw4426step2Labels = raw4426step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4426step1 raw4426step1Labels permutation14 hz
    mixedMoment B raw4426step2 raw4426step2Labels = mixedMoment B raw4426step3 raw4426step3Labels := by
      have ha : raw4426step3 = (fun i j => raw4426step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4426step3 raw4426step2; decide +kernel
      have hl : raw4426step3Labels = raw4426step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4426step2 raw4426step2Labels permutation7 permutation3
    mixedMoment B raw4426step3 raw4426step3Labels = mixedMoment B raw4426step4 raw4426step4Labels := by
      have ha : raw4426step4 = -raw4426step3 := by apply Matrix.ext; change ∀ i j, raw4426step4 i j = -(raw4426step3 i j); unfold raw4426step4 raw4426step3; decide +kernel
      have hl : raw4426step4Labels = raw4426step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node832 node832Labels := by rfl

theorem canonical4427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4427 raw4427Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw4427 raw4427Labels = mixedMoment B raw4427step0 raw4427step0Labels := by
      have hz : ∀ j, raw4427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4427step0 = (fun i j => raw4427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4427step0 raw4427; decide +kernel
      have hl : raw4427step0Labels = raw4427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4427 raw4427Labels permutation434 hz
    mixedMoment B raw4427step0 raw4427step0Labels = mixedMoment B raw4427step1 raw4427step1Labels := by
      have hz : ∀ j, raw4427step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4427step1 = (fun i j => raw4427step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4427step1 raw4427step0; decide +kernel
      have hl : raw4427step1Labels = raw4427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4427step0 raw4427step0Labels permutation80 hz
    mixedMoment B raw4427step1 raw4427step1Labels = mixedMoment B raw4427step2 raw4427step2Labels := by
      have ha : raw4427step2 = (fun i j => raw4427step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4427step2 raw4427step1; decide +kernel
      have hl : raw4427step2Labels = raw4427step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4427step1 raw4427step1Labels permutation31 permutation3
    mixedMoment B raw4427step2 raw4427step2Labels = mixedMoment B raw4427step3 raw4427step3Labels := by
      have ha : raw4427step3 = -raw4427step2 := by apply Matrix.ext; change ∀ i j, raw4427step3 i j = -(raw4427step2 i j); unfold raw4427step3 raw4427step2; decide +kernel
      have hl : raw4427step3Labels = raw4427step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node828 node828Labels := by rfl

theorem canonical4428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4428 raw4428Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw4428 raw4428Labels = mixedMoment B raw4428step0 raw4428step0Labels := by
      have hz : ∀ j, raw4428 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4428step0 = (fun i j => raw4428 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4428step0 raw4428; decide +kernel
      have hl : raw4428step0Labels = raw4428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4428 raw4428Labels permutation434 hz
    mixedMoment B raw4428step0 raw4428step0Labels = mixedMoment B raw4428step1 raw4428step1Labels := by
      have hz : ∀ j, raw4428step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4428step1 = (fun i j => raw4428step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4428step1 raw4428step0; decide +kernel
      have hl : raw4428step1Labels = raw4428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4428step0 raw4428step0Labels permutation56 hz
    mixedMoment B raw4428step1 raw4428step1Labels = mixedMoment B raw4428step2 raw4428step2Labels := by
      have ha : raw4428step2 = (fun i j => raw4428step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4428step2 raw4428step1; decide +kernel
      have hl : raw4428step2Labels = raw4428step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4428step1 raw4428step1Labels permutation31 permutation3
    mixedMoment B raw4428step2 raw4428step2Labels = mixedMoment B raw4428step3 raw4428step3Labels := by
      have ha : raw4428step3 = -raw4428step2 := by apply Matrix.ext; change ∀ i j, raw4428step3 i j = -(raw4428step2 i j); unfold raw4428step3 raw4428step2; decide +kernel
      have hl : raw4428step3Labels = raw4428step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node828 node828Labels := by rfl

theorem canonical4429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4429 raw4429Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw4429 raw4429Labels = mixedMoment B raw4429step0 raw4429step0Labels := by
      have hz : ∀ j, raw4429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4429step0 = (fun i j => raw4429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4429step0 raw4429; decide +kernel
      have hl : raw4429step0Labels = raw4429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4429 raw4429Labels permutation346 hz
    mixedMoment B raw4429step0 raw4429step0Labels = mixedMoment B raw4429step1 raw4429step1Labels := by
      have hz : ∀ j, raw4429step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4429step1 = (fun i j => raw4429step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4429step1 raw4429step0; decide +kernel
      have hl : raw4429step1Labels = raw4429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4429step0 raw4429step0Labels permutation56 hz
    mixedMoment B raw4429step1 raw4429step1Labels = mixedMoment B raw4429step2 raw4429step2Labels := by
      have ha : raw4429step2 = (fun i j => raw4429step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4429step2 raw4429step1; decide +kernel
      have hl : raw4429step2Labels = raw4429step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4429step1 raw4429step1Labels permutation31 permutation3
    mixedMoment B raw4429step2 raw4429step2Labels = mixedMoment B raw4429step3 raw4429step3Labels := by
      have ha : raw4429step3 = -raw4429step2 := by apply Matrix.ext; change ∀ i j, raw4429step3 i j = -(raw4429step2 i j); unfold raw4429step3 raw4429step2; decide +kernel
      have hl : raw4429step3Labels = raw4429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node828 node828Labels := by rfl

theorem canonical4430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4430 raw4430Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw4430 raw4430Labels = mixedMoment B raw4430step0 raw4430step0Labels := by
      have hz : ∀ j, raw4430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4430step0 = (fun i j => raw4430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4430step0 raw4430; decide +kernel
      have hl : raw4430step0Labels = raw4430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4430 raw4430Labels permutation434 hz
    mixedMoment B raw4430step0 raw4430step0Labels = mixedMoment B raw4430step1 raw4430step1Labels := by
      have hz : ∀ j, raw4430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4430step1 = (fun i j => raw4430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4430step1 raw4430step0; decide +kernel
      have hl : raw4430step1Labels = raw4430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4430step0 raw4430step0Labels permutation80 hz
    mixedMoment B raw4430step1 raw4430step1Labels = mixedMoment B raw4430step2 raw4430step2Labels := by
      have hz : ∀ j, raw4430step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4430step2 = (fun i j => raw4430step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4430step2 raw4430step1; decide +kernel
      have hl : raw4430step2Labels = raw4430step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4430step1 raw4430step1Labels permutation14 hz
    mixedMoment B raw4430step2 raw4430step2Labels = mixedMoment B raw4430step3 raw4430step3Labels := by
      have ha : raw4430step3 = (fun i j => raw4430step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4430step3 raw4430step2; decide +kernel
      have hl : raw4430step3Labels = raw4430step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4430step2 raw4430step2Labels permutation7 permutation3
    mixedMoment B raw4430step3 raw4430step3Labels = mixedMoment B raw4430step4 raw4430step4Labels := by
      have ha : raw4430step4 = -raw4430step3 := by apply Matrix.ext; change ∀ i j, raw4430step4 i j = -(raw4430step3 i j); unfold raw4430step4 raw4430step3; decide +kernel
      have hl : raw4430step4Labels = raw4430step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node860 node860Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4491 raw4491Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw4491 raw4491Labels = mixedMoment B raw4491step0 raw4491step0Labels := by
      have hz : ∀ j, raw4491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4491step0 = (fun i j => raw4491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4491step0 raw4491; decide +kernel
      have hl : raw4491step0Labels = raw4491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4491 raw4491Labels permutation434 hz
    mixedMoment B raw4491step0 raw4491step0Labels = mixedMoment B raw4491step1 raw4491step1Labels := by
      have hz : ∀ j, raw4491step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4491step1 = (fun i j => raw4491step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4491step1 raw4491step0; decide +kernel
      have hl : raw4491step1Labels = raw4491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4491step0 raw4491step0Labels permutation80 hz
    mixedMoment B raw4491step1 raw4491step1Labels = mixedMoment B raw4491step2 raw4491step2Labels := by
      have ha : raw4491step2 = (fun i j => raw4491step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4491step2 raw4491step1; decide +kernel
      have hl : raw4491step2Labels = raw4491step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4491step1 raw4491step1Labels permutation28 permutation7
    mixedMoment B raw4491step2 raw4491step2Labels = mixedMoment B raw4491step3 raw4491step3Labels := by
      have ha : raw4491step3 = raw4491step2 := by apply Matrix.ext; unfold raw4491step3 raw4491step2; decide +kernel
      have hl : raw4491step2Labels = labelEmbedding1 ∘ raw4491step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4491step2 raw4491step2Labels raw4491step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical4492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4492 raw4492Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw4492 raw4492Labels = mixedMoment B raw4492step0 raw4492step0Labels := by
      have hz : ∀ j, raw4492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4492step0 = (fun i j => raw4492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4492step0 raw4492; decide +kernel
      have hl : raw4492step0Labels = raw4492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4492 raw4492Labels permutation434 hz
    mixedMoment B raw4492step0 raw4492step0Labels = mixedMoment B raw4492step1 raw4492step1Labels := by
      have hz : ∀ j, raw4492step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4492step1 = (fun i j => raw4492step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4492step1 raw4492step0; decide +kernel
      have hl : raw4492step1Labels = raw4492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4492step0 raw4492step0Labels permutation56 hz
    mixedMoment B raw4492step1 raw4492step1Labels = mixedMoment B raw4492step2 raw4492step2Labels := by
      have ha : raw4492step2 = (fun i j => raw4492step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4492step2 raw4492step1; decide +kernel
      have hl : raw4492step2Labels = raw4492step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4492step1 raw4492step1Labels permutation28 permutation7
    mixedMoment B raw4492step2 raw4492step2Labels = mixedMoment B raw4492step3 raw4492step3Labels := by
      have ha : raw4492step3 = raw4492step2 := by apply Matrix.ext; unfold raw4492step3 raw4492step2; decide +kernel
      have hl : raw4492step2Labels = labelEmbedding1 ∘ raw4492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4492step2 raw4492step2Labels raw4492step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical4493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4493 raw4493Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw4493 raw4493Labels = mixedMoment B raw4493step0 raw4493step0Labels := by
      have hz : ∀ j, raw4493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4493step0 = (fun i j => raw4493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4493step0 raw4493; decide +kernel
      have hl : raw4493step0Labels = raw4493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4493 raw4493Labels permutation346 hz
    mixedMoment B raw4493step0 raw4493step0Labels = mixedMoment B raw4493step1 raw4493step1Labels := by
      have hz : ∀ j, raw4493step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4493step1 = (fun i j => raw4493step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4493step1 raw4493step0; decide +kernel
      have hl : raw4493step1Labels = raw4493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4493step0 raw4493step0Labels permutation56 hz
    mixedMoment B raw4493step1 raw4493step1Labels = mixedMoment B raw4493step2 raw4493step2Labels := by
      have ha : raw4493step2 = (fun i j => raw4493step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4493step2 raw4493step1; decide +kernel
      have hl : raw4493step2Labels = raw4493step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4493step1 raw4493step1Labels permutation28 permutation7
    mixedMoment B raw4493step2 raw4493step2Labels = mixedMoment B raw4493step3 raw4493step3Labels := by
      have ha : raw4493step3 = raw4493step2 := by apply Matrix.ext; unfold raw4493step3 raw4493step2; decide +kernel
      have hl : raw4493step2Labels = labelEmbedding1 ∘ raw4493step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4493step2 raw4493step2Labels raw4493step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical4494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4494 raw4494Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw4494 raw4494Labels = mixedMoment B raw4494step0 raw4494step0Labels := by
      have hz : ∀ j, raw4494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4494step0 = (fun i j => raw4494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4494step0 raw4494; decide +kernel
      have hl : raw4494step0Labels = raw4494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4494 raw4494Labels permutation434 hz
    mixedMoment B raw4494step0 raw4494step0Labels = mixedMoment B raw4494step1 raw4494step1Labels := by
      have hz : ∀ j, raw4494step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4494step1 = (fun i j => raw4494step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4494step1 raw4494step0; decide +kernel
      have hl : raw4494step1Labels = raw4494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4494step0 raw4494step0Labels permutation80 hz
    mixedMoment B raw4494step1 raw4494step1Labels = mixedMoment B raw4494step2 raw4494step2Labels := by
      have hz : ∀ j, raw4494step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4494step2 = (fun i j => raw4494step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4494step2 raw4494step1; decide +kernel
      have hl : raw4494step2Labels = raw4494step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4494step1 raw4494step1Labels permutation14 hz
    mixedMoment B raw4494step2 raw4494step2Labels = mixedMoment B raw4494step3 raw4494step3Labels := by
      have ha : raw4494step3 = (fun i j => raw4494step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4494step3 raw4494step2; decide +kernel
      have hl : raw4494step3Labels = raw4494step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4494step2 raw4494step2Labels permutation6 permutation7
    mixedMoment B raw4494step3 raw4494step3Labels = mixedMoment B raw4494step4 raw4494step4Labels := by
      have ha : raw4494step4 = raw4494step3 := by apply Matrix.ext; unfold raw4494step4 raw4494step3; decide +kernel
      have hl : raw4494step3Labels = labelEmbedding1 ∘ raw4494step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4494step3 raw4494step3Labels raw4494step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4495 raw4495Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw4495 raw4495Labels = mixedMoment B raw4495step0 raw4495step0Labels := by
      have hz : ∀ j, raw4495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4495step0 = (fun i j => raw4495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4495step0 raw4495; decide +kernel
      have hl : raw4495step0Labels = raw4495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4495 raw4495Labels permutation434 hz
    mixedMoment B raw4495step0 raw4495step0Labels = mixedMoment B raw4495step1 raw4495step1Labels := by
      have hz : ∀ j, raw4495step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4495step1 = (fun i j => raw4495step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4495step1 raw4495step0; decide +kernel
      have hl : raw4495step1Labels = raw4495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4495step0 raw4495step0Labels permutation80 hz
    mixedMoment B raw4495step1 raw4495step1Labels = mixedMoment B raw4495step2 raw4495step2Labels := by
      have hz : ∀ j, raw4495step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4495step2 = (fun i j => raw4495step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4495step2 raw4495step1; decide +kernel
      have hl : raw4495step2Labels = raw4495step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4495step1 raw4495step1Labels permutation14 hz
    mixedMoment B raw4495step2 raw4495step2Labels = mixedMoment B raw4495step3 raw4495step3Labels := by
      have ha : raw4495step3 = (fun i j => raw4495step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4495step3 raw4495step2; decide +kernel
      have hl : raw4495step3Labels = raw4495step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4495step2 raw4495step2Labels permutation6 permutation7
    mixedMoment B raw4495step3 raw4495step3Labels = mixedMoment B raw4495step4 raw4495step4Labels := by
      have ha : raw4495step4 = raw4495step3 := by apply Matrix.ext; unfold raw4495step4 raw4495step3; decide +kernel
      have hl : raw4495step3Labels = labelEmbedding1 ∘ raw4495step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4495step3 raw4495step3Labels raw4495step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical4496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4496 raw4496Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw4496 raw4496Labels = mixedMoment B raw4496step0 raw4496step0Labels := by
      have hz : ∀ j, raw4496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4496step0 = (fun i j => raw4496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4496step0 raw4496; decide +kernel
      have hl : raw4496step0Labels = raw4496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4496 raw4496Labels permutation434 hz
    mixedMoment B raw4496step0 raw4496step0Labels = mixedMoment B raw4496step1 raw4496step1Labels := by
      have hz : ∀ j, raw4496step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4496step1 = (fun i j => raw4496step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4496step1 raw4496step0; decide +kernel
      have hl : raw4496step1Labels = raw4496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4496step0 raw4496step0Labels permutation80 hz
    mixedMoment B raw4496step1 raw4496step1Labels = mixedMoment B raw4496step2 raw4496step2Labels := by
      have ha : raw4496step2 = (fun i j => raw4496step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4496step2 raw4496step1; decide +kernel
      have hl : raw4496step2Labels = raw4496step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4496step1 raw4496step1Labels permutation12 permutation5
    mixedMoment B raw4496step2 raw4496step2Labels = mixedMoment B raw4496step3 raw4496step3Labels := by
      have ha : raw4496step3 = -raw4496step2 := by apply Matrix.ext; change ∀ i j, raw4496step3 i j = -(raw4496step2 i j); unfold raw4496step3 raw4496step2; decide +kernel
      have hl : raw4496step3Labels = raw4496step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4496step3 raw4496step3Labels = mixedMoment B raw4496step4 raw4496step4Labels := by
      have ha : raw4496step4 = raw4496step3 := by apply Matrix.ext; unfold raw4496step4 raw4496step3; decide +kernel
      have hl : raw4496step3Labels = labelEmbedding1 ∘ raw4496step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4496step3 raw4496step3Labels raw4496step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

theorem canonical4497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4497 raw4497Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4497 raw4497Labels = mixedMoment B raw4497step0 raw4497step0Labels := by
      have hz : ∀ j, raw4497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4497step0 = (fun i j => raw4497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4497step0 raw4497; decide +kernel
      have hl : raw4497step0Labels = raw4497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4497 raw4497Labels permutation434 hz
    mixedMoment B raw4497step0 raw4497step0Labels = mixedMoment B raw4497step1 raw4497step1Labels := by
      have ha : raw4497step1 = (fun i j => raw4497step0 (permutation136 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4497step1 raw4497step0; decide +kernel
      have hl : raw4497step1Labels = raw4497step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4497step0 raw4497step0Labels permutation136 permutation7
    mixedMoment B raw4497step1 raw4497step1Labels = mixedMoment B raw4497step2 raw4497step2Labels := by
      have ha : raw4497step2 = raw4497step1 := by apply Matrix.ext; unfold raw4497step2 raw4497step1; decide +kernel
      have hl : raw4497step1Labels = labelEmbedding1 ∘ raw4497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4497step1 raw4497step1Labels raw4497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4498 raw4498Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4498 raw4498Labels = mixedMoment B raw4498step0 raw4498step0Labels := by
      have hz : ∀ j, raw4498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4498step0 = (fun i j => raw4498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4498step0 raw4498; decide +kernel
      have hl : raw4498step0Labels = raw4498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4498 raw4498Labels permutation346 hz
    mixedMoment B raw4498step0 raw4498step0Labels = mixedMoment B raw4498step1 raw4498step1Labels := by
      have ha : raw4498step1 = (fun i j => raw4498step0 (permutation136 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4498step1 raw4498step0; decide +kernel
      have hl : raw4498step1Labels = raw4498step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4498step0 raw4498step0Labels permutation136 permutation7
    mixedMoment B raw4498step1 raw4498step1Labels = mixedMoment B raw4498step2 raw4498step2Labels := by
      have ha : raw4498step2 = raw4498step1 := by apply Matrix.ext; unfold raw4498step2 raw4498step1; decide +kernel
      have hl : raw4498step1Labels = labelEmbedding1 ∘ raw4498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4498step1 raw4498step1Labels raw4498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical4499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4499 raw4499Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw4499 raw4499Labels = mixedMoment B raw4499step0 raw4499step0Labels := by
      have hz : ∀ j, raw4499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4499step0 = (fun i j => raw4499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4499step0 raw4499; decide +kernel
      have hl : raw4499step0Labels = raw4499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4499 raw4499Labels permutation434 hz
    mixedMoment B raw4499step0 raw4499step0Labels = mixedMoment B raw4499step1 raw4499step1Labels := by
      have hz : ∀ j, raw4499step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4499step1 = (fun i j => raw4499step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4499step1 raw4499step0; decide +kernel
      have hl : raw4499step1Labels = raw4499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4499step0 raw4499step0Labels permutation80 hz
    mixedMoment B raw4499step1 raw4499step1Labels = mixedMoment B raw4499step2 raw4499step2Labels := by
      have ha : raw4499step2 = (fun i j => raw4499step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4499step2 raw4499step1; decide +kernel
      have hl : raw4499step2Labels = raw4499step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4499step1 raw4499step1Labels permutation28 permutation7
    mixedMoment B raw4499step2 raw4499step2Labels = mixedMoment B raw4499step3 raw4499step3Labels := by
      have ha : raw4499step3 = raw4499step2 := by apply Matrix.ext; unfold raw4499step3 raw4499step2; decide +kernel
      have hl : raw4499step2Labels = labelEmbedding1 ∘ raw4499step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4499step2 raw4499step2Labels raw4499step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical4500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4500 raw4500Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw4500 raw4500Labels = mixedMoment B raw4500step0 raw4500step0Labels := by
      have hz : ∀ j, raw4500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4500step0 = (fun i j => raw4500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4500step0 raw4500; decide +kernel
      have hl : raw4500step0Labels = raw4500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4500 raw4500Labels permutation434 hz
    mixedMoment B raw4500step0 raw4500step0Labels = mixedMoment B raw4500step1 raw4500step1Labels := by
      have hz : ∀ j, raw4500step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4500step1 = (fun i j => raw4500step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4500step1 raw4500step0; decide +kernel
      have hl : raw4500step1Labels = raw4500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4500step0 raw4500step0Labels permutation80 hz
    mixedMoment B raw4500step1 raw4500step1Labels = mixedMoment B raw4500step2 raw4500step2Labels := by
      have ha : raw4500step2 = (fun i j => raw4500step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4500step2 raw4500step1; decide +kernel
      have hl : raw4500step2Labels = raw4500step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4500step1 raw4500step1Labels permutation28 permutation7
    mixedMoment B raw4500step2 raw4500step2Labels = mixedMoment B raw4500step3 raw4500step3Labels := by
      have ha : raw4500step3 = raw4500step2 := by apply Matrix.ext; unfold raw4500step3 raw4500step2; decide +kernel
      have hl : raw4500step2Labels = labelEmbedding1 ∘ raw4500step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4500step2 raw4500step2Labels raw4500step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical4501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4501 raw4501Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw4501 raw4501Labels = mixedMoment B raw4501step0 raw4501step0Labels := by
      have hz : ∀ j, raw4501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4501step0 = (fun i j => raw4501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4501step0 raw4501; decide +kernel
      have hl : raw4501step0Labels = raw4501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4501 raw4501Labels permutation434 hz
    mixedMoment B raw4501step0 raw4501step0Labels = mixedMoment B raw4501step1 raw4501step1Labels := by
      have hz : ∀ j, raw4501step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4501step1 = (fun i j => raw4501step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4501step1 raw4501step0; decide +kernel
      have hl : raw4501step1Labels = raw4501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4501step0 raw4501step0Labels permutation56 hz
    mixedMoment B raw4501step1 raw4501step1Labels = mixedMoment B raw4501step2 raw4501step2Labels := by
      have ha : raw4501step2 = (fun i j => raw4501step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4501step2 raw4501step1; decide +kernel
      have hl : raw4501step2Labels = raw4501step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4501step1 raw4501step1Labels permutation12 permutation5
    mixedMoment B raw4501step2 raw4501step2Labels = mixedMoment B raw4501step3 raw4501step3Labels := by
      have ha : raw4501step3 = -raw4501step2 := by apply Matrix.ext; change ∀ i j, raw4501step3 i j = -(raw4501step2 i j); unfold raw4501step3 raw4501step2; decide +kernel
      have hl : raw4501step3Labels = raw4501step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4501step3 raw4501step3Labels = mixedMoment B raw4501step4 raw4501step4Labels := by
      have ha : raw4501step4 = raw4501step3 := by apply Matrix.ext; unfold raw4501step4 raw4501step3; decide +kernel
      have hl : raw4501step3Labels = labelEmbedding1 ∘ raw4501step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4501step3 raw4501step3Labels raw4501step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

theorem canonical4502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4502 raw4502Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4502 raw4502Labels = mixedMoment B raw4502step0 raw4502step0Labels := by
      have hz : ∀ j, raw4502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4502step0 = (fun i j => raw4502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4502step0 raw4502; decide +kernel
      have hl : raw4502step0Labels = raw4502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4502 raw4502Labels permutation434 hz
    mixedMoment B raw4502step0 raw4502step0Labels = mixedMoment B raw4502step1 raw4502step1Labels := by
      have ha : raw4502step1 = (fun i j => raw4502step0 (permutation142 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4502step1 raw4502step0; decide +kernel
      have hl : raw4502step1Labels = raw4502step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4502step0 raw4502step0Labels permutation142 permutation7
    mixedMoment B raw4502step1 raw4502step1Labels = mixedMoment B raw4502step2 raw4502step2Labels := by
      have ha : raw4502step2 = raw4502step1 := by apply Matrix.ext; unfold raw4502step2 raw4502step1; decide +kernel
      have hl : raw4502step1Labels = labelEmbedding1 ∘ raw4502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4502step1 raw4502step1Labels raw4502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4503 raw4503Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4503 raw4503Labels = mixedMoment B raw4503step0 raw4503step0Labels := by
      have hz : ∀ j, raw4503 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4503step0 = (fun i j => raw4503 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4503step0 raw4503; decide +kernel
      have hl : raw4503step0Labels = raw4503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4503 raw4503Labels permutation265 hz
    mixedMoment B raw4503step0 raw4503step0Labels = mixedMoment B raw4503step1 raw4503step1Labels := by
      have ha : raw4503step1 = (fun i j => raw4503step0 (permutation136 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4503step1 raw4503step0; decide +kernel
      have hl : raw4503step1Labels = raw4503step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4503step0 raw4503step0Labels permutation136 permutation7
    mixedMoment B raw4503step1 raw4503step1Labels = mixedMoment B raw4503step2 raw4503step2Labels := by
      have ha : raw4503step2 = raw4503step1 := by apply Matrix.ext; unfold raw4503step2 raw4503step1; decide +kernel
      have hl : raw4503step1Labels = labelEmbedding1 ∘ raw4503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4503step1 raw4503step1Labels raw4503step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical4504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4504 raw4504Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw4504 raw4504Labels = mixedMoment B raw4504step0 raw4504step0Labels := by
      have hz : ∀ j, raw4504 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4504step0 = (fun i j => raw4504 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4504step0 raw4504; decide +kernel
      have hl : raw4504step0Labels = raw4504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4504 raw4504Labels permutation434 hz
    mixedMoment B raw4504step0 raw4504step0Labels = mixedMoment B raw4504step1 raw4504step1Labels := by
      have hz : ∀ j, raw4504step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4504step1 = (fun i j => raw4504step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4504step1 raw4504step0; decide +kernel
      have hl : raw4504step1Labels = raw4504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4504step0 raw4504step0Labels permutation56 hz
    mixedMoment B raw4504step1 raw4504step1Labels = mixedMoment B raw4504step2 raw4504step2Labels := by
      have ha : raw4504step2 = (fun i j => raw4504step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4504step2 raw4504step1; decide +kernel
      have hl : raw4504step2Labels = raw4504step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4504step1 raw4504step1Labels permutation28 permutation7
    mixedMoment B raw4504step2 raw4504step2Labels = mixedMoment B raw4504step3 raw4504step3Labels := by
      have ha : raw4504step3 = raw4504step2 := by apply Matrix.ext; unfold raw4504step3 raw4504step2; decide +kernel
      have hl : raw4504step2Labels = labelEmbedding1 ∘ raw4504step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4504step2 raw4504step2Labels raw4504step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4505 raw4505Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw4505 raw4505Labels = mixedMoment B raw4505step0 raw4505step0Labels := by
      have hz : ∀ j, raw4505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4505step0 = (fun i j => raw4505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4505step0 raw4505; decide +kernel
      have hl : raw4505step0Labels = raw4505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4505 raw4505Labels permutation434 hz
    mixedMoment B raw4505step0 raw4505step0Labels = mixedMoment B raw4505step1 raw4505step1Labels := by
      have hz : ∀ j, raw4505step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4505step1 = (fun i j => raw4505step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4505step1 raw4505step0; decide +kernel
      have hl : raw4505step1Labels = raw4505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4505step0 raw4505step0Labels permutation56 hz
    mixedMoment B raw4505step1 raw4505step1Labels = mixedMoment B raw4505step2 raw4505step2Labels := by
      have ha : raw4505step2 = (fun i j => raw4505step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4505step2 raw4505step1; decide +kernel
      have hl : raw4505step2Labels = raw4505step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4505step1 raw4505step1Labels permutation28 permutation7
    mixedMoment B raw4505step2 raw4505step2Labels = mixedMoment B raw4505step3 raw4505step3Labels := by
      have ha : raw4505step3 = raw4505step2 := by apply Matrix.ext; unfold raw4505step3 raw4505step2; decide +kernel
      have hl : raw4505step2Labels = labelEmbedding1 ∘ raw4505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4505step2 raw4505step2Labels raw4505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical4506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4506 raw4506Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw4506 raw4506Labels = mixedMoment B raw4506step0 raw4506step0Labels := by
      have hz : ∀ j, raw4506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4506step0 = (fun i j => raw4506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4506step0 raw4506; decide +kernel
      have hl : raw4506step0Labels = raw4506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4506 raw4506Labels permutation346 hz
    mixedMoment B raw4506step0 raw4506step0Labels = mixedMoment B raw4506step1 raw4506step1Labels := by
      have hz : ∀ j, raw4506step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4506step1 = (fun i j => raw4506step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4506step1 raw4506step0; decide +kernel
      have hl : raw4506step1Labels = raw4506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4506step0 raw4506step0Labels permutation56 hz
    mixedMoment B raw4506step1 raw4506step1Labels = mixedMoment B raw4506step2 raw4506step2Labels := by
      have ha : raw4506step2 = (fun i j => raw4506step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4506step2 raw4506step1; decide +kernel
      have hl : raw4506step2Labels = raw4506step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4506step1 raw4506step1Labels permutation12 permutation5
    mixedMoment B raw4506step2 raw4506step2Labels = mixedMoment B raw4506step3 raw4506step3Labels := by
      have ha : raw4506step3 = -raw4506step2 := by apply Matrix.ext; change ∀ i j, raw4506step3 i j = -(raw4506step2 i j); unfold raw4506step3 raw4506step2; decide +kernel
      have hl : raw4506step3Labels = raw4506step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4506step3 raw4506step3Labels = mixedMoment B raw4506step4 raw4506step4Labels := by
      have ha : raw4506step4 = raw4506step3 := by apply Matrix.ext; unfold raw4506step4 raw4506step3; decide +kernel
      have hl : raw4506step3Labels = labelEmbedding1 ∘ raw4506step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4506step3 raw4506step3Labels raw4506step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

theorem canonical4507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4507 raw4507Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4507 raw4507Labels = mixedMoment B raw4507step0 raw4507step0Labels := by
      have hz : ∀ j, raw4507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4507step0 = (fun i j => raw4507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4507step0 raw4507; decide +kernel
      have hl : raw4507step0Labels = raw4507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4507 raw4507Labels permutation346 hz
    mixedMoment B raw4507step0 raw4507step0Labels = mixedMoment B raw4507step1 raw4507step1Labels := by
      have ha : raw4507step1 = (fun i j => raw4507step0 (permutation142 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4507step1 raw4507step0; decide +kernel
      have hl : raw4507step1Labels = raw4507step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4507step0 raw4507step0Labels permutation142 permutation7
    mixedMoment B raw4507step1 raw4507step1Labels = mixedMoment B raw4507step2 raw4507step2Labels := by
      have ha : raw4507step2 = raw4507step1 := by apply Matrix.ext; unfold raw4507step2 raw4507step1; decide +kernel
      have hl : raw4507step1Labels = labelEmbedding1 ∘ raw4507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4507step1 raw4507step1Labels raw4507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical4508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4508 raw4508Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw4508 raw4508Labels = mixedMoment B raw4508step0 raw4508step0Labels := by
      have hz : ∀ j, raw4508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4508step0 = (fun i j => raw4508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4508step0 raw4508; decide +kernel
      have hl : raw4508step0Labels = raw4508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4508 raw4508Labels permutation265 hz
    mixedMoment B raw4508step0 raw4508step0Labels = mixedMoment B raw4508step1 raw4508step1Labels := by
      have ha : raw4508step1 = (fun i j => raw4508step0 (permutation142 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4508step1 raw4508step0; decide +kernel
      have hl : raw4508step1Labels = raw4508step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4508step0 raw4508step0Labels permutation142 permutation7
    mixedMoment B raw4508step1 raw4508step1Labels = mixedMoment B raw4508step2 raw4508step2Labels := by
      have ha : raw4508step2 = raw4508step1 := by apply Matrix.ext; unfold raw4508step2 raw4508step1; decide +kernel
      have hl : raw4508step1Labels = labelEmbedding1 ∘ raw4508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4508step1 raw4508step1Labels raw4508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical4509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4509 raw4509Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw4509 raw4509Labels = mixedMoment B raw4509step0 raw4509step0Labels := by
      have hz : ∀ j, raw4509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4509step0 = (fun i j => raw4509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4509step0 raw4509; decide +kernel
      have hl : raw4509step0Labels = raw4509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4509 raw4509Labels permutation346 hz
    mixedMoment B raw4509step0 raw4509step0Labels = mixedMoment B raw4509step1 raw4509step1Labels := by
      have hz : ∀ j, raw4509step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4509step1 = (fun i j => raw4509step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4509step1 raw4509step0; decide +kernel
      have hl : raw4509step1Labels = raw4509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4509step0 raw4509step0Labels permutation56 hz
    mixedMoment B raw4509step1 raw4509step1Labels = mixedMoment B raw4509step2 raw4509step2Labels := by
      have ha : raw4509step2 = (fun i j => raw4509step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4509step2 raw4509step1; decide +kernel
      have hl : raw4509step2Labels = raw4509step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4509step1 raw4509step1Labels permutation28 permutation7
    mixedMoment B raw4509step2 raw4509step2Labels = mixedMoment B raw4509step3 raw4509step3Labels := by
      have ha : raw4509step3 = raw4509step2 := by apply Matrix.ext; unfold raw4509step3 raw4509step2; decide +kernel
      have hl : raw4509step2Labels = labelEmbedding1 ∘ raw4509step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4509step2 raw4509step2Labels raw4509step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical4510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4510 raw4510Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw4510 raw4510Labels = mixedMoment B raw4510step0 raw4510step0Labels := by
      have hz : ∀ j, raw4510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4510step0 = (fun i j => raw4510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4510step0 raw4510; decide +kernel
      have hl : raw4510step0Labels = raw4510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4510 raw4510Labels permutation346 hz
    mixedMoment B raw4510step0 raw4510step0Labels = mixedMoment B raw4510step1 raw4510step1Labels := by
      have hz : ∀ j, raw4510step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4510step1 = (fun i j => raw4510step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4510step1 raw4510step0; decide +kernel
      have hl : raw4510step1Labels = raw4510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4510step0 raw4510step0Labels permutation56 hz
    mixedMoment B raw4510step1 raw4510step1Labels = mixedMoment B raw4510step2 raw4510step2Labels := by
      have ha : raw4510step2 = (fun i j => raw4510step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4510step2 raw4510step1; decide +kernel
      have hl : raw4510step2Labels = raw4510step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4510step1 raw4510step1Labels permutation28 permutation7
    mixedMoment B raw4510step2 raw4510step2Labels = mixedMoment B raw4510step3 raw4510step3Labels := by
      have ha : raw4510step3 = raw4510step2 := by apply Matrix.ext; unfold raw4510step3 raw4510step2; decide +kernel
      have hl : raw4510step2Labels = labelEmbedding1 ∘ raw4510step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4510step2 raw4510step2Labels raw4510step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4511 raw4511Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw4511 raw4511Labels = mixedMoment B raw4511step0 raw4511step0Labels := by
      have hz : ∀ j, raw4511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4511step0 = (fun i j => raw4511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4511step0 raw4511; decide +kernel
      have hl : raw4511step0Labels = raw4511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4511 raw4511Labels permutation434 hz
    mixedMoment B raw4511step0 raw4511step0Labels = mixedMoment B raw4511step1 raw4511step1Labels := by
      have hz : ∀ j, raw4511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4511step1 = (fun i j => raw4511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4511step1 raw4511step0; decide +kernel
      have hl : raw4511step1Labels = raw4511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4511step0 raw4511step0Labels permutation80 hz
    mixedMoment B raw4511step1 raw4511step1Labels = mixedMoment B raw4511step2 raw4511step2Labels := by
      have hz : ∀ j, raw4511step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4511step2 = (fun i j => raw4511step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4511step2 raw4511step1; decide +kernel
      have hl : raw4511step2Labels = raw4511step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4511step1 raw4511step1Labels permutation14 hz
    mixedMoment B raw4511step2 raw4511step2Labels = mixedMoment B raw4511step3 raw4511step3Labels := by
      have ha : raw4511step3 = (fun i j => raw4511step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4511step3 raw4511step2; decide +kernel
      have hl : raw4511step3Labels = raw4511step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4511step2 raw4511step2Labels permutation3 permutation5
    mixedMoment B raw4511step3 raw4511step3Labels = mixedMoment B raw4511step4 raw4511step4Labels := by
      have ha : raw4511step4 = -raw4511step3 := by apply Matrix.ext; change ∀ i j, raw4511step4 i j = -(raw4511step3 i j); unfold raw4511step4 raw4511step3; decide +kernel
      have hl : raw4511step4Labels = raw4511step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4511step4 raw4511step4Labels = mixedMoment B raw4511step5 raw4511step5Labels := by
      have ha : raw4511step5 = raw4511step4 := by apply Matrix.ext; unfold raw4511step5 raw4511step4; decide +kernel
      have hl : raw4511step4Labels = labelEmbedding1 ∘ raw4511step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4511step4 raw4511step4Labels raw4511step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1747 node1747Labels := by rfl

theorem canonical4512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4512 raw4512Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw4512 raw4512Labels = mixedMoment B raw4512step0 raw4512step0Labels := by
      have hz : ∀ j, raw4512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4512step0 = (fun i j => raw4512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4512step0 raw4512; decide +kernel
      have hl : raw4512step0Labels = raw4512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4512 raw4512Labels permutation434 hz
    mixedMoment B raw4512step0 raw4512step0Labels = mixedMoment B raw4512step1 raw4512step1Labels := by
      have hz : ∀ j, raw4512step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4512step1 = (fun i j => raw4512step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4512step1 raw4512step0; decide +kernel
      have hl : raw4512step1Labels = raw4512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4512step0 raw4512step0Labels permutation80 hz
    mixedMoment B raw4512step1 raw4512step1Labels = mixedMoment B raw4512step2 raw4512step2Labels := by
      have ha : raw4512step2 = (fun i j => raw4512step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4512step2 raw4512step1; decide +kernel
      have hl : raw4512step2Labels = raw4512step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4512step1 raw4512step1Labels permutation28 permutation7
    mixedMoment B raw4512step2 raw4512step2Labels = mixedMoment B raw4512step3 raw4512step3Labels := by
      have ha : raw4512step3 = raw4512step2 := by apply Matrix.ext; unfold raw4512step3 raw4512step2; decide +kernel
      have hl : raw4512step2Labels = labelEmbedding1 ∘ raw4512step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4512step2 raw4512step2Labels raw4512step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

theorem canonical4513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4513 raw4513Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw4513 raw4513Labels = mixedMoment B raw4513step0 raw4513step0Labels := by
      have hz : ∀ j, raw4513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4513step0 = (fun i j => raw4513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4513step0 raw4513; decide +kernel
      have hl : raw4513step0Labels = raw4513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4513 raw4513Labels permutation434 hz
    mixedMoment B raw4513step0 raw4513step0Labels = mixedMoment B raw4513step1 raw4513step1Labels := by
      have hz : ∀ j, raw4513step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4513step1 = (fun i j => raw4513step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4513step1 raw4513step0; decide +kernel
      have hl : raw4513step1Labels = raw4513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4513step0 raw4513step0Labels permutation56 hz
    mixedMoment B raw4513step1 raw4513step1Labels = mixedMoment B raw4513step2 raw4513step2Labels := by
      have ha : raw4513step2 = (fun i j => raw4513step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4513step2 raw4513step1; decide +kernel
      have hl : raw4513step2Labels = raw4513step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4513step1 raw4513step1Labels permutation28 permutation7
    mixedMoment B raw4513step2 raw4513step2Labels = mixedMoment B raw4513step3 raw4513step3Labels := by
      have ha : raw4513step3 = raw4513step2 := by apply Matrix.ext; unfold raw4513step3 raw4513step2; decide +kernel
      have hl : raw4513step2Labels = labelEmbedding1 ∘ raw4513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4513step2 raw4513step2Labels raw4513step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

theorem canonical4514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4514 raw4514Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw4514 raw4514Labels = mixedMoment B raw4514step0 raw4514step0Labels := by
      have hz : ∀ j, raw4514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4514step0 = (fun i j => raw4514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4514step0 raw4514; decide +kernel
      have hl : raw4514step0Labels = raw4514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4514 raw4514Labels permutation346 hz
    mixedMoment B raw4514step0 raw4514step0Labels = mixedMoment B raw4514step1 raw4514step1Labels := by
      have hz : ∀ j, raw4514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4514step1 = (fun i j => raw4514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4514step1 raw4514step0; decide +kernel
      have hl : raw4514step1Labels = raw4514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4514step0 raw4514step0Labels permutation56 hz
    mixedMoment B raw4514step1 raw4514step1Labels = mixedMoment B raw4514step2 raw4514step2Labels := by
      have ha : raw4514step2 = (fun i j => raw4514step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4514step2 raw4514step1; decide +kernel
      have hl : raw4514step2Labels = raw4514step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4514step1 raw4514step1Labels permutation28 permutation7
    mixedMoment B raw4514step2 raw4514step2Labels = mixedMoment B raw4514step3 raw4514step3Labels := by
      have ha : raw4514step3 = raw4514step2 := by apply Matrix.ext; unfold raw4514step3 raw4514step2; decide +kernel
      have hl : raw4514step2Labels = labelEmbedding1 ∘ raw4514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4514step2 raw4514step2Labels raw4514step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

theorem canonical4515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4515 raw4515Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw4515 raw4515Labels = mixedMoment B raw4515step0 raw4515step0Labels := by
      have hz : ∀ j, raw4515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4515step0 = (fun i j => raw4515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4515step0 raw4515; decide +kernel
      have hl : raw4515step0Labels = raw4515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4515 raw4515Labels permutation434 hz
    mixedMoment B raw4515step0 raw4515step0Labels = mixedMoment B raw4515step1 raw4515step1Labels := by
      have hz : ∀ j, raw4515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4515step1 = (fun i j => raw4515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4515step1 raw4515step0; decide +kernel
      have hl : raw4515step1Labels = raw4515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4515step0 raw4515step0Labels permutation80 hz
    mixedMoment B raw4515step1 raw4515step1Labels = mixedMoment B raw4515step2 raw4515step2Labels := by
      have hz : ∀ j, raw4515step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4515step2 = (fun i j => raw4515step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4515step2 raw4515step1; decide +kernel
      have hl : raw4515step2Labels = raw4515step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4515step1 raw4515step1Labels permutation14 hz
    mixedMoment B raw4515step2 raw4515step2Labels = mixedMoment B raw4515step3 raw4515step3Labels := by
      have ha : raw4515step3 = (fun i j => raw4515step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4515step3 raw4515step2; decide +kernel
      have hl : raw4515step3Labels = raw4515step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4515step2 raw4515step2Labels permutation6 permutation7
    mixedMoment B raw4515step3 raw4515step3Labels = mixedMoment B raw4515step4 raw4515step4Labels := by
      have ha : raw4515step4 = raw4515step3 := by apply Matrix.ext; unfold raw4515step4 raw4515step3; decide +kernel
      have hl : raw4515step3Labels = labelEmbedding1 ∘ raw4515step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4515step3 raw4515step3Labels raw4515step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical4516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4516 raw4516Labels = mixedMoment B node1757 node1757Labels := by
  calc
    mixedMoment B raw4516 raw4516Labels = mixedMoment B raw4516step0 raw4516step0Labels := by
      have hz : ∀ j, raw4516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4516step0 = (fun i j => raw4516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4516step0 raw4516; decide +kernel
      have hl : raw4516step0Labels = raw4516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4516 raw4516Labels permutation434 hz
    mixedMoment B raw4516step0 raw4516step0Labels = mixedMoment B raw4516step1 raw4516step1Labels := by
      have hz : ∀ j, raw4516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4516step1 = (fun i j => raw4516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4516step1 raw4516step0; decide +kernel
      have hl : raw4516step1Labels = raw4516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4516step0 raw4516step0Labels permutation80 hz
    mixedMoment B raw4516step1 raw4516step1Labels = mixedMoment B raw4516step2 raw4516step2Labels := by
      have hz : ∀ j, raw4516step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4516step2 = (fun i j => raw4516step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4516step2 raw4516step1; decide +kernel
      have hl : raw4516step2Labels = raw4516step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4516step1 raw4516step1Labels permutation14 hz
    mixedMoment B raw4516step2 raw4516step2Labels = mixedMoment B raw4516step3 raw4516step3Labels := by
      have ha : raw4516step3 = (fun i j => raw4516step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4516step3 raw4516step2; decide +kernel
      have hl : raw4516step3Labels = raw4516step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4516step2 raw4516step2Labels permutation3 permutation5
    mixedMoment B raw4516step3 raw4516step3Labels = mixedMoment B raw4516step4 raw4516step4Labels := by
      have ha : raw4516step4 = -raw4516step3 := by apply Matrix.ext; change ∀ i j, raw4516step4 i j = -(raw4516step3 i j); unfold raw4516step4 raw4516step3; decide +kernel
      have hl : raw4516step4Labels = raw4516step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4516step4 raw4516step4Labels = mixedMoment B raw4516step5 raw4516step5Labels := by
      have ha : raw4516step5 = raw4516step4 := by apply Matrix.ext; unfold raw4516step5 raw4516step4; decide +kernel
      have hl : raw4516step4Labels = labelEmbedding1 ∘ raw4516step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4516step4 raw4516step4Labels raw4516step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1757 node1757Labels := by rfl

theorem canonical4517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4517 raw4517Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw4517 raw4517Labels = mixedMoment B raw4517step0 raw4517step0Labels := by
      have hz : ∀ j, raw4517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4517step0 = (fun i j => raw4517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4517step0 raw4517; decide +kernel
      have hl : raw4517step0Labels = raw4517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4517 raw4517Labels permutation434 hz
    mixedMoment B raw4517step0 raw4517step0Labels = mixedMoment B raw4517step1 raw4517step1Labels := by
      have hz : ∀ j, raw4517step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4517step1 = (fun i j => raw4517step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4517step1 raw4517step0; decide +kernel
      have hl : raw4517step1Labels = raw4517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4517step0 raw4517step0Labels permutation80 hz
    mixedMoment B raw4517step1 raw4517step1Labels = mixedMoment B raw4517step2 raw4517step2Labels := by
      have ha : raw4517step2 = (fun i j => raw4517step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4517step2 raw4517step1; decide +kernel
      have hl : raw4517step2Labels = raw4517step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4517step1 raw4517step1Labels permutation28 permutation7
    mixedMoment B raw4517step2 raw4517step2Labels = mixedMoment B raw4517step3 raw4517step3Labels := by
      have ha : raw4517step3 = raw4517step2 := by apply Matrix.ext; unfold raw4517step3 raw4517step2; decide +kernel
      have hl : raw4517step2Labels = labelEmbedding1 ∘ raw4517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4517step2 raw4517step2Labels raw4517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical4518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4518 raw4518Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw4518 raw4518Labels = mixedMoment B raw4518step0 raw4518step0Labels := by
      have hz : ∀ j, raw4518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4518step0 = (fun i j => raw4518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4518step0 raw4518; decide +kernel
      have hl : raw4518step0Labels = raw4518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4518 raw4518Labels permutation434 hz
    mixedMoment B raw4518step0 raw4518step0Labels = mixedMoment B raw4518step1 raw4518step1Labels := by
      have hz : ∀ j, raw4518step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4518step1 = (fun i j => raw4518step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4518step1 raw4518step0; decide +kernel
      have hl : raw4518step1Labels = raw4518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4518step0 raw4518step0Labels permutation56 hz
    mixedMoment B raw4518step1 raw4518step1Labels = mixedMoment B raw4518step2 raw4518step2Labels := by
      have ha : raw4518step2 = (fun i j => raw4518step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4518step2 raw4518step1; decide +kernel
      have hl : raw4518step2Labels = raw4518step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4518step1 raw4518step1Labels permutation28 permutation7
    mixedMoment B raw4518step2 raw4518step2Labels = mixedMoment B raw4518step3 raw4518step3Labels := by
      have ha : raw4518step3 = raw4518step2 := by apply Matrix.ext; unfold raw4518step3 raw4518step2; decide +kernel
      have hl : raw4518step2Labels = labelEmbedding1 ∘ raw4518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4518step2 raw4518step2Labels raw4518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical4519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4519 raw4519Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw4519 raw4519Labels = mixedMoment B raw4519step0 raw4519step0Labels := by
      have hz : ∀ j, raw4519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4519step0 = (fun i j => raw4519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4519step0 raw4519; decide +kernel
      have hl : raw4519step0Labels = raw4519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4519 raw4519Labels permutation346 hz
    mixedMoment B raw4519step0 raw4519step0Labels = mixedMoment B raw4519step1 raw4519step1Labels := by
      have hz : ∀ j, raw4519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4519step1 = (fun i j => raw4519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4519step1 raw4519step0; decide +kernel
      have hl : raw4519step1Labels = raw4519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4519step0 raw4519step0Labels permutation56 hz
    mixedMoment B raw4519step1 raw4519step1Labels = mixedMoment B raw4519step2 raw4519step2Labels := by
      have ha : raw4519step2 = (fun i j => raw4519step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4519step2 raw4519step1; decide +kernel
      have hl : raw4519step2Labels = raw4519step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4519step1 raw4519step1Labels permutation28 permutation7
    mixedMoment B raw4519step2 raw4519step2Labels = mixedMoment B raw4519step3 raw4519step3Labels := by
      have ha : raw4519step3 = raw4519step2 := by apply Matrix.ext; unfold raw4519step3 raw4519step2; decide +kernel
      have hl : raw4519step2Labels = labelEmbedding1 ∘ raw4519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4519step2 raw4519step2Labels raw4519step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical4520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4520 raw4520Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw4520 raw4520Labels = mixedMoment B raw4520step0 raw4520step0Labels := by
      have hz : ∀ j, raw4520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4520step0 = (fun i j => raw4520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4520step0 raw4520; decide +kernel
      have hl : raw4520step0Labels = raw4520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4520 raw4520Labels permutation434 hz
    mixedMoment B raw4520step0 raw4520step0Labels = mixedMoment B raw4520step1 raw4520step1Labels := by
      have hz : ∀ j, raw4520step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4520step1 = (fun i j => raw4520step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4520step1 raw4520step0; decide +kernel
      have hl : raw4520step1Labels = raw4520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4520step0 raw4520step0Labels permutation80 hz
    mixedMoment B raw4520step1 raw4520step1Labels = mixedMoment B raw4520step2 raw4520step2Labels := by
      have hz : ∀ j, raw4520step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4520step2 = (fun i j => raw4520step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4520step2 raw4520step1; decide +kernel
      have hl : raw4520step2Labels = raw4520step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4520step1 raw4520step1Labels permutation14 hz
    mixedMoment B raw4520step2 raw4520step2Labels = mixedMoment B raw4520step3 raw4520step3Labels := by
      have ha : raw4520step3 = (fun i j => raw4520step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4520step3 raw4520step2; decide +kernel
      have hl : raw4520step3Labels = raw4520step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4520step2 raw4520step2Labels permutation6 permutation7
    mixedMoment B raw4520step3 raw4520step3Labels = mixedMoment B raw4520step4 raw4520step4Labels := by
      have ha : raw4520step4 = raw4520step3 := by apply Matrix.ext; unfold raw4520step4 raw4520step3; decide +kernel
      have hl : raw4520step3Labels = labelEmbedding1 ∘ raw4520step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4520step3 raw4520step3Labels raw4520step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

theorem canonical4521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4521 raw4521Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw4521 raw4521Labels = mixedMoment B raw4521step0 raw4521step0Labels := by
      have hz : ∀ j, raw4521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4521step0 = (fun i j => raw4521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4521step0 raw4521; decide +kernel
      have hl : raw4521step0Labels = raw4521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4521 raw4521Labels permutation434 hz
    mixedMoment B raw4521step0 raw4521step0Labels = mixedMoment B raw4521step1 raw4521step1Labels := by
      have hz : ∀ j, raw4521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4521step1 = (fun i j => raw4521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4521step1 raw4521step0; decide +kernel
      have hl : raw4521step1Labels = raw4521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4521step0 raw4521step0Labels permutation80 hz
    mixedMoment B raw4521step1 raw4521step1Labels = mixedMoment B raw4521step2 raw4521step2Labels := by
      have hz : ∀ j, raw4521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4521step2 = (fun i j => raw4521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4521step2 raw4521step1; decide +kernel
      have hl : raw4521step2Labels = raw4521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4521step1 raw4521step1Labels permutation14 hz
    mixedMoment B raw4521step2 raw4521step2Labels = mixedMoment B raw4521step3 raw4521step3Labels := by
      have ha : raw4521step3 = (fun i j => raw4521step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4521step3 raw4521step2; decide +kernel
      have hl : raw4521step3Labels = raw4521step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4521step2 raw4521step2Labels permutation7 permutation2
    mixedMoment B raw4521step3 raw4521step3Labels = mixedMoment B raw4521step4 raw4521step4Labels := by
      have ha : raw4521step4 = -raw4521step3 := by apply Matrix.ext; change ∀ i j, raw4521step4 i j = -(raw4521step3 i j); unfold raw4521step4 raw4521step3; decide +kernel
      have hl : raw4521step4Labels = raw4521step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical4522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4522 raw4522Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw4522 raw4522Labels = mixedMoment B raw4522step0 raw4522step0Labels := by
      have hz : ∀ j, raw4522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4522step0 = (fun i j => raw4522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4522step0 raw4522; decide +kernel
      have hl : raw4522step0Labels = raw4522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4522 raw4522Labels permutation434 hz
    mixedMoment B raw4522step0 raw4522step0Labels = mixedMoment B raw4522step1 raw4522step1Labels := by
      have hz : ∀ j, raw4522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4522step1 = (fun i j => raw4522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4522step1 raw4522step0; decide +kernel
      have hl : raw4522step1Labels = raw4522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4522step0 raw4522step0Labels permutation80 hz
    mixedMoment B raw4522step1 raw4522step1Labels = mixedMoment B raw4522step2 raw4522step2Labels := by
      have ha : raw4522step2 = (fun i j => raw4522step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4522step2 raw4522step1; decide +kernel
      have hl : raw4522step2Labels = raw4522step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4522step1 raw4522step1Labels permutation31 permutation2
    mixedMoment B raw4522step2 raw4522step2Labels = mixedMoment B raw4522step3 raw4522step3Labels := by
      have ha : raw4522step3 = -raw4522step2 := by apply Matrix.ext; change ∀ i j, raw4522step3 i j = -(raw4522step2 i j); unfold raw4522step3 raw4522step2; decide +kernel
      have hl : raw4522step3Labels = raw4522step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical4523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4523 raw4523Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw4523 raw4523Labels = mixedMoment B raw4523step0 raw4523step0Labels := by
      have hz : ∀ j, raw4523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4523step0 = (fun i j => raw4523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4523step0 raw4523; decide +kernel
      have hl : raw4523step0Labels = raw4523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4523 raw4523Labels permutation434 hz
    mixedMoment B raw4523step0 raw4523step0Labels = mixedMoment B raw4523step1 raw4523step1Labels := by
      have hz : ∀ j, raw4523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4523step1 = (fun i j => raw4523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4523step1 raw4523step0; decide +kernel
      have hl : raw4523step1Labels = raw4523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4523step0 raw4523step0Labels permutation56 hz
    mixedMoment B raw4523step1 raw4523step1Labels = mixedMoment B raw4523step2 raw4523step2Labels := by
      have ha : raw4523step2 = (fun i j => raw4523step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4523step2 raw4523step1; decide +kernel
      have hl : raw4523step2Labels = raw4523step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4523step1 raw4523step1Labels permutation31 permutation2
    mixedMoment B raw4523step2 raw4523step2Labels = mixedMoment B raw4523step3 raw4523step3Labels := by
      have ha : raw4523step3 = -raw4523step2 := by apply Matrix.ext; change ∀ i j, raw4523step3 i j = -(raw4523step2 i j); unfold raw4523step3 raw4523step2; decide +kernel
      have hl : raw4523step3Labels = raw4523step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical4524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4524 raw4524Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw4524 raw4524Labels = mixedMoment B raw4524step0 raw4524step0Labels := by
      have hz : ∀ j, raw4524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4524step0 = (fun i j => raw4524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4524step0 raw4524; decide +kernel
      have hl : raw4524step0Labels = raw4524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4524 raw4524Labels permutation346 hz
    mixedMoment B raw4524step0 raw4524step0Labels = mixedMoment B raw4524step1 raw4524step1Labels := by
      have hz : ∀ j, raw4524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4524step1 = (fun i j => raw4524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4524step1 raw4524step0; decide +kernel
      have hl : raw4524step1Labels = raw4524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4524step0 raw4524step0Labels permutation56 hz
    mixedMoment B raw4524step1 raw4524step1Labels = mixedMoment B raw4524step2 raw4524step2Labels := by
      have ha : raw4524step2 = (fun i j => raw4524step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4524step2 raw4524step1; decide +kernel
      have hl : raw4524step2Labels = raw4524step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4524step1 raw4524step1Labels permutation31 permutation2
    mixedMoment B raw4524step2 raw4524step2Labels = mixedMoment B raw4524step3 raw4524step3Labels := by
      have ha : raw4524step3 = -raw4524step2 := by apply Matrix.ext; change ∀ i j, raw4524step3 i j = -(raw4524step2 i j); unfold raw4524step3 raw4524step2; decide +kernel
      have hl : raw4524step3Labels = raw4524step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical4525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4525 raw4525Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw4525 raw4525Labels = mixedMoment B raw4525step0 raw4525step0Labels := by
      have hz : ∀ j, raw4525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4525step0 = (fun i j => raw4525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4525step0 raw4525; decide +kernel
      have hl : raw4525step0Labels = raw4525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4525 raw4525Labels permutation434 hz
    mixedMoment B raw4525step0 raw4525step0Labels = mixedMoment B raw4525step1 raw4525step1Labels := by
      have hz : ∀ j, raw4525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4525step1 = (fun i j => raw4525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4525step1 raw4525step0; decide +kernel
      have hl : raw4525step1Labels = raw4525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4525step0 raw4525step0Labels permutation80 hz
    mixedMoment B raw4525step1 raw4525step1Labels = mixedMoment B raw4525step2 raw4525step2Labels := by
      have hz : ∀ j, raw4525step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4525step2 = (fun i j => raw4525step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4525step2 raw4525step1; decide +kernel
      have hl : raw4525step2Labels = raw4525step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4525step1 raw4525step1Labels permutation14 hz
    mixedMoment B raw4525step2 raw4525step2Labels = mixedMoment B raw4525step3 raw4525step3Labels := by
      have ha : raw4525step3 = (fun i j => raw4525step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4525step3 raw4525step2; decide +kernel
      have hl : raw4525step3Labels = raw4525step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4525step2 raw4525step2Labels permutation7 permutation2
    mixedMoment B raw4525step3 raw4525step3Labels = mixedMoment B raw4525step4 raw4525step4Labels := by
      have ha : raw4525step4 = -raw4525step3 := by apply Matrix.ext; change ∀ i j, raw4525step4 i j = -(raw4525step3 i j); unfold raw4525step4 raw4525step3; decide +kernel
      have hl : raw4525step4Labels = raw4525step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2293 node2293Labels := by rfl

theorem canonical4526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4526 raw4526Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw4526 raw4526Labels = mixedMoment B raw4526step0 raw4526step0Labels := by
      have hz : ∀ j, raw4526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4526step0 = (fun i j => raw4526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4526step0 raw4526; decide +kernel
      have hl : raw4526step0Labels = raw4526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4526 raw4526Labels permutation434 hz
    mixedMoment B raw4526step0 raw4526step0Labels = mixedMoment B raw4526step1 raw4526step1Labels := by
      have hz : ∀ j, raw4526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4526step1 = (fun i j => raw4526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4526step1 raw4526step0; decide +kernel
      have hl : raw4526step1Labels = raw4526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4526step0 raw4526step0Labels permutation80 hz
    mixedMoment B raw4526step1 raw4526step1Labels = mixedMoment B raw4526step2 raw4526step2Labels := by
      have hz : ∀ j, raw4526step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4526step2 = (fun i j => raw4526step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4526step2 raw4526step1; decide +kernel
      have hl : raw4526step2Labels = raw4526step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4526step1 raw4526step1Labels permutation14 hz
    mixedMoment B raw4526step2 raw4526step2Labels = mixedMoment B raw4526step3 raw4526step3Labels := by
      have ha : raw4526step3 = (fun i j => raw4526step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4526step3 raw4526step2; decide +kernel
      have hl : raw4526step3Labels = raw4526step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4526step2 raw4526step2Labels permutation7 permutation2
    mixedMoment B raw4526step3 raw4526step3Labels = mixedMoment B raw4526step4 raw4526step4Labels := by
      have ha : raw4526step4 = -raw4526step3 := by apply Matrix.ext; change ∀ i j, raw4526step4 i j = -(raw4526step3 i j); unfold raw4526step4 raw4526step3; decide +kernel
      have hl : raw4526step4Labels = raw4526step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

theorem canonical4527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4527 raw4527Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw4527 raw4527Labels = mixedMoment B raw4527step0 raw4527step0Labels := by
      have hz : ∀ j, raw4527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4527step0 = (fun i j => raw4527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4527step0 raw4527; decide +kernel
      have hl : raw4527step0Labels = raw4527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4527 raw4527Labels permutation434 hz
    mixedMoment B raw4527step0 raw4527step0Labels = mixedMoment B raw4527step1 raw4527step1Labels := by
      have hz : ∀ j, raw4527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4527step1 = (fun i j => raw4527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4527step1 raw4527step0; decide +kernel
      have hl : raw4527step1Labels = raw4527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4527step0 raw4527step0Labels permutation80 hz
    mixedMoment B raw4527step1 raw4527step1Labels = mixedMoment B raw4527step2 raw4527step2Labels := by
      have hz : ∀ j, raw4527step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4527step2 = (fun i j => raw4527step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4527step2 raw4527step1; decide +kernel
      have hl : raw4527step2Labels = raw4527step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4527step1 raw4527step1Labels permutation14 hz
    mixedMoment B raw4527step2 raw4527step2Labels = mixedMoment B raw4527step3 raw4527step3Labels := by
      have ha : raw4527step3 = (fun i j => raw4527step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4527step3 raw4527step2; decide +kernel
      have hl : raw4527step3Labels = raw4527step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4527step2 raw4527step2Labels permutation6 permutation0
    mixedMoment B raw4527step3 raw4527step3Labels = mixedMoment B raw4527step4 raw4527step4Labels := by
      have ha : raw4527step4 = -raw4527step3 := by apply Matrix.ext; change ∀ i j, raw4527step4 i j = -(raw4527step3 i j); unfold raw4527step4 raw4527step3; decide +kernel
      have hl : raw4527step4Labels = raw4527step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical4528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4528 raw4528Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw4528 raw4528Labels = mixedMoment B raw4528step0 raw4528step0Labels := by
      have hz : ∀ j, raw4528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4528step0 = (fun i j => raw4528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4528step0 raw4528; decide +kernel
      have hl : raw4528step0Labels = raw4528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4528 raw4528Labels permutation434 hz
    mixedMoment B raw4528step0 raw4528step0Labels = mixedMoment B raw4528step1 raw4528step1Labels := by
      have hz : ∀ j, raw4528step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4528step1 = (fun i j => raw4528step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4528step1 raw4528step0; decide +kernel
      have hl : raw4528step1Labels = raw4528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4528step0 raw4528step0Labels permutation80 hz
    mixedMoment B raw4528step1 raw4528step1Labels = mixedMoment B raw4528step2 raw4528step2Labels := by
      have ha : raw4528step2 = (fun i j => raw4528step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4528step2 raw4528step1; decide +kernel
      have hl : raw4528step2Labels = raw4528step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4528step1 raw4528step1Labels permutation10 permutation2
    _ = mixedMoment B node1369 node1369Labels := by rfl

theorem canonical4529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4529 raw4529Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw4529 raw4529Labels = mixedMoment B raw4529step0 raw4529step0Labels := by
      have hz : ∀ j, raw4529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4529step0 = (fun i j => raw4529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4529step0 raw4529; decide +kernel
      have hl : raw4529step0Labels = raw4529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4529 raw4529Labels permutation434 hz
    mixedMoment B raw4529step0 raw4529step0Labels = mixedMoment B raw4529step1 raw4529step1Labels := by
      have hz : ∀ j, raw4529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4529step1 = (fun i j => raw4529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4529step1 raw4529step0; decide +kernel
      have hl : raw4529step1Labels = raw4529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4529step0 raw4529step0Labels permutation56 hz
    mixedMoment B raw4529step1 raw4529step1Labels = mixedMoment B raw4529step2 raw4529step2Labels := by
      have ha : raw4529step2 = (fun i j => raw4529step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4529step2 raw4529step1; decide +kernel
      have hl : raw4529step2Labels = raw4529step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4529step1 raw4529step1Labels permutation10 permutation2
    _ = mixedMoment B node1369 node1369Labels := by rfl

theorem canonical4530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4530 raw4530Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw4530 raw4530Labels = mixedMoment B raw4530step0 raw4530step0Labels := by
      have hz : ∀ j, raw4530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4530step0 = (fun i j => raw4530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4530step0 raw4530; decide +kernel
      have hl : raw4530step0Labels = raw4530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4530 raw4530Labels permutation346 hz
    mixedMoment B raw4530step0 raw4530step0Labels = mixedMoment B raw4530step1 raw4530step1Labels := by
      have hz : ∀ j, raw4530step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4530step1 = (fun i j => raw4530step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4530step1 raw4530step0; decide +kernel
      have hl : raw4530step1Labels = raw4530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4530step0 raw4530step0Labels permutation56 hz
    mixedMoment B raw4530step1 raw4530step1Labels = mixedMoment B raw4530step2 raw4530step2Labels := by
      have ha : raw4530step2 = (fun i j => raw4530step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4530step2 raw4530step1; decide +kernel
      have hl : raw4530step2Labels = raw4530step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4530step1 raw4530step1Labels permutation10 permutation2
    _ = mixedMoment B node1369 node1369Labels := by rfl

theorem canonical4531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4531 raw4531Labels = mixedMoment B node1438 node1438Labels := by
  calc
    mixedMoment B raw4531 raw4531Labels = mixedMoment B raw4531step0 raw4531step0Labels := by
      have hz : ∀ j, raw4531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4531step0 = (fun i j => raw4531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4531step0 raw4531; decide +kernel
      have hl : raw4531step0Labels = raw4531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4531 raw4531Labels permutation434 hz
    mixedMoment B raw4531step0 raw4531step0Labels = mixedMoment B raw4531step1 raw4531step1Labels := by
      have hz : ∀ j, raw4531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4531step1 = (fun i j => raw4531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4531step1 raw4531step0; decide +kernel
      have hl : raw4531step1Labels = raw4531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4531step0 raw4531step0Labels permutation80 hz
    mixedMoment B raw4531step1 raw4531step1Labels = mixedMoment B raw4531step2 raw4531step2Labels := by
      have hz : ∀ j, raw4531step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4531step2 = (fun i j => raw4531step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4531step2 raw4531step1; decide +kernel
      have hl : raw4531step2Labels = raw4531step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4531step1 raw4531step1Labels permutation14 hz
    _ = mixedMoment B node1438 node1438Labels := by rfl

theorem canonical4532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4532 raw4532Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw4532 raw4532Labels = mixedMoment B raw4532step0 raw4532step0Labels := by
      have hz : ∀ j, raw4532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4532step0 = (fun i j => raw4532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4532step0 raw4532; decide +kernel
      have hl : raw4532step0Labels = raw4532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4532 raw4532Labels permutation434 hz
    mixedMoment B raw4532step0 raw4532step0Labels = mixedMoment B raw4532step1 raw4532step1Labels := by
      have hz : ∀ j, raw4532step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4532step1 = (fun i j => raw4532step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4532step1 raw4532step0; decide +kernel
      have hl : raw4532step1Labels = raw4532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4532step0 raw4532step0Labels permutation80 hz
    mixedMoment B raw4532step1 raw4532step1Labels = mixedMoment B raw4532step2 raw4532step2Labels := by
      have hz : ∀ j, raw4532step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4532step2 = (fun i j => raw4532step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4532step2 raw4532step1; decide +kernel
      have hl : raw4532step2Labels = raw4532step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4532step1 raw4532step1Labels permutation14 hz
    mixedMoment B raw4532step2 raw4532step2Labels = mixedMoment B raw4532step3 raw4532step3Labels := by
      have ha : raw4532step3 = (fun i j => raw4532step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4532step3 raw4532step2; decide +kernel
      have hl : raw4532step3Labels = raw4532step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4532step2 raw4532step2Labels permutation7 permutation2
    mixedMoment B raw4532step3 raw4532step3Labels = mixedMoment B raw4532step4 raw4532step4Labels := by
      have ha : raw4532step4 = -raw4532step3 := by apply Matrix.ext; change ∀ i j, raw4532step4 i j = -(raw4532step3 i j); unfold raw4532step4 raw4532step3; decide +kernel
      have hl : raw4532step4Labels = raw4532step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1064 node1064Labels := by rfl

theorem canonical4533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4533 raw4533Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw4533 raw4533Labels = mixedMoment B raw4533step0 raw4533step0Labels := by
      have hz : ∀ j, raw4533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4533step0 = (fun i j => raw4533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4533step0 raw4533; decide +kernel
      have hl : raw4533step0Labels = raw4533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4533 raw4533Labels permutation434 hz
    mixedMoment B raw4533step0 raw4533step0Labels = mixedMoment B raw4533step1 raw4533step1Labels := by
      have ha : raw4533step1 = (fun i j => raw4533step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4533step1 raw4533step0; decide +kernel
      have hl : raw4533step1Labels = raw4533step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4533step0 raw4533step0Labels permutation139 permutation2
    mixedMoment B raw4533step1 raw4533step1Labels = mixedMoment B raw4533step2 raw4533step2Labels := by
      have ha : raw4533step2 = -raw4533step1 := by apply Matrix.ext; change ∀ i j, raw4533step2 i j = -(raw4533step1 i j); unfold raw4533step2 raw4533step1; decide +kernel
      have hl : raw4533step2Labels = raw4533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

theorem canonical4534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4534 raw4534Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw4534 raw4534Labels = mixedMoment B raw4534step0 raw4534step0Labels := by
      have hz : ∀ j, raw4534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4534step0 = (fun i j => raw4534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4534step0 raw4534; decide +kernel
      have hl : raw4534step0Labels = raw4534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4534 raw4534Labels permutation346 hz
    mixedMoment B raw4534step0 raw4534step0Labels = mixedMoment B raw4534step1 raw4534step1Labels := by
      have ha : raw4534step1 = (fun i j => raw4534step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4534step1 raw4534step0; decide +kernel
      have hl : raw4534step1Labels = raw4534step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4534step0 raw4534step0Labels permutation139 permutation2
    mixedMoment B raw4534step1 raw4534step1Labels = mixedMoment B raw4534step2 raw4534step2Labels := by
      have ha : raw4534step2 = -raw4534step1 := by apply Matrix.ext; change ∀ i j, raw4534step2 i j = -(raw4534step1 i j); unfold raw4534step2 raw4534step1; decide +kernel
      have hl : raw4534step2Labels = raw4534step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

theorem canonical4535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4535 raw4535Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw4535 raw4535Labels = mixedMoment B raw4535step0 raw4535step0Labels := by
      have hz : ∀ j, raw4535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4535step0 = (fun i j => raw4535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4535step0 raw4535; decide +kernel
      have hl : raw4535step0Labels = raw4535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4535 raw4535Labels permutation434 hz
    mixedMoment B raw4535step0 raw4535step0Labels = mixedMoment B raw4535step1 raw4535step1Labels := by
      have hz : ∀ j, raw4535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4535step1 = (fun i j => raw4535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4535step1 raw4535step0; decide +kernel
      have hl : raw4535step1Labels = raw4535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4535step0 raw4535step0Labels permutation80 hz
    mixedMoment B raw4535step1 raw4535step1Labels = mixedMoment B raw4535step2 raw4535step2Labels := by
      have ha : raw4535step2 = (fun i j => raw4535step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4535step2 raw4535step1; decide +kernel
      have hl : raw4535step2Labels = raw4535step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4535step1 raw4535step1Labels permutation29 permutation2
    mixedMoment B raw4535step2 raw4535step2Labels = mixedMoment B raw4535step3 raw4535step3Labels := by
      have ha : raw4535step3 = -raw4535step2 := by apply Matrix.ext; change ∀ i j, raw4535step3 i j = -(raw4535step2 i j); unfold raw4535step3 raw4535step2; decide +kernel
      have hl : raw4535step3Labels = raw4535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical4536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4536 raw4536Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw4536 raw4536Labels = mixedMoment B raw4536step0 raw4536step0Labels := by
      have hz : ∀ j, raw4536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4536step0 = (fun i j => raw4536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4536step0 raw4536; decide +kernel
      have hl : raw4536step0Labels = raw4536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4536 raw4536Labels permutation434 hz
    mixedMoment B raw4536step0 raw4536step0Labels = mixedMoment B raw4536step1 raw4536step1Labels := by
      have hz : ∀ j, raw4536step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4536step1 = (fun i j => raw4536step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4536step1 raw4536step0; decide +kernel
      have hl : raw4536step1Labels = raw4536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4536step0 raw4536step0Labels permutation80 hz
    mixedMoment B raw4536step1 raw4536step1Labels = mixedMoment B raw4536step2 raw4536step2Labels := by
      have ha : raw4536step2 = (fun i j => raw4536step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4536step2 raw4536step1; decide +kernel
      have hl : raw4536step2Labels = raw4536step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4536step1 raw4536step1Labels permutation10 permutation2
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical4537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4537 raw4537Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw4537 raw4537Labels = mixedMoment B raw4537step0 raw4537step0Labels := by
      have hz : ∀ j, raw4537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4537step0 = (fun i j => raw4537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4537step0 raw4537; decide +kernel
      have hl : raw4537step0Labels = raw4537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4537 raw4537Labels permutation434 hz
    mixedMoment B raw4537step0 raw4537step0Labels = mixedMoment B raw4537step1 raw4537step1Labels := by
      have ha : raw4537step1 = (fun i j => raw4537step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4537step1 raw4537step0; decide +kernel
      have hl : raw4537step1Labels = raw4537step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4537step0 raw4537step0Labels permutation145 permutation2
    mixedMoment B raw4537step1 raw4537step1Labels = mixedMoment B raw4537step2 raw4537step2Labels := by
      have ha : raw4537step2 = -raw4537step1 := by apply Matrix.ext; change ∀ i j, raw4537step2 i j = -(raw4537step1 i j); unfold raw4537step2 raw4537step1; decide +kernel
      have hl : raw4537step2Labels = raw4537step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

theorem canonical4538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4538 raw4538Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw4538 raw4538Labels = mixedMoment B raw4538step0 raw4538step0Labels := by
      have hz : ∀ j, raw4538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4538step0 = (fun i j => raw4538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4538step0 raw4538; decide +kernel
      have hl : raw4538step0Labels = raw4538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4538 raw4538Labels permutation346 hz
    mixedMoment B raw4538step0 raw4538step0Labels = mixedMoment B raw4538step1 raw4538step1Labels := by
      have ha : raw4538step1 = (fun i j => raw4538step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4538step1 raw4538step0; decide +kernel
      have hl : raw4538step1Labels = raw4538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4538step0 raw4538step0Labels permutation145 permutation2
    mixedMoment B raw4538step1 raw4538step1Labels = mixedMoment B raw4538step2 raw4538step2Labels := by
      have ha : raw4538step2 = -raw4538step1 := by apply Matrix.ext; change ∀ i j, raw4538step2 i j = -(raw4538step1 i j); unfold raw4538step2 raw4538step1; decide +kernel
      have hl : raw4538step2Labels = raw4538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

theorem canonical4539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4539 raw4539Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw4539 raw4539Labels = mixedMoment B raw4539step0 raw4539step0Labels := by
      have hz : ∀ j, raw4539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4539step0 = (fun i j => raw4539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4539step0 raw4539; decide +kernel
      have hl : raw4539step0Labels = raw4539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4539 raw4539Labels permutation434 hz
    mixedMoment B raw4539step0 raw4539step0Labels = mixedMoment B raw4539step1 raw4539step1Labels := by
      have hz : ∀ j, raw4539step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4539step1 = (fun i j => raw4539step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4539step1 raw4539step0; decide +kernel
      have hl : raw4539step1Labels = raw4539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4539step0 raw4539step0Labels permutation80 hz
    mixedMoment B raw4539step1 raw4539step1Labels = mixedMoment B raw4539step2 raw4539step2Labels := by
      have ha : raw4539step2 = (fun i j => raw4539step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4539step2 raw4539step1; decide +kernel
      have hl : raw4539step2Labels = raw4539step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4539step1 raw4539step1Labels permutation31 permutation2
    mixedMoment B raw4539step2 raw4539step2Labels = mixedMoment B raw4539step3 raw4539step3Labels := by
      have ha : raw4539step3 = -raw4539step2 := by apply Matrix.ext; change ∀ i j, raw4539step3 i j = -(raw4539step2 i j); unfold raw4539step3 raw4539step2; decide +kernel
      have hl : raw4539step3Labels = raw4539step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

theorem canonical4540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4540 raw4540Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw4540 raw4540Labels = mixedMoment B raw4540step0 raw4540step0Labels := by
      have hz : ∀ j, raw4540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4540step0 = (fun i j => raw4540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4540step0 raw4540; decide +kernel
      have hl : raw4540step0Labels = raw4540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4540 raw4540Labels permutation434 hz
    mixedMoment B raw4540step0 raw4540step0Labels = mixedMoment B raw4540step1 raw4540step1Labels := by
      have hz : ∀ j, raw4540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4540step1 = (fun i j => raw4540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4540step1 raw4540step0; decide +kernel
      have hl : raw4540step1Labels = raw4540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4540step0 raw4540step0Labels permutation80 hz
    mixedMoment B raw4540step1 raw4540step1Labels = mixedMoment B raw4540step2 raw4540step2Labels := by
      have ha : raw4540step2 = (fun i j => raw4540step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4540step2 raw4540step1; decide +kernel
      have hl : raw4540step2Labels = raw4540step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4540step1 raw4540step1Labels permutation31 permutation2
    mixedMoment B raw4540step2 raw4540step2Labels = mixedMoment B raw4540step3 raw4540step3Labels := by
      have ha : raw4540step3 = -raw4540step2 := by apply Matrix.ext; change ∀ i j, raw4540step3 i j = -(raw4540step2 i j); unfold raw4540step3 raw4540step2; decide +kernel
      have hl : raw4540step3Labels = raw4540step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1059 node1059Labels := by rfl

theorem canonical4541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4541 raw4541Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw4541 raw4541Labels = mixedMoment B raw4541step0 raw4541step0Labels := by
      have hz : ∀ j, raw4541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4541step0 = (fun i j => raw4541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4541step0 raw4541; decide +kernel
      have hl : raw4541step0Labels = raw4541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4541 raw4541Labels permutation434 hz
    mixedMoment B raw4541step0 raw4541step0Labels = mixedMoment B raw4541step1 raw4541step1Labels := by
      have hz : ∀ j, raw4541step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4541step1 = (fun i j => raw4541step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4541step1 raw4541step0; decide +kernel
      have hl : raw4541step1Labels = raw4541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4541step0 raw4541step0Labels permutation56 hz
    mixedMoment B raw4541step1 raw4541step1Labels = mixedMoment B raw4541step2 raw4541step2Labels := by
      have ha : raw4541step2 = (fun i j => raw4541step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4541step2 raw4541step1; decide +kernel
      have hl : raw4541step2Labels = raw4541step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4541step1 raw4541step1Labels permutation31 permutation2
    mixedMoment B raw4541step2 raw4541step2Labels = mixedMoment B raw4541step3 raw4541step3Labels := by
      have ha : raw4541step3 = -raw4541step2 := by apply Matrix.ext; change ∀ i j, raw4541step3 i j = -(raw4541step2 i j); unfold raw4541step3 raw4541step2; decide +kernel
      have hl : raw4541step3Labels = raw4541step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

theorem canonical4542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4542 raw4542Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw4542 raw4542Labels = mixedMoment B raw4542step0 raw4542step0Labels := by
      have hz : ∀ j, raw4542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4542step0 = (fun i j => raw4542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4542step0 raw4542; decide +kernel
      have hl : raw4542step0Labels = raw4542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4542 raw4542Labels permutation346 hz
    mixedMoment B raw4542step0 raw4542step0Labels = mixedMoment B raw4542step1 raw4542step1Labels := by
      have hz : ∀ j, raw4542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4542step1 = (fun i j => raw4542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4542step1 raw4542step0; decide +kernel
      have hl : raw4542step1Labels = raw4542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4542step0 raw4542step0Labels permutation56 hz
    mixedMoment B raw4542step1 raw4542step1Labels = mixedMoment B raw4542step2 raw4542step2Labels := by
      have ha : raw4542step2 = (fun i j => raw4542step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4542step2 raw4542step1; decide +kernel
      have hl : raw4542step2Labels = raw4542step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4542step1 raw4542step1Labels permutation31 permutation2
    mixedMoment B raw4542step2 raw4542step2Labels = mixedMoment B raw4542step3 raw4542step3Labels := by
      have ha : raw4542step3 = -raw4542step2 := by apply Matrix.ext; change ∀ i j, raw4542step3 i j = -(raw4542step2 i j); unfold raw4542step3 raw4542step2; decide +kernel
      have hl : raw4542step3Labels = raw4542step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

theorem canonical4543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4543 raw4543Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw4543 raw4543Labels = mixedMoment B raw4543step0 raw4543step0Labels := by
      have hz : ∀ j, raw4543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4543step0 = (fun i j => raw4543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4543step0 raw4543; decide +kernel
      have hl : raw4543step0Labels = raw4543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4543 raw4543Labels permutation434 hz
    mixedMoment B raw4543step0 raw4543step0Labels = mixedMoment B raw4543step1 raw4543step1Labels := by
      have hz : ∀ j, raw4543step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4543step1 = (fun i j => raw4543step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4543step1 raw4543step0; decide +kernel
      have hl : raw4543step1Labels = raw4543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4543step0 raw4543step0Labels permutation80 hz
    mixedMoment B raw4543step1 raw4543step1Labels = mixedMoment B raw4543step2 raw4543step2Labels := by
      have hz : ∀ j, raw4543step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4543step2 = (fun i j => raw4543step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4543step2 raw4543step1; decide +kernel
      have hl : raw4543step2Labels = raw4543step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4543step1 raw4543step1Labels permutation14 hz
    mixedMoment B raw4543step2 raw4543step2Labels = mixedMoment B raw4543step3 raw4543step3Labels := by
      have ha : raw4543step3 = (fun i j => raw4543step2 (permutation5 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4543step3 raw4543step2; decide +kernel
      have hl : raw4543step3Labels = raw4543step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4543step2 raw4543step2Labels permutation5 permutation4
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical4544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4544 raw4544Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw4544 raw4544Labels = mixedMoment B raw4544step0 raw4544step0Labels := by
      have hz : ∀ j, raw4544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4544step0 = (fun i j => raw4544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4544step0 raw4544; decide +kernel
      have hl : raw4544step0Labels = raw4544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4544 raw4544Labels permutation434 hz
    mixedMoment B raw4544step0 raw4544step0Labels = mixedMoment B raw4544step1 raw4544step1Labels := by
      have hz : ∀ j, raw4544step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4544step1 = (fun i j => raw4544step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4544step1 raw4544step0; decide +kernel
      have hl : raw4544step1Labels = raw4544step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4544step0 raw4544step0Labels permutation56 hz
    mixedMoment B raw4544step1 raw4544step1Labels = mixedMoment B raw4544step2 raw4544step2Labels := by
      have ha : raw4544step2 = (fun i j => raw4544step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4544step2 raw4544step1; decide +kernel
      have hl : raw4544step2Labels = raw4544step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4544step1 raw4544step1Labels permutation29 permutation2
    mixedMoment B raw4544step2 raw4544step2Labels = mixedMoment B raw4544step3 raw4544step3Labels := by
      have ha : raw4544step3 = -raw4544step2 := by apply Matrix.ext; change ∀ i j, raw4544step3 i j = -(raw4544step2 i j); unfold raw4544step3 raw4544step2; decide +kernel
      have hl : raw4544step3Labels = raw4544step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical4545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4545 raw4545Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw4545 raw4545Labels = mixedMoment B raw4545step0 raw4545step0Labels := by
      have hz : ∀ j, raw4545 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4545step0 = (fun i j => raw4545 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4545step0 raw4545; decide +kernel
      have hl : raw4545step0Labels = raw4545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4545 raw4545Labels permutation346 hz
    mixedMoment B raw4545step0 raw4545step0Labels = mixedMoment B raw4545step1 raw4545step1Labels := by
      have hz : ∀ j, raw4545step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4545step1 = (fun i j => raw4545step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4545step1 raw4545step0; decide +kernel
      have hl : raw4545step1Labels = raw4545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4545step0 raw4545step0Labels permutation56 hz
    mixedMoment B raw4545step1 raw4545step1Labels = mixedMoment B raw4545step2 raw4545step2Labels := by
      have ha : raw4545step2 = (fun i j => raw4545step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4545step2 raw4545step1; decide +kernel
      have hl : raw4545step2Labels = raw4545step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4545step1 raw4545step1Labels permutation29 permutation2
    mixedMoment B raw4545step2 raw4545step2Labels = mixedMoment B raw4545step3 raw4545step3Labels := by
      have ha : raw4545step3 = -raw4545step2 := by apply Matrix.ext; change ∀ i j, raw4545step3 i j = -(raw4545step2 i j); unfold raw4545step3 raw4545step2; decide +kernel
      have hl : raw4545step3Labels = raw4545step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical4546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4546 raw4546Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw4546 raw4546Labels = mixedMoment B raw4546step0 raw4546step0Labels := by
      have hz : ∀ j, raw4546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4546step0 = (fun i j => raw4546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4546step0 raw4546; decide +kernel
      have hl : raw4546step0Labels = raw4546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4546 raw4546Labels permutation434 hz
    mixedMoment B raw4546step0 raw4546step0Labels = mixedMoment B raw4546step1 raw4546step1Labels := by
      have hz : ∀ j, raw4546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4546step1 = (fun i j => raw4546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4546step1 raw4546step0; decide +kernel
      have hl : raw4546step1Labels = raw4546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4546step0 raw4546step0Labels permutation80 hz
    mixedMoment B raw4546step1 raw4546step1Labels = mixedMoment B raw4546step2 raw4546step2Labels := by
      have hz : ∀ j, raw4546step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4546step2 = (fun i j => raw4546step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4546step2 raw4546step1; decide +kernel
      have hl : raw4546step2Labels = raw4546step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4546step1 raw4546step1Labels permutation14 hz
    mixedMoment B raw4546step2 raw4546step2Labels = mixedMoment B raw4546step3 raw4546step3Labels := by
      have ha : raw4546step3 = (fun i j => raw4546step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4546step3 raw4546step2; decide +kernel
      have hl : raw4546step3Labels = raw4546step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4546step2 raw4546step2Labels permutation7 permutation2
    mixedMoment B raw4546step3 raw4546step3Labels = mixedMoment B raw4546step4 raw4546step4Labels := by
      have ha : raw4546step4 = -raw4546step3 := by apply Matrix.ext; change ∀ i j, raw4546step4 i j = -(raw4546step3 i j); unfold raw4546step4 raw4546step3; decide +kernel
      have hl : raw4546step4Labels = raw4546step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical4547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4547 raw4547Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw4547 raw4547Labels = mixedMoment B raw4547step0 raw4547step0Labels := by
      have hz : ∀ j, raw4547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4547step0 = (fun i j => raw4547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4547step0 raw4547; decide +kernel
      have hl : raw4547step0Labels = raw4547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4547 raw4547Labels permutation434 hz
    mixedMoment B raw4547step0 raw4547step0Labels = mixedMoment B raw4547step1 raw4547step1Labels := by
      have hz : ∀ j, raw4547step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4547step1 = (fun i j => raw4547step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4547step1 raw4547step0; decide +kernel
      have hl : raw4547step1Labels = raw4547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4547step0 raw4547step0Labels permutation56 hz
    mixedMoment B raw4547step1 raw4547step1Labels = mixedMoment B raw4547step2 raw4547step2Labels := by
      have ha : raw4547step2 = (fun i j => raw4547step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4547step2 raw4547step1; decide +kernel
      have hl : raw4547step2Labels = raw4547step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4547step1 raw4547step1Labels permutation31 permutation2
    mixedMoment B raw4547step2 raw4547step2Labels = mixedMoment B raw4547step3 raw4547step3Labels := by
      have ha : raw4547step3 = -raw4547step2 := by apply Matrix.ext; change ∀ i j, raw4547step3 i j = -(raw4547step2 i j); unfold raw4547step3 raw4547step2; decide +kernel
      have hl : raw4547step3Labels = raw4547step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1059 node1059Labels := by rfl

theorem canonical4548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4548 raw4548Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw4548 raw4548Labels = mixedMoment B raw4548step0 raw4548step0Labels := by
      have hz : ∀ j, raw4548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4548step0 = (fun i j => raw4548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4548step0 raw4548; decide +kernel
      have hl : raw4548step0Labels = raw4548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4548 raw4548Labels permutation346 hz
    mixedMoment B raw4548step0 raw4548step0Labels = mixedMoment B raw4548step1 raw4548step1Labels := by
      have hz : ∀ j, raw4548step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4548step1 = (fun i j => raw4548step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4548step1 raw4548step0; decide +kernel
      have hl : raw4548step1Labels = raw4548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4548step0 raw4548step0Labels permutation56 hz
    mixedMoment B raw4548step1 raw4548step1Labels = mixedMoment B raw4548step2 raw4548step2Labels := by
      have ha : raw4548step2 = (fun i j => raw4548step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4548step2 raw4548step1; decide +kernel
      have hl : raw4548step2Labels = raw4548step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4548step1 raw4548step1Labels permutation31 permutation2
    mixedMoment B raw4548step2 raw4548step2Labels = mixedMoment B raw4548step3 raw4548step3Labels := by
      have ha : raw4548step3 = -raw4548step2 := by apply Matrix.ext; change ∀ i j, raw4548step3 i j = -(raw4548step2 i j); unfold raw4548step3 raw4548step2; decide +kernel
      have hl : raw4548step3Labels = raw4548step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1059 node1059Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw554 raw554Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw554 raw554Labels = mixedMoment B raw554step0 raw554step0Labels := by
      have ha : raw554step0 = (fun i j => raw554 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw554step0 raw554; decide +kernel
      have hl : raw554step0Labels = raw554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw554 raw554Labels permutation2 permutation5
    mixedMoment B raw554step0 raw554step0Labels = mixedMoment B raw554step1 raw554step1Labels := by
      have ha : raw554step1 = raw554step0 := by apply Matrix.ext; unfold raw554step1 raw554step0; decide +kernel
      have hl : raw554step0Labels = labelEmbedding1 ∘ raw554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw554step0 raw554step0Labels raw554step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

theorem canonical555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw555 raw555Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw555 raw555Labels = mixedMoment B raw555step0 raw555step0Labels := by
      have ha : raw555step0 = (fun i j => raw555 (permutation5 i) (permutation2 j)) := by apply Matrix.ext; unfold raw555step0 raw555; decide +kernel
      have hl : raw555step0Labels = raw555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw555 raw555Labels permutation5 permutation2
    _ = mixedMoment B node507 node507Labels := by rfl

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

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_GroupedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit grouping formulas for the two- and three-column equality
patterns. These discharge the dependent finite-label calculations once,
so concrete certificate rows need only ordinary integer arithmetic. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family3_0 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1 + A i 2) := by
  change groupedColumns A (fun _ : Fin 3 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family3_1 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 1) =
      (fun i => ![A i 0 + A i 1, A i 2]) := by
  change groupedColumns A (![0, 0, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_2 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 2) =
      (fun i => ![A i 0 + A i 2, A i 1]) := by
  change groupedColumns A (![0, 1, 0] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_3 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 3) =
      (fun i => ![A i 0, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_4 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 4) = A := by
  change groupedColumns A (fun j : Fin 3 => j) = _
  ext i b
  simp [groupedColumns, Finset.sum_filter]

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleRules
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

/-- The five equality patterns for three sampled column indices. -/
theorem single_label_three {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 3) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family3 EqualityPatterns.covers3
  rw [sum_fin_five] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3,
    EqualityPatterns.blocks3, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Nat.descFactorial] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

theorem canonical5214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5214 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5214 = injectiveMoment H raw5214step0 := by
      have hz : ∀ j, raw5214 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5214step0 = (fun i j => raw5214 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5214 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7683 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7683 = injectiveMoment H raw7683step0 := by
      have heq : raw7683step0 = (fun i j => raw7683 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7683 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8985 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8985 = injectiveMoment H raw8985step0 := by
      have hz : ∀ j, raw8985 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8985step0 = (fun i j => raw8985 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8985 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw813 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw813 = injectiveMoment H raw813step0 := by
      have heq : raw813step0 = -raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw813).symm
    injectiveMoment H raw813step0 = injectiveMoment H raw813step1 := by
      have heq : raw813step1 = (fun i j => raw813step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw813step0 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node507 node507Labels = Sparse.eval singlePairValue507 (familyPairVector B) := by
  have hp := single_label_three B hB node507
  have hl : node507Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node507 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node507 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 2) = PairSemantics.raw8985 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node507 PairSemantics.raw8985; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8985 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 3) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node507 PairSemantics.raw5183; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node507 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value41 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node507 (EqualityPatterns.family3.label 4) = PairSemantics.raw4141 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node507 PairSemantics.raw4141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4141 hH).trans (PairSemantics.sound41 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue507, PairSemantics.value0, PairSemantics.value4, PairSemantics.value41, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node420 node420Labels = Sparse.eval singlePairValue420 (familyPairVector B) := by
  have hp := single_label_three B hB node420
  have hl : node420Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node420 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node420 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node420 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node420 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value36 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 4) = PairSemantics.raw813 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node420 PairSemantics.raw813; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical813 hH).trans (PairSemantics.sound36 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue420, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value11, PairSemantics.value36, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2788 node2788Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw284 singletonSmall2788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2788) = raw284Labels := by decide +kernel
  rw [hl, canonical284 B hB] at h
  have hc0 : mixedMoment B raw284 (Fin.cases (0 : Fin 1) singletonSmall2788) =
      mixedMoment B node420 node420Labels := by
    have ha : raw284 = raw285 := by apply Matrix.ext; unfold raw284 raw285; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2788 = raw285Labels := by decide +kernel
    rw [ha, hj, canonical285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3121 node3121Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw404 singletonSmall3121
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3121) = raw404Labels := by decide +kernel
  rw [hl, canonical404 B hB] at h
  have hc0 : mixedMoment B raw404 (Fin.cases (0 : Fin 1) singletonSmall3121) =
      mixedMoment B node420 node420Labels := by
    have ha : raw404 = raw405 := by apply Matrix.ext; unfold raw404 raw405; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3121 = raw405Labels := by decide +kernel
    rw [ha, hj, canonical405 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3916 node3916Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node507 node507Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw554 singletonSmall3916
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3916) = raw554Labels := by decide +kernel
  rw [hl, canonical554 B hB] at h
  have hc0 : mixedMoment B raw554 (Fin.cases (0 : Fin 1) singletonSmall3916) =
      mixedMoment B node507 node507Labels := by
    have ha : raw554 = raw555 := by apply Matrix.ext; unfold raw554 raw555; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3916 = raw555Labels := by decide +kernel
    rw [ha, hj, canonical555 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem sound420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node420 node420Labels = Sparse.eval nodeValue420 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue420 (familyPairVector B) := singlePair420 B _hB
    _ = _ := by norm_num [singlePairValue420, nodeValue420, Sparse.eval, mixedVector] <;> ring

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2281 node2281Labels = Sparse.eval nodeValue2281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2281) = mixedMoment B node2281 node2281Labels := rfl
  simpa [nodeValue2281, Sparse.eval] using hc.symm

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

theorem sound2788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2788 node2788Labels = Sparse.eval nodeValue2788 (mixedVector B) := by
  have h := singleton2788 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue2788, nodeValue420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3633 node3633Labels = Sparse.eval nodeValue3633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3633) = mixedMoment B node3633 node3633Labels := rfl
  simpa [nodeValue3633, Sparse.eval] using hc.symm

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

theorem sound828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node828 node828Labels = Sparse.eval nodeValue828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 828) = mixedMoment B node828 node828Labels := rfl
  simpa [nodeValue828, Sparse.eval] using hc.symm

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

theorem sound832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node832 node832Labels = Sparse.eval nodeValue832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 832) = mixedMoment B node832 node832Labels := rfl
  simpa [nodeValue832, Sparse.eval] using hc.symm

theorem sound860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node860 node860Labels = Sparse.eval nodeValue860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 860) = mixedMoment B node860 node860Labels := rfl
  simpa [nodeValue860, Sparse.eval] using hc.symm

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

theorem sound1059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1059 node1059Labels = Sparse.eval nodeValue1059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1059) = mixedMoment B node1059 node1059Labels := rfl
  simpa [nodeValue1059, Sparse.eval] using hc.symm

theorem sound1064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1064 node1064Labels = Sparse.eval nodeValue1064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1064) = mixedMoment B node1064 node1064Labels := rfl
  simpa [nodeValue1064, Sparse.eval] using hc.symm

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

theorem sound1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1091 node1091Labels = Sparse.eval nodeValue1091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1091) = mixedMoment B node1091 node1091Labels := rfl
  simpa [nodeValue1091, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1190 node1190Labels = Sparse.eval nodeValue1190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1190) = mixedMoment B node1190 node1190Labels := rfl
  simpa [nodeValue1190, Sparse.eval] using hc.symm

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

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

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

theorem sound1369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1369 node1369Labels = Sparse.eval nodeValue1369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1369) = mixedMoment B node1369 node1369Labels := rfl
  simpa [nodeValue1369, Sparse.eval] using hc.symm

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

theorem sound1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1438 node1438Labels = Sparse.eval nodeValue1438 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1438) = mixedMoment B node1438 node1438Labels := rfl
  simpa [nodeValue1438, Sparse.eval] using hc.symm

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

theorem sound1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1729 node1729Labels = Sparse.eval nodeValue1729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1729) = mixedMoment B node1729 node1729Labels := rfl
  simpa [nodeValue1729, Sparse.eval] using hc.symm

theorem sound1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1746 node1746Labels = Sparse.eval nodeValue1746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1746) = mixedMoment B node1746 node1746Labels := rfl
  simpa [nodeValue1746, Sparse.eval] using hc.symm

theorem sound1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1747 node1747Labels = Sparse.eval nodeValue1747 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1747) = mixedMoment B node1747 node1747Labels := rfl
  simpa [nodeValue1747, Sparse.eval] using hc.symm

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

theorem sound1757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1757 node1757Labels = Sparse.eval nodeValue1757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1757) = mixedMoment B node1757 node1757Labels := rfl
  simpa [nodeValue1757, Sparse.eval] using hc.symm

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

theorem sound1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1926 node1926Labels = Sparse.eval nodeValue1926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1926) = mixedMoment B node1926 node1926Labels := rfl
  simpa [nodeValue1926, Sparse.eval] using hc.symm

theorem sound1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1951 node1951Labels = Sparse.eval nodeValue1951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1951) = mixedMoment B node1951 node1951Labels := rfl
  simpa [nodeValue1951, Sparse.eval] using hc.symm

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

theorem sound2035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2035 node2035Labels = Sparse.eval nodeValue2035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2035) = mixedMoment B node2035 node2035Labels := rfl
  simpa [nodeValue2035, Sparse.eval] using hc.symm

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

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

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

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

theorem sound2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2134 node2134Labels = Sparse.eval nodeValue2134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2134) = mixedMoment B node2134 node2134Labels := rfl
  simpa [nodeValue2134, Sparse.eval] using hc.symm

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

theorem sound2207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2207 node2207Labels = Sparse.eval nodeValue2207 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2207) = mixedMoment B node2207 node2207Labels := rfl
  simpa [nodeValue2207, Sparse.eval] using hc.symm

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
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

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2267 node2267Labels = Sparse.eval nodeValue2267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2267) = mixedMoment B node2267 node2267Labels := rfl
  simpa [nodeValue2267, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

theorem sound2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2293 node2293Labels = Sparse.eval nodeValue2293 (mixedVector B) := by
  simpa only [nodeValue2293, Sparse.eval_nil] using zero2293 B _hB _hF

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

theorem sound2744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2744 node2744Labels = Sparse.eval nodeValue2744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2744) = mixedMoment B node2744 node2744Labels := rfl
  simpa [nodeValue2744, Sparse.eval] using hc.symm

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

theorem sound2789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2789 node2789Labels = Sparse.eval nodeValue2789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2789) = mixedMoment B node2789 node2789Labels := rfl
  simpa [nodeValue2789, Sparse.eval] using hc.symm

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

theorem sound3052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3052 node3052Labels = Sparse.eval nodeValue3052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3052) = mixedMoment B node3052 node3052Labels := rfl
  simpa [nodeValue3052, Sparse.eval] using hc.symm

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

theorem sound3121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3121 node3121Labels = Sparse.eval nodeValue3121 (mixedVector B) := by
  have h := singleton3121 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue3121, nodeValue420, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3634 node3634Labels = Sparse.eval nodeValue3634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3634) = mixedMoment B node3634 node3634Labels := rfl
  simpa [nodeValue3634, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node507 node507Labels = Sparse.eval nodeValue507 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue507 (familyPairVector B) := singlePair507 B _hB
    _ = _ := by norm_num [singlePairValue507, nodeValue507, Sparse.eval, mixedVector] <;> ring

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

theorem sound3916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3916 node3916Labels = Sparse.eval nodeValue3916 (mixedVector B) := by
  have h := singleton3916 B _hB
  rw [sound507 B _hB _hF] at h
  norm_num [nodeValue3916, nodeValue507, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources3
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm116 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA116 + difference 0 0) (sourceB116 + difference 0 0) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA116 + difference 0 0) (sourceB116 + difference 0 0) sourceC116) = raw4097 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4097; decide +kernel
    rw [ha]
    exact (canonical4097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA116 + difference 1 0) (sourceB116 + difference 0 1) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA116 + difference 1 0) (sourceB116 + difference 0 1) sourceC116) = raw4376 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4376; decide +kernel
    rw [ha]
    exact (canonical4376 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA116 + difference 2 0) (sourceB116 + difference 0 2) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA116 + difference 2 0) (sourceB116 + difference 0 2) sourceC116) = raw4377 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4377; decide +kernel
    rw [ha]
    exact (canonical4377 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA116 + difference 3 0) (sourceB116 + difference 0 3) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA116 + difference 3 0) (sourceB116 + difference 0 3) sourceC116) = raw4272 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4272; decide +kernel
    rw [ha]
    exact (canonical4272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA116 + difference 4 0) (sourceB116 + difference 0 4) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA116 + difference 4 0) (sourceB116 + difference 0 4) sourceC116) = raw4091 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4091; decide +kernel
    rw [ha]
    exact (canonical4091 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA116 + difference 5 0) (sourceB116 + difference 0 5) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA116 + difference 5 0) (sourceB116 + difference 0 5) sourceC116) = raw4378 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4378; decide +kernel
    rw [ha]
    exact (canonical4378 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA116 + sourceB116) sourceC116) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA116 + sourceB116) sourceC116) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA116 sourceB116 sourceC116 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA116 sourceB116 sourceC116
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm116, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm118 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA118 + difference 0 1) (sourceB118 + difference 1 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA118 + difference 0 1) (sourceB118 + difference 1 0) sourceC118) = raw4401 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4401; decide +kernel
    rw [ha]
    exact (canonical4401 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA118 + difference 0 2) (sourceB118 + difference 2 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA118 + difference 0 2) (sourceB118 + difference 2 0) sourceC118) = raw4402 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4402; decide +kernel
    rw [ha]
    exact (canonical4402 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA118 + difference 0 3) (sourceB118 + difference 3 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA118 + difference 0 3) (sourceB118 + difference 3 0) sourceC118) = raw4403 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4403; decide +kernel
    rw [ha]
    exact (canonical4403 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA118 + difference 0 4) (sourceB118 + difference 4 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA118 + difference 0 4) (sourceB118 + difference 4 0) sourceC118) = raw4404 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4404; decide +kernel
    rw [ha]
    exact (canonical4404 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA118 + difference 0 5) (sourceB118 + difference 5 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3916) := by
    have ha : (tripleCharges (sourceA118 + difference 0 5) (sourceB118 + difference 5 0) sourceC118) = raw4405 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4405; decide +kernel
    rw [ha]
    exact (canonical4405 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA118 + difference 1 0) (sourceB118 + difference 0 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA118 + difference 1 0) (sourceB118 + difference 0 1) sourceC118) = raw4406 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4406; decide +kernel
    rw [ha]
    exact (canonical4406 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA118 + difference 1 2) (sourceB118 + difference 2 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 1 2) (sourceB118 + difference 2 1) sourceC118) = raw4407 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4407; decide +kernel
    rw [ha]
    exact (canonical4407 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA118 + difference 1 3) (sourceB118 + difference 3 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 1 3) (sourceB118 + difference 3 1) sourceC118) = raw4408 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4408; decide +kernel
    rw [ha]
    exact (canonical4408 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA118 + difference 1 4) (sourceB118 + difference 4 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA118 + difference 1 4) (sourceB118 + difference 4 1) sourceC118) = raw4409 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4409; decide +kernel
    rw [ha]
    exact (canonical4409 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA118 + difference 1 5) (sourceB118 + difference 5 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA118 + difference 1 5) (sourceB118 + difference 5 1) sourceC118) = raw4410 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4410; decide +kernel
    rw [ha]
    exact (canonical4410 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA118 + difference 2 0) (sourceB118 + difference 0 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA118 + difference 2 0) (sourceB118 + difference 0 2) sourceC118) = raw4411 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4411; decide +kernel
    rw [ha]
    exact (canonical4411 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA118 + difference 2 1) (sourceB118 + difference 1 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 2 1) (sourceB118 + difference 1 2) sourceC118) = raw4412 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4412; decide +kernel
    rw [ha]
    exact (canonical4412 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA118 + difference 2 3) (sourceB118 + difference 3 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 2 3) (sourceB118 + difference 3 2) sourceC118) = raw4413 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4413; decide +kernel
    rw [ha]
    exact (canonical4413 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA118 + difference 2 4) (sourceB118 + difference 4 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA118 + difference 2 4) (sourceB118 + difference 4 2) sourceC118) = raw4414 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4414; decide +kernel
    rw [ha]
    exact (canonical4414 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA118 + difference 2 5) (sourceB118 + difference 5 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA118 + difference 2 5) (sourceB118 + difference 5 2) sourceC118) = raw4415 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4415; decide +kernel
    rw [ha]
    exact (canonical4415 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA118 + difference 3 0) (sourceB118 + difference 0 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA118 + difference 3 0) (sourceB118 + difference 0 3) sourceC118) = raw4416 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4416; decide +kernel
    rw [ha]
    exact (canonical4416 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA118 + difference 3 1) (sourceB118 + difference 1 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 3 1) (sourceB118 + difference 1 3) sourceC118) = raw4417 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4417; decide +kernel
    rw [ha]
    exact (canonical4417 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA118 + difference 3 2) (sourceB118 + difference 2 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 3 2) (sourceB118 + difference 2 3) sourceC118) = raw4418 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4418; decide +kernel
    rw [ha]
    exact (canonical4418 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA118 + difference 3 4) (sourceB118 + difference 4 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA118 + difference 3 4) (sourceB118 + difference 4 3) sourceC118) = raw4419 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4419; decide +kernel
    rw [ha]
    exact (canonical4419 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA118 + difference 3 5) (sourceB118 + difference 5 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA118 + difference 3 5) (sourceB118 + difference 5 3) sourceC118) = raw4420 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4420; decide +kernel
    rw [ha]
    exact (canonical4420 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA118 + difference 4 0) (sourceB118 + difference 0 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA118 + difference 4 0) (sourceB118 + difference 0 4) sourceC118) = raw4421 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4421; decide +kernel
    rw [ha]
    exact (canonical4421 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA118 + difference 4 1) (sourceB118 + difference 1 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA118 + difference 4 1) (sourceB118 + difference 1 4) sourceC118) = raw4422 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4422; decide +kernel
    rw [ha]
    exact (canonical4422 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA118 + difference 4 2) (sourceB118 + difference 2 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA118 + difference 4 2) (sourceB118 + difference 2 4) sourceC118) = raw4423 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4423; decide +kernel
    rw [ha]
    exact (canonical4423 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA118 + difference 4 3) (sourceB118 + difference 3 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA118 + difference 4 3) (sourceB118 + difference 3 4) sourceC118) = raw4424 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4424; decide +kernel
    rw [ha]
    exact (canonical4424 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA118 + difference 4 5) (sourceB118 + difference 5 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA118 + difference 4 5) (sourceB118 + difference 5 4) sourceC118) = raw4425 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4425; decide +kernel
    rw [ha]
    exact (canonical4425 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA118 + difference 5 0) (sourceB118 + difference 0 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA118 + difference 5 0) (sourceB118 + difference 0 5) sourceC118) = raw4426 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4426; decide +kernel
    rw [ha]
    exact (canonical4426 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA118 + difference 5 1) (sourceB118 + difference 1 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA118 + difference 5 1) (sourceB118 + difference 1 5) sourceC118) = raw4427 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4427; decide +kernel
    rw [ha]
    exact (canonical4427 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA118 + difference 5 2) (sourceB118 + difference 2 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA118 + difference 5 2) (sourceB118 + difference 2 5) sourceC118) = raw4428 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4428; decide +kernel
    rw [ha]
    exact (canonical4428 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA118 + difference 5 3) (sourceB118 + difference 3 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA118 + difference 5 3) (sourceB118 + difference 3 5) sourceC118) = raw4429 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4429; decide +kernel
    rw [ha]
    exact (canonical4429 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA118 + difference 5 4) (sourceB118 + difference 4 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 860) := by
    have ha : (tripleCharges (sourceA118 + difference 5 4) (sourceB118 + difference 4 5) sourceC118) = raw4430 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4430; decide +kernel
    rw [ha]
    exact (canonical4430 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA118 sourceB118 sourceC118
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm118, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm121 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA121 + difference 0 1) (sourceB121 + difference 1 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA121 + difference 0 1) (sourceB121 + difference 1 0) sourceC121) = raw4491 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4491; decide +kernel
    rw [ha]
    exact (canonical4491 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA121 + difference 0 2) (sourceB121 + difference 2 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA121 + difference 0 2) (sourceB121 + difference 2 0) sourceC121) = raw4492 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4492; decide +kernel
    rw [ha]
    exact (canonical4492 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA121 + difference 0 3) (sourceB121 + difference 3 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA121 + difference 0 3) (sourceB121 + difference 3 0) sourceC121) = raw4493 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4493; decide +kernel
    rw [ha]
    exact (canonical4493 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA121 + difference 0 4) (sourceB121 + difference 4 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA121 + difference 0 4) (sourceB121 + difference 4 0) sourceC121) = raw4494 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4494; decide +kernel
    rw [ha]
    exact (canonical4494 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA121 + difference 0 5) (sourceB121 + difference 5 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA121 + difference 0 5) (sourceB121 + difference 5 0) sourceC121) = raw4495 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4495; decide +kernel
    rw [ha]
    exact (canonical4495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA121 + difference 1 0) (sourceB121 + difference 0 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA121 + difference 1 0) (sourceB121 + difference 0 1) sourceC121) = raw4496 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4496; decide +kernel
    rw [ha]
    exact (canonical4496 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA121 + difference 1 2) (sourceB121 + difference 2 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 1 2) (sourceB121 + difference 2 1) sourceC121) = raw4497 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4497; decide +kernel
    rw [ha]
    exact (canonical4497 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA121 + difference 1 3) (sourceB121 + difference 3 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 1 3) (sourceB121 + difference 3 1) sourceC121) = raw4498 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4498; decide +kernel
    rw [ha]
    exact (canonical4498 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA121 + difference 1 4) (sourceB121 + difference 4 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA121 + difference 1 4) (sourceB121 + difference 4 1) sourceC121) = raw4499 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4499; decide +kernel
    rw [ha]
    exact (canonical4499 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA121 + difference 1 5) (sourceB121 + difference 5 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA121 + difference 1 5) (sourceB121 + difference 5 1) sourceC121) = raw4500 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4500; decide +kernel
    rw [ha]
    exact (canonical4500 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA121 + difference 2 0) (sourceB121 + difference 0 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA121 + difference 2 0) (sourceB121 + difference 0 2) sourceC121) = raw4501 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4501; decide +kernel
    rw [ha]
    exact (canonical4501 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA121 + difference 2 1) (sourceB121 + difference 1 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 2 1) (sourceB121 + difference 1 2) sourceC121) = raw4502 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4502; decide +kernel
    rw [ha]
    exact (canonical4502 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA121 + difference 2 3) (sourceB121 + difference 3 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 2 3) (sourceB121 + difference 3 2) sourceC121) = raw4503 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4503; decide +kernel
    rw [ha]
    exact (canonical4503 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA121 + difference 2 4) (sourceB121 + difference 4 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA121 + difference 2 4) (sourceB121 + difference 4 2) sourceC121) = raw4504 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4504; decide +kernel
    rw [ha]
    exact (canonical4504 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA121 + difference 2 5) (sourceB121 + difference 5 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA121 + difference 2 5) (sourceB121 + difference 5 2) sourceC121) = raw4505 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4505; decide +kernel
    rw [ha]
    exact (canonical4505 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA121 + difference 3 0) (sourceB121 + difference 0 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA121 + difference 3 0) (sourceB121 + difference 0 3) sourceC121) = raw4506 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4506; decide +kernel
    rw [ha]
    exact (canonical4506 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA121 + difference 3 1) (sourceB121 + difference 1 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 3 1) (sourceB121 + difference 1 3) sourceC121) = raw4507 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4507; decide +kernel
    rw [ha]
    exact (canonical4507 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA121 + difference 3 2) (sourceB121 + difference 2 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 3 2) (sourceB121 + difference 2 3) sourceC121) = raw4508 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4508; decide +kernel
    rw [ha]
    exact (canonical4508 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA121 + difference 3 4) (sourceB121 + difference 4 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA121 + difference 3 4) (sourceB121 + difference 4 3) sourceC121) = raw4509 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4509; decide +kernel
    rw [ha]
    exact (canonical4509 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA121 + difference 3 5) (sourceB121 + difference 5 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA121 + difference 3 5) (sourceB121 + difference 5 3) sourceC121) = raw4510 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4510; decide +kernel
    rw [ha]
    exact (canonical4510 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA121 + difference 4 0) (sourceB121 + difference 0 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA121 + difference 4 0) (sourceB121 + difference 0 4) sourceC121) = raw4511 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4511; decide +kernel
    rw [ha]
    exact (canonical4511 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA121 + difference 4 1) (sourceB121 + difference 1 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA121 + difference 4 1) (sourceB121 + difference 1 4) sourceC121) = raw4512 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4512; decide +kernel
    rw [ha]
    exact (canonical4512 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA121 + difference 4 2) (sourceB121 + difference 2 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA121 + difference 4 2) (sourceB121 + difference 2 4) sourceC121) = raw4513 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4513; decide +kernel
    rw [ha]
    exact (canonical4513 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA121 + difference 4 3) (sourceB121 + difference 3 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA121 + difference 4 3) (sourceB121 + difference 3 4) sourceC121) = raw4514 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4514; decide +kernel
    rw [ha]
    exact (canonical4514 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA121 + difference 4 5) (sourceB121 + difference 5 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA121 + difference 4 5) (sourceB121 + difference 5 4) sourceC121) = raw4515 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4515; decide +kernel
    rw [ha]
    exact (canonical4515 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA121 + difference 5 0) (sourceB121 + difference 0 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA121 + difference 5 0) (sourceB121 + difference 0 5) sourceC121) = raw4516 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4516; decide +kernel
    rw [ha]
    exact (canonical4516 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA121 + difference 5 1) (sourceB121 + difference 1 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA121 + difference 5 1) (sourceB121 + difference 1 5) sourceC121) = raw4517 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4517; decide +kernel
    rw [ha]
    exact (canonical4517 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA121 + difference 5 2) (sourceB121 + difference 2 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA121 + difference 5 2) (sourceB121 + difference 2 5) sourceC121) = raw4518 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4518; decide +kernel
    rw [ha]
    exact (canonical4518 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA121 + difference 5 3) (sourceB121 + difference 3 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA121 + difference 5 3) (sourceB121 + difference 3 5) sourceC121) = raw4519 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4519; decide +kernel
    rw [ha]
    exact (canonical4519 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA121 + difference 5 4) (sourceB121 + difference 4 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA121 + difference 5 4) (sourceB121 + difference 4 5) sourceC121) = raw4520 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4520; decide +kernel
    rw [ha]
    exact (canonical4520 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA121 sourceB121 sourceC121
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm121, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm122 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA122 + difference 0 0) (sourceB122 + difference 0 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA122 + difference 0 0) (sourceB122 + difference 0 0) sourceC122) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA122 + difference 0 1) (sourceB122 + difference 1 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA122 + difference 0 1) (sourceB122 + difference 1 0) sourceC122) = raw4522 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4522; decide +kernel
    rw [ha]
    exact (canonical4522 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA122 + difference 0 2) (sourceB122 + difference 2 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA122 + difference 0 2) (sourceB122 + difference 2 0) sourceC122) = raw4523 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4523; decide +kernel
    rw [ha]
    exact (canonical4523 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA122 + difference 0 3) (sourceB122 + difference 3 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA122 + difference 0 3) (sourceB122 + difference 3 0) sourceC122) = raw4524 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4524; decide +kernel
    rw [ha]
    exact (canonical4524 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA122 + difference 0 4) (sourceB122 + difference 4 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA122 + difference 0 4) (sourceB122 + difference 4 0) sourceC122) = raw4525 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4525; decide +kernel
    rw [ha]
    exact (canonical4525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA122 + difference 0 5) (sourceB122 + difference 5 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA122 + difference 0 5) (sourceB122 + difference 5 0) sourceC122) = raw4526 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4526; decide +kernel
    rw [ha]
    exact (canonical4526 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA122 + sourceB122) sourceC122) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA122 + sourceB122) sourceC122) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA122 sourceB122 sourceC122 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA122 sourceB122 sourceC122
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm122, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm123 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA123 + difference 0 0) (sourceB123 + difference 0 0) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA123 + difference 0 0) (sourceB123 + difference 0 0) sourceC123) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA123 + difference 1 0) (sourceB123 + difference 0 1) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA123 + difference 1 0) (sourceB123 + difference 0 1) sourceC123) = raw4528 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4528; decide +kernel
    rw [ha]
    exact (canonical4528 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA123 + difference 2 0) (sourceB123 + difference 0 2) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA123 + difference 2 0) (sourceB123 + difference 0 2) sourceC123) = raw4529 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4529; decide +kernel
    rw [ha]
    exact (canonical4529 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA123 + difference 3 0) (sourceB123 + difference 0 3) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA123 + difference 3 0) (sourceB123 + difference 0 3) sourceC123) = raw4530 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4530; decide +kernel
    rw [ha]
    exact (canonical4530 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA123 + difference 4 0) (sourceB123 + difference 0 4) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1438) := by
    have ha : (tripleCharges (sourceA123 + difference 4 0) (sourceB123 + difference 0 4) sourceC123) = raw4531 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4531; decide +kernel
    rw [ha]
    exact (canonical4531 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA123 + difference 5 0) (sourceB123 + difference 0 5) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA123 + difference 5 0) (sourceB123 + difference 0 5) sourceC123) = raw4532 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4532; decide +kernel
    rw [ha]
    exact (canonical4532 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA123 + sourceB123) sourceC123) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA123 + sourceB123) sourceC123) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA123 sourceB123 sourceC123 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA123 sourceB123 sourceC123
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm123, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm124 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA124 + difference 1 0) (sourceB124 + difference 0 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA124 + difference 1 0) (sourceB124 + difference 0 1) sourceC124) = raw4528 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4528; decide +kernel
    rw [ha]
    exact (canonical4528 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA124 + difference 1 1) (sourceB124 + difference 1 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA124 + difference 1 1) (sourceB124 + difference 1 1) sourceC124) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA124 + difference 1 2) (sourceB124 + difference 2 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA124 + difference 1 2) (sourceB124 + difference 2 1) sourceC124) = raw4533 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4533; decide +kernel
    rw [ha]
    exact (canonical4533 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA124 + difference 1 3) (sourceB124 + difference 3 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA124 + difference 1 3) (sourceB124 + difference 3 1) sourceC124) = raw4534 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4534; decide +kernel
    rw [ha]
    exact (canonical4534 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA124 + difference 1 4) (sourceB124 + difference 4 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA124 + difference 1 4) (sourceB124 + difference 4 1) sourceC124) = raw4535 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4535; decide +kernel
    rw [ha]
    exact (canonical4535 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA124 + difference 1 5) (sourceB124 + difference 5 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA124 + difference 1 5) (sourceB124 + difference 5 1) sourceC124) = raw4536 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4536; decide +kernel
    rw [ha]
    exact (canonical4536 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA124 + sourceB124) sourceC124) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA124 + sourceB124) sourceC124) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA124 sourceB124 sourceC124 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA124 sourceB124 sourceC124
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm124, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm125 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA125 + difference 0 1) (sourceB125 + difference 1 0) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA125 + difference 0 1) (sourceB125 + difference 1 0) sourceC125) = raw4522 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4522; decide +kernel
    rw [ha]
    exact (canonical4522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA125 + difference 1 1) (sourceB125 + difference 1 1) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA125 + difference 1 1) (sourceB125 + difference 1 1) sourceC125) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA125 + difference 2 1) (sourceB125 + difference 1 2) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA125 + difference 2 1) (sourceB125 + difference 1 2) sourceC125) = raw4537 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4537; decide +kernel
    rw [ha]
    exact (canonical4537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA125 + difference 3 1) (sourceB125 + difference 1 3) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA125 + difference 3 1) (sourceB125 + difference 1 3) sourceC125) = raw4538 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4538; decide +kernel
    rw [ha]
    exact (canonical4538 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA125 + difference 4 1) (sourceB125 + difference 1 4) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA125 + difference 4 1) (sourceB125 + difference 1 4) sourceC125) = raw4539 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4539; decide +kernel
    rw [ha]
    exact (canonical4539 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA125 + difference 5 1) (sourceB125 + difference 1 5) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA125 + difference 5 1) (sourceB125 + difference 1 5) sourceC125) = raw4540 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4540; decide +kernel
    rw [ha]
    exact (canonical4540 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA125 + sourceB125) sourceC125) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA125 + sourceB125) sourceC125) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA125 sourceB125 sourceC125 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA125 sourceB125 sourceC125
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm125, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm126 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA126 + difference 4 0) (sourceB126 + difference 0 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1438) := by
    have ha : (tripleCharges (sourceA126 + difference 4 0) (sourceB126 + difference 0 4) sourceC126) = raw4531 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4531; decide +kernel
    rw [ha]
    exact (canonical4531 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA126 + difference 4 1) (sourceB126 + difference 1 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA126 + difference 4 1) (sourceB126 + difference 1 4) sourceC126) = raw4539 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4539; decide +kernel
    rw [ha]
    exact (canonical4539 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA126 + difference 4 2) (sourceB126 + difference 2 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA126 + difference 4 2) (sourceB126 + difference 2 4) sourceC126) = raw4541 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4541; decide +kernel
    rw [ha]
    exact (canonical4541 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA126 + difference 4 3) (sourceB126 + difference 3 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA126 + difference 4 3) (sourceB126 + difference 3 4) sourceC126) = raw4542 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4542; decide +kernel
    rw [ha]
    exact (canonical4542 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA126 + difference 4 4) (sourceB126 + difference 4 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA126 + difference 4 4) (sourceB126 + difference 4 4) sourceC126) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA126 + difference 4 5) (sourceB126 + difference 5 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA126 + difference 4 5) (sourceB126 + difference 5 4) sourceC126) = raw4543 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4543; decide +kernel
    rw [ha]
    exact (canonical4543 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA126 + sourceB126) sourceC126) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA126 + sourceB126) sourceC126) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA126 sourceB126 sourceC126 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA126 sourceB126 sourceC126
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm126, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm127 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA127 + difference 0 4) (sourceB127 + difference 4 0) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA127 + difference 0 4) (sourceB127 + difference 4 0) sourceC127) = raw4525 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4525; decide +kernel
    rw [ha]
    exact (canonical4525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA127 + difference 1 4) (sourceB127 + difference 4 1) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA127 + difference 1 4) (sourceB127 + difference 4 1) sourceC127) = raw4535 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4535; decide +kernel
    rw [ha]
    exact (canonical4535 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA127 + difference 2 4) (sourceB127 + difference 4 2) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA127 + difference 2 4) (sourceB127 + difference 4 2) sourceC127) = raw4544 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4544; decide +kernel
    rw [ha]
    exact (canonical4544 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA127 + difference 3 4) (sourceB127 + difference 4 3) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA127 + difference 3 4) (sourceB127 + difference 4 3) sourceC127) = raw4545 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4545; decide +kernel
    rw [ha]
    exact (canonical4545 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA127 + difference 4 4) (sourceB127 + difference 4 4) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA127 + difference 4 4) (sourceB127 + difference 4 4) sourceC127) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA127 + difference 5 4) (sourceB127 + difference 4 5) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA127 + difference 5 4) (sourceB127 + difference 4 5) sourceC127) = raw4546 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4546; decide +kernel
    rw [ha]
    exact (canonical4546 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA127 + sourceB127) sourceC127) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA127 + sourceB127) sourceC127) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA127 sourceB127 sourceC127 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA127 sourceB127 sourceC127
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm127, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources4
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm128 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA128 + difference 5 0) (sourceB128 + difference 0 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA128 + difference 5 0) (sourceB128 + difference 0 5) sourceC128) = raw4532 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4532; decide +kernel
    rw [ha]
    exact (canonical4532 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA128 + difference 5 1) (sourceB128 + difference 1 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA128 + difference 5 1) (sourceB128 + difference 1 5) sourceC128) = raw4540 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4540; decide +kernel
    rw [ha]
    exact (canonical4540 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA128 + difference 5 2) (sourceB128 + difference 2 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA128 + difference 5 2) (sourceB128 + difference 2 5) sourceC128) = raw4547 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4547; decide +kernel
    rw [ha]
    exact (canonical4547 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA128 + difference 5 3) (sourceB128 + difference 3 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA128 + difference 5 3) (sourceB128 + difference 3 5) sourceC128) = raw4548 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4548; decide +kernel
    rw [ha]
    exact (canonical4548 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA128 + difference 5 4) (sourceB128 + difference 4 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA128 + difference 5 4) (sourceB128 + difference 4 5) sourceC128) = raw4546 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4546; decide +kernel
    rw [ha]
    exact (canonical4546 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA128 + difference 5 5) (sourceB128 + difference 5 5) sourceC128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA128 + difference 5 5) (sourceB128 + difference 5 5) sourceC128) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA128 sourceB128 sourceC128 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA128 + sourceB128) sourceC128) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA128 + sourceB128) sourceC128) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA128 sourceB128 sourceC128 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA128 sourceB128 sourceC128
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm128, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck96 : Integer.Sparse.reindex keyMap MixedData.row96 = numericRow96 := by decide +kernel

theorem numericCheck96 (x : Master → ℝ) : Integer.Sparse.eval numericRow96 x =
    (1 : ℝ) * reducedSource96 x := by
  norm_num [numericRow96, reducedSource96, Integer.Sparse.eval, Sparse.eval, nodeValue2290, nodeValue2292, nodeValue2294, nodeValue3634, nodeValue4085]

theorem reindexCheck98 : Integer.Sparse.reindex keyMap MixedData.row98 = numericRow98 := by decide +kernel

theorem numericCheck98 (x : Master → ℝ) : Integer.Sparse.eval numericRow98 x =
    (720 : ℝ) * reducedSource98 x := by
  norm_num [numericRow98, reducedSource98, Integer.Sparse.eval, Sparse.eval, nodeValue828, nodeValue832, nodeValue860, nodeValue1190, nodeValue1297, nodeValue1926, nodeValue1951, nodeValue2112, nodeValue2279, nodeValue2294, nodeValue3054, nodeValue3121, nodeValue3916]
  ring

theorem reindexCheck101 : Integer.Sparse.reindex keyMap MixedData.row101 = numericRow101 := by decide +kernel

theorem numericCheck101 (x : Master → ℝ) : Integer.Sparse.eval numericRow101 x =
    (144 : ℝ) * reducedSource101 x := by
  norm_num [numericRow101, reducedSource101, Integer.Sparse.eval, Sparse.eval, nodeValue1729, nodeValue1746, nodeValue1747, nodeValue1756, nodeValue1757, nodeValue2207, nodeValue2230, nodeValue2266, nodeValue2267, nodeValue2293, nodeValue2744, nodeValue2788, nodeValue2789]
  ring

theorem reindexCheck102 : Integer.Sparse.reindex keyMap MixedData.row102 = numericRow102 := by decide +kernel

theorem numericCheck102 (x : Master → ℝ) : Integer.Sparse.eval numericRow102 x =
    (1 : ℝ) * reducedSource102 x := by
  norm_num [numericRow102, reducedSource102, Integer.Sparse.eval, Sparse.eval, nodeValue2278, nodeValue2281, nodeValue2293, nodeValue3633, nodeValue4084]

theorem reindexCheck103 : Integer.Sparse.reindex keyMap MixedData.row103 = numericRow103 := by decide +kernel

theorem numericCheck103 (x : Master → ℝ) : Integer.Sparse.eval numericRow103 x =
    (1 : ℝ) * reducedSource103 x := by
  norm_num [numericRow103, reducedSource103, Integer.Sparse.eval, Sparse.eval, nodeValue1064, nodeValue1369, nodeValue1438, nodeValue2281, nodeValue4084]

theorem reindexCheck104 : Integer.Sparse.reindex keyMap MixedData.row104 = numericRow104 := by decide +kernel

theorem numericCheck104 (x : Master → ℝ) : Integer.Sparse.eval numericRow104 x =
    (1 : ℝ) * reducedSource104 x := by
  norm_num [numericRow104, reducedSource104, Integer.Sparse.eval, Sparse.eval, nodeValue1369, nodeValue2035, nodeValue2062, nodeValue2281, nodeValue3052, nodeValue4084]

theorem reindexCheck105 : Integer.Sparse.reindex keyMap MixedData.row105 = numericRow105 := by decide +kernel

theorem numericCheck105 (x : Master → ℝ) : Integer.Sparse.eval numericRow105 x =
    (1 : ℝ) * reducedSource105 x := by
  norm_num [numericRow105, reducedSource105, Integer.Sparse.eval, Sparse.eval, nodeValue1059, nodeValue2035, nodeValue2134, nodeValue2278, nodeValue2281, nodeValue4084]

theorem reindexCheck106 : Integer.Sparse.reindex keyMap MixedData.row106 = numericRow106 := by decide +kernel

theorem numericCheck106 (x : Master → ℝ) : Integer.Sparse.eval numericRow106 x =
    (1 : ℝ) * reducedSource106 x := by
  norm_num [numericRow106, reducedSource106, Integer.Sparse.eval, Sparse.eval, nodeValue1438, nodeValue2134, nodeValue2281, nodeValue2789, nodeValue4084]

theorem reindexCheck107 : Integer.Sparse.reindex keyMap MixedData.row107 = numericRow107 := by decide +kernel

theorem numericCheck107 (x : Master → ℝ) : Integer.Sparse.eval numericRow107 x =
    (1 : ℝ) * reducedSource107 x := by
  norm_num [numericRow107, reducedSource107, Integer.Sparse.eval, Sparse.eval, nodeValue1091, nodeValue2062, nodeValue2281, nodeValue2293, nodeValue4084]

theorem reindexCheck108 : Integer.Sparse.reindex keyMap MixedData.row108 = numericRow108 := by decide +kernel

theorem numericCheck108 (x : Master → ℝ) : Integer.Sparse.eval numericRow108 x =
    (1 : ℝ) * reducedSource108 x := by
  norm_num [numericRow108, reducedSource108, Integer.Sparse.eval, Sparse.eval, nodeValue1059, nodeValue1064, nodeValue1091, nodeValue2281, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero96 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource96 (mixedVector B) = 0 := by
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h3634 : mixedVector B (Sum.inr 3634) = Sparse.eval nodeValue3634 (mixedVector B) := by
    change mixedMoment B node3634 node3634Labels = _
    exact sound3634 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm116, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2290, h2292, h2294, h3634, h4085, reducedSource96] using sourceEq116 B hB

theorem rowSound96 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row96 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck96, numericCheck96, reducedZero96 B hB hF, mul_zero]

theorem reducedZero98 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource98 (mixedVector B) = 0 := by
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h832 : mixedVector B (Sum.inr 832) = Sparse.eval nodeValue832 (mixedVector B) := by
    change mixedMoment B node832 node832Labels = _
    exact sound832 B hB hF
  have h860 : mixedVector B (Sum.inr 860) = Sparse.eval nodeValue860 (mixedVector B) := by
    change mixedMoment B node860 node860Labels = _
    exact sound860 B hB hF
  have h1190 : mixedVector B (Sum.inr 1190) = Sparse.eval nodeValue1190 (mixedVector B) := by
    change mixedMoment B node1190 node1190Labels = _
    exact sound1190 B hB hF
  have h1297 : mixedVector B (Sum.inr 1297) = Sparse.eval nodeValue1297 (mixedVector B) := by
    change mixedMoment B node1297 node1297Labels = _
    exact sound1297 B hB hF
  have h1926 : mixedVector B (Sum.inr 1926) = Sparse.eval nodeValue1926 (mixedVector B) := by
    change mixedMoment B node1926 node1926Labels = _
    exact sound1926 B hB hF
  have h1951 : mixedVector B (Sum.inr 1951) = Sparse.eval nodeValue1951 (mixedVector B) := by
    change mixedMoment B node1951 node1951Labels = _
    exact sound1951 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3121 : mixedVector B (Sum.inr 3121) = Sparse.eval nodeValue3121 (mixedVector B) := by
    change mixedMoment B node3121 node3121Labels = _
    exact sound3121 B hB hF
  have h3916 : mixedVector B (Sum.inr 3916) = Sparse.eval nodeValue3916 (mixedVector B) := by
    change mixedMoment B node3916 node3916Labels = _
    exact sound3916 B hB hF
  simpa only [sourceForm118, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h828, h832, h860, h1190, h1297, h1926, h1951, h2112, h2279, h2294, h3054, h3121, h3916, reducedSource98] using sourceEq118 B hB

theorem rowSound98 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row98 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck98, numericCheck98, reducedZero98 B hB hF, mul_zero]

theorem reducedZero101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource101 (mixedVector B) = 0 := by
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h1757 : mixedVector B (Sum.inr 1757) = Sparse.eval nodeValue1757 (mixedVector B) := by
    change mixedMoment B node1757 node1757Labels = _
    exact sound1757 B hB hF
  have h2207 : mixedVector B (Sum.inr 2207) = Sparse.eval nodeValue2207 (mixedVector B) := by
    change mixedMoment B node2207 node2207Labels = _
    exact sound2207 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2267 : mixedVector B (Sum.inr 2267) = Sparse.eval nodeValue2267 (mixedVector B) := by
    change mixedMoment B node2267 node2267Labels = _
    exact sound2267 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2788 : mixedVector B (Sum.inr 2788) = Sparse.eval nodeValue2788 (mixedVector B) := by
    change mixedMoment B node2788 node2788Labels = _
    exact sound2788 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  simpa only [sourceForm121, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1729, h1746, h1747, h1756, h1757, h2207, h2230, h2266, h2267, h2293, h2744, h2788, h2789, reducedSource101] using sourceEq121 B hB

theorem rowSound101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row101 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck101, numericCheck101, reducedZero101 B hB hF, mul_zero]

theorem reducedZero102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource102 (mixedVector B) = 0 := by
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm122, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2278, h2281, h2293, h3633, h4084, reducedSource102] using sourceEq122 B hB

theorem rowSound102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row102 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck102, numericCheck102, reducedZero102 B hB hF, mul_zero]

theorem reducedZero103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource103 (mixedVector B) = 0 := by
  have h1064 : mixedVector B (Sum.inr 1064) = Sparse.eval nodeValue1064 (mixedVector B) := by
    change mixedMoment B node1064 node1064Labels = _
    exact sound1064 B hB hF
  have h1369 : mixedVector B (Sum.inr 1369) = Sparse.eval nodeValue1369 (mixedVector B) := by
    change mixedMoment B node1369 node1369Labels = _
    exact sound1369 B hB hF
  have h1438 : mixedVector B (Sum.inr 1438) = Sparse.eval nodeValue1438 (mixedVector B) := by
    change mixedMoment B node1438 node1438Labels = _
    exact sound1438 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm123, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1064, h1369, h1438, h2281, h4084, reducedSource103] using sourceEq123 B hB

theorem rowSound103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row103 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck103, numericCheck103, reducedZero103 B hB hF, mul_zero]

theorem reducedZero104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource104 (mixedVector B) = 0 := by
  have h1369 : mixedVector B (Sum.inr 1369) = Sparse.eval nodeValue1369 (mixedVector B) := by
    change mixedMoment B node1369 node1369Labels = _
    exact sound1369 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm124, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1369, h2035, h2062, h2281, h3052, h4084, reducedSource104] using sourceEq124 B hB

theorem rowSound104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row104 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck104, numericCheck104, reducedZero104 B hB hF, mul_zero]

theorem reducedZero105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource105 (mixedVector B) = 0 := by
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm125, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1059, h2035, h2134, h2278, h2281, h4084, reducedSource105] using sourceEq125 B hB

theorem rowSound105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row105 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck105, numericCheck105, reducedZero105 B hB hF, mul_zero]

theorem reducedZero106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource106 (mixedVector B) = 0 := by
  have h1438 : mixedVector B (Sum.inr 1438) = Sparse.eval nodeValue1438 (mixedVector B) := by
    change mixedMoment B node1438 node1438Labels = _
    exact sound1438 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm126, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1438, h2134, h2281, h2789, h4084, reducedSource106] using sourceEq126 B hB

theorem rowSound106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row106 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck106, numericCheck106, reducedZero106 B hB hF, mul_zero]

theorem reducedZero107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource107 (mixedVector B) = 0 := by
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm127, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1091, h2062, h2281, h2293, h4084, reducedSource107] using sourceEq127 B hB

theorem rowSound107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row107 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck107, numericCheck107, reducedZero107 B hB hF, mul_zero]

theorem reducedZero108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource108 (mixedVector B) = 0 := by
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h1064 : mixedVector B (Sum.inr 1064) = Sparse.eval nodeValue1064 (mixedVector B) := by
    change mixedMoment B node1064 node1064Labels = _
    exact sound1064 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h2281 : mixedVector B (Sum.inr 2281) = Sparse.eval nodeValue2281 (mixedVector B) := by
    change mixedMoment B node2281 node2281Labels = _
    exact sound2281 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm128, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1059, h1064, h1091, h2281, h4084, reducedSource108] using sourceEq128 B hB

theorem rowSound108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row108 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck108, numericCheck108, reducedZero108 B hB hF, mul_zero]

theorem sourceRowsAt96 : MixedData.sourceRows (96 : Fin 2425) =
    MixedData.row96 := by decide +kernel

theorem sourceRowsAt97 : MixedData.sourceRows (97 : Fin 2425) =
    MixedData.row97 := by decide +kernel

theorem sourceRowsAt98 : MixedData.sourceRows (98 : Fin 2425) =
    MixedData.row98 := by decide +kernel

theorem sourceRowsAt99 : MixedData.sourceRows (99 : Fin 2425) =
    MixedData.row99 := by decide +kernel

theorem sourceRowsAt100 : MixedData.sourceRows (100 : Fin 2425) =
    MixedData.row100 := by decide +kernel

theorem sourceRowsAt101 : MixedData.sourceRows (101 : Fin 2425) =
    MixedData.row101 := by decide +kernel

theorem sourceRowsAt102 : MixedData.sourceRows (102 : Fin 2425) =
    MixedData.row102 := by decide +kernel

theorem sourceRowsAt103 : MixedData.sourceRows (103 : Fin 2425) =
    MixedData.row103 := by decide +kernel

theorem sourceRowsAt104 : MixedData.sourceRows (104 : Fin 2425) =
    MixedData.row104 := by decide +kernel

theorem sourceRowsAt105 : MixedData.sourceRows (105 : Fin 2425) =
    MixedData.row105 := by decide +kernel

theorem sourceRowsAt106 : MixedData.sourceRows (106 : Fin 2425) =
    MixedData.row106 := by decide +kernel

theorem sourceRowsAt107 : MixedData.sourceRows (107 : Fin 2425) =
    MixedData.row107 := by decide +kernel

theorem sourceRowsAt108 : MixedData.sourceRows (108 : Fin 2425) =
    MixedData.row108 := by decide +kernel

theorem sourceRowsAt109 : MixedData.sourceRows (109 : Fin 2425) =
    MixedData.row109 := by decide +kernel

theorem sourceRowsAt110 : MixedData.sourceRows (110 : Fin 2425) =
    MixedData.row110 := by decide +kernel

theorem sourceRowsAt111 : MixedData.sourceRows (111 : Fin 2425) =
    MixedData.row111 := by decide +kernel

theorem chunkSound6_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 6) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 96 ∨ k.val = 97 ∨ k.val = 98 ∨ k.val = 99 ∨ k.val = 100 ∨ k.val = 101 ∨ k.val = 102 ∨ k.val = 103 ∨ k.val = 104 ∨ k.val = 105 ∨ k.val = 106 ∨ k.val = 107 ∨ k.val = 108 ∨ k.val = 109 ∨ k.val = 110 ∨ k.val = 111 := by omega
  rcases heq with h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111
  · have he : k = (96 : Fin 2425) := Fin.ext h96
    subst k
    rw [sourceRowsAt96]
    exact rowSound96 B hB hF
  · have he : k = (97 : Fin 2425) := Fin.ext h97
    subst k
    rw [sourceRowsAt97]
    exact rowSound97_e B hB hF
  · have he : k = (98 : Fin 2425) := Fin.ext h98
    subst k
    rw [sourceRowsAt98]
    exact rowSound98 B hB hF
  · have he : k = (99 : Fin 2425) := Fin.ext h99
    subst k
    rw [sourceRowsAt99]
    exact rowSound99_e B hB hF
  · have he : k = (100 : Fin 2425) := Fin.ext h100
    subst k
    rw [sourceRowsAt100]
    exact rowSound100_e B hB hF
  · have he : k = (101 : Fin 2425) := Fin.ext h101
    subst k
    rw [sourceRowsAt101]
    exact rowSound101 B hB hF
  · have he : k = (102 : Fin 2425) := Fin.ext h102
    subst k
    rw [sourceRowsAt102]
    exact rowSound102 B hB hF
  · have he : k = (103 : Fin 2425) := Fin.ext h103
    subst k
    rw [sourceRowsAt103]
    exact rowSound103 B hB hF
  · have he : k = (104 : Fin 2425) := Fin.ext h104
    subst k
    rw [sourceRowsAt104]
    exact rowSound104 B hB hF
  · have he : k = (105 : Fin 2425) := Fin.ext h105
    subst k
    rw [sourceRowsAt105]
    exact rowSound105 B hB hF
  · have he : k = (106 : Fin 2425) := Fin.ext h106
    subst k
    rw [sourceRowsAt106]
    exact rowSound106 B hB hF
  · have he : k = (107 : Fin 2425) := Fin.ext h107
    subst k
    rw [sourceRowsAt107]
    exact rowSound107 B hB hF
  · have he : k = (108 : Fin 2425) := Fin.ext h108
    subst k
    rw [sourceRowsAt108]
    exact rowSound108 B hB hF
  · have he : k = (109 : Fin 2425) := Fin.ext h109
    subst k
    rw [sourceRowsAt109]
    exact rowSound109_e B hB hF
  · have he : k = (110 : Fin 2425) := Fin.ext h110
    subst k
    rw [sourceRowsAt110]
    exact rowSound110_e B hB hF
  · have he : k = (111 : Fin 2425) := Fin.ext h111
    subst k
    rw [sourceRowsAt111]
    exact rowSound111_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e_oai
