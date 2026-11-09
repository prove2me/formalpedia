-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:22:41.972114+00:00
-- url     : https://prove2.me/submissions/f113c8b4-6229-4657-8d05-7c02c11f3fe9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound864_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound865_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound866_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound867_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound868_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound872_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound873_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound877_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound878_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14797 raw14797Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14797 raw14797Labels = mixedMoment B raw14797step0 raw14797step0Labels := by
      have hz : ∀ j, raw14797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14797step0 = (fun i j => raw14797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14797step0 raw14797; decide +kernel
      have hl : raw14797step0Labels = raw14797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797 raw14797Labels permutation434 hz
    mixedMoment B raw14797step0 raw14797step0Labels = mixedMoment B raw14797step1 raw14797step1Labels := by
      have hz : ∀ j, raw14797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14797step1 = (fun i j => raw14797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14797step1 raw14797step0; decide +kernel
      have hl : raw14797step1Labels = raw14797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797step0 raw14797step0Labels permutation80 hz
    mixedMoment B raw14797step1 raw14797step1Labels = mixedMoment B raw14797step2 raw14797step2Labels := by
      have ha : raw14797step2 = (fun i j => raw14797step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14797step2 raw14797step1; decide +kernel
      have hl : raw14797step2Labels = raw14797step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14797step1 raw14797step1Labels permutation31 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

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

theorem canonical15739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15739 raw15739Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw15739 raw15739Labels = mixedMoment B raw15739step0 raw15739step0Labels := by
      have hz : ∀ j, raw15739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15739step0 = (fun i j => raw15739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15739step0 raw15739; decide +kernel
      have hl : raw15739step0Labels = raw15739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15739 raw15739Labels permutation346 hz
    mixedMoment B raw15739step0 raw15739step0Labels = mixedMoment B raw15739step1 raw15739step1Labels := by
      have ha : raw15739step1 = (fun i j => raw15739step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15739step1 raw15739step0; decide +kernel
      have hl : raw15739step1Labels = raw15739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15739step0 raw15739step0Labels permutation127 permutation2
    _ = mixedMoment B node3961 node3961Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15744 raw15744Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15744 raw15744Labels = mixedMoment B raw15744step0 raw15744step0Labels := by
      have hz : ∀ j, raw15744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15744step0 = (fun i j => raw15744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15744step0 raw15744; decide +kernel
      have hl : raw15744step0Labels = raw15744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15744 raw15744Labels permutation346 hz
    mixedMoment B raw15744step0 raw15744step0Labels = mixedMoment B raw15744step1 raw15744step1Labels := by
      have ha : raw15744step1 = (fun i j => raw15744step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15744step1 raw15744step0; decide +kernel
      have hl : raw15744step1Labels = raw15744step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15744step0 raw15744step0Labels permutation44 permutation4
    mixedMoment B raw15744step1 raw15744step1Labels = mixedMoment B raw15744step2 raw15744step2Labels := by
      have ha : raw15744step2 = -raw15744step1 := by apply Matrix.ext; change ∀ i j, raw15744step2 i j = -(raw15744step1 i j); unfold raw15744step2 raw15744step1; decide +kernel
      have hl : raw15744step2Labels = raw15744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16210 raw16210Labels = mixedMoment B node3944 node3944Labels := by
  calc
    mixedMoment B raw16210 raw16210Labels = mixedMoment B raw16210step0 raw16210step0Labels := by
      have ha : raw16210step0 = (fun i j => raw16210 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16210step0 raw16210; decide +kernel
      have hl : raw16210step0Labels = raw16210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16210 raw16210Labels permutation583 permutation2
    _ = mixedMoment B node3944 node3944Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16427 raw16427Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16427 raw16427Labels = mixedMoment B raw16427step0 raw16427step0Labels := by
      have hz : ∀ j, raw16427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16427step0 = (fun i j => raw16427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16427step0 raw16427; decide +kernel
      have hl : raw16427step0Labels = raw16427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16427 raw16427Labels permutation346 hz
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical16428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16428 raw16428Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw16428 raw16428Labels = mixedMoment B raw16428step0 raw16428step0Labels := by
      have hz : ∀ j, raw16428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16428step0 = (fun i j => raw16428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16428step0 raw16428; decide +kernel
      have hl : raw16428step0Labels = raw16428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16428 raw16428Labels permutation346 hz
    mixedMoment B raw16428step0 raw16428step0Labels = mixedMoment B raw16428step1 raw16428step1Labels := by
      have ha : raw16428step1 = (fun i j => raw16428step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16428step1 raw16428step0; decide +kernel
      have hl : raw16428step1Labels = raw16428step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16428step0 raw16428step0Labels permutation66 permutation4
    mixedMoment B raw16428step1 raw16428step1Labels = mixedMoment B raw16428step2 raw16428step2Labels := by
      have ha : raw16428step2 = -raw16428step1 := by apply Matrix.ext; change ∀ i j, raw16428step2 i j = -(raw16428step1 i j); unfold raw16428step2 raw16428step1; decide +kernel
      have hl : raw16428step2Labels = raw16428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2955 node2955Labels := by rfl

theorem canonical16429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16429 raw16429Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw16429 raw16429Labels = mixedMoment B raw16429step0 raw16429step0Labels := by
      have ha : raw16429step0 = (fun i j => raw16429 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16429step0 raw16429; decide +kernel
      have hl : raw16429step0Labels = raw16429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16429 raw16429Labels permutation528 permutation4
    _ = mixedMoment B node3947 node3947Labels := by rfl

theorem canonical16430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16430 raw16430Labels = mixedMoment B node3929 node3929Labels := by
  calc
    mixedMoment B raw16430 raw16430Labels = mixedMoment B raw16430step0 raw16430step0Labels := by
      have hz : ∀ j, raw16430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16430step0 = (fun i j => raw16430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16430step0 raw16430; decide +kernel
      have hl : raw16430step0Labels = raw16430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16430 raw16430Labels permutation346 hz
    mixedMoment B raw16430step0 raw16430step0Labels = mixedMoment B raw16430step1 raw16430step1Labels := by
      have ha : raw16430step1 = (fun i j => raw16430step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16430step1 raw16430step0; decide +kernel
      have hl : raw16430step1Labels = raw16430step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16430step0 raw16430step0Labels permutation66 permutation4
    mixedMoment B raw16430step1 raw16430step1Labels = mixedMoment B raw16430step2 raw16430step2Labels := by
      have ha : raw16430step2 = -raw16430step1 := by apply Matrix.ext; change ∀ i j, raw16430step2 i j = -(raw16430step1 i j); unfold raw16430step2 raw16430step1; decide +kernel
      have hl : raw16430step2Labels = raw16430step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3929 node3929Labels := by rfl

theorem canonical16431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16431 raw16431Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw16431 raw16431Labels = mixedMoment B raw16431step0 raw16431step0Labels := by
      have hz : ∀ j, raw16431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16431step0 = (fun i j => raw16431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16431step0 raw16431; decide +kernel
      have hl : raw16431step0Labels = raw16431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16431 raw16431Labels permutation346 hz
    mixedMoment B raw16431step0 raw16431step0Labels = mixedMoment B raw16431step1 raw16431step1Labels := by
      have ha : raw16431step1 = (fun i j => raw16431step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16431step1 raw16431step0; decide +kernel
      have hl : raw16431step1Labels = raw16431step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16431step0 raw16431step0Labels permutation67 permutation4
    mixedMoment B raw16431step1 raw16431step1Labels = mixedMoment B raw16431step2 raw16431step2Labels := by
      have ha : raw16431step2 = -raw16431step1 := by apply Matrix.ext; change ∀ i j, raw16431step2 i j = -(raw16431step1 i j); unfold raw16431step2 raw16431step1; decide +kernel
      have hl : raw16431step2Labels = raw16431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical16432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16432 raw16432Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw16432 raw16432Labels = mixedMoment B raw16432step0 raw16432step0Labels := by
      have hz : ∀ j, raw16432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16432step0 = (fun i j => raw16432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16432step0 raw16432; decide +kernel
      have hl : raw16432step0Labels = raw16432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16432 raw16432Labels permutation346 hz
    mixedMoment B raw16432step0 raw16432step0Labels = mixedMoment B raw16432step1 raw16432step1Labels := by
      have ha : raw16432step1 = (fun i j => raw16432step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16432step1 raw16432step0; decide +kernel
      have hl : raw16432step1Labels = raw16432step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16432step0 raw16432step0Labels permutation109 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical16433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16433 raw16433Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16433 raw16433Labels = mixedMoment B raw16433step0 raw16433step0Labels := by
      have hz : ∀ j, raw16433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16433step0 = (fun i j => raw16433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16433step0 raw16433; decide +kernel
      have hl : raw16433step0Labels = raw16433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16433 raw16433Labels permutation346 hz
    mixedMoment B raw16433step0 raw16433step0Labels = mixedMoment B raw16433step1 raw16433step1Labels := by
      have ha : raw16433step1 = (fun i j => raw16433step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16433step1 raw16433step0; decide +kernel
      have hl : raw16433step1Labels = raw16433step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16433step0 raw16433step0Labels permutation44 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical16435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16435 raw16435Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw16435 raw16435Labels = mixedMoment B raw16435step0 raw16435step0Labels := by
      have hz : ∀ j, raw16435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16435step0 = (fun i j => raw16435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16435step0 raw16435; decide +kernel
      have hl : raw16435step0Labels = raw16435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16435 raw16435Labels permutation346 hz
    mixedMoment B raw16435step0 raw16435step0Labels = mixedMoment B raw16435step1 raw16435step1Labels := by
      have ha : raw16435step1 = (fun i j => raw16435step0 (permutation63 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16435step1 raw16435step0; decide +kernel
      have hl : raw16435step1Labels = raw16435step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16435step0 raw16435step0Labels permutation63 permutation4
    mixedMoment B raw16435step1 raw16435step1Labels = mixedMoment B raw16435step2 raw16435step2Labels := by
      have ha : raw16435step2 = -raw16435step1 := by apply Matrix.ext; change ∀ i j, raw16435step2 i j = -(raw16435step1 i j); unfold raw16435step2 raw16435step1; decide +kernel
      have hl : raw16435step2Labels = raw16435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3092 node3092Labels := by rfl

theorem canonical16438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16438 raw16438Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw16438 raw16438Labels = mixedMoment B raw16438step0 raw16438step0Labels := by
      have hz : ∀ j, raw16438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16438step0 = (fun i j => raw16438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16438step0 raw16438; decide +kernel
      have hl : raw16438step0Labels = raw16438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16438 raw16438Labels permutation346 hz
    mixedMoment B raw16438step0 raw16438step0Labels = mixedMoment B raw16438step1 raw16438step1Labels := by
      have ha : raw16438step1 = (fun i j => raw16438step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16438step1 raw16438step0; decide +kernel
      have hl : raw16438step1Labels = raw16438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16438step0 raw16438step0Labels permutation34 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

theorem canonical16439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16439 raw16439Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw16439 raw16439Labels = mixedMoment B raw16439step0 raw16439step0Labels := by
      have ha : raw16439step0 = (fun i j => raw16439 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16439step0 raw16439; decide +kernel
      have hl : raw16439step0Labels = raw16439Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16439 raw16439Labels permutation178 permutation2
    _ = mixedMoment B node3827 node3827Labels := by rfl

theorem canonical16440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16440 raw16440Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16440 raw16440Labels = mixedMoment B raw16440step0 raw16440step0Labels := by
      have hz : ∀ j, raw16440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16440step0 = (fun i j => raw16440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16440step0 raw16440; decide +kernel
      have hl : raw16440step0Labels = raw16440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16440 raw16440Labels permutation346 hz
    mixedMoment B raw16440step0 raw16440step0Labels = mixedMoment B raw16440step1 raw16440step1Labels := by
      have ha : raw16440step1 = (fun i j => raw16440step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16440step1 raw16440step0; decide +kernel
      have hl : raw16440step1Labels = raw16440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16440step0 raw16440step0Labels permutation34 permutation2
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical16441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16441 raw16441Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw16441 raw16441Labels = mixedMoment B raw16441step0 raw16441step0Labels := by
      have hz : ∀ j, raw16441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16441step0 = (fun i j => raw16441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16441step0 raw16441; decide +kernel
      have hl : raw16441step0Labels = raw16441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16441 raw16441Labels permutation346 hz
    mixedMoment B raw16441step0 raw16441step0Labels = mixedMoment B raw16441step1 raw16441step1Labels := by
      have ha : raw16441step1 = (fun i j => raw16441step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16441step1 raw16441step0; decide +kernel
      have hl : raw16441step1Labels = raw16441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16441step0 raw16441step0Labels permutation34 permutation2
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical16442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16442 raw16442Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw16442 raw16442Labels = mixedMoment B raw16442step0 raw16442step0Labels := by
      have hz : ∀ j, raw16442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16442step0 = (fun i j => raw16442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16442step0 raw16442; decide +kernel
      have hl : raw16442step0Labels = raw16442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16442 raw16442Labels permutation346 hz
    mixedMoment B raw16442step0 raw16442step0Labels = mixedMoment B raw16442step1 raw16442step1Labels := by
      have ha : raw16442step1 = (fun i j => raw16442step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16442step1 raw16442step0; decide +kernel
      have hl : raw16442step1Labels = raw16442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16442step0 raw16442step0Labels permutation56 permutation2
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical16443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16443 raw16443Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw16443 raw16443Labels = mixedMoment B raw16443step0 raw16443step0Labels := by
      have ha : raw16443step0 = (fun i j => raw16443 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16443step0 raw16443; decide +kernel
      have hl : raw16443step0Labels = raw16443Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16443 raw16443Labels permutation572 permutation7
    mixedMoment B raw16443step0 raw16443step0Labels = mixedMoment B raw16443step1 raw16443step1Labels := by
      have ha : raw16443step1 = raw16443step0 := by apply Matrix.ext; unfold raw16443step1 raw16443step0; decide +kernel
      have hl : raw16443step0Labels = labelEmbedding10 ∘ raw16443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16443step0 raw16443step0Labels raw16443step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

theorem canonical16444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16444 raw16444Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16444 raw16444Labels = mixedMoment B raw16444step0 raw16444step0Labels := by
      have hz : ∀ j, raw16444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16444step0 = (fun i j => raw16444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16444step0 raw16444; decide +kernel
      have hl : raw16444step0Labels = raw16444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16444 raw16444Labels permutation346 hz
    mixedMoment B raw16444step0 raw16444step0Labels = mixedMoment B raw16444step1 raw16444step1Labels := by
      have ha : raw16444step1 = (fun i j => raw16444step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16444step1 raw16444step0; decide +kernel
      have hl : raw16444step1Labels = raw16444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16444step0 raw16444step0Labels permutation123 permutation7
    mixedMoment B raw16444step1 raw16444step1Labels = mixedMoment B raw16444step2 raw16444step2Labels := by
      have ha : raw16444step2 = raw16444step1 := by apply Matrix.ext; unfold raw16444step2 raw16444step1; decide +kernel
      have hl : raw16444step1Labels = labelEmbedding10 ∘ raw16444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16444step1 raw16444step1Labels raw16444step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical16445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16445 raw16445Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16445 raw16445Labels = mixedMoment B raw16445step0 raw16445step0Labels := by
      have hz : ∀ j, raw16445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16445step0 = (fun i j => raw16445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16445step0 raw16445; decide +kernel
      have hl : raw16445step0Labels = raw16445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16445 raw16445Labels permutation346 hz
    mixedMoment B raw16445step0 raw16445step0Labels = mixedMoment B raw16445step1 raw16445step1Labels := by
      have ha : raw16445step1 = (fun i j => raw16445step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16445step1 raw16445step0; decide +kernel
      have hl : raw16445step1Labels = raw16445step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16445step0 raw16445step0Labels permutation109 permutation4
    mixedMoment B raw16445step1 raw16445step1Labels = mixedMoment B raw16445step2 raw16445step2Labels := by
      have ha : raw16445step2 = -raw16445step1 := by apply Matrix.ext; change ∀ i j, raw16445step2 i j = -(raw16445step1 i j); unfold raw16445step2 raw16445step1; decide +kernel
      have hl : raw16445step2Labels = raw16445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16445step2 raw16445step2Labels = mixedMoment B raw16445step3 raw16445step3Labels := by
      have ha : raw16445step3 = raw16445step2 := by apply Matrix.ext; unfold raw16445step3 raw16445step2; decide +kernel
      have hl : raw16445step2Labels = labelEmbedding7 ∘ raw16445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16445step2 raw16445step2Labels raw16445step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical16446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16446 raw16446Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw16446 raw16446Labels = mixedMoment B raw16446step0 raw16446step0Labels := by
      have hz : ∀ j, raw16446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16446step0 = (fun i j => raw16446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16446step0 raw16446; decide +kernel
      have hl : raw16446step0Labels = raw16446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16446 raw16446Labels permutation346 hz
    mixedMoment B raw16446step0 raw16446step0Labels = mixedMoment B raw16446step1 raw16446step1Labels := by
      have ha : raw16446step1 = (fun i j => raw16446step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16446step1 raw16446step0; decide +kernel
      have hl : raw16446step1Labels = raw16446step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16446step0 raw16446step0Labels permutation63 permutation6
    mixedMoment B raw16446step1 raw16446step1Labels = mixedMoment B raw16446step2 raw16446step2Labels := by
      have ha : raw16446step2 = -raw16446step1 := by apply Matrix.ext; change ∀ i j, raw16446step2 i j = -(raw16446step1 i j); unfold raw16446step2 raw16446step1; decide +kernel
      have hl : raw16446step2Labels = raw16446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16446step2 raw16446step2Labels = mixedMoment B raw16446step3 raw16446step3Labels := by
      have ha : raw16446step3 = raw16446step2 := by apply Matrix.ext; unfold raw16446step3 raw16446step2; decide +kernel
      have hl : raw16446step2Labels = labelEmbedding9 ∘ raw16446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16446step2 raw16446step2Labels raw16446step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical16447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16447 raw16447Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw16447 raw16447Labels = mixedMoment B raw16447step0 raw16447step0Labels := by
      have hz : ∀ j, raw16447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16447step0 = (fun i j => raw16447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16447step0 raw16447; decide +kernel
      have hl : raw16447step0Labels = raw16447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16447 raw16447Labels permutation346 hz
    mixedMoment B raw16447step0 raw16447step0Labels = mixedMoment B raw16447step1 raw16447step1Labels := by
      have ha : raw16447step1 = (fun i j => raw16447step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16447step1 raw16447step0; decide +kernel
      have hl : raw16447step1Labels = raw16447step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16447step0 raw16447step0Labels permutation47 permutation5
    mixedMoment B raw16447step1 raw16447step1Labels = mixedMoment B raw16447step2 raw16447step2Labels := by
      have ha : raw16447step2 = -raw16447step1 := by apply Matrix.ext; change ∀ i j, raw16447step2 i j = -(raw16447step1 i j); unfold raw16447step2 raw16447step1; decide +kernel
      have hl : raw16447step2Labels = raw16447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16447step2 raw16447step2Labels = mixedMoment B raw16447step3 raw16447step3Labels := by
      have ha : raw16447step3 = raw16447step2 := by apply Matrix.ext; unfold raw16447step3 raw16447step2; decide +kernel
      have hl : raw16447step2Labels = labelEmbedding8 ∘ raw16447step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16447step2 raw16447step2Labels raw16447step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

theorem canonical16448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16448 raw16448Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw16448 raw16448Labels = mixedMoment B raw16448step0 raw16448step0Labels := by
      have ha : raw16448step0 = (fun i j => raw16448 (permutation319 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16448step0 raw16448; decide +kernel
      have hl : raw16448step0Labels = raw16448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16448 raw16448Labels permutation319 permutation4
    mixedMoment B raw16448step0 raw16448step0Labels = mixedMoment B raw16448step1 raw16448step1Labels := by
      have ha : raw16448step1 = raw16448step0 := by apply Matrix.ext; unfold raw16448step1 raw16448step0; decide +kernel
      have hl : raw16448step0Labels = labelEmbedding7 ∘ raw16448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16448step0 raw16448step0Labels raw16448step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5402 node5402Labels := by rfl

theorem canonical16449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16449 raw16449Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw16449 raw16449Labels = mixedMoment B raw16449step0 raw16449step0Labels := by
      have hz : ∀ j, raw16449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16449step0 = (fun i j => raw16449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16449step0 raw16449; decide +kernel
      have hl : raw16449step0Labels = raw16449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16449 raw16449Labels permutation346 hz
    mixedMoment B raw16449step0 raw16449step0Labels = mixedMoment B raw16449step1 raw16449step1Labels := by
      have ha : raw16449step1 = (fun i j => raw16449step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16449step1 raw16449step0; decide +kernel
      have hl : raw16449step1Labels = raw16449step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16449step0 raw16449step0Labels permutation38 permutation3
    mixedMoment B raw16449step1 raw16449step1Labels = mixedMoment B raw16449step2 raw16449step2Labels := by
      have ha : raw16449step2 = raw16449step1 := by apply Matrix.ext; unfold raw16449step2 raw16449step1; decide +kernel
      have hl : raw16449step1Labels = labelEmbedding6 ∘ raw16449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16449step1 raw16449step1Labels raw16449step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical16450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16450 raw16450Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw16450 raw16450Labels = mixedMoment B raw16450step0 raw16450step0Labels := by
      have hz : ∀ j, raw16450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16450step0 = (fun i j => raw16450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16450step0 raw16450; decide +kernel
      have hl : raw16450step0Labels = raw16450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16450 raw16450Labels permutation346 hz
    mixedMoment B raw16450step0 raw16450step0Labels = mixedMoment B raw16450step1 raw16450step1Labels := by
      have ha : raw16450step1 = (fun i j => raw16450step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16450step1 raw16450step0; decide +kernel
      have hl : raw16450step1Labels = raw16450step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16450step0 raw16450step0Labels permutation109 permutation4
    mixedMoment B raw16450step1 raw16450step1Labels = mixedMoment B raw16450step2 raw16450step2Labels := by
      have ha : raw16450step2 = -raw16450step1 := by apply Matrix.ext; change ∀ i j, raw16450step2 i j = -(raw16450step1 i j); unfold raw16450step2 raw16450step1; decide +kernel
      have hl : raw16450step2Labels = raw16450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16450step2 raw16450step2Labels = mixedMoment B raw16450step3 raw16450step3Labels := by
      have ha : raw16450step3 = raw16450step2 := by apply Matrix.ext; unfold raw16450step3 raw16450step2; decide +kernel
      have hl : raw16450step2Labels = labelEmbedding7 ∘ raw16450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16450step2 raw16450step2Labels raw16450step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical16451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16451 raw16451Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16451 raw16451Labels = mixedMoment B raw16451step0 raw16451step0Labels := by
      have hz : ∀ j, raw16451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16451step0 = (fun i j => raw16451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16451step0 raw16451; decide +kernel
      have hl : raw16451step0Labels = raw16451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16451 raw16451Labels permutation346 hz
    mixedMoment B raw16451step0 raw16451step0Labels = mixedMoment B raw16451step1 raw16451step1Labels := by
      have ha : raw16451step1 = (fun i j => raw16451step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16451step1 raw16451step0; decide +kernel
      have hl : raw16451step1Labels = raw16451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16451step0 raw16451step0Labels permutation67 permutation4
    mixedMoment B raw16451step1 raw16451step1Labels = mixedMoment B raw16451step2 raw16451step2Labels := by
      have ha : raw16451step2 = raw16451step1 := by apply Matrix.ext; unfold raw16451step2 raw16451step1; decide +kernel
      have hl : raw16451step1Labels = labelEmbedding7 ∘ raw16451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16451step1 raw16451step1Labels raw16451step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical16452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16452 raw16452Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw16452 raw16452Labels = mixedMoment B raw16452step0 raw16452step0Labels := by
      have ha : raw16452step0 = (fun i j => raw16452 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16452step0 raw16452; decide +kernel
      have hl : raw16452step0Labels = raw16452Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16452 raw16452Labels permutation160 permutation3
    mixedMoment B raw16452step0 raw16452step0Labels = mixedMoment B raw16452step1 raw16452step1Labels := by
      have ha : raw16452step1 = raw16452step0 := by apply Matrix.ext; unfold raw16452step1 raw16452step0; decide +kernel
      have hl : raw16452step0Labels = labelEmbedding6 ∘ raw16452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16452step0 raw16452step0Labels raw16452step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

theorem canonical16453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16453 raw16453Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw16453 raw16453Labels = mixedMoment B raw16453step0 raw16453step0Labels := by
      have ha : raw16453step0 = (fun i j => raw16453 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16453step0 raw16453; decide +kernel
      have hl : raw16453step0Labels = raw16453Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16453 raw16453Labels permutation271 permutation2
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical16454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16454 raw16454Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw16454 raw16454Labels = mixedMoment B raw16454step0 raw16454step0Labels := by
      have ha : raw16454step0 = (fun i j => raw16454 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16454step0 raw16454; decide +kernel
      have hl : raw16454step0Labels = raw16454Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16454 raw16454Labels permutation202 permutation3
    mixedMoment B raw16454step0 raw16454step0Labels = mixedMoment B raw16454step1 raw16454step1Labels := by
      have ha : raw16454step1 = raw16454step0 := by apply Matrix.ext; unfold raw16454step1 raw16454step0; decide +kernel
      have hl : raw16454step0Labels = labelEmbedding6 ∘ raw16454step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16454step0 raw16454step0Labels raw16454step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical16455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16455 raw16455Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw16455 raw16455Labels = mixedMoment B raw16455step0 raw16455step0Labels := by
      have ha : raw16455step0 = (fun i j => raw16455 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16455step0 raw16455; decide +kernel
      have hl : raw16455step0Labels = raw16455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16455 raw16455Labels permutation528 permutation4
    mixedMoment B raw16455step0 raw16455step0Labels = mixedMoment B raw16455step1 raw16455step1Labels := by
      have ha : raw16455step1 = -raw16455step0 := by apply Matrix.ext; change ∀ i j, raw16455step1 i j = -(raw16455step0 i j); unfold raw16455step1 raw16455step0; decide +kernel
      have hl : raw16455step1Labels = raw16455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16455step1 raw16455step1Labels = mixedMoment B raw16455step2 raw16455step2Labels := by
      have ha : raw16455step2 = raw16455step1 := by apply Matrix.ext; unfold raw16455step2 raw16455step1; decide +kernel
      have hl : raw16455step1Labels = labelEmbedding7 ∘ raw16455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16455step1 raw16455step1Labels raw16455step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5382 node5382Labels := by rfl

theorem canonical16456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16456 raw16456Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw16456 raw16456Labels = mixedMoment B raw16456step0 raw16456step0Labels := by
      have ha : raw16456step0 = (fun i j => raw16456 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16456step0 raw16456; decide +kernel
      have hl : raw16456step0Labels = raw16456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16456 raw16456Labels permutation161 permutation3
    mixedMoment B raw16456step0 raw16456step0Labels = mixedMoment B raw16456step1 raw16456step1Labels := by
      have ha : raw16456step1 = raw16456step0 := by apply Matrix.ext; unfold raw16456step1 raw16456step0; decide +kernel
      have hl : raw16456step0Labels = labelEmbedding6 ∘ raw16456step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16456step0 raw16456step0Labels raw16456step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical16457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16457 raw16457Labels = mixedMoment B node4861 node4861Labels := by
  calc
    mixedMoment B raw16457 raw16457Labels = mixedMoment B raw16457step0 raw16457step0Labels := by
      have hz : ∀ j, raw16457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16457step0 = (fun i j => raw16457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16457step0 raw16457; decide +kernel
      have hl : raw16457step0Labels = raw16457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16457 raw16457Labels permutation346 hz
    mixedMoment B raw16457step0 raw16457step0Labels = mixedMoment B raw16457step1 raw16457step1Labels := by
      have ha : raw16457step1 = (fun i j => raw16457step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16457step1 raw16457step0; decide +kernel
      have hl : raw16457step1Labels = raw16457step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16457step0 raw16457step0Labels permutation34 permutation3
    mixedMoment B raw16457step1 raw16457step1Labels = mixedMoment B raw16457step2 raw16457step2Labels := by
      have ha : raw16457step2 = raw16457step1 := by apply Matrix.ext; unfold raw16457step2 raw16457step1; decide +kernel
      have hl : raw16457step1Labels = labelEmbedding6 ∘ raw16457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16457step1 raw16457step1Labels raw16457step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4861 node4861Labels := by rfl

theorem canonical16458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16458 raw16458Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw16458 raw16458Labels = mixedMoment B raw16458step0 raw16458step0Labels := by
      have hz : ∀ j, raw16458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16458step0 = (fun i j => raw16458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16458step0 raw16458; decide +kernel
      have hl : raw16458step0Labels = raw16458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16458 raw16458Labels permutation346 hz
    mixedMoment B raw16458step0 raw16458step0Labels = mixedMoment B raw16458step1 raw16458step1Labels := by
      have ha : raw16458step1 = (fun i j => raw16458step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16458step1 raw16458step0; decide +kernel
      have hl : raw16458step1Labels = raw16458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16458step0 raw16458step0Labels permutation56 permutation2
    _ = mixedMoment B node5385 node5385Labels := by rfl

theorem canonical16459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16459 raw16459Labels = mixedMoment B node5399 node5399Labels := by
  calc
    mixedMoment B raw16459 raw16459Labels = mixedMoment B raw16459step0 raw16459step0Labels := by
      have ha : raw16459step0 = (fun i j => raw16459 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16459step0 raw16459; decide +kernel
      have hl : raw16459step0Labels = raw16459Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16459 raw16459Labels permutation178 permutation3
    mixedMoment B raw16459step0 raw16459step0Labels = mixedMoment B raw16459step1 raw16459step1Labels := by
      have ha : raw16459step1 = raw16459step0 := by apply Matrix.ext; unfold raw16459step1 raw16459step0; decide +kernel
      have hl : raw16459step0Labels = labelEmbedding6 ∘ raw16459step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16459step0 raw16459step0Labels raw16459step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5399 node5399Labels := by rfl

theorem canonical16460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16460 raw16460Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw16460 raw16460Labels = mixedMoment B raw16460step0 raw16460step0Labels := by
      have hz : ∀ j, raw16460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16460step0 = (fun i j => raw16460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16460step0 raw16460; decide +kernel
      have hl : raw16460step0Labels = raw16460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16460 raw16460Labels permutation346 hz
    mixedMoment B raw16460step0 raw16460step0Labels = mixedMoment B raw16460step1 raw16460step1Labels := by
      have ha : raw16460step1 = (fun i j => raw16460step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16460step1 raw16460step0; decide +kernel
      have hl : raw16460step1Labels = raw16460step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16460step0 raw16460step0Labels permutation108 permutation4
    mixedMoment B raw16460step1 raw16460step1Labels = mixedMoment B raw16460step2 raw16460step2Labels := by
      have ha : raw16460step2 = -raw16460step1 := by apply Matrix.ext; change ∀ i j, raw16460step2 i j = -(raw16460step1 i j); unfold raw16460step2 raw16460step1; decide +kernel
      have hl : raw16460step2Labels = raw16460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16460step2 raw16460step2Labels = mixedMoment B raw16460step3 raw16460step3Labels := by
      have ha : raw16460step3 = raw16460step2 := by apply Matrix.ext; unfold raw16460step3 raw16460step2; decide +kernel
      have hl : raw16460step2Labels = labelEmbedding7 ∘ raw16460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16460step2 raw16460step2Labels raw16460step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5385 node5385Labels := by rfl

theorem canonical16461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16461 raw16461Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16461 raw16461Labels = mixedMoment B raw16461step0 raw16461step0Labels := by
      have hz : ∀ j, raw16461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16461step0 = (fun i j => raw16461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16461step0 raw16461; decide +kernel
      have hl : raw16461step0Labels = raw16461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16461 raw16461Labels permutation346 hz
    mixedMoment B raw16461step0 raw16461step0Labels = mixedMoment B raw16461step1 raw16461step1Labels := by
      have ha : raw16461step1 = (fun i j => raw16461step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16461step1 raw16461step0; decide +kernel
      have hl : raw16461step1Labels = raw16461step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16461step0 raw16461step0Labels permutation48 permutation5
    mixedMoment B raw16461step1 raw16461step1Labels = mixedMoment B raw16461step2 raw16461step2Labels := by
      have ha : raw16461step2 = -raw16461step1 := by apply Matrix.ext; change ∀ i j, raw16461step2 i j = -(raw16461step1 i j); unfold raw16461step2 raw16461step1; decide +kernel
      have hl : raw16461step2Labels = raw16461step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16461step2 raw16461step2Labels = mixedMoment B raw16461step3 raw16461step3Labels := by
      have ha : raw16461step3 = raw16461step2 := by apply Matrix.ext; unfold raw16461step3 raw16461step2; decide +kernel
      have hl : raw16461step2Labels = labelEmbedding8 ∘ raw16461step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16461step2 raw16461step2Labels raw16461step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical16462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16462 raw16462Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw16462 raw16462Labels = mixedMoment B raw16462step0 raw16462step0Labels := by
      have hz : ∀ j, raw16462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16462step0 = (fun i j => raw16462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16462step0 raw16462; decide +kernel
      have hl : raw16462step0Labels = raw16462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16462 raw16462Labels permutation346 hz
    mixedMoment B raw16462step0 raw16462step0Labels = mixedMoment B raw16462step1 raw16462step1Labels := by
      have ha : raw16462step1 = (fun i j => raw16462step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16462step1 raw16462step0; decide +kernel
      have hl : raw16462step1Labels = raw16462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16462step0 raw16462step0Labels permutation32 permutation3
    mixedMoment B raw16462step1 raw16462step1Labels = mixedMoment B raw16462step2 raw16462step2Labels := by
      have ha : raw16462step2 = raw16462step1 := by apply Matrix.ext; unfold raw16462step2 raw16462step1; decide +kernel
      have hl : raw16462step1Labels = labelEmbedding6 ∘ raw16462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16462step1 raw16462step1Labels raw16462step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

theorem canonical16463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16463 raw16463Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw16463 raw16463Labels = mixedMoment B raw16463step0 raw16463step0Labels := by
      have hz : ∀ j, raw16463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16463step0 = (fun i j => raw16463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16463step0 raw16463; decide +kernel
      have hl : raw16463step0Labels = raw16463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16463 raw16463Labels permutation346 hz
    mixedMoment B raw16463step0 raw16463step0Labels = mixedMoment B raw16463step1 raw16463step1Labels := by
      have ha : raw16463step1 = (fun i j => raw16463step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16463step1 raw16463step0; decide +kernel
      have hl : raw16463step1Labels = raw16463step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16463step0 raw16463step0Labels permutation126 permutation2
    mixedMoment B raw16463step1 raw16463step1Labels = mixedMoment B raw16463step2 raw16463step2Labels := by
      have ha : raw16463step2 = -raw16463step1 := by apply Matrix.ext; change ∀ i j, raw16463step2 i j = -(raw16463step1 i j); unfold raw16463step2 raw16463step1; decide +kernel
      have hl : raw16463step2Labels = raw16463step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical16464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16464 raw16464Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw16464 raw16464Labels = mixedMoment B raw16464step0 raw16464step0Labels := by
      have ha : raw16464step0 = (fun i j => raw16464 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16464step0 raw16464; decide +kernel
      have hl : raw16464step0Labels = raw16464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16464 raw16464Labels permutation589 permutation2
    mixedMoment B raw16464step0 raw16464step0Labels = mixedMoment B raw16464step1 raw16464step1Labels := by
      have ha : raw16464step1 = -raw16464step0 := by apply Matrix.ext; change ∀ i j, raw16464step1 i j = -(raw16464step0 i j); unfold raw16464step1 raw16464step0; decide +kernel
      have hl : raw16464step1Labels = raw16464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical16465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16465 raw16465Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw16465 raw16465Labels = mixedMoment B raw16465step0 raw16465step0Labels := by
      have hz : ∀ j, raw16465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16465step0 = (fun i j => raw16465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16465step0 raw16465; decide +kernel
      have hl : raw16465step0Labels = raw16465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16465 raw16465Labels permutation346 hz
    mixedMoment B raw16465step0 raw16465step0Labels = mixedMoment B raw16465step1 raw16465step1Labels := by
      have ha : raw16465step1 = (fun i j => raw16465step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16465step1 raw16465step0; decide +kernel
      have hl : raw16465step1Labels = raw16465step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16465step0 raw16465step0Labels permutation127 permutation2
    mixedMoment B raw16465step1 raw16465step1Labels = mixedMoment B raw16465step2 raw16465step2Labels := by
      have ha : raw16465step2 = -raw16465step1 := by apply Matrix.ext; change ∀ i j, raw16465step2 i j = -(raw16465step1 i j); unfold raw16465step2 raw16465step1; decide +kernel
      have hl : raw16465step2Labels = raw16465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical16466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16466 raw16466Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16466 raw16466Labels = mixedMoment B raw16466step0 raw16466step0Labels := by
      have hz : ∀ j, raw16466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16466step0 = (fun i j => raw16466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16466step0 raw16466; decide +kernel
      have hl : raw16466step0Labels = raw16466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16466 raw16466Labels permutation346 hz
    mixedMoment B raw16466step0 raw16466step0Labels = mixedMoment B raw16466step1 raw16466step1Labels := by
      have ha : raw16466step1 = (fun i j => raw16466step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16466step1 raw16466step0; decide +kernel
      have hl : raw16466step1Labels = raw16466step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16466step0 raw16466step0Labels permutation127 permutation2
    mixedMoment B raw16466step1 raw16466step1Labels = mixedMoment B raw16466step2 raw16466step2Labels := by
      have ha : raw16466step2 = -raw16466step1 := by apply Matrix.ext; change ∀ i j, raw16466step2 i j = -(raw16466step1 i j); unfold raw16466step2 raw16466step1; decide +kernel
      have hl : raw16466step2Labels = raw16466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical16467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16467 raw16467Labels = mixedMoment B node4850 node4850Labels := by
  calc
    mixedMoment B raw16467 raw16467Labels = mixedMoment B raw16467step0 raw16467step0Labels := by
      have hz : ∀ j, raw16467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16467step0 = (fun i j => raw16467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16467step0 raw16467; decide +kernel
      have hl : raw16467step0Labels = raw16467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16467 raw16467Labels permutation346 hz
    mixedMoment B raw16467step0 raw16467step0Labels = mixedMoment B raw16467step1 raw16467step1Labels := by
      have ha : raw16467step1 = (fun i j => raw16467step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16467step1 raw16467step0; decide +kernel
      have hl : raw16467step1Labels = raw16467step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16467step0 raw16467step0Labels permutation32 permutation3
    mixedMoment B raw16467step1 raw16467step1Labels = mixedMoment B raw16467step2 raw16467step2Labels := by
      have ha : raw16467step2 = raw16467step1 := by apply Matrix.ext; unfold raw16467step2 raw16467step1; decide +kernel
      have hl : raw16467step1Labels = labelEmbedding6 ∘ raw16467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16467step1 raw16467step1Labels raw16467step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4850 node4850Labels := by rfl

theorem canonical16468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16468 raw16468Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw16468 raw16468Labels = mixedMoment B raw16468step0 raw16468step0Labels := by
      have hz : ∀ j, raw16468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16468step0 = (fun i j => raw16468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16468step0 raw16468; decide +kernel
      have hl : raw16468step0Labels = raw16468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16468 raw16468Labels permutation346 hz
    mixedMoment B raw16468step0 raw16468step0Labels = mixedMoment B raw16468step1 raw16468step1Labels := by
      have ha : raw16468step1 = (fun i j => raw16468step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16468step1 raw16468step0; decide +kernel
      have hl : raw16468step1Labels = raw16468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16468step0 raw16468step0Labels permutation151 permutation3
    mixedMoment B raw16468step1 raw16468step1Labels = mixedMoment B raw16468step2 raw16468step2Labels := by
      have ha : raw16468step2 = -raw16468step1 := by apply Matrix.ext; change ∀ i j, raw16468step2 i j = -(raw16468step1 i j); unfold raw16468step2 raw16468step1; decide +kernel
      have hl : raw16468step2Labels = raw16468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16468step2 raw16468step2Labels = mixedMoment B raw16468step3 raw16468step3Labels := by
      have ha : raw16468step3 = raw16468step2 := by apply Matrix.ext; unfold raw16468step3 raw16468step2; decide +kernel
      have hl : raw16468step2Labels = labelEmbedding6 ∘ raw16468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16468step2 raw16468step2Labels raw16468step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

theorem canonical16469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16469 raw16469Labels = mixedMoment B node5183 node5183Labels := by
  calc
    mixedMoment B raw16469 raw16469Labels = mixedMoment B raw16469step0 raw16469step0Labels := by
      have ha : raw16469step0 = (fun i j => raw16469 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16469step0 raw16469; decide +kernel
      have hl : raw16469step0Labels = raw16469Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16469 raw16469Labels permutation686 permutation3
    mixedMoment B raw16469step0 raw16469step0Labels = mixedMoment B raw16469step1 raw16469step1Labels := by
      have ha : raw16469step1 = -raw16469step0 := by apply Matrix.ext; change ∀ i j, raw16469step1 i j = -(raw16469step0 i j); unfold raw16469step1 raw16469step0; decide +kernel
      have hl : raw16469step1Labels = raw16469step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16469step1 raw16469step1Labels = mixedMoment B raw16469step2 raw16469step2Labels := by
      have ha : raw16469step2 = raw16469step1 := by apply Matrix.ext; unfold raw16469step2 raw16469step1; decide +kernel
      have hl : raw16469step1Labels = labelEmbedding6 ∘ raw16469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16469step1 raw16469step1Labels raw16469step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5183 node5183Labels := by rfl

theorem canonical16470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16470 raw16470Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw16470 raw16470Labels = mixedMoment B raw16470step0 raw16470step0Labels := by
      have hz : ∀ j, raw16470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16470step0 = (fun i j => raw16470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16470step0 raw16470; decide +kernel
      have hl : raw16470step0Labels = raw16470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16470 raw16470Labels permutation346 hz
    mixedMoment B raw16470step0 raw16470step0Labels = mixedMoment B raw16470step1 raw16470step1Labels := by
      have ha : raw16470step1 = (fun i j => raw16470step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16470step1 raw16470step0; decide +kernel
      have hl : raw16470step1Labels = raw16470step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16470step0 raw16470step0Labels permutation149 permutation3
    mixedMoment B raw16470step1 raw16470step1Labels = mixedMoment B raw16470step2 raw16470step2Labels := by
      have ha : raw16470step2 = -raw16470step1 := by apply Matrix.ext; change ∀ i j, raw16470step2 i j = -(raw16470step1 i j); unfold raw16470step2 raw16470step1; decide +kernel
      have hl : raw16470step2Labels = raw16470step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16470step2 raw16470step2Labels = mixedMoment B raw16470step3 raw16470step3Labels := by
      have ha : raw16470step3 = raw16470step2 := by apply Matrix.ext; unfold raw16470step3 raw16470step2; decide +kernel
      have hl : raw16470step2Labels = labelEmbedding6 ∘ raw16470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16470step2 raw16470step2Labels raw16470step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

theorem canonical16471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16471 raw16471Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw16471 raw16471Labels = mixedMoment B raw16471step0 raw16471step0Labels := by
      have hz : ∀ j, raw16471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16471step0 = (fun i j => raw16471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16471step0 raw16471; decide +kernel
      have hl : raw16471step0Labels = raw16471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16471 raw16471Labels permutation346 hz
    mixedMoment B raw16471step0 raw16471step0Labels = mixedMoment B raw16471step1 raw16471step1Labels := by
      have ha : raw16471step1 = (fun i j => raw16471step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16471step1 raw16471step0; decide +kernel
      have hl : raw16471step1Labels = raw16471step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16471step0 raw16471step0Labels permutation145 permutation3
    mixedMoment B raw16471step1 raw16471step1Labels = mixedMoment B raw16471step2 raw16471step2Labels := by
      have ha : raw16471step2 = -raw16471step1 := by apply Matrix.ext; change ∀ i j, raw16471step2 i j = -(raw16471step1 i j); unfold raw16471step2 raw16471step1; decide +kernel
      have hl : raw16471step2Labels = raw16471step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16471step2 raw16471step2Labels = mixedMoment B raw16471step3 raw16471step3Labels := by
      have ha : raw16471step3 = raw16471step2 := by apply Matrix.ext; unfold raw16471step3 raw16471step2; decide +kernel
      have hl : raw16471step2Labels = labelEmbedding6 ∘ raw16471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16471step2 raw16471step2Labels raw16471step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16532 raw16532Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw16532 raw16532Labels = mixedMoment B raw16532step0 raw16532step0Labels := by
      have hz : ∀ j, raw16532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16532step0 = (fun i j => raw16532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16532step0 raw16532; decide +kernel
      have hl : raw16532step0Labels = raw16532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16532 raw16532Labels permutation346 hz
    mixedMoment B raw16532step0 raw16532step0Labels = mixedMoment B raw16532step1 raw16532step1Labels := by
      have ha : raw16532step1 = (fun i j => raw16532step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16532step1 raw16532step0; decide +kernel
      have hl : raw16532step1Labels = raw16532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16532step0 raw16532step0Labels permutation151 permutation2
    mixedMoment B raw16532step1 raw16532step1Labels = mixedMoment B raw16532step2 raw16532step2Labels := by
      have ha : raw16532step2 = -raw16532step1 := by apply Matrix.ext; change ∀ i j, raw16532step2 i j = -(raw16532step1 i j); unfold raw16532step2 raw16532step1; decide +kernel
      have hl : raw16532step2Labels = raw16532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical16536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16536 raw16536Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw16536 raw16536Labels = mixedMoment B raw16536step0 raw16536step0Labels := by
      have hz : ∀ j, raw16536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16536step0 = (fun i j => raw16536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16536step0 raw16536; decide +kernel
      have hl : raw16536step0Labels = raw16536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16536 raw16536Labels permutation346 hz
    mixedMoment B raw16536step0 raw16536step0Labels = mixedMoment B raw16536step1 raw16536step1Labels := by
      have ha : raw16536step1 = (fun i j => raw16536step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16536step1 raw16536step0; decide +kernel
      have hl : raw16536step1Labels = raw16536step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16536step0 raw16536step0Labels permutation33 permutation2
    _ = mixedMoment B node3174 node3174Labels := by rfl

theorem canonical16538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16538 raw16538Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw16538 raw16538Labels = mixedMoment B raw16538step0 raw16538step0Labels := by
      have hz : ∀ j, raw16538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16538step0 = (fun i j => raw16538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16538step0 raw16538; decide +kernel
      have hl : raw16538step0Labels = raw16538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16538 raw16538Labels permutation346 hz
    mixedMoment B raw16538step0 raw16538step0Labels = mixedMoment B raw16538step1 raw16538step1Labels := by
      have hz : ∀ j, raw16538step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw16538step1 = (fun i j => raw16538step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw16538step1 raw16538step0; decide +kernel
      have hl : raw16538step1Labels = raw16538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16538step0 raw16538step0Labels permutation32 hz
    mixedMoment B raw16538step1 raw16538step1Labels = mixedMoment B raw16538step2 raw16538step2Labels := by
      have ha : raw16538step2 = (fun i j => raw16538step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16538step2 raw16538step1; decide +kernel
      have hl : raw16538step2Labels = raw16538step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16538step1 raw16538step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical16539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16539 raw16539Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw16539 raw16539Labels = mixedMoment B raw16539step0 raw16539step0Labels := by
      have hz : ∀ j, raw16539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16539step0 = (fun i j => raw16539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16539step0 raw16539; decide +kernel
      have hl : raw16539step0Labels = raw16539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16539 raw16539Labels permutation346 hz
    mixedMoment B raw16539step0 raw16539step0Labels = mixedMoment B raw16539step1 raw16539step1Labels := by
      have ha : raw16539step1 = (fun i j => raw16539step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16539step1 raw16539step0; decide +kernel
      have hl : raw16539step1Labels = raw16539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16539step0 raw16539step0Labels permutation56 permutation2
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical16540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16540 raw16540Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw16540 raw16540Labels = mixedMoment B raw16540step0 raw16540step0Labels := by
      have ha : raw16540step0 = (fun i j => raw16540 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16540step0 raw16540; decide +kernel
      have hl : raw16540step0Labels = raw16540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16540 raw16540Labels permutation271 permutation2
    _ = mixedMoment B node3720 node3720Labels := by rfl

theorem canonical16541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16541 raw16541Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw16541 raw16541Labels = mixedMoment B raw16541step0 raw16541step0Labels := by
      have hz : ∀ j, raw16541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16541step0 = (fun i j => raw16541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16541step0 raw16541; decide +kernel
      have hl : raw16541step0Labels = raw16541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16541 raw16541Labels permutation346 hz
    mixedMoment B raw16541step0 raw16541step0Labels = mixedMoment B raw16541step1 raw16541step1Labels := by
      have ha : raw16541step1 = (fun i j => raw16541step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16541step1 raw16541step0; decide +kernel
      have hl : raw16541step1Labels = raw16541step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16541step0 raw16541step0Labels permutation56 permutation2
    _ = mixedMoment B node3733 node3733Labels := by rfl

theorem canonical16542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16542 raw16542Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw16542 raw16542Labels = mixedMoment B raw16542step0 raw16542step0Labels := by
      have hz : ∀ j, raw16542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16542step0 = (fun i j => raw16542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16542step0 raw16542; decide +kernel
      have hl : raw16542step0Labels = raw16542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16542 raw16542Labels permutation346 hz
    mixedMoment B raw16542step0 raw16542step0Labels = mixedMoment B raw16542step1 raw16542step1Labels := by
      have ha : raw16542step1 = (fun i j => raw16542step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16542step1 raw16542step0; decide +kernel
      have hl : raw16542step1Labels = raw16542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16542step0 raw16542step0Labels permutation126 permutation2
    mixedMoment B raw16542step1 raw16542step1Labels = mixedMoment B raw16542step2 raw16542step2Labels := by
      have ha : raw16542step2 = -raw16542step1 := by apply Matrix.ext; change ∀ i j, raw16542step2 i j = -(raw16542step1 i j); unfold raw16542step2 raw16542step1; decide +kernel
      have hl : raw16542step2Labels = raw16542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical16543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16543 raw16543Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw16543 raw16543Labels = mixedMoment B raw16543step0 raw16543step0Labels := by
      have hz : ∀ j, raw16543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16543step0 = (fun i j => raw16543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16543step0 raw16543; decide +kernel
      have hl : raw16543step0Labels = raw16543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16543 raw16543Labels permutation346 hz
    mixedMoment B raw16543step0 raw16543step0Labels = mixedMoment B raw16543step1 raw16543step1Labels := by
      have ha : raw16543step1 = (fun i j => raw16543step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16543step1 raw16543step0; decide +kernel
      have hl : raw16543step1Labels = raw16543step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16543step0 raw16543step0Labels permutation150 permutation2
    mixedMoment B raw16543step1 raw16543step1Labels = mixedMoment B raw16543step2 raw16543step2Labels := by
      have ha : raw16543step2 = -raw16543step1 := by apply Matrix.ext; change ∀ i j, raw16543step2 i j = -(raw16543step1 i j); unfold raw16543step2 raw16543step1; decide +kernel
      have hl : raw16543step2Labels = raw16543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2867 node2867Labels := by rfl

theorem canonical16545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16545 raw16545Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw16545 raw16545Labels = mixedMoment B raw16545step0 raw16545step0Labels := by
      have ha : raw16545step0 = (fun i j => raw16545 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16545step0 raw16545; decide +kernel
      have hl : raw16545step0Labels = raw16545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16545 raw16545Labels permutation528 permutation4
    mixedMoment B raw16545step0 raw16545step0Labels = mixedMoment B raw16545step1 raw16545step1Labels := by
      have ha : raw16545step1 = -raw16545step0 := by apply Matrix.ext; change ∀ i j, raw16545step1 i j = -(raw16545step0 i j); unfold raw16545step1 raw16545step0; decide +kernel
      have hl : raw16545step1Labels = raw16545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3730 node3730Labels := by rfl

theorem canonical16550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16550 raw16550Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw16550 raw16550Labels = mixedMoment B raw16550step0 raw16550step0Labels := by
      have ha : raw16550step0 = (fun i j => raw16550 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16550step0 raw16550; decide +kernel
      have hl : raw16550step0Labels = raw16550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16550 raw16550Labels permutation589 permutation2
    mixedMoment B raw16550step0 raw16550step0Labels = mixedMoment B raw16550step1 raw16550step1Labels := by
      have ha : raw16550step1 = -raw16550step0 := by apply Matrix.ext; change ∀ i j, raw16550step1 i j = -(raw16550step0 i j); unfold raw16550step1 raw16550step0; decide +kernel
      have hl : raw16550step1Labels = raw16550step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

theorem canonical16552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16552 raw16552Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw16552 raw16552Labels = mixedMoment B raw16552step0 raw16552step0Labels := by
      have hz : ∀ j, raw16552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16552step0 = (fun i j => raw16552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16552step0 raw16552; decide +kernel
      have hl : raw16552step0Labels = raw16552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16552 raw16552Labels permutation346 hz
    mixedMoment B raw16552step0 raw16552step0Labels = mixedMoment B raw16552step1 raw16552step1Labels := by
      have ha : raw16552step1 = (fun i j => raw16552step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16552step1 raw16552step0; decide +kernel
      have hl : raw16552step1Labels = raw16552step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16552step0 raw16552step0Labels permutation108 permutation4
    mixedMoment B raw16552step1 raw16552step1Labels = mixedMoment B raw16552step2 raw16552step2Labels := by
      have ha : raw16552step2 = -raw16552step1 := by apply Matrix.ext; change ∀ i j, raw16552step2 i j = -(raw16552step1 i j); unfold raw16552step2 raw16552step1; decide +kernel
      have hl : raw16552step2Labels = raw16552step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3733 node3733Labels := by rfl

theorem canonical16554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16554 raw16554Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw16554 raw16554Labels = mixedMoment B raw16554step0 raw16554step0Labels := by
      have hz : ∀ j, raw16554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16554step0 = (fun i j => raw16554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16554step0 raw16554; decide +kernel
      have hl : raw16554step0Labels = raw16554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16554 raw16554Labels permutation346 hz
    mixedMoment B raw16554step0 raw16554step0Labels = mixedMoment B raw16554step1 raw16554step1Labels := by
      have ha : raw16554step1 = (fun i j => raw16554step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16554step1 raw16554step0; decide +kernel
      have hl : raw16554step1Labels = raw16554step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16554step0 raw16554step0Labels permutation127 permutation2
    mixedMoment B raw16554step1 raw16554step1Labels = mixedMoment B raw16554step2 raw16554step2Labels := by
      have ha : raw16554step2 = -raw16554step1 := by apply Matrix.ext; change ∀ i j, raw16554step2 i j = -(raw16554step1 i j); unfold raw16554step2 raw16554step1; decide +kernel
      have hl : raw16554step2Labels = raw16554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical16555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16555 raw16555Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw16555 raw16555Labels = mixedMoment B raw16555step0 raw16555step0Labels := by
      have hz : ∀ j, raw16555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16555step0 = (fun i j => raw16555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16555step0 raw16555; decide +kernel
      have hl : raw16555step0Labels = raw16555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16555 raw16555Labels permutation346 hz
    mixedMoment B raw16555step0 raw16555step0Labels = mixedMoment B raw16555step1 raw16555step1Labels := by
      have ha : raw16555step1 = (fun i j => raw16555step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16555step1 raw16555step0; decide +kernel
      have hl : raw16555step1Labels = raw16555step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16555step0 raw16555step0Labels permutation127 permutation2
    mixedMoment B raw16555step1 raw16555step1Labels = mixedMoment B raw16555step2 raw16555step2Labels := by
      have ha : raw16555step2 = -raw16555step1 := by apply Matrix.ext; change ∀ i j, raw16555step2 i j = -(raw16555step1 i j); unfold raw16555step2 raw16555step1; decide +kernel
      have hl : raw16555step2Labels = raw16555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical16556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16556 raw16556Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw16556 raw16556Labels = mixedMoment B raw16556step0 raw16556step0Labels := by
      have hz : ∀ j, raw16556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16556step0 = (fun i j => raw16556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16556step0 raw16556; decide +kernel
      have hl : raw16556step0Labels = raw16556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16556 raw16556Labels permutation346 hz
    mixedMoment B raw16556step0 raw16556step0Labels = mixedMoment B raw16556step1 raw16556step1Labels := by
      have ha : raw16556step1 = (fun i j => raw16556step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16556step1 raw16556step0; decide +kernel
      have hl : raw16556step1Labels = raw16556step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16556step0 raw16556step0Labels permutation109 permutation4
    mixedMoment B raw16556step1 raw16556step1Labels = mixedMoment B raw16556step2 raw16556step2Labels := by
      have ha : raw16556step2 = -raw16556step1 := by apply Matrix.ext; change ∀ i j, raw16556step2 i j = -(raw16556step1 i j); unfold raw16556step2 raw16556step1; decide +kernel
      have hl : raw16556step2Labels = raw16556step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical16557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16557 raw16557Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw16557 raw16557Labels = mixedMoment B raw16557step0 raw16557step0Labels := by
      have hz : ∀ j, raw16557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16557step0 = (fun i j => raw16557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16557step0 raw16557; decide +kernel
      have hl : raw16557step0Labels = raw16557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16557 raw16557Labels permutation346 hz
    mixedMoment B raw16557step0 raw16557step0Labels = mixedMoment B raw16557step1 raw16557step1Labels := by
      have ha : raw16557step1 = (fun i j => raw16557step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16557step1 raw16557step0; decide +kernel
      have hl : raw16557step1Labels = raw16557step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16557step0 raw16557step0Labels permutation109 permutation4
    mixedMoment B raw16557step1 raw16557step1Labels = mixedMoment B raw16557step2 raw16557step2Labels := by
      have ha : raw16557step2 = -raw16557step1 := by apply Matrix.ext; change ∀ i j, raw16557step2 i j = -(raw16557step1 i j); unfold raw16557step2 raw16557step1; decide +kernel
      have hl : raw16557step2Labels = raw16557step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical16558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16558 raw16558Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw16558 raw16558Labels = mixedMoment B raw16558step0 raw16558step0Labels := by
      have hz : ∀ j, raw16558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16558step0 = (fun i j => raw16558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16558step0 raw16558; decide +kernel
      have hl : raw16558step0Labels = raw16558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16558 raw16558Labels permutation346 hz
    mixedMoment B raw16558step0 raw16558step0Labels = mixedMoment B raw16558step1 raw16558step1Labels := by
      have ha : raw16558step1 = (fun i j => raw16558step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16558step1 raw16558step0; decide +kernel
      have hl : raw16558step1Labels = raw16558step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16558step0 raw16558step0Labels permutation151 permutation2
    mixedMoment B raw16558step1 raw16558step1Labels = mixedMoment B raw16558step2 raw16558step2Labels := by
      have ha : raw16558step2 = -raw16558step1 := by apply Matrix.ext; change ∀ i j, raw16558step2 i j = -(raw16558step1 i j); unfold raw16558step2 raw16558step1; decide +kernel
      have hl : raw16558step2Labels = raw16558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

theorem canonical16596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16596 raw16596Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw16596 raw16596Labels = mixedMoment B raw16596step0 raw16596step0Labels := by
      have hz : ∀ j, raw16596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16596step0 = (fun i j => raw16596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16596step0 raw16596; decide +kernel
      have hl : raw16596step0Labels = raw16596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16596 raw16596Labels permutation434 hz
    mixedMoment B raw16596step0 raw16596step0Labels = mixedMoment B raw16596step1 raw16596step1Labels := by
      have hz : ∀ j, raw16596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16596step1 = (fun i j => raw16596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16596step1 raw16596step0; decide +kernel
      have hl : raw16596step1Labels = raw16596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16596step0 raw16596step0Labels permutation80 hz
    mixedMoment B raw16596step1 raw16596step1Labels = mixedMoment B raw16596step2 raw16596step2Labels := by
      have ha : raw16596step2 = (fun i j => raw16596step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16596step2 raw16596step1; decide +kernel
      have hl : raw16596step2Labels = raw16596step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16596step1 raw16596step1Labels permutation24 permutation2
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical16597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16597 raw16597Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw16597 raw16597Labels = mixedMoment B raw16597step0 raw16597step0Labels := by
      have hz : ∀ j, raw16597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16597step0 = (fun i j => raw16597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16597step0 raw16597; decide +kernel
      have hl : raw16597step0Labels = raw16597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16597 raw16597Labels permutation346 hz
    mixedMoment B raw16597step0 raw16597step0Labels = mixedMoment B raw16597step1 raw16597step1Labels := by
      have ha : raw16597step1 = (fun i j => raw16597step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16597step1 raw16597step0; decide +kernel
      have hl : raw16597step1Labels = raw16597step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16597step0 raw16597step0Labels permutation126 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

theorem canonical16598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16598 raw16598Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw16598 raw16598Labels = mixedMoment B raw16598step0 raw16598step0Labels := by
      have hz : ∀ j, raw16598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16598step0 = (fun i j => raw16598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16598step0 raw16598; decide +kernel
      have hl : raw16598step0Labels = raw16598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16598 raw16598Labels permutation346 hz
    mixedMoment B raw16598step0 raw16598step0Labels = mixedMoment B raw16598step1 raw16598step1Labels := by
      have ha : raw16598step1 = (fun i j => raw16598step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16598step1 raw16598step0; decide +kernel
      have hl : raw16598step1Labels = raw16598step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16598step0 raw16598step0Labels permutation150 permutation2
    _ = mixedMoment B node3705 node3705Labels := by rfl

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

theorem canonical2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2400 raw2400Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw2400 raw2400Labels = mixedMoment B raw2400step0 raw2400step0Labels := by
      have ha : raw2400step0 = (fun i j => raw2400 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2400step0 raw2400; decide +kernel
      have hl : raw2400step0Labels = raw2400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2400 raw2400Labels permutation32 permutation4
    mixedMoment B raw2400step0 raw2400step0Labels = mixedMoment B raw2400step1 raw2400step1Labels := by
      have ha : raw2400step1 = raw2400step0 := by apply Matrix.ext; unfold raw2400step1 raw2400step0; decide +kernel
      have hl : raw2400step0Labels = labelEmbedding7 ∘ raw2400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2400step0 raw2400step0Labels raw2400step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2401 raw2401Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw2401 raw2401Labels = mixedMoment B raw2401step0 raw2401step0Labels := by
      have ha : raw2401step0 = (fun i j => raw2401 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2401step0 raw2401; decide +kernel
      have hl : raw2401step0Labels = raw2401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2401 raw2401Labels permutation32 permutation4
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2402 raw2402Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw2402 raw2402Labels = mixedMoment B raw2402step0 raw2402step0Labels := by
      have ha : raw2402step0 = (fun i j => raw2402 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2402step0 raw2402; decide +kernel
      have hl : raw2402step0Labels = raw2402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2402 raw2402Labels permutation34 permutation6
    mixedMoment B raw2402step0 raw2402step0Labels = mixedMoment B raw2402step1 raw2402step1Labels := by
      have ha : raw2402step1 = -raw2402step0 := by apply Matrix.ext; change ∀ i j, raw2402step1 i j = -(raw2402step0 i j); unfold raw2402step1 raw2402step0; decide +kernel
      have hl : raw2402step1Labels = raw2402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2402step1 raw2402step1Labels = mixedMoment B raw2402step2 raw2402step2Labels := by
      have ha : raw2402step2 = raw2402step1 := by apply Matrix.ext; unfold raw2402step2 raw2402step1; decide +kernel
      have hl : raw2402step1Labels = labelEmbedding1 ∘ raw2402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2402step1 raw2402step1Labels raw2402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical2418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2418 raw2418Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw2418 raw2418Labels = mixedMoment B raw2418step0 raw2418step0Labels := by
      have ha : raw2418step0 = (fun i j => raw2418 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2418step0 raw2418; decide +kernel
      have hl : raw2418step0Labels = raw2418Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2418 raw2418Labels permutation32 permutation4
    mixedMoment B raw2418step0 raw2418step0Labels = mixedMoment B raw2418step1 raw2418step1Labels := by
      have ha : raw2418step1 = raw2418step0 := by apply Matrix.ext; unfold raw2418step1 raw2418step0; decide +kernel
      have hl : raw2418step0Labels = labelEmbedding7 ∘ raw2418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2418step0 raw2418step0Labels raw2418step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical2419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2419 raw2419Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw2419 raw2419Labels = mixedMoment B raw2419step0 raw2419step0Labels := by
      have ha : raw2419step0 = (fun i j => raw2419 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2419step0 raw2419; decide +kernel
      have hl : raw2419step0Labels = raw2419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2419 raw2419Labels permutation32 permutation4
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical2420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2420 raw2420Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw2420 raw2420Labels = mixedMoment B raw2420step0 raw2420step0Labels := by
      have ha : raw2420step0 = (fun i j => raw2420 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2420step0 raw2420; decide +kernel
      have hl : raw2420step0Labels = raw2420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2420 raw2420Labels permutation36 permutation6
    mixedMoment B raw2420step0 raw2420step0Labels = mixedMoment B raw2420step1 raw2420step1Labels := by
      have ha : raw2420step1 = -raw2420step0 := by apply Matrix.ext; change ∀ i j, raw2420step1 i j = -(raw2420step0 i j); unfold raw2420step1 raw2420step0; decide +kernel
      have hl : raw2420step1Labels = raw2420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2420step1 raw2420step1Labels = mixedMoment B raw2420step2 raw2420step2Labels := by
      have ha : raw2420step2 = raw2420step1 := by apply Matrix.ext; unfold raw2420step2 raw2420step1; decide +kernel
      have hl : raw2420step1Labels = labelEmbedding1 ∘ raw2420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2420step1 raw2420step1Labels raw2420step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

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

theorem canonical2439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2439 raw2439Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw2439 raw2439Labels = mixedMoment B raw2439step0 raw2439step0Labels := by
      have ha : raw2439step0 = (fun i j => raw2439 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2439step0 raw2439; decide +kernel
      have hl : raw2439step0Labels = raw2439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2439 raw2439Labels permutation32 permutation4
    mixedMoment B raw2439step0 raw2439step0Labels = mixedMoment B raw2439step1 raw2439step1Labels := by
      have ha : raw2439step1 = raw2439step0 := by apply Matrix.ext; unfold raw2439step1 raw2439step0; decide +kernel
      have hl : raw2439step0Labels = labelEmbedding7 ∘ raw2439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2439step0 raw2439step0Labels raw2439step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2440 raw2440Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw2440 raw2440Labels = mixedMoment B raw2440step0 raw2440step0Labels := by
      have ha : raw2440step0 = (fun i j => raw2440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2440step0 raw2440; decide +kernel
      have hl : raw2440step0Labels = raw2440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2440 raw2440Labels permutation32 permutation4
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical2441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2441 raw2441Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw2441 raw2441Labels = mixedMoment B raw2441step0 raw2441step0Labels := by
      have ha : raw2441step0 = (fun i j => raw2441 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2441step0 raw2441; decide +kernel
      have hl : raw2441step0Labels = raw2441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2441 raw2441Labels permutation149 permutation6
    mixedMoment B raw2441step0 raw2441step0Labels = mixedMoment B raw2441step1 raw2441step1Labels := by
      have ha : raw2441step1 = raw2441step0 := by apply Matrix.ext; unfold raw2441step1 raw2441step0; decide +kernel
      have hl : raw2441step0Labels = labelEmbedding1 ∘ raw2441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2441step0 raw2441step0Labels raw2441step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical2490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2490 raw2490Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2490 raw2490Labels = mixedMoment B raw2490step0 raw2490step0Labels := by
      have ha : raw2490step0 = (fun i j => raw2490 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2490step0 raw2490; decide +kernel
      have hl : raw2490step0Labels = raw2490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2490 raw2490Labels permutation32 permutation4
    mixedMoment B raw2490step0 raw2490step0Labels = mixedMoment B raw2490step1 raw2490step1Labels := by
      have ha : raw2490step1 = raw2490step0 := by apply Matrix.ext; unfold raw2490step1 raw2490step0; decide +kernel
      have hl : raw2490step0Labels = labelEmbedding7 ∘ raw2490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2490step0 raw2490step0Labels raw2490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical2491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2491 raw2491Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2491 raw2491Labels = mixedMoment B raw2491step0 raw2491step0Labels := by
      have ha : raw2491step0 = (fun i j => raw2491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2491step0 raw2491; decide +kernel
      have hl : raw2491step0Labels = raw2491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2491 raw2491Labels permutation32 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical2492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2492 raw2492Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw2492 raw2492Labels = mixedMoment B raw2492step0 raw2492step0Labels := by
      have ha : raw2492step0 = (fun i j => raw2492 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2492step0 raw2492; decide +kernel
      have hl : raw2492step0Labels = raw2492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2492 raw2492Labels permutation36 permutation6
    mixedMoment B raw2492step0 raw2492step0Labels = mixedMoment B raw2492step1 raw2492step1Labels := by
      have ha : raw2492step1 = -raw2492step0 := by apply Matrix.ext; change ∀ i j, raw2492step1 i j = -(raw2492step0 i j); unfold raw2492step1 raw2492step0; decide +kernel
      have hl : raw2492step1Labels = raw2492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2492step1 raw2492step1Labels = mixedMoment B raw2492step2 raw2492step2Labels := by
      have ha : raw2492step2 = raw2492step1 := by apply Matrix.ext; unfold raw2492step2 raw2492step1; decide +kernel
      have hl : raw2492step1Labels = labelEmbedding1 ∘ raw2492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2492step1 raw2492step1Labels raw2492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

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

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

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

theorem canonical2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2589 raw2589Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2589 raw2589Labels = mixedMoment B raw2589step0 raw2589step0Labels := by
      have ha : raw2589step0 = (fun i j => raw2589 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2589step0 raw2589; decide +kernel
      have hl : raw2589step0Labels = raw2589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2589 raw2589Labels permutation32 permutation4
    mixedMoment B raw2589step0 raw2589step0Labels = mixedMoment B raw2589step1 raw2589step1Labels := by
      have ha : raw2589step1 = raw2589step0 := by apply Matrix.ext; unfold raw2589step1 raw2589step0; decide +kernel
      have hl : raw2589step0Labels = labelEmbedding7 ∘ raw2589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2589step0 raw2589step0Labels raw2589step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2590 raw2590Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2590 raw2590Labels = mixedMoment B raw2590step0 raw2590step0Labels := by
      have ha : raw2590step0 = (fun i j => raw2590 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2590step0 raw2590; decide +kernel
      have hl : raw2590step0Labels = raw2590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2590 raw2590Labels permutation32 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2591 raw2591Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw2591 raw2591Labels = mixedMoment B raw2591step0 raw2591step0Labels := by
      have ha : raw2591step0 = (fun i j => raw2591 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2591step0 raw2591; decide +kernel
      have hl : raw2591step0Labels = raw2591Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2591 raw2591Labels permutation56 permutation6
    mixedMoment B raw2591step0 raw2591step0Labels = mixedMoment B raw2591step1 raw2591step1Labels := by
      have ha : raw2591step1 = -raw2591step0 := by apply Matrix.ext; change ∀ i j, raw2591step1 i j = -(raw2591step0 i j); unfold raw2591step1 raw2591step0; decide +kernel
      have hl : raw2591step1Labels = raw2591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2591step1 raw2591step1Labels = mixedMoment B raw2591step2 raw2591step2Labels := by
      have ha : raw2591step2 = raw2591step1 := by apply Matrix.ext; unfold raw2591step2 raw2591step1; decide +kernel
      have hl : raw2591step1Labels = labelEmbedding1 ∘ raw2591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2591step1 raw2591step1Labels raw2591step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

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

theorem singleton5355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5355 node5355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3693 node3693Labels + mixedMoment B node3770 node3770Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2400 singletonSmall5355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5355) = raw2400Labels := by decide +kernel
  rw [hl, canonical2400 B hB] at h
  have hc0 : mixedMoment B raw2400 (Fin.cases (0 : Fin 2) singletonSmall5355) =
      mixedMoment B node3693 node3693Labels := by
    have ha : raw2400 = raw2401 := by apply Matrix.ext; unfold raw2400 raw2401; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5355 = raw2401Labels := by decide +kernel
    rw [ha, hj, canonical2401 B hB]
  have hc1 : mixedMoment B raw2400 (Fin.cases (1 : Fin 2) singletonSmall5355) =
      mixedMoment B node3770 node3770Labels := by
    have ha : raw2400 = raw2402 := by apply Matrix.ext; unfold raw2400 raw2402; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5355 = raw2402Labels := by decide +kernel
    rw [ha, hj, canonical2402 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5370 node5370Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3706 node3706Labels + mixedMoment B node3771 node3771Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2418 singletonSmall5370
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5370) = raw2418Labels := by decide +kernel
  rw [hl, canonical2418 B hB] at h
  have hc0 : mixedMoment B raw2418 (Fin.cases (0 : Fin 2) singletonSmall5370) =
      mixedMoment B node3706 node3706Labels := by
    have ha : raw2418 = raw2419 := by apply Matrix.ext; unfold raw2418 raw2419; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5370 = raw2419Labels := by decide +kernel
    rw [ha, hj, canonical2419 B hB]
  have hc1 : mixedMoment B raw2418 (Fin.cases (1 : Fin 2) singletonSmall5370) =
      mixedMoment B node3771 node3771Labels := by
    have ha : raw2418 = raw2420 := by apply Matrix.ext; unfold raw2418 raw2420; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5370 = raw2420Labels := by decide +kernel
    rw [ha, hj, canonical2420 B hB]
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

theorem singleton5384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5384 node5384Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3732 node3732Labels + mixedMoment B node3811 node3811Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2439 singletonSmall5384
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5384) = raw2439Labels := by decide +kernel
  rw [hl, canonical2439 B hB] at h
  have hc0 : mixedMoment B raw2439 (Fin.cases (0 : Fin 2) singletonSmall5384) =
      mixedMoment B node3732 node3732Labels := by
    have ha : raw2439 = raw2440 := by apply Matrix.ext; unfold raw2439 raw2440; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5384 = raw2440Labels := by decide +kernel
    rw [ha, hj, canonical2440 B hB]
  have hc1 : mixedMoment B raw2439 (Fin.cases (1 : Fin 2) singletonSmall5384) =
      mixedMoment B node3811 node3811Labels := by
    have ha : raw2439 = raw2441 := by apply Matrix.ext; unfold raw2439 raw2441; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5384 = raw2441Labels := by decide +kernel
    rw [ha, hj, canonical2441 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5411 node5411Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3809 node3809Labels + mixedMoment B node3813 node3813Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2490 singletonSmall5411
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5411) = raw2490Labels := by decide +kernel
  rw [hl, canonical2490 B hB] at h
  have hc0 : mixedMoment B raw2490 (Fin.cases (0 : Fin 2) singletonSmall5411) =
      mixedMoment B node3809 node3809Labels := by
    have ha : raw2490 = raw2491 := by apply Matrix.ext; unfold raw2490 raw2491; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5411 = raw2491Labels := by decide +kernel
    rw [ha, hj, canonical2491 B hB]
  have hc1 : mixedMoment B raw2490 (Fin.cases (1 : Fin 2) singletonSmall5411) =
      mixedMoment B node3813 node3813Labels := by
    have ha : raw2490 = raw2492 := by apply Matrix.ext; unfold raw2490 raw2492; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5411 = raw2492Labels := by decide +kernel
    rw [ha, hj, canonical2492 B hB]
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

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
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

theorem singleton5473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5473 node5473Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3958 node3958Labels + mixedMoment B node3961 node3961Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2589 singletonSmall5473
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5473) = raw2589Labels := by decide +kernel
  rw [hl, canonical2589 B hB] at h
  have hc0 : mixedMoment B raw2589 (Fin.cases (0 : Fin 2) singletonSmall5473) =
      mixedMoment B node3958 node3958Labels := by
    have ha : raw2589 = raw2590 := by apply Matrix.ext; unfold raw2589 raw2590; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5473 = raw2590Labels := by decide +kernel
    rw [ha, hj, canonical2590 B hB]
  have hc1 : mixedMoment B raw2589 (Fin.cases (1 : Fin 2) singletonSmall5473) =
      mixedMoment B node3961 node3961Labels := by
    have ha : raw2589 = raw2591 := by apply Matrix.ext; unfold raw2589 raw2591; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5473 = raw2591Labels := by decide +kernel
    rw [ha, hj, canonical2591 B hB]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2633 node2633Labels = Sparse.eval nodeValue2633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2633) = mixedMoment B node2633 node2633Labels := rfl
  simpa [nodeValue2633, Sparse.eval] using hc.symm

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

theorem sound2867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2867 node2867Labels = Sparse.eval nodeValue2867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2867) = mixedMoment B node2867 node2867Labels := rfl
  simpa [nodeValue2867, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2882 node2882Labels = Sparse.eval nodeValue2882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2882) = mixedMoment B node2882 node2882Labels := rfl
  simpa [nodeValue2882, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2955 node2955Labels = Sparse.eval nodeValue2955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2955) = mixedMoment B node2955 node2955Labels := rfl
  simpa [nodeValue2955, Sparse.eval] using hc.symm

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

theorem sound3040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3040 node3040Labels = Sparse.eval nodeValue3040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3040) = mixedMoment B node3040 node3040Labels := rfl
  simpa [nodeValue3040, Sparse.eval] using hc.symm

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

theorem sound3092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3092 node3092Labels = Sparse.eval nodeValue3092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3092) = mixedMoment B node3092 node3092Labels := rfl
  simpa [nodeValue3092, Sparse.eval] using hc.symm

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

theorem sound3174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3174 node3174Labels = Sparse.eval nodeValue3174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3174) = mixedMoment B node3174 node3174Labels := rfl
  simpa [nodeValue3174, Sparse.eval] using hc.symm

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

theorem sound3691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3691 node3691Labels = Sparse.eval nodeValue3691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3691) = mixedMoment B node3691 node3691Labels := rfl
  simpa [nodeValue3691, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

theorem sound3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3705 node3705Labels = Sparse.eval nodeValue3705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3705) = mixedMoment B node3705 node3705Labels := rfl
  simpa [nodeValue3705, Sparse.eval] using hc.symm

theorem sound3706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3706 node3706Labels = Sparse.eval nodeValue3706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3706) = mixedMoment B node3706 node3706Labels := rfl
  simpa [nodeValue3706, Sparse.eval] using hc.symm

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

theorem sound3720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3720 node3720Labels = Sparse.eval nodeValue3720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3720) = mixedMoment B node3720 node3720Labels := rfl
  simpa [nodeValue3720, Sparse.eval] using hc.symm

theorem sound3730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3730 node3730Labels = Sparse.eval nodeValue3730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3730) = mixedMoment B node3730 node3730Labels := rfl
  simpa [nodeValue3730, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3733 node3733Labels = Sparse.eval nodeValue3733 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3733) = mixedMoment B node3733 node3733Labels := rfl
  simpa [nodeValue3733, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

theorem sound3771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3771 node3771Labels = Sparse.eval nodeValue3771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3771) = mixedMoment B node3771 node3771Labels := rfl
  simpa [nodeValue3771, Sparse.eval] using hc.symm

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

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3827 node3827Labels = Sparse.eval nodeValue3827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3827) = mixedMoment B node3827 node3827Labels := rfl
  simpa [nodeValue3827, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3881 node3881Labels = Sparse.eval nodeValue3881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3881) = mixedMoment B node3881 node3881Labels := rfl
  simpa [nodeValue3881, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

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

theorem zero3944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3944 node3944Labels = 0 := by
  exact mixedMoment_alpha B hF node3944 node3944Labels 1 permutation202
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

theorem sound3929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3929 node3929Labels = Sparse.eval nodeValue3929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3929) = mixedMoment B node3929 node3929Labels := rfl
  simpa [nodeValue3929, Sparse.eval] using hc.symm

theorem sound3944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3944 node3944Labels = Sparse.eval nodeValue3944 (mixedVector B) := by
  simpa only [nodeValue3944, Sparse.eval_nil] using zero3944 B _hB _hF

theorem sound3947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3947 node3947Labels = Sparse.eval nodeValue3947 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3947) = mixedMoment B node3947 node3947Labels := rfl
  simpa [nodeValue3947, Sparse.eval] using hc.symm

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

theorem sound3959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3959 node3959Labels = Sparse.eval nodeValue3959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3959) = mixedMoment B node3959 node3959Labels := rfl
  simpa [nodeValue3959, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

theorem sound3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3963 node3963Labels = Sparse.eval nodeValue3963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3963) = mixedMoment B node3963 node3963Labels := rfl
  simpa [nodeValue3963, Sparse.eval] using hc.symm

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

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4849 node4849Labels = Sparse.eval nodeValue4849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4849) = mixedMoment B node4849 node4849Labels := rfl
  simpa [nodeValue4849, Sparse.eval] using hc.symm

theorem sound4850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4850 node4850Labels = Sparse.eval nodeValue4850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4850) = mixedMoment B node4850 node4850Labels := rfl
  simpa [nodeValue4850, Sparse.eval] using hc.symm

theorem sound4856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4856 node4856Labels = Sparse.eval nodeValue4856 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4856) = mixedMoment B node4856 node4856Labels := rfl
  simpa [nodeValue4856, Sparse.eval] using hc.symm

theorem sound4861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4861 node4861Labels = Sparse.eval nodeValue4861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4861) = mixedMoment B node4861 node4861Labels := rfl
  simpa [nodeValue4861, Sparse.eval] using hc.symm

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

theorem sound4867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4867 node4867Labels = Sparse.eval nodeValue4867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4867) = mixedMoment B node4867 node4867Labels := rfl
  simpa [nodeValue4867, Sparse.eval] using hc.symm

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

theorem sound5183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5183 node5183Labels = Sparse.eval nodeValue5183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5183) = mixedMoment B node5183 node5183Labels := rfl
  simpa [nodeValue5183, Sparse.eval] using hc.symm

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

theorem sound5188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5188 node5188Labels = Sparse.eval nodeValue5188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5188) = mixedMoment B node5188 node5188Labels := rfl
  simpa [nodeValue5188, Sparse.eval] using hc.symm

theorem sound5198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5198 node5198Labels = Sparse.eval nodeValue5198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5198) = mixedMoment B node5198 node5198Labels := rfl
  simpa [nodeValue5198, Sparse.eval] using hc.symm

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

theorem sound5264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5264 node5264Labels = Sparse.eval nodeValue5264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5264) = mixedMoment B node5264 node5264Labels := rfl
  simpa [nodeValue5264, Sparse.eval] using hc.symm

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

theorem sound5353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5353 node5353Labels = Sparse.eval nodeValue5353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5353) = mixedMoment B node5353 node5353Labels := rfl
  simpa [nodeValue5353, Sparse.eval] using hc.symm

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5370 node5370Labels = Sparse.eval nodeValue5370 (mixedVector B) := by
  have h := singleton5370 B _hB
  rw [sound3706 B _hB _hF, sound3771 B _hB _hF] at h
  norm_num [nodeValue5370, nodeValue3706, nodeValue3771, Sparse.eval] at h ⊢
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

theorem sound5382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5382 node5382Labels = Sparse.eval nodeValue5382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5382) = mixedMoment B node5382 node5382Labels := rfl
  simpa [nodeValue5382, Sparse.eval] using hc.symm

theorem sound5384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5384 node5384Labels = Sparse.eval nodeValue5384 (mixedVector B) := by
  have h := singleton5384 B _hB
  rw [sound3732 B _hB _hF, sound3811 B _hB _hF] at h
  norm_num [nodeValue5384, nodeValue3732, nodeValue3811, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5385 node5385Labels = Sparse.eval nodeValue5385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5385) = mixedMoment B node5385 node5385Labels := rfl
  simpa [nodeValue5385, Sparse.eval] using hc.symm

theorem sound5399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5399 node5399Labels = Sparse.eval nodeValue5399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5399) = mixedMoment B node5399 node5399Labels := rfl
  simpa [nodeValue5399, Sparse.eval] using hc.symm

theorem sound5402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5402 node5402Labels = Sparse.eval nodeValue5402 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5402) = mixedMoment B node5402 node5402Labels := rfl
  simpa [nodeValue5402, Sparse.eval] using hc.symm

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5421 node5421Labels = Sparse.eval nodeValue5421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5421) = mixedMoment B node5421 node5421Labels := rfl
  simpa [nodeValue5421, Sparse.eval] using hc.symm

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5436 node5436Labels = Sparse.eval nodeValue5436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5436) = mixedMoment B node5436 node5436Labels := rfl
  simpa [nodeValue5436, Sparse.eval] using hc.symm

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
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

theorem sound5445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5445 node5445Labels = Sparse.eval nodeValue5445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5445) = mixedMoment B node5445 node5445Labels := rfl
  simpa [nodeValue5445, Sparse.eval] using hc.symm

theorem sound5446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5446 node5446Labels = Sparse.eval nodeValue5446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5446) = mixedMoment B node5446 node5446Labels := rfl
  simpa [nodeValue5446, Sparse.eval] using hc.symm

theorem sound5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = Sparse.eval nodeValue5471 (mixedVector B) := by
  simpa only [nodeValue5471, Sparse.eval_nil] using zero5471 B _hB _hF

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources31
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1001 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 0) (sourceB1001 + difference 0 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 0) (sourceB1001 + difference 0 0) sourceC1001) = raw16427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16427; decide +kernel
    rw [ha]
    exact (canonical16427 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 1) (sourceB1001 + difference 1 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 1) (sourceB1001 + difference 1 0) sourceC1001) = raw16428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16428; decide +kernel
    rw [ha]
    exact (canonical16428 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 2) (sourceB1001 + difference 2 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 2) (sourceB1001 + difference 2 0) sourceC1001) = raw16429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16429; decide +kernel
    rw [ha]
    exact (canonical16429 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 3) (sourceB1001 + difference 3 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3929) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 3) (sourceB1001 + difference 3 0) sourceC1001) = raw16430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16430; decide +kernel
    rw [ha]
    exact (canonical16430 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 4) (sourceB1001 + difference 4 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 4) (sourceB1001 + difference 4 0) sourceC1001) = raw16431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16431; decide +kernel
    rw [ha]
    exact (canonical16431 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1001 + difference 0 5) (sourceB1001 + difference 5 0) sourceC1001) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA1001 + difference 0 5) (sourceB1001 + difference 5 0) sourceC1001) = raw16432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1001 sourceB1001 sourceC1001 difference raw16432; decide +kernel
    rw [ha]
    exact (canonical16432 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1001 + sourceB1001) sourceC1001) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1001 + sourceB1001) sourceC1001) = raw16433 := by
      apply Matrix.ext; unfold doubleCharges sourceA1001 sourceB1001 sourceC1001 raw16433; decide +kernel
    rw [ha]
    exact (canonical16433 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1001 sourceB1001 sourceC1001
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1001, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1003 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 0) (sourceB1003 + difference 0 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 0) (sourceB1003 + difference 0 3) sourceC1003) = raw16438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16438; decide +kernel
    rw [ha]
    exact (canonical16438 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 1) (sourceB1003 + difference 1 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 1) (sourceB1003 + difference 1 3) sourceC1003) = raw16435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16435; decide +kernel
    rw [ha]
    exact (canonical16435 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 2) (sourceB1003 + difference 2 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 2) (sourceB1003 + difference 2 3) sourceC1003) = raw16439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16439; decide +kernel
    rw [ha]
    exact (canonical16439 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 3) (sourceB1003 + difference 3 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 3) (sourceB1003 + difference 3 3) sourceC1003) = raw16427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16427; decide +kernel
    rw [ha]
    exact (canonical16427 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 4) (sourceB1003 + difference 4 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 4) (sourceB1003 + difference 4 3) sourceC1003) = raw16440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16440; decide +kernel
    rw [ha]
    exact (canonical16440 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1003 + difference 3 5) (sourceB1003 + difference 5 3) sourceC1003) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA1003 + difference 3 5) (sourceB1003 + difference 5 3) sourceC1003) = raw16441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1003 sourceB1003 sourceC1003 difference raw16441; decide +kernel
    rw [ha]
    exact (canonical16441 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1003 + sourceB1003) sourceC1003) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1003 + sourceB1003) sourceC1003) = raw16433 := by
      apply Matrix.ext; unfold doubleCharges sourceA1003 sourceB1003 sourceC1003 raw16433; decide +kernel
    rw [ha]
    exact (canonical16433 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1003 sourceB1003 sourceC1003
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1003, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1004 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 1) (sourceB1004 + difference 1 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 1) (sourceB1004 + difference 1 0) sourceC1004) = raw16442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16442; decide +kernel
    rw [ha]
    exact (canonical16442 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 2) (sourceB1004 + difference 2 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 2) (sourceB1004 + difference 2 0) sourceC1004) = raw16443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16443; decide +kernel
    rw [ha]
    exact (canonical16443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 3) (sourceB1004 + difference 3 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 3) (sourceB1004 + difference 3 0) sourceC1004) = raw16444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16444; decide +kernel
    rw [ha]
    exact (canonical16444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 4) (sourceB1004 + difference 4 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 4) (sourceB1004 + difference 4 0) sourceC1004) = raw16445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16445; decide +kernel
    rw [ha]
    exact (canonical16445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1004 + difference 0 5) (sourceB1004 + difference 5 0) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1004 + difference 0 5) (sourceB1004 + difference 5 0) sourceC1004) = raw16446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16446; decide +kernel
    rw [ha]
    exact (canonical16446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 0) (sourceB1004 + difference 0 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 0) (sourceB1004 + difference 0 1) sourceC1004) = raw16447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16447; decide +kernel
    rw [ha]
    exact (canonical16447 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 2) (sourceB1004 + difference 2 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 2) (sourceB1004 + difference 2 1) sourceC1004) = raw16448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16448; decide +kernel
    rw [ha]
    exact (canonical16448 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 3) (sourceB1004 + difference 3 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 3) (sourceB1004 + difference 3 1) sourceC1004) = raw16449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16449; decide +kernel
    rw [ha]
    exact (canonical16449 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 4) (sourceB1004 + difference 4 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 4) (sourceB1004 + difference 4 1) sourceC1004) = raw16450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16450; decide +kernel
    rw [ha]
    exact (canonical16450 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1004 + difference 1 5) (sourceB1004 + difference 5 1) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1004 + difference 1 5) (sourceB1004 + difference 5 1) sourceC1004) = raw16451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16451; decide +kernel
    rw [ha]
    exact (canonical16451 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 0) (sourceB1004 + difference 0 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 0) (sourceB1004 + difference 0 2) sourceC1004) = raw16452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16452; decide +kernel
    rw [ha]
    exact (canonical16452 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 1) (sourceB1004 + difference 1 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 1) (sourceB1004 + difference 1 2) sourceC1004) = raw16453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16453; decide +kernel
    rw [ha]
    exact (canonical16453 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 3) (sourceB1004 + difference 3 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 3) (sourceB1004 + difference 3 2) sourceC1004) = raw16454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16454; decide +kernel
    rw [ha]
    exact (canonical16454 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 4) (sourceB1004 + difference 4 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 4) (sourceB1004 + difference 4 2) sourceC1004) = raw16455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16455; decide +kernel
    rw [ha]
    exact (canonical16455 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1004 + difference 2 5) (sourceB1004 + difference 5 2) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1004 + difference 2 5) (sourceB1004 + difference 5 2) sourceC1004) = raw16456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16456; decide +kernel
    rw [ha]
    exact (canonical16456 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 0) (sourceB1004 + difference 0 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4861) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 0) (sourceB1004 + difference 0 3) sourceC1004) = raw16457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16457; decide +kernel
    rw [ha]
    exact (canonical16457 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 1) (sourceB1004 + difference 1 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 1) (sourceB1004 + difference 1 3) sourceC1004) = raw16458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16458; decide +kernel
    rw [ha]
    exact (canonical16458 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 2) (sourceB1004 + difference 2 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5399) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 2) (sourceB1004 + difference 2 3) sourceC1004) = raw16459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16459; decide +kernel
    rw [ha]
    exact (canonical16459 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 4) (sourceB1004 + difference 4 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5385) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 4) (sourceB1004 + difference 4 3) sourceC1004) = raw16460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16460; decide +kernel
    rw [ha]
    exact (canonical16460 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1004 + difference 3 5) (sourceB1004 + difference 5 3) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1004 + difference 3 5) (sourceB1004 + difference 5 3) sourceC1004) = raw16461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16461; decide +kernel
    rw [ha]
    exact (canonical16461 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 0) (sourceB1004 + difference 0 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 0) (sourceB1004 + difference 0 4) sourceC1004) = raw16462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16462; decide +kernel
    rw [ha]
    exact (canonical16462 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 1) (sourceB1004 + difference 1 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 1) (sourceB1004 + difference 1 4) sourceC1004) = raw16463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16463; decide +kernel
    rw [ha]
    exact (canonical16463 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 2) (sourceB1004 + difference 2 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 2) (sourceB1004 + difference 2 4) sourceC1004) = raw16464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16464; decide +kernel
    rw [ha]
    exact (canonical16464 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 3) (sourceB1004 + difference 3 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 3) (sourceB1004 + difference 3 4) sourceC1004) = raw16465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16465; decide +kernel
    rw [ha]
    exact (canonical16465 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1004 + difference 4 5) (sourceB1004 + difference 5 4) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1004 + difference 4 5) (sourceB1004 + difference 5 4) sourceC1004) = raw16466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16466; decide +kernel
    rw [ha]
    exact (canonical16466 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 0) (sourceB1004 + difference 0 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 0) (sourceB1004 + difference 0 5) sourceC1004) = raw16467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16467; decide +kernel
    rw [ha]
    exact (canonical16467 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 1) (sourceB1004 + difference 1 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 1) (sourceB1004 + difference 1 5) sourceC1004) = raw16468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16468; decide +kernel
    rw [ha]
    exact (canonical16468 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 2) (sourceB1004 + difference 2 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5183) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 2) (sourceB1004 + difference 2 5) sourceC1004) = raw16469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16469; decide +kernel
    rw [ha]
    exact (canonical16469 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 3) (sourceB1004 + difference 3 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 3) (sourceB1004 + difference 3 5) sourceC1004) = raw16470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16470; decide +kernel
    rw [ha]
    exact (canonical16470 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1004 + difference 5 4) (sourceB1004 + difference 4 5) sourceC1004) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA1004 + difference 5 4) (sourceB1004 + difference 4 5) sourceC1004) = raw16471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1004 sourceB1004 sourceC1004 difference raw16471; decide +kernel
    rw [ha]
    exact (canonical16471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1004 sourceB1004 sourceC1004
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1004, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1008 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1008 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1008 + difference 0 1) (sourceB1008 + difference 1 0) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA1008 + difference 0 1) (sourceB1008 + difference 1 0) sourceC1008) = raw16539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16539; decide +kernel
    rw [ha]
    exact (canonical16539 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1008 + difference 1 1) (sourceB1008 + difference 1 1) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1008 + difference 1 1) (sourceB1008 + difference 1 1) sourceC1008) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1008 + difference 2 1) (sourceB1008 + difference 1 2) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA1008 + difference 2 1) (sourceB1008 + difference 1 2) sourceC1008) = raw16540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16540; decide +kernel
    rw [ha]
    exact (canonical16540 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1008 + difference 3 1) (sourceB1008 + difference 1 3) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA1008 + difference 3 1) (sourceB1008 + difference 1 3) sourceC1008) = raw16541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16541; decide +kernel
    rw [ha]
    exact (canonical16541 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1008 + difference 4 1) (sourceB1008 + difference 1 4) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA1008 + difference 4 1) (sourceB1008 + difference 1 4) sourceC1008) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1008 + difference 5 1) (sourceB1008 + difference 1 5) sourceC1008) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA1008 + difference 5 1) (sourceB1008 + difference 1 5) sourceC1008) = raw16543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1008 sourceB1008 sourceC1008 difference raw16543; decide +kernel
    rw [ha]
    exact (canonical16543 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1008 + sourceB1008) sourceC1008) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1008 + sourceB1008) sourceC1008) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1008 sourceB1008 sourceC1008 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1008 sourceB1008 sourceC1008
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1008, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1012 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 0) (sourceB1012 + difference 0 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 0) (sourceB1012 + difference 0 4) sourceC1012) = raw16536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16536; decide +kernel
    rw [ha]
    exact (canonical16536 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 1) (sourceB1012 + difference 1 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 1) (sourceB1012 + difference 1 4) sourceC1012) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 2) (sourceB1012 + difference 2 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 2) (sourceB1012 + difference 2 4) sourceC1012) = raw16550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16550; decide +kernel
    rw [ha]
    exact (canonical16550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 3) (sourceB1012 + difference 3 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 3) (sourceB1012 + difference 3 4) sourceC1012) = raw16554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16554; decide +kernel
    rw [ha]
    exact (canonical16554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 4) (sourceB1012 + difference 4 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 4) (sourceB1012 + difference 4 4) sourceC1012) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1012 + difference 4 5) (sourceB1012 + difference 5 4) sourceC1012) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA1012 + difference 4 5) (sourceB1012 + difference 5 4) sourceC1012) = raw16555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1012 sourceB1012 sourceC1012 difference raw16555; decide +kernel
    rw [ha]
    exact (canonical16555 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1012 + sourceB1012) sourceC1012) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1012 + sourceB1012) sourceC1012) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1012 sourceB1012 sourceC1012 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1012 sourceB1012 sourceC1012
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1012, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1013 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1013 + difference 0 4) (sourceB1013 + difference 4 0) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA1013 + difference 0 4) (sourceB1013 + difference 4 0) sourceC1013) = raw16556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16556; decide +kernel
    rw [ha]
    exact (canonical16556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1013 + difference 1 4) (sourceB1013 + difference 4 1) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA1013 + difference 1 4) (sourceB1013 + difference 4 1) sourceC1013) = raw16557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16557; decide +kernel
    rw [ha]
    exact (canonical16557 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1013 + difference 2 4) (sourceB1013 + difference 4 2) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA1013 + difference 2 4) (sourceB1013 + difference 4 2) sourceC1013) = raw16545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16545; decide +kernel
    rw [ha]
    exact (canonical16545 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1013 + difference 3 4) (sourceB1013 + difference 4 3) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA1013 + difference 3 4) (sourceB1013 + difference 4 3) sourceC1013) = raw16552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16552; decide +kernel
    rw [ha]
    exact (canonical16552 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1013 + difference 4 4) (sourceB1013 + difference 4 4) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA1013 + difference 4 4) (sourceB1013 + difference 4 4) sourceC1013) = raw16532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16532; decide +kernel
    rw [ha]
    exact (canonical16532 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1013 + difference 5 4) (sourceB1013 + difference 4 5) sourceC1013) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA1013 + difference 5 4) (sourceB1013 + difference 4 5) sourceC1013) = raw16558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1013 sourceB1013 sourceC1013 difference raw16558; decide +kernel
    rw [ha]
    exact (canonical16558 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1013 + sourceB1013) sourceC1013) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1013 + sourceB1013) sourceC1013) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA1013 sourceB1013 sourceC1013 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1013 sourceB1013 sourceC1013
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1013, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1017 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 0) (sourceB1017 + difference 0 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 0) (sourceB1017 + difference 0 0) sourceC1017) = raw15744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw15744; decide +kernel
    rw [ha]
    exact (canonical15744 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 1) (sourceB1017 + difference 1 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 1) (sourceB1017 + difference 1 0) sourceC1017) = raw15739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw15739; decide +kernel
    rw [ha]
    exact (canonical15739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 2) (sourceB1017 + difference 2 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3944) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 2) (sourceB1017 + difference 2 0) sourceC1017) = raw16210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw16210; decide +kernel
    rw [ha]
    exact (canonical16210 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 3) (sourceB1017 + difference 3 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 3) (sourceB1017 + difference 3 0) sourceC1017) = raw16596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw16596; decide +kernel
    rw [ha]
    exact (canonical16596 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 4) (sourceB1017 + difference 4 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 4) (sourceB1017 + difference 4 0) sourceC1017) = raw16597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw16597; decide +kernel
    rw [ha]
    exact (canonical16597 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1017 + difference 0 5) (sourceB1017 + difference 5 0) sourceC1017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA1017 + difference 0 5) (sourceB1017 + difference 5 0) sourceC1017) = raw16598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1017 sourceB1017 sourceC1017 difference raw16598; decide +kernel
    rw [ha]
    exact (canonical16598 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1017 + sourceB1017) sourceC1017) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1017 + sourceB1017) sourceC1017) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA1017 sourceB1017 sourceC1017 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1017 sourceB1017 sourceC1017
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1017, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck869 : Integer.Sparse.reindex keyMap MixedData.row869 = numericRow869 := by decide +kernel

theorem numericCheck869 (x : Master → ℝ) : Integer.Sparse.eval numericRow869 x =
    (1 : ℝ) * reducedSource869 x := by
  norm_num [numericRow869, reducedSource869, Integer.Sparse.eval, Sparse.eval, nodeValue2955, nodeValue3881, nodeValue3929, nodeValue3947, nodeValue3958, nodeValue3983, nodeValue4091]

theorem reindexCheck870 : Integer.Sparse.reindex keyMap MixedData.row870 = numericRow870 := by decide +kernel

theorem numericCheck870 (x : Master → ℝ) : Integer.Sparse.eval numericRow870 x =
    (1 : ℝ) * reducedSource870 x := by
  norm_num [numericRow870, reducedSource870, Integer.Sparse.eval, Sparse.eval, nodeValue2633, nodeValue3092, nodeValue3827, nodeValue3876, nodeValue3881, nodeValue3885, nodeValue4091]

theorem reindexCheck871 : Integer.Sparse.reindex keyMap MixedData.row871 = numericRow871 := by decide +kernel

theorem numericCheck871 (x : Master → ℝ) : Integer.Sparse.eval numericRow871 x =
    (2880 : ℝ) * reducedSource871 x := by
  norm_num [numericRow871, reducedSource871, Integer.Sparse.eval, Sparse.eval, nodeValue4849, nodeValue4850, nodeValue4856, nodeValue4861, nodeValue4867, nodeValue5183, nodeValue5188, nodeValue5198, nodeValue5264, nodeValue5353, nodeValue5355, nodeValue5370, nodeValue5379, nodeValue5382, nodeValue5384, nodeValue5385, nodeValue5399, nodeValue5402, nodeValue5411, nodeValue5421, nodeValue5428, nodeValue5436, nodeValue5438, nodeValue5445, nodeValue5446, nodeValue5471, nodeValue5473, nodeValue5483]
  ring

theorem reindexCheck874 : Integer.Sparse.reindex keyMap MixedData.row874 = numericRow874 := by decide +kernel

theorem numericCheck874 (x : Master → ℝ) : Integer.Sparse.eval numericRow874 x =
    (1 : ℝ) * reducedSource874 x := by
  norm_num [numericRow874, reducedSource874, Integer.Sparse.eval, Sparse.eval, nodeValue2867, nodeValue3693, nodeValue3720, nodeValue3733, nodeValue3845, nodeValue3959, nodeValue4092]

theorem reindexCheck875 : Integer.Sparse.reindex keyMap MixedData.row875 = numericRow875 := by decide +kernel

theorem numericCheck875 (x : Master → ℝ) : Integer.Sparse.eval numericRow875 x =
    (1 : ℝ) * reducedSource875 x := by
  norm_num [numericRow875, reducedSource875, Integer.Sparse.eval, Sparse.eval, nodeValue3174, nodeValue3691, nodeValue3693, nodeValue3706, nodeValue3809, nodeValue3959, nodeValue4092]

theorem reindexCheck876 : Integer.Sparse.reindex keyMap MixedData.row876 = numericRow876 := by decide +kernel

theorem numericCheck876 (x : Master → ℝ) : Integer.Sparse.eval numericRow876 x =
    (1 : ℝ) * reducedSource876 x := by
  norm_num [numericRow876, reducedSource876, Integer.Sparse.eval, Sparse.eval, nodeValue3040, nodeValue3730, nodeValue3732, nodeValue3733, nodeValue3857, nodeValue3959, nodeValue4092]

theorem reindexCheck879 : Integer.Sparse.reindex keyMap MixedData.row879 = numericRow879 := by decide +kernel

theorem numericCheck879 (x : Master → ℝ) : Integer.Sparse.eval numericRow879 x =
    (1 : ℝ) * reducedSource879 x := by
  norm_num [numericRow879, reducedSource879, Integer.Sparse.eval, Sparse.eval, nodeValue2882, nodeValue3705, nodeValue3884, nodeValue3944, nodeValue3961, nodeValue3963, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero869 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource869 (mixedVector B) = 0 := by
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3929 : mixedVector B (Sum.inr 3929) = Sparse.eval nodeValue3929 (mixedVector B) := by
    change mixedMoment B node3929 node3929Labels = _
    exact sound3929 B hB hF
  have h3947 : mixedVector B (Sum.inr 3947) = Sparse.eval nodeValue3947 (mixedVector B) := by
    change mixedMoment B node3947 node3947Labels = _
    exact sound3947 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1001, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2955, h3881, h3929, h3947, h3958, h3983, h4091, reducedSource869] using sourceEq1001 B hB

theorem rowSound869 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row869 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck869, numericCheck869, reducedZero869 B hB hF, mul_zero]

theorem reducedZero870 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource870 (mixedVector B) = 0 := by
  have h2633 : mixedVector B (Sum.inr 2633) = Sparse.eval nodeValue2633 (mixedVector B) := by
    change mixedMoment B node2633 node2633Labels = _
    exact sound2633 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3827 : mixedVector B (Sum.inr 3827) = Sparse.eval nodeValue3827 (mixedVector B) := by
    change mixedMoment B node3827 node3827Labels = _
    exact sound3827 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1003, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2633, h3092, h3827, h3876, h3881, h3885, h4091, reducedSource870] using sourceEq1003 B hB

theorem rowSound870 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row870 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck870, numericCheck870, reducedZero870 B hB hF, mul_zero]

theorem reducedZero871 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource871 (mixedVector B) = 0 := by
  have h4849 : mixedVector B (Sum.inr 4849) = Sparse.eval nodeValue4849 (mixedVector B) := by
    change mixedMoment B node4849 node4849Labels = _
    exact sound4849 B hB hF
  have h4850 : mixedVector B (Sum.inr 4850) = Sparse.eval nodeValue4850 (mixedVector B) := by
    change mixedMoment B node4850 node4850Labels = _
    exact sound4850 B hB hF
  have h4856 : mixedVector B (Sum.inr 4856) = Sparse.eval nodeValue4856 (mixedVector B) := by
    change mixedMoment B node4856 node4856Labels = _
    exact sound4856 B hB hF
  have h4861 : mixedVector B (Sum.inr 4861) = Sparse.eval nodeValue4861 (mixedVector B) := by
    change mixedMoment B node4861 node4861Labels = _
    exact sound4861 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h5183 : mixedVector B (Sum.inr 5183) = Sparse.eval nodeValue5183 (mixedVector B) := by
    change mixedMoment B node5183 node5183Labels = _
    exact sound5183 B hB hF
  have h5188 : mixedVector B (Sum.inr 5188) = Sparse.eval nodeValue5188 (mixedVector B) := by
    change mixedMoment B node5188 node5188Labels = _
    exact sound5188 B hB hF
  have h5198 : mixedVector B (Sum.inr 5198) = Sparse.eval nodeValue5198 (mixedVector B) := by
    change mixedMoment B node5198 node5198Labels = _
    exact sound5198 B hB hF
  have h5264 : mixedVector B (Sum.inr 5264) = Sparse.eval nodeValue5264 (mixedVector B) := by
    change mixedMoment B node5264 node5264Labels = _
    exact sound5264 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5382 : mixedVector B (Sum.inr 5382) = Sparse.eval nodeValue5382 (mixedVector B) := by
    change mixedMoment B node5382 node5382Labels = _
    exact sound5382 B hB hF
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5385 : mixedVector B (Sum.inr 5385) = Sparse.eval nodeValue5385 (mixedVector B) := by
    change mixedMoment B node5385 node5385Labels = _
    exact sound5385 B hB hF
  have h5399 : mixedVector B (Sum.inr 5399) = Sparse.eval nodeValue5399 (mixedVector B) := by
    change mixedMoment B node5399 node5399Labels = _
    exact sound5399 B hB hF
  have h5402 : mixedVector B (Sum.inr 5402) = Sparse.eval nodeValue5402 (mixedVector B) := by
    change mixedMoment B node5402 node5402Labels = _
    exact sound5402 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5436 : mixedVector B (Sum.inr 5436) = Sparse.eval nodeValue5436 (mixedVector B) := by
    change mixedMoment B node5436 node5436Labels = _
    exact sound5436 B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5471 : mixedVector B (Sum.inr 5471) = Sparse.eval nodeValue5471 (mixedVector B) := by
    change mixedMoment B node5471 node5471Labels = _
    exact sound5471 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  simpa only [sourceForm1004, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4849, h4850, h4856, h4861, h4867, h5183, h5188, h5198, h5264, h5353, h5355, h5370, h5379, h5382, h5384, h5385, h5399, h5402, h5411, h5421, h5428, h5436, h5438, h5445, h5446, h5471, h5473, h5483, reducedSource871] using sourceEq1004 B hB

theorem rowSound871 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row871 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck871, numericCheck871, reducedZero871 B hB hF, mul_zero]

theorem reducedZero874 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource874 (mixedVector B) = 0 := by
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h3720 : mixedVector B (Sum.inr 3720) = Sparse.eval nodeValue3720 (mixedVector B) := by
    change mixedMoment B node3720 node3720Labels = _
    exact sound3720 B hB hF
  have h3733 : mixedVector B (Sum.inr 3733) = Sparse.eval nodeValue3733 (mixedVector B) := by
    change mixedMoment B node3733 node3733Labels = _
    exact sound3733 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1008, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2867, h3693, h3720, h3733, h3845, h3959, h4092, reducedSource874] using sourceEq1008 B hB

theorem rowSound874 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row874 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck874, numericCheck874, reducedZero874 B hB hF, mul_zero]

theorem reducedZero875 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource875 (mixedVector B) = 0 := by
  have h3174 : mixedVector B (Sum.inr 3174) = Sparse.eval nodeValue3174 (mixedVector B) := by
    change mixedMoment B node3174 node3174Labels = _
    exact sound3174 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1012, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3174, h3691, h3693, h3706, h3809, h3959, h4092, reducedSource875] using sourceEq1012 B hB

theorem rowSound875 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row875 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck875, numericCheck875, reducedZero875 B hB hF, mul_zero]

theorem reducedZero876 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource876 (mixedVector B) = 0 := by
  have h3040 : mixedVector B (Sum.inr 3040) = Sparse.eval nodeValue3040 (mixedVector B) := by
    change mixedMoment B node3040 node3040Labels = _
    exact sound3040 B hB hF
  have h3730 : mixedVector B (Sum.inr 3730) = Sparse.eval nodeValue3730 (mixedVector B) := by
    change mixedMoment B node3730 node3730Labels = _
    exact sound3730 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3733 : mixedVector B (Sum.inr 3733) = Sparse.eval nodeValue3733 (mixedVector B) := by
    change mixedMoment B node3733 node3733Labels = _
    exact sound3733 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1013, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3040, h3730, h3732, h3733, h3857, h3959, h4092, reducedSource876] using sourceEq1013 B hB

theorem rowSound876 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row876 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck876, numericCheck876, reducedZero876 B hB hF, mul_zero]

theorem reducedZero879 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource879 (mixedVector B) = 0 := by
  have h2882 : mixedVector B (Sum.inr 2882) = Sparse.eval nodeValue2882 (mixedVector B) := by
    change mixedMoment B node2882 node2882Labels = _
    exact sound2882 B hB hF
  have h3705 : mixedVector B (Sum.inr 3705) = Sparse.eval nodeValue3705 (mixedVector B) := by
    change mixedMoment B node3705 node3705Labels = _
    exact sound3705 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3944 : mixedVector B (Sum.inr 3944) = Sparse.eval nodeValue3944 (mixedVector B) := by
    change mixedMoment B node3944 node3944Labels = _
    exact sound3944 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1017, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2882, h3705, h3884, h3944, h3961, h3963, h4092, reducedSource879] using sourceEq1017 B hB

theorem rowSound879 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row879 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck879, numericCheck879, reducedZero879 B hB hF, mul_zero]

theorem sourceRowsAt864 : MixedData.sourceRows (864 : Fin 2425) =
    MixedData.row864 := by decide +kernel

theorem sourceRowsAt865 : MixedData.sourceRows (865 : Fin 2425) =
    MixedData.row865 := by decide +kernel

theorem sourceRowsAt866 : MixedData.sourceRows (866 : Fin 2425) =
    MixedData.row866 := by decide +kernel

theorem sourceRowsAt867 : MixedData.sourceRows (867 : Fin 2425) =
    MixedData.row867 := by decide +kernel

theorem sourceRowsAt868 : MixedData.sourceRows (868 : Fin 2425) =
    MixedData.row868 := by decide +kernel

theorem sourceRowsAt869 : MixedData.sourceRows (869 : Fin 2425) =
    MixedData.row869 := by decide +kernel

theorem sourceRowsAt870 : MixedData.sourceRows (870 : Fin 2425) =
    MixedData.row870 := by decide +kernel

theorem sourceRowsAt871 : MixedData.sourceRows (871 : Fin 2425) =
    MixedData.row871 := by decide +kernel

theorem sourceRowsAt872 : MixedData.sourceRows (872 : Fin 2425) =
    MixedData.row872 := by decide +kernel

theorem sourceRowsAt873 : MixedData.sourceRows (873 : Fin 2425) =
    MixedData.row873 := by decide +kernel

theorem sourceRowsAt874 : MixedData.sourceRows (874 : Fin 2425) =
    MixedData.row874 := by decide +kernel

theorem sourceRowsAt875 : MixedData.sourceRows (875 : Fin 2425) =
    MixedData.row875 := by decide +kernel

theorem sourceRowsAt876 : MixedData.sourceRows (876 : Fin 2425) =
    MixedData.row876 := by decide +kernel

theorem sourceRowsAt877 : MixedData.sourceRows (877 : Fin 2425) =
    MixedData.row877 := by decide +kernel

theorem sourceRowsAt878 : MixedData.sourceRows (878 : Fin 2425) =
    MixedData.row878 := by decide +kernel

theorem sourceRowsAt879 : MixedData.sourceRows (879 : Fin 2425) =
    MixedData.row879 := by decide +kernel

theorem chunkSound54_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 54) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 864 ∨ k.val = 865 ∨ k.val = 866 ∨ k.val = 867 ∨ k.val = 868 ∨ k.val = 869 ∨ k.val = 870 ∨ k.val = 871 ∨ k.val = 872 ∨ k.val = 873 ∨ k.val = 874 ∨ k.val = 875 ∨ k.val = 876 ∨ k.val = 877 ∨ k.val = 878 ∨ k.val = 879 := by omega
  rcases heq with h864 | h865 | h866 | h867 | h868 | h869 | h870 | h871 | h872 | h873 | h874 | h875 | h876 | h877 | h878 | h879
  · have he : k = (864 : Fin 2425) := Fin.ext h864
    subst k
    rw [sourceRowsAt864]
    exact rowSound864_e B hB hF
  · have he : k = (865 : Fin 2425) := Fin.ext h865
    subst k
    rw [sourceRowsAt865]
    exact rowSound865_e B hB hF
  · have he : k = (866 : Fin 2425) := Fin.ext h866
    subst k
    rw [sourceRowsAt866]
    exact rowSound866_e B hB hF
  · have he : k = (867 : Fin 2425) := Fin.ext h867
    subst k
    rw [sourceRowsAt867]
    exact rowSound867_e B hB hF
  · have he : k = (868 : Fin 2425) := Fin.ext h868
    subst k
    rw [sourceRowsAt868]
    exact rowSound868_e B hB hF
  · have he : k = (869 : Fin 2425) := Fin.ext h869
    subst k
    rw [sourceRowsAt869]
    exact rowSound869 B hB hF
  · have he : k = (870 : Fin 2425) := Fin.ext h870
    subst k
    rw [sourceRowsAt870]
    exact rowSound870 B hB hF
  · have he : k = (871 : Fin 2425) := Fin.ext h871
    subst k
    rw [sourceRowsAt871]
    exact rowSound871 B hB hF
  · have he : k = (872 : Fin 2425) := Fin.ext h872
    subst k
    rw [sourceRowsAt872]
    exact rowSound872_e B hB hF
  · have he : k = (873 : Fin 2425) := Fin.ext h873
    subst k
    rw [sourceRowsAt873]
    exact rowSound873_e B hB hF
  · have he : k = (874 : Fin 2425) := Fin.ext h874
    subst k
    rw [sourceRowsAt874]
    exact rowSound874 B hB hF
  · have he : k = (875 : Fin 2425) := Fin.ext h875
    subst k
    rw [sourceRowsAt875]
    exact rowSound875 B hB hF
  · have he : k = (876 : Fin 2425) := Fin.ext h876
    subst k
    rw [sourceRowsAt876]
    exact rowSound876 B hB hF
  · have he : k = (877 : Fin 2425) := Fin.ext h877
    subst k
    rw [sourceRowsAt877]
    exact rowSound877_e B hB hF
  · have he : k = (878 : Fin 2425) := Fin.ext h878
    subst k
    rw [sourceRowsAt878]
    exact rowSound878_e B hB hF
  · have he : k = (879 : Fin 2425) := Fin.ext h879
    subst k
    rw [sourceRowsAt879]
    exact rowSound879 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound54_e_oai
