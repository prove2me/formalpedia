-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:41:15.096794+00:00
-- url     : https://prove2.me/submissions/e7a16c31-6b02-425d-a071-6bddd0b60d24

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero1472_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1477_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1478_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1479_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1480_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1484_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1731 raw1731Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw1731 raw1731Labels = mixedMoment B raw1731step0 raw1731step0Labels := by
      have ha : raw1731step0 = (fun i j => raw1731 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1731step0 raw1731; decide +kernel
      have hl : raw1731step0Labels = raw1731Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1731 raw1731Labels permutation152 permutation4
    mixedMoment B raw1731step0 raw1731step0Labels = mixedMoment B raw1731step1 raw1731step1Labels := by
      have ha : raw1731step1 = raw1731step0 := by apply Matrix.ext; unfold raw1731step1 raw1731step0; decide +kernel
      have hl : raw1731step0Labels = labelEmbedding7 ∘ raw1731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1731step0 raw1731step0Labels raw1731step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical1732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1732 raw1732Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw1732 raw1732Labels = mixedMoment B raw1732step0 raw1732step0Labels := by
      have ha : raw1732step0 = (fun i j => raw1732 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1732step0 raw1732; decide +kernel
      have hl : raw1732step0Labels = raw1732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1732 raw1732Labels permutation152 permutation4
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical1733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1733 raw1733Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw1733 raw1733Labels = mixedMoment B raw1733step0 raw1733step0Labels := by
      have ha : raw1733step0 = (fun i j => raw1733 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1733step0 raw1733; decide +kernel
      have hl : raw1733step0Labels = raw1733Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1733 raw1733Labels permutation160 permutation6
    mixedMoment B raw1733step0 raw1733step0Labels = mixedMoment B raw1733step1 raw1733step1Labels := by
      have ha : raw1733step1 = -raw1733step0 := by apply Matrix.ext; change ∀ i j, raw1733step1 i j = -(raw1733step0 i j); unfold raw1733step1 raw1733step0; decide +kernel
      have hl : raw1733step1Labels = raw1733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1733step1 raw1733step1Labels = mixedMoment B raw1733step2 raw1733step2Labels := by
      have ha : raw1733step2 = raw1733step1 := by apply Matrix.ext; unfold raw1733step2 raw1733step1; decide +kernel
      have hl : raw1733step1Labels = labelEmbedding1 ∘ raw1733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1733step1 raw1733step1Labels raw1733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1791 raw1791Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw1791 raw1791Labels = mixedMoment B raw1791step0 raw1791step0Labels := by
      have ha : raw1791step0 = (fun i j => raw1791 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1791step0 raw1791; decide +kernel
      have hl : raw1791step0Labels = raw1791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1791 raw1791Labels permutation32 permutation4
    mixedMoment B raw1791step0 raw1791step0Labels = mixedMoment B raw1791step1 raw1791step1Labels := by
      have ha : raw1791step1 = raw1791step0 := by apply Matrix.ext; unfold raw1791step1 raw1791step0; decide +kernel
      have hl : raw1791step0Labels = labelEmbedding7 ∘ raw1791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1791step0 raw1791step0Labels raw1791step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

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

theorem canonical1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1792 raw1792Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw1792 raw1792Labels = mixedMoment B raw1792step0 raw1792step0Labels := by
      have ha : raw1792step0 = (fun i j => raw1792 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1792step0 raw1792; decide +kernel
      have hl : raw1792step0Labels = raw1792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1792 raw1792Labels permutation32 permutation4
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1793 raw1793Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw1793 raw1793Labels = mixedMoment B raw1793step0 raw1793step0Labels := by
      have ha : raw1793step0 = (fun i j => raw1793 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1793step0 raw1793; decide +kernel
      have hl : raw1793step0Labels = raw1793Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1793 raw1793Labels permutation40 permutation6
    mixedMoment B raw1793step0 raw1793step0Labels = mixedMoment B raw1793step1 raw1793step1Labels := by
      have ha : raw1793step1 = -raw1793step0 := by apply Matrix.ext; change ∀ i j, raw1793step1 i j = -(raw1793step0 i j); unfold raw1793step1 raw1793step0; decide +kernel
      have hl : raw1793step1Labels = raw1793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1793step1 raw1793step1Labels = mixedMoment B raw1793step2 raw1793step2Labels := by
      have ha : raw1793step2 = raw1793step1 := by apply Matrix.ext; unfold raw1793step2 raw1793step1; decide +kernel
      have hl : raw1793step1Labels = labelEmbedding1 ∘ raw1793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1793step1 raw1793step1Labels raw1793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21373 raw21373Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw21373 raw21373Labels = mixedMoment B raw21373step0 raw21373step0Labels := by
      have hz : ∀ j, raw21373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21373step0 = (fun i j => raw21373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21373step0 raw21373; decide +kernel
      have hl : raw21373step0Labels = raw21373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21373 raw21373Labels permutation434 hz
    mixedMoment B raw21373step0 raw21373step0Labels = mixedMoment B raw21373step1 raw21373step1Labels := by
      have hz : ∀ j, raw21373step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21373step1 = (fun i j => raw21373step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21373step1 raw21373step0; decide +kernel
      have hl : raw21373step1Labels = raw21373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21373step0 raw21373step0Labels permutation80 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

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

theorem canonical21382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21382 raw21382Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw21382 raw21382Labels = mixedMoment B raw21382step0 raw21382step0Labels := by
      have hz : ∀ j, raw21382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21382step0 = (fun i j => raw21382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21382step0 raw21382; decide +kernel
      have hl : raw21382step0Labels = raw21382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21382 raw21382Labels permutation346 hz
    _ = mixedMoment B node4151 node4151Labels := by rfl

theorem canonical21383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21383 raw21383Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw21383 raw21383Labels = mixedMoment B raw21383step0 raw21383step0Labels := by
      have hz : ∀ j, raw21383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21383step0 = (fun i j => raw21383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21383step0 raw21383; decide +kernel
      have hl : raw21383step0Labels = raw21383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21383 raw21383Labels permutation346 hz
    _ = mixedMoment B node4365 node4365Labels := by rfl

theorem canonical21384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21384 raw21384Labels = mixedMoment B node4326 node4326Labels := by
  calc
    mixedMoment B raw21384 raw21384Labels = mixedMoment B raw21384step0 raw21384step0Labels := by
      have ha : raw21384step0 = (fun i j => raw21384 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21384step0 raw21384; decide +kernel
      have hl : raw21384step0Labels = raw21384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21384 raw21384Labels permutation176 permutation2
    _ = mixedMoment B node4326 node4326Labels := by rfl

theorem canonical21385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21385 raw21385Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21385 raw21385Labels = mixedMoment B raw21385step0 raw21385step0Labels := by
      have hz : ∀ j, raw21385 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21385step0 = (fun i j => raw21385 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21385step0 raw21385; decide +kernel
      have hl : raw21385step0Labels = raw21385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21385 raw21385Labels permutation520 hz
    mixedMoment B raw21385step0 raw21385step0Labels = mixedMoment B raw21385step1 raw21385step1Labels := by
      have hz : ∀ j, raw21385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21385step1 = (fun i j => raw21385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21385step1 raw21385step0; decide +kernel
      have hl : raw21385step1Labels = raw21385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21385step0 raw21385step0Labels permutation80 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical21429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21429 raw21429Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw21429 raw21429Labels = mixedMoment B raw21429step0 raw21429step0Labels := by
      have hz : ∀ j, raw21429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21429step0 = (fun i j => raw21429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21429step0 raw21429; decide +kernel
      have hl : raw21429step0Labels = raw21429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21429 raw21429Labels permutation434 hz
    mixedMoment B raw21429step0 raw21429step0Labels = mixedMoment B raw21429step1 raw21429step1Labels := by
      have hz : ∀ j, raw21429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21429step1 = (fun i j => raw21429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21429step1 raw21429step0; decide +kernel
      have hl : raw21429step1Labels = raw21429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21429step0 raw21429step0Labels permutation80 hz
    mixedMoment B raw21429step1 raw21429step1Labels = mixedMoment B raw21429step2 raw21429step2Labels := by
      have ha : raw21429step2 = (fun i j => raw21429step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21429step2 raw21429step1; decide +kernel
      have hl : raw21429step2Labels = raw21429step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21429step1 raw21429step1Labels permutation10 permutation7
    mixedMoment B raw21429step2 raw21429step2Labels = mixedMoment B raw21429step3 raw21429step3Labels := by
      have ha : raw21429step3 = -raw21429step2 := by apply Matrix.ext; change ∀ i j, raw21429step3 i j = -(raw21429step2 i j); unfold raw21429step3 raw21429step2; decide +kernel
      have hl : raw21429step3Labels = raw21429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21429step3 raw21429step3Labels = mixedMoment B raw21429step4 raw21429step4Labels := by
      have ha : raw21429step4 = raw21429step3 := by apply Matrix.ext; unfold raw21429step4 raw21429step3; decide +kernel
      have hl : raw21429step3Labels = labelEmbedding1 ∘ raw21429step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21429step3 raw21429step3Labels raw21429step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical21434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21434 raw21434Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21434 raw21434Labels = mixedMoment B raw21434step0 raw21434step0Labels := by
      have hz : ∀ j, raw21434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21434step0 = (fun i j => raw21434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21434step0 raw21434; decide +kernel
      have hl : raw21434step0Labels = raw21434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21434 raw21434Labels permutation434 hz
    mixedMoment B raw21434step0 raw21434step0Labels = mixedMoment B raw21434step1 raw21434step1Labels := by
      have hz : ∀ j, raw21434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21434step1 = (fun i j => raw21434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21434step1 raw21434step0; decide +kernel
      have hl : raw21434step1Labels = raw21434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21434step0 raw21434step0Labels permutation80 hz
    mixedMoment B raw21434step1 raw21434step1Labels = mixedMoment B raw21434step2 raw21434step2Labels := by
      have ha : raw21434step2 = (fun i j => raw21434step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21434step2 raw21434step1; decide +kernel
      have hl : raw21434step2Labels = raw21434step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21434step1 raw21434step1Labels permutation10 permutation7
    mixedMoment B raw21434step2 raw21434step2Labels = mixedMoment B raw21434step3 raw21434step3Labels := by
      have ha : raw21434step3 = -raw21434step2 := by apply Matrix.ext; change ∀ i j, raw21434step3 i j = -(raw21434step2 i j); unfold raw21434step3 raw21434step2; decide +kernel
      have hl : raw21434step3Labels = raw21434step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21434step3 raw21434step3Labels = mixedMoment B raw21434step4 raw21434step4Labels := by
      have ha : raw21434step4 = raw21434step3 := by apply Matrix.ext; unfold raw21434step4 raw21434step3; decide +kernel
      have hl : raw21434step3Labels = labelEmbedding1 ∘ raw21434step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21434step3 raw21434step3Labels raw21434step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical21439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21439 raw21439Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw21439 raw21439Labels = mixedMoment B raw21439step0 raw21439step0Labels := by
      have hz : ∀ j, raw21439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21439step0 = (fun i j => raw21439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21439step0 raw21439; decide +kernel
      have hl : raw21439step0Labels = raw21439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21439 raw21439Labels permutation434 hz
    mixedMoment B raw21439step0 raw21439step0Labels = mixedMoment B raw21439step1 raw21439step1Labels := by
      have ha : raw21439step1 = (fun i j => raw21439step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21439step1 raw21439step0; decide +kernel
      have hl : raw21439step1Labels = raw21439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21439step0 raw21439step0Labels permutation40 permutation7
    mixedMoment B raw21439step1 raw21439step1Labels = mixedMoment B raw21439step2 raw21439step2Labels := by
      have ha : raw21439step2 = -raw21439step1 := by apply Matrix.ext; change ∀ i j, raw21439step2 i j = -(raw21439step1 i j); unfold raw21439step2 raw21439step1; decide +kernel
      have hl : raw21439step2Labels = raw21439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21439step2 raw21439step2Labels = mixedMoment B raw21439step3 raw21439step3Labels := by
      have ha : raw21439step3 = raw21439step2 := by apply Matrix.ext; unfold raw21439step3 raw21439step2; decide +kernel
      have hl : raw21439step2Labels = labelEmbedding1 ∘ raw21439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21439step2 raw21439step2Labels raw21439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical21440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21440 raw21440Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw21440 raw21440Labels = mixedMoment B raw21440step0 raw21440step0Labels := by
      have hz : ∀ j, raw21440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21440step0 = (fun i j => raw21440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21440step0 raw21440; decide +kernel
      have hl : raw21440step0Labels = raw21440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21440 raw21440Labels permutation346 hz
    mixedMoment B raw21440step0 raw21440step0Labels = mixedMoment B raw21440step1 raw21440step1Labels := by
      have ha : raw21440step1 = (fun i j => raw21440step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21440step1 raw21440step0; decide +kernel
      have hl : raw21440step1Labels = raw21440step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21440step0 raw21440step0Labels permutation40 permutation7
    mixedMoment B raw21440step1 raw21440step1Labels = mixedMoment B raw21440step2 raw21440step2Labels := by
      have ha : raw21440step2 = -raw21440step1 := by apply Matrix.ext; change ∀ i j, raw21440step2 i j = -(raw21440step1 i j); unfold raw21440step2 raw21440step1; decide +kernel
      have hl : raw21440step2Labels = raw21440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21440step2 raw21440step2Labels = mixedMoment B raw21440step3 raw21440step3Labels := by
      have ha : raw21440step3 = raw21440step2 := by apply Matrix.ext; unfold raw21440step3 raw21440step2; decide +kernel
      have hl : raw21440step2Labels = labelEmbedding1 ∘ raw21440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21440step2 raw21440step2Labels raw21440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

theorem canonical21441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21441 raw21441Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw21441 raw21441Labels = mixedMoment B raw21441step0 raw21441step0Labels := by
      have hz : ∀ j, raw21441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21441step0 = (fun i j => raw21441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21441step0 raw21441; decide +kernel
      have hl : raw21441step0Labels = raw21441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21441 raw21441Labels permutation346 hz
    mixedMoment B raw21441step0 raw21441step0Labels = mixedMoment B raw21441step1 raw21441step1Labels := by
      have ha : raw21441step1 = (fun i j => raw21441step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21441step1 raw21441step0; decide +kernel
      have hl : raw21441step1Labels = raw21441step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21441step0 raw21441step0Labels permutation40 permutation7
    mixedMoment B raw21441step1 raw21441step1Labels = mixedMoment B raw21441step2 raw21441step2Labels := by
      have ha : raw21441step2 = -raw21441step1 := by apply Matrix.ext; change ∀ i j, raw21441step2 i j = -(raw21441step1 i j); unfold raw21441step2 raw21441step1; decide +kernel
      have hl : raw21441step2Labels = raw21441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21441step2 raw21441step2Labels = mixedMoment B raw21441step3 raw21441step3Labels := by
      have ha : raw21441step3 = raw21441step2 := by apply Matrix.ext; unfold raw21441step3 raw21441step2; decide +kernel
      have hl : raw21441step2Labels = labelEmbedding1 ∘ raw21441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21441step2 raw21441step2Labels raw21441step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

theorem canonical21442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21442 raw21442Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw21442 raw21442Labels = mixedMoment B raw21442step0 raw21442step0Labels := by
      have ha : raw21442step0 = (fun i j => raw21442 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21442step0 raw21442; decide +kernel
      have hl : raw21442step0Labels = raw21442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21442 raw21442Labels permutation184 permutation7
    mixedMoment B raw21442step0 raw21442step0Labels = mixedMoment B raw21442step1 raw21442step1Labels := by
      have ha : raw21442step1 = -raw21442step0 := by apply Matrix.ext; change ∀ i j, raw21442step1 i j = -(raw21442step0 i j); unfold raw21442step1 raw21442step0; decide +kernel
      have hl : raw21442step1Labels = raw21442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21442step1 raw21442step1Labels = mixedMoment B raw21442step2 raw21442step2Labels := by
      have ha : raw21442step2 = raw21442step1 := by apply Matrix.ext; unfold raw21442step2 raw21442step1; decide +kernel
      have hl : raw21442step1Labels = labelEmbedding1 ∘ raw21442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21442step1 raw21442step1Labels raw21442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

theorem canonical21443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21443 raw21443Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21443 raw21443Labels = mixedMoment B raw21443step0 raw21443step0Labels := by
      have hz : ∀ j, raw21443 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21443step0 = (fun i j => raw21443 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21443step0 raw21443; decide +kernel
      have hl : raw21443step0Labels = raw21443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21443 raw21443Labels permutation520 hz
    mixedMoment B raw21443step0 raw21443step0Labels = mixedMoment B raw21443step1 raw21443step1Labels := by
      have hz : ∀ j, raw21443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21443step1 = (fun i j => raw21443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21443step1 raw21443step0; decide +kernel
      have hl : raw21443step1Labels = raw21443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21443step0 raw21443step0Labels permutation80 hz
    mixedMoment B raw21443step1 raw21443step1Labels = mixedMoment B raw21443step2 raw21443step2Labels := by
      have ha : raw21443step2 = (fun i j => raw21443step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21443step2 raw21443step1; decide +kernel
      have hl : raw21443step2Labels = raw21443step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21443step1 raw21443step1Labels permutation10 permutation7
    mixedMoment B raw21443step2 raw21443step2Labels = mixedMoment B raw21443step3 raw21443step3Labels := by
      have ha : raw21443step3 = -raw21443step2 := by apply Matrix.ext; change ∀ i j, raw21443step3 i j = -(raw21443step2 i j); unfold raw21443step3 raw21443step2; decide +kernel
      have hl : raw21443step3Labels = raw21443step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21443step3 raw21443step3Labels = mixedMoment B raw21443step4 raw21443step4Labels := by
      have ha : raw21443step4 = raw21443step3 := by apply Matrix.ext; unfold raw21443step4 raw21443step3; decide +kernel
      have hl : raw21443step3Labels = labelEmbedding1 ∘ raw21443step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21443step3 raw21443step3Labels raw21443step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical21449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21449 raw21449Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw21449 raw21449Labels = mixedMoment B raw21449step0 raw21449step0Labels := by
      have hz : ∀ j, raw21449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21449step0 = (fun i j => raw21449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21449step0 raw21449; decide +kernel
      have hl : raw21449step0Labels = raw21449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21449 raw21449Labels permutation434 hz
    mixedMoment B raw21449step0 raw21449step0Labels = mixedMoment B raw21449step1 raw21449step1Labels := by
      have hz : ∀ j, raw21449step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21449step1 = (fun i j => raw21449step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21449step1 raw21449step0; decide +kernel
      have hl : raw21449step1Labels = raw21449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21449step0 raw21449step0Labels permutation80 hz
    mixedMoment B raw21449step1 raw21449step1Labels = mixedMoment B raw21449step2 raw21449step2Labels := by
      have ha : raw21449step2 = (fun i j => raw21449step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21449step2 raw21449step1; decide +kernel
      have hl : raw21449step2Labels = raw21449step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21449step1 raw21449step1Labels permutation10 permutation7
    mixedMoment B raw21449step2 raw21449step2Labels = mixedMoment B raw21449step3 raw21449step3Labels := by
      have ha : raw21449step3 = -raw21449step2 := by apply Matrix.ext; change ∀ i j, raw21449step3 i j = -(raw21449step2 i j); unfold raw21449step3 raw21449step2; decide +kernel
      have hl : raw21449step3Labels = raw21449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21449step3 raw21449step3Labels = mixedMoment B raw21449step4 raw21449step4Labels := by
      have ha : raw21449step4 = raw21449step3 := by apply Matrix.ext; unfold raw21449step4 raw21449step3; decide +kernel
      have hl : raw21449step3Labels = labelEmbedding1 ∘ raw21449step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21449step3 raw21449step3Labels raw21449step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical21458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21458 raw21458Labels = mixedMoment B node579 node579Labels := by
  calc
    mixedMoment B raw21458 raw21458Labels = mixedMoment B raw21458step0 raw21458step0Labels := by
      have hz : ∀ j, raw21458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21458step0 = (fun i j => raw21458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21458step0 raw21458; decide +kernel
      have hl : raw21458step0Labels = raw21458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21458 raw21458Labels permutation346 hz
    _ = mixedMoment B node579 node579Labels := by rfl

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

theorem canonical21465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21465 raw21465Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw21465 raw21465Labels = mixedMoment B raw21465step0 raw21465step0Labels := by
      have hz : ∀ j, raw21465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21465step0 = (fun i j => raw21465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21465step0 raw21465; decide +kernel
      have hl : raw21465step0Labels = raw21465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21465 raw21465Labels permutation434 hz
    mixedMoment B raw21465step0 raw21465step0Labels = mixedMoment B raw21465step1 raw21465step1Labels := by
      have hz : ∀ j, raw21465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21465step1 = (fun i j => raw21465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21465step1 raw21465step0; decide +kernel
      have hl : raw21465step1Labels = raw21465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21465step0 raw21465step0Labels permutation80 hz
    mixedMoment B raw21465step1 raw21465step1Labels = mixedMoment B raw21465step2 raw21465step2Labels := by
      have ha : raw21465step2 = (fun i j => raw21465step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21465step2 raw21465step1; decide +kernel
      have hl : raw21465step2Labels = raw21465step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21465step1 raw21465step1Labels permutation10 permutation2
    _ = mixedMoment B node1082 node1082Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical196
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25195 raw25195Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw25195 raw25195Labels = mixedMoment B raw25195step0 raw25195step0Labels := by
      have hz : ∀ j, raw25195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25195step0 = (fun i j => raw25195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25195step0 raw25195; decide +kernel
      have hl : raw25195step0Labels = raw25195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25195 raw25195Labels permutation346 hz
    mixedMoment B raw25195step0 raw25195step0Labels = mixedMoment B raw25195step1 raw25195step1Labels := by
      have ha : raw25195step1 = (fun i j => raw25195step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25195step1 raw25195step0; decide +kernel
      have hl : raw25195step1Labels = raw25195step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25195step0 raw25195step0Labels permutation44 permutation7
    mixedMoment B raw25195step1 raw25195step1Labels = mixedMoment B raw25195step2 raw25195step2Labels := by
      have ha : raw25195step2 = -raw25195step1 := by apply Matrix.ext; change ∀ i j, raw25195step2 i j = -(raw25195step1 i j); unfold raw25195step2 raw25195step1; decide +kernel
      have hl : raw25195step2Labels = raw25195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25195step2 raw25195step2Labels = mixedMoment B raw25195step3 raw25195step3Labels := by
      have ha : raw25195step3 = raw25195step2 := by apply Matrix.ext; unfold raw25195step3 raw25195step2; decide +kernel
      have hl : raw25195step2Labels = labelEmbedding1 ∘ raw25195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25195step2 raw25195step2Labels raw25195step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical25196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25196 raw25196Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25196 raw25196Labels = mixedMoment B raw25196step0 raw25196step0Labels := by
      have ha : raw25196step0 = (fun i j => raw25196 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25196step0 raw25196; decide +kernel
      have hl : raw25196step0Labels = raw25196Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25196 raw25196Labels permutation188 permutation7
    mixedMoment B raw25196step0 raw25196step0Labels = mixedMoment B raw25196step1 raw25196step1Labels := by
      have ha : raw25196step1 = -raw25196step0 := by apply Matrix.ext; change ∀ i j, raw25196step1 i j = -(raw25196step0 i j); unfold raw25196step1 raw25196step0; decide +kernel
      have hl : raw25196step1Labels = raw25196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25196step1 raw25196step1Labels = mixedMoment B raw25196step2 raw25196step2Labels := by
      have ha : raw25196step2 = raw25196step1 := by apply Matrix.ext; unfold raw25196step2 raw25196step1; decide +kernel
      have hl : raw25196step1Labels = labelEmbedding1 ∘ raw25196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25196step1 raw25196step1Labels raw25196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical25197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25197 raw25197Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw25197 raw25197Labels = mixedMoment B raw25197step0 raw25197step0Labels := by
      have hz : ∀ j, raw25197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25197step0 = (fun i j => raw25197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25197step0 raw25197; decide +kernel
      have hl : raw25197step0Labels = raw25197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25197 raw25197Labels permutation346 hz
    mixedMoment B raw25197step0 raw25197step0Labels = mixedMoment B raw25197step1 raw25197step1Labels := by
      have ha : raw25197step1 = (fun i j => raw25197step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25197step1 raw25197step0; decide +kernel
      have hl : raw25197step1Labels = raw25197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25197step0 raw25197step0Labels permutation44 permutation7
    mixedMoment B raw25197step1 raw25197step1Labels = mixedMoment B raw25197step2 raw25197step2Labels := by
      have ha : raw25197step2 = -raw25197step1 := by apply Matrix.ext; change ∀ i j, raw25197step2 i j = -(raw25197step1 i j); unfold raw25197step2 raw25197step1; decide +kernel
      have hl : raw25197step2Labels = raw25197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25197step2 raw25197step2Labels = mixedMoment B raw25197step3 raw25197step3Labels := by
      have ha : raw25197step3 = raw25197step2 := by apply Matrix.ext; unfold raw25197step3 raw25197step2; decide +kernel
      have hl : raw25197step2Labels = labelEmbedding1 ∘ raw25197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25197step2 raw25197step2Labels raw25197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical25198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25198 raw25198Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw25198 raw25198Labels = mixedMoment B raw25198step0 raw25198step0Labels := by
      have hz : ∀ j, raw25198 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25198step0 = (fun i j => raw25198 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25198step0 raw25198; decide +kernel
      have hl : raw25198step0Labels = raw25198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25198 raw25198Labels permutation520 hz
    mixedMoment B raw25198step0 raw25198step0Labels = mixedMoment B raw25198step1 raw25198step1Labels := by
      have hz : ∀ j, raw25198step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25198step1 = (fun i j => raw25198step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25198step1 raw25198step0; decide +kernel
      have hl : raw25198step1Labels = raw25198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25198step0 raw25198step0Labels permutation80 hz
    mixedMoment B raw25198step1 raw25198step1Labels = mixedMoment B raw25198step2 raw25198step2Labels := by
      have ha : raw25198step2 = (fun i j => raw25198step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25198step2 raw25198step1; decide +kernel
      have hl : raw25198step2Labels = raw25198step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25198step1 raw25198step1Labels permutation8 permutation7
    mixedMoment B raw25198step2 raw25198step2Labels = mixedMoment B raw25198step3 raw25198step3Labels := by
      have ha : raw25198step3 = -raw25198step2 := by apply Matrix.ext; change ∀ i j, raw25198step3 i j = -(raw25198step2 i j); unfold raw25198step3 raw25198step2; decide +kernel
      have hl : raw25198step3Labels = raw25198step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25198step3 raw25198step3Labels = mixedMoment B raw25198step4 raw25198step4Labels := by
      have ha : raw25198step4 = raw25198step3 := by apply Matrix.ext; unfold raw25198step4 raw25198step3; decide +kernel
      have hl : raw25198step3Labels = labelEmbedding1 ∘ raw25198step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25198step3 raw25198step3Labels raw25198step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical25199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25199 raw25199Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw25199 raw25199Labels = mixedMoment B raw25199step0 raw25199step0Labels := by
      have hz : ∀ j, raw25199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25199step0 = (fun i j => raw25199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25199step0 raw25199; decide +kernel
      have hl : raw25199step0Labels = raw25199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25199 raw25199Labels permutation346 hz
    mixedMoment B raw25199step0 raw25199step0Labels = mixedMoment B raw25199step1 raw25199step1Labels := by
      have ha : raw25199step1 = (fun i j => raw25199step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25199step1 raw25199step0; decide +kernel
      have hl : raw25199step1Labels = raw25199step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25199step0 raw25199step0Labels permutation44 permutation7
    mixedMoment B raw25199step1 raw25199step1Labels = mixedMoment B raw25199step2 raw25199step2Labels := by
      have ha : raw25199step2 = -raw25199step1 := by apply Matrix.ext; change ∀ i j, raw25199step2 i j = -(raw25199step1 i j); unfold raw25199step2 raw25199step1; decide +kernel
      have hl : raw25199step2Labels = raw25199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25199step2 raw25199step2Labels = mixedMoment B raw25199step3 raw25199step3Labels := by
      have ha : raw25199step3 = raw25199step2 := by apply Matrix.ext; unfold raw25199step3 raw25199step2; decide +kernel
      have hl : raw25199step2Labels = labelEmbedding1 ∘ raw25199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25199step2 raw25199step2Labels raw25199step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical25200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25200 raw25200Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw25200 raw25200Labels = mixedMoment B raw25200step0 raw25200step0Labels := by
      have hz : ∀ j, raw25200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25200step0 = (fun i j => raw25200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25200step0 raw25200; decide +kernel
      have hl : raw25200step0Labels = raw25200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25200 raw25200Labels permutation346 hz
    mixedMoment B raw25200step0 raw25200step0Labels = mixedMoment B raw25200step1 raw25200step1Labels := by
      have ha : raw25200step1 = (fun i j => raw25200step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25200step1 raw25200step0; decide +kernel
      have hl : raw25200step1Labels = raw25200step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25200step0 raw25200step0Labels permutation44 permutation7
    mixedMoment B raw25200step1 raw25200step1Labels = mixedMoment B raw25200step2 raw25200step2Labels := by
      have ha : raw25200step2 = -raw25200step1 := by apply Matrix.ext; change ∀ i j, raw25200step2 i j = -(raw25200step1 i j); unfold raw25200step2 raw25200step1; decide +kernel
      have hl : raw25200step2Labels = raw25200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25200step2 raw25200step2Labels = mixedMoment B raw25200step3 raw25200step3Labels := by
      have ha : raw25200step3 = raw25200step2 := by apply Matrix.ext; unfold raw25200step3 raw25200step2; decide +kernel
      have hl : raw25200step2Labels = labelEmbedding1 ∘ raw25200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25200step2 raw25200step2Labels raw25200step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1517 node1517Labels := by rfl

theorem canonical25201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25201 raw25201Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw25201 raw25201Labels = mixedMoment B raw25201step0 raw25201step0Labels := by
      have ha : raw25201step0 = (fun i j => raw25201 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25201step0 raw25201; decide +kernel
      have hl : raw25201step0Labels = raw25201Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25201 raw25201Labels permutation188 permutation7
    mixedMoment B raw25201step0 raw25201step0Labels = mixedMoment B raw25201step1 raw25201step1Labels := by
      have ha : raw25201step1 = -raw25201step0 := by apply Matrix.ext; change ∀ i j, raw25201step1 i j = -(raw25201step0 i j); unfold raw25201step1 raw25201step0; decide +kernel
      have hl : raw25201step1Labels = raw25201step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25201step1 raw25201step1Labels = mixedMoment B raw25201step2 raw25201step2Labels := by
      have ha : raw25201step2 = raw25201step1 := by apply Matrix.ext; unfold raw25201step2 raw25201step1; decide +kernel
      have hl : raw25201step1Labels = labelEmbedding1 ∘ raw25201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25201step1 raw25201step1Labels raw25201step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

theorem canonical25202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25202 raw25202Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25202 raw25202Labels = mixedMoment B raw25202step0 raw25202step0Labels := by
      have hz : ∀ j, raw25202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25202step0 = (fun i j => raw25202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25202step0 raw25202; decide +kernel
      have hl : raw25202step0Labels = raw25202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25202 raw25202Labels permutation346 hz
    mixedMoment B raw25202step0 raw25202step0Labels = mixedMoment B raw25202step1 raw25202step1Labels := by
      have ha : raw25202step1 = (fun i j => raw25202step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25202step1 raw25202step0; decide +kernel
      have hl : raw25202step1Labels = raw25202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25202step0 raw25202step0Labels permutation46 permutation7
    mixedMoment B raw25202step1 raw25202step1Labels = mixedMoment B raw25202step2 raw25202step2Labels := by
      have ha : raw25202step2 = -raw25202step1 := by apply Matrix.ext; change ∀ i j, raw25202step2 i j = -(raw25202step1 i j); unfold raw25202step2 raw25202step1; decide +kernel
      have hl : raw25202step2Labels = raw25202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25202step2 raw25202step2Labels = mixedMoment B raw25202step3 raw25202step3Labels := by
      have ha : raw25202step3 = raw25202step2 := by apply Matrix.ext; unfold raw25202step3 raw25202step2; decide +kernel
      have hl : raw25202step2Labels = labelEmbedding1 ∘ raw25202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25202step2 raw25202step2Labels raw25202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical25203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25203 raw25203Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw25203 raw25203Labels = mixedMoment B raw25203step0 raw25203step0Labels := by
      have hz : ∀ j, raw25203 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25203step0 = (fun i j => raw25203 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25203step0 raw25203; decide +kernel
      have hl : raw25203step0Labels = raw25203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25203 raw25203Labels permutation520 hz
    mixedMoment B raw25203step0 raw25203step0Labels = mixedMoment B raw25203step1 raw25203step1Labels := by
      have hz : ∀ j, raw25203step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25203step1 = (fun i j => raw25203step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25203step1 raw25203step0; decide +kernel
      have hl : raw25203step1Labels = raw25203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25203step0 raw25203step0Labels permutation80 hz
    mixedMoment B raw25203step1 raw25203step1Labels = mixedMoment B raw25203step2 raw25203step2Labels := by
      have ha : raw25203step2 = (fun i j => raw25203step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25203step2 raw25203step1; decide +kernel
      have hl : raw25203step2Labels = raw25203step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25203step1 raw25203step1Labels permutation8 permutation7
    mixedMoment B raw25203step2 raw25203step2Labels = mixedMoment B raw25203step3 raw25203step3Labels := by
      have ha : raw25203step3 = -raw25203step2 := by apply Matrix.ext; change ∀ i j, raw25203step3 i j = -(raw25203step2 i j); unfold raw25203step3 raw25203step2; decide +kernel
      have hl : raw25203step3Labels = raw25203step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25203step3 raw25203step3Labels = mixedMoment B raw25203step4 raw25203step4Labels := by
      have ha : raw25203step4 = raw25203step3 := by apply Matrix.ext; unfold raw25203step4 raw25203step3; decide +kernel
      have hl : raw25203step3Labels = labelEmbedding1 ∘ raw25203step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25203step3 raw25203step3Labels raw25203step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1753 node1753Labels := by rfl

theorem canonical25204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25204 raw25204Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw25204 raw25204Labels = mixedMoment B raw25204step0 raw25204step0Labels := by
      have hz : ∀ j, raw25204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25204step0 = (fun i j => raw25204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25204step0 raw25204; decide +kernel
      have hl : raw25204step0Labels = raw25204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25204 raw25204Labels permutation346 hz
    mixedMoment B raw25204step0 raw25204step0Labels = mixedMoment B raw25204step1 raw25204step1Labels := by
      have ha : raw25204step1 = (fun i j => raw25204step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25204step1 raw25204step0; decide +kernel
      have hl : raw25204step1Labels = raw25204step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25204step0 raw25204step0Labels permutation44 permutation7
    mixedMoment B raw25204step1 raw25204step1Labels = mixedMoment B raw25204step2 raw25204step2Labels := by
      have ha : raw25204step2 = -raw25204step1 := by apply Matrix.ext; change ∀ i j, raw25204step2 i j = -(raw25204step1 i j); unfold raw25204step2 raw25204step1; decide +kernel
      have hl : raw25204step2Labels = raw25204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25204step2 raw25204step2Labels = mixedMoment B raw25204step3 raw25204step3Labels := by
      have ha : raw25204step3 = raw25204step2 := by apply Matrix.ext; unfold raw25204step3 raw25204step2; decide +kernel
      have hl : raw25204step2Labels = labelEmbedding1 ∘ raw25204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25204step2 raw25204step2Labels raw25204step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1726 node1726Labels := by rfl

theorem canonical25205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25205 raw25205Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw25205 raw25205Labels = mixedMoment B raw25205step0 raw25205step0Labels := by
      have ha : raw25205step0 = (fun i j => raw25205 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25205step0 raw25205; decide +kernel
      have hl : raw25205step0Labels = raw25205Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25205 raw25205Labels permutation188 permutation7
    mixedMoment B raw25205step0 raw25205step0Labels = mixedMoment B raw25205step1 raw25205step1Labels := by
      have ha : raw25205step1 = -raw25205step0 := by apply Matrix.ext; change ∀ i j, raw25205step1 i j = -(raw25205step0 i j); unfold raw25205step1 raw25205step0; decide +kernel
      have hl : raw25205step1Labels = raw25205step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25205step1 raw25205step1Labels = mixedMoment B raw25205step2 raw25205step2Labels := by
      have ha : raw25205step2 = raw25205step1 := by apply Matrix.ext; unfold raw25205step2 raw25205step1; decide +kernel
      have hl : raw25205step1Labels = labelEmbedding1 ∘ raw25205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25205step1 raw25205step1Labels raw25205step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical25206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25206 raw25206Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw25206 raw25206Labels = mixedMoment B raw25206step0 raw25206step0Labels := by
      have ha : raw25206step0 = (fun i j => raw25206 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25206step0 raw25206; decide +kernel
      have hl : raw25206step0Labels = raw25206Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25206 raw25206Labels permutation188 permutation7
    mixedMoment B raw25206step0 raw25206step0Labels = mixedMoment B raw25206step1 raw25206step1Labels := by
      have ha : raw25206step1 = -raw25206step0 := by apply Matrix.ext; change ∀ i j, raw25206step1 i j = -(raw25206step0 i j); unfold raw25206step1 raw25206step0; decide +kernel
      have hl : raw25206step1Labels = raw25206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25206step1 raw25206step1Labels = mixedMoment B raw25206step2 raw25206step2Labels := by
      have ha : raw25206step2 = raw25206step1 := by apply Matrix.ext; unfold raw25206step2 raw25206step1; decide +kernel
      have hl : raw25206step1Labels = labelEmbedding1 ∘ raw25206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25206step1 raw25206step1Labels raw25206step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

theorem canonical25207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25207 raw25207Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw25207 raw25207Labels = mixedMoment B raw25207step0 raw25207step0Labels := by
      have ha : raw25207step0 = (fun i j => raw25207 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25207step0 raw25207; decide +kernel
      have hl : raw25207step0Labels = raw25207Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25207 raw25207Labels permutation188 permutation7
    mixedMoment B raw25207step0 raw25207step0Labels = mixedMoment B raw25207step1 raw25207step1Labels := by
      have ha : raw25207step1 = -raw25207step0 := by apply Matrix.ext; change ∀ i j, raw25207step1 i j = -(raw25207step0 i j); unfold raw25207step1 raw25207step0; decide +kernel
      have hl : raw25207step1Labels = raw25207step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25207step1 raw25207step1Labels = mixedMoment B raw25207step2 raw25207step2Labels := by
      have ha : raw25207step2 = raw25207step1 := by apply Matrix.ext; unfold raw25207step2 raw25207step1; decide +kernel
      have hl : raw25207step1Labels = labelEmbedding1 ∘ raw25207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25207step1 raw25207step1Labels raw25207step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

theorem canonical25208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25208 raw25208Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25208 raw25208Labels = mixedMoment B raw25208step0 raw25208step0Labels := by
      have hz : ∀ j, raw25208 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25208step0 = (fun i j => raw25208 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25208step0 raw25208; decide +kernel
      have hl : raw25208step0Labels = raw25208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25208 raw25208Labels permutation520 hz
    mixedMoment B raw25208step0 raw25208step0Labels = mixedMoment B raw25208step1 raw25208step1Labels := by
      have ha : raw25208step1 = (fun i j => raw25208step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25208step1 raw25208step0; decide +kernel
      have hl : raw25208step1Labels = raw25208step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25208step0 raw25208step0Labels permutation38 permutation7
    mixedMoment B raw25208step1 raw25208step1Labels = mixedMoment B raw25208step2 raw25208step2Labels := by
      have ha : raw25208step2 = -raw25208step1 := by apply Matrix.ext; change ∀ i j, raw25208step2 i j = -(raw25208step1 i j); unfold raw25208step2 raw25208step1; decide +kernel
      have hl : raw25208step2Labels = raw25208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25208step2 raw25208step2Labels = mixedMoment B raw25208step3 raw25208step3Labels := by
      have ha : raw25208step3 = raw25208step2 := by apply Matrix.ext; unfold raw25208step3 raw25208step2; decide +kernel
      have hl : raw25208step2Labels = labelEmbedding1 ∘ raw25208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25208step2 raw25208step2Labels raw25208step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical25209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25209 raw25209Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw25209 raw25209Labels = mixedMoment B raw25209step0 raw25209step0Labels := by
      have ha : raw25209step0 = (fun i j => raw25209 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25209step0 raw25209; decide +kernel
      have hl : raw25209step0Labels = raw25209Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25209 raw25209Labels permutation188 permutation7
    mixedMoment B raw25209step0 raw25209step0Labels = mixedMoment B raw25209step1 raw25209step1Labels := by
      have ha : raw25209step1 = -raw25209step0 := by apply Matrix.ext; change ∀ i j, raw25209step1 i j = -(raw25209step0 i j); unfold raw25209step1 raw25209step0; decide +kernel
      have hl : raw25209step1Labels = raw25209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25209step1 raw25209step1Labels = mixedMoment B raw25209step2 raw25209step2Labels := by
      have ha : raw25209step2 = raw25209step1 := by apply Matrix.ext; unfold raw25209step2 raw25209step1; decide +kernel
      have hl : raw25209step1Labels = labelEmbedding1 ∘ raw25209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25209step1 raw25209step1Labels raw25209step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical25210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25210 raw25210Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw25210 raw25210Labels = mixedMoment B raw25210step0 raw25210step0Labels := by
      have hz : ∀ j, raw25210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25210step0 = (fun i j => raw25210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25210step0 raw25210; decide +kernel
      have hl : raw25210step0Labels = raw25210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25210 raw25210Labels permutation346 hz
    mixedMoment B raw25210step0 raw25210step0Labels = mixedMoment B raw25210step1 raw25210step1Labels := by
      have ha : raw25210step1 = (fun i j => raw25210step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25210step1 raw25210step0; decide +kernel
      have hl : raw25210step1Labels = raw25210step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25210step0 raw25210step0Labels permutation44 permutation7
    mixedMoment B raw25210step1 raw25210step1Labels = mixedMoment B raw25210step2 raw25210step2Labels := by
      have ha : raw25210step2 = -raw25210step1 := by apply Matrix.ext; change ∀ i j, raw25210step2 i j = -(raw25210step1 i j); unfold raw25210step2 raw25210step1; decide +kernel
      have hl : raw25210step2Labels = raw25210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25210step2 raw25210step2Labels = mixedMoment B raw25210step3 raw25210step3Labels := by
      have ha : raw25210step3 = raw25210step2 := by apply Matrix.ext; unfold raw25210step3 raw25210step2; decide +kernel
      have hl : raw25210step2Labels = labelEmbedding1 ∘ raw25210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25210step2 raw25210step2Labels raw25210step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical25211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25211 raw25211Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw25211 raw25211Labels = mixedMoment B raw25211step0 raw25211step0Labels := by
      have hz : ∀ j, raw25211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25211step0 = (fun i j => raw25211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25211step0 raw25211; decide +kernel
      have hl : raw25211step0Labels = raw25211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25211 raw25211Labels permutation346 hz
    mixedMoment B raw25211step0 raw25211step0Labels = mixedMoment B raw25211step1 raw25211step1Labels := by
      have ha : raw25211step1 = (fun i j => raw25211step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25211step1 raw25211step0; decide +kernel
      have hl : raw25211step1Labels = raw25211step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25211step0 raw25211step0Labels permutation44 permutation7
    mixedMoment B raw25211step1 raw25211step1Labels = mixedMoment B raw25211step2 raw25211step2Labels := by
      have ha : raw25211step2 = -raw25211step1 := by apply Matrix.ext; change ∀ i j, raw25211step2 i j = -(raw25211step1 i j); unfold raw25211step2 raw25211step1; decide +kernel
      have hl : raw25211step2Labels = raw25211step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25211step2 raw25211step2Labels = mixedMoment B raw25211step3 raw25211step3Labels := by
      have ha : raw25211step3 = raw25211step2 := by apply Matrix.ext; unfold raw25211step3 raw25211step2; decide +kernel
      have hl : raw25211step2Labels = labelEmbedding1 ∘ raw25211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25211step2 raw25211step2Labels raw25211step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

theorem canonical25212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25212 raw25212Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw25212 raw25212Labels = mixedMoment B raw25212step0 raw25212step0Labels := by
      have ha : raw25212step0 = (fun i j => raw25212 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25212step0 raw25212; decide +kernel
      have hl : raw25212step0Labels = raw25212Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25212 raw25212Labels permutation188 permutation7
    mixedMoment B raw25212step0 raw25212step0Labels = mixedMoment B raw25212step1 raw25212step1Labels := by
      have ha : raw25212step1 = -raw25212step0 := by apply Matrix.ext; change ∀ i j, raw25212step1 i j = -(raw25212step0 i j); unfold raw25212step1 raw25212step0; decide +kernel
      have hl : raw25212step1Labels = raw25212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25212step1 raw25212step1Labels = mixedMoment B raw25212step2 raw25212step2Labels := by
      have ha : raw25212step2 = raw25212step1 := by apply Matrix.ext; unfold raw25212step2 raw25212step1; decide +kernel
      have hl : raw25212step1Labels = labelEmbedding1 ∘ raw25212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25212step1 raw25212step1Labels raw25212step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

theorem canonical25213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25213 raw25213Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw25213 raw25213Labels = mixedMoment B raw25213step0 raw25213step0Labels := by
      have hz : ∀ j, raw25213 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25213step0 = (fun i j => raw25213 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25213step0 raw25213; decide +kernel
      have hl : raw25213step0Labels = raw25213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25213 raw25213Labels permutation520 hz
    mixedMoment B raw25213step0 raw25213step0Labels = mixedMoment B raw25213step1 raw25213step1Labels := by
      have hz : ∀ j, raw25213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25213step1 = (fun i j => raw25213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25213step1 raw25213step0; decide +kernel
      have hl : raw25213step1Labels = raw25213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25213step0 raw25213step0Labels permutation80 hz
    mixedMoment B raw25213step1 raw25213step1Labels = mixedMoment B raw25213step2 raw25213step2Labels := by
      have ha : raw25213step2 = (fun i j => raw25213step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25213step2 raw25213step1; decide +kernel
      have hl : raw25213step2Labels = raw25213step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25213step1 raw25213step1Labels permutation8 permutation7
    mixedMoment B raw25213step2 raw25213step2Labels = mixedMoment B raw25213step3 raw25213step3Labels := by
      have ha : raw25213step3 = -raw25213step2 := by apply Matrix.ext; change ∀ i j, raw25213step3 i j = -(raw25213step2 i j); unfold raw25213step3 raw25213step2; decide +kernel
      have hl : raw25213step3Labels = raw25213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25213step3 raw25213step3Labels = mixedMoment B raw25213step4 raw25213step4Labels := by
      have ha : raw25213step4 = raw25213step3 := by apply Matrix.ext; unfold raw25213step4 raw25213step3; decide +kernel
      have hl : raw25213step3Labels = labelEmbedding1 ∘ raw25213step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25213step3 raw25213step3Labels raw25213step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical25214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25214 raw25214Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25214 raw25214Labels = mixedMoment B raw25214step0 raw25214step0Labels := by
      have hz : ∀ j, raw25214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25214step0 = (fun i j => raw25214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25214step0 raw25214; decide +kernel
      have hl : raw25214step0Labels = raw25214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25214 raw25214Labels permutation346 hz
    mixedMoment B raw25214step0 raw25214step0Labels = mixedMoment B raw25214step1 raw25214step1Labels := by
      have ha : raw25214step1 = (fun i j => raw25214step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25214step1 raw25214step0; decide +kernel
      have hl : raw25214step1Labels = raw25214step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25214step0 raw25214step0Labels permutation45 permutation7
    mixedMoment B raw25214step1 raw25214step1Labels = mixedMoment B raw25214step2 raw25214step2Labels := by
      have ha : raw25214step2 = -raw25214step1 := by apply Matrix.ext; change ∀ i j, raw25214step2 i j = -(raw25214step1 i j); unfold raw25214step2 raw25214step1; decide +kernel
      have hl : raw25214step2Labels = raw25214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25214step2 raw25214step2Labels = mixedMoment B raw25214step3 raw25214step3Labels := by
      have ha : raw25214step3 = raw25214step2 := by apply Matrix.ext; unfold raw25214step3 raw25214step2; decide +kernel
      have hl : raw25214step2Labels = labelEmbedding1 ∘ raw25214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25214step2 raw25214step2Labels raw25214step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical25215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25215 raw25215Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw25215 raw25215Labels = mixedMoment B raw25215step0 raw25215step0Labels := by
      have hz : ∀ j, raw25215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25215step0 = (fun i j => raw25215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25215step0 raw25215; decide +kernel
      have hl : raw25215step0Labels = raw25215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25215 raw25215Labels permutation346 hz
    mixedMoment B raw25215step0 raw25215step0Labels = mixedMoment B raw25215step1 raw25215step1Labels := by
      have ha : raw25215step1 = (fun i j => raw25215step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25215step1 raw25215step0; decide +kernel
      have hl : raw25215step1Labels = raw25215step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25215step0 raw25215step0Labels permutation44 permutation7
    mixedMoment B raw25215step1 raw25215step1Labels = mixedMoment B raw25215step2 raw25215step2Labels := by
      have ha : raw25215step2 = -raw25215step1 := by apply Matrix.ext; change ∀ i j, raw25215step2 i j = -(raw25215step1 i j); unfold raw25215step2 raw25215step1; decide +kernel
      have hl : raw25215step2Labels = raw25215step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25215step2 raw25215step2Labels = mixedMoment B raw25215step3 raw25215step3Labels := by
      have ha : raw25215step3 = raw25215step2 := by apply Matrix.ext; unfold raw25215step3 raw25215step2; decide +kernel
      have hl : raw25215step2Labels = labelEmbedding1 ∘ raw25215step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25215step2 raw25215step2Labels raw25215step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25216 raw25216Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25216 raw25216Labels = mixedMoment B raw25216step0 raw25216step0Labels := by
      have hz : ∀ j, raw25216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25216step0 = (fun i j => raw25216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25216step0 raw25216; decide +kernel
      have hl : raw25216step0Labels = raw25216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25216 raw25216Labels permutation346 hz
    mixedMoment B raw25216step0 raw25216step0Labels = mixedMoment B raw25216step1 raw25216step1Labels := by
      have ha : raw25216step1 = (fun i j => raw25216step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25216step1 raw25216step0; decide +kernel
      have hl : raw25216step1Labels = raw25216step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25216step0 raw25216step0Labels permutation44 permutation7
    mixedMoment B raw25216step1 raw25216step1Labels = mixedMoment B raw25216step2 raw25216step2Labels := by
      have ha : raw25216step2 = -raw25216step1 := by apply Matrix.ext; change ∀ i j, raw25216step2 i j = -(raw25216step1 i j); unfold raw25216step2 raw25216step1; decide +kernel
      have hl : raw25216step2Labels = raw25216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25216step2 raw25216step2Labels = mixedMoment B raw25216step3 raw25216step3Labels := by
      have ha : raw25216step3 = raw25216step2 := by apply Matrix.ext; unfold raw25216step3 raw25216step2; decide +kernel
      have hl : raw25216step2Labels = labelEmbedding1 ∘ raw25216step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25216step2 raw25216step2Labels raw25216step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

theorem canonical25217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25217 raw25217Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw25217 raw25217Labels = mixedMoment B raw25217step0 raw25217step0Labels := by
      have ha : raw25217step0 = (fun i j => raw25217 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25217step0 raw25217; decide +kernel
      have hl : raw25217step0Labels = raw25217Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25217 raw25217Labels permutation188 permutation7
    mixedMoment B raw25217step0 raw25217step0Labels = mixedMoment B raw25217step1 raw25217step1Labels := by
      have ha : raw25217step1 = -raw25217step0 := by apply Matrix.ext; change ∀ i j, raw25217step1 i j = -(raw25217step0 i j); unfold raw25217step1 raw25217step0; decide +kernel
      have hl : raw25217step1Labels = raw25217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25217step1 raw25217step1Labels = mixedMoment B raw25217step2 raw25217step2Labels := by
      have ha : raw25217step2 = raw25217step1 := by apply Matrix.ext; unfold raw25217step2 raw25217step1; decide +kernel
      have hl : raw25217step1Labels = labelEmbedding1 ∘ raw25217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25217step1 raw25217step1Labels raw25217step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical25218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25218 raw25218Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw25218 raw25218Labels = mixedMoment B raw25218step0 raw25218step0Labels := by
      have hz : ∀ j, raw25218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25218step0 = (fun i j => raw25218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25218step0 raw25218; decide +kernel
      have hl : raw25218step0Labels = raw25218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25218 raw25218Labels permutation346 hz
    mixedMoment B raw25218step0 raw25218step0Labels = mixedMoment B raw25218step1 raw25218step1Labels := by
      have ha : raw25218step1 = (fun i j => raw25218step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25218step1 raw25218step0; decide +kernel
      have hl : raw25218step1Labels = raw25218step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25218step0 raw25218step0Labels permutation44 permutation7
    mixedMoment B raw25218step1 raw25218step1Labels = mixedMoment B raw25218step2 raw25218step2Labels := by
      have ha : raw25218step2 = -raw25218step1 := by apply Matrix.ext; change ∀ i j, raw25218step2 i j = -(raw25218step1 i j); unfold raw25218step2 raw25218step1; decide +kernel
      have hl : raw25218step2Labels = raw25218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25218step2 raw25218step2Labels = mixedMoment B raw25218step3 raw25218step3Labels := by
      have ha : raw25218step3 = raw25218step2 := by apply Matrix.ext; unfold raw25218step3 raw25218step2; decide +kernel
      have hl : raw25218step2Labels = labelEmbedding1 ∘ raw25218step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25218step2 raw25218step2Labels raw25218step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

theorem canonical25219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25219 raw25219Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw25219 raw25219Labels = mixedMoment B raw25219step0 raw25219step0Labels := by
      have hz : ∀ j, raw25219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25219step0 = (fun i j => raw25219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25219step0 raw25219; decide +kernel
      have hl : raw25219step0Labels = raw25219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25219 raw25219Labels permutation346 hz
    mixedMoment B raw25219step0 raw25219step0Labels = mixedMoment B raw25219step1 raw25219step1Labels := by
      have ha : raw25219step1 = (fun i j => raw25219step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25219step1 raw25219step0; decide +kernel
      have hl : raw25219step1Labels = raw25219step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25219step0 raw25219step0Labels permutation44 permutation7
    mixedMoment B raw25219step1 raw25219step1Labels = mixedMoment B raw25219step2 raw25219step2Labels := by
      have ha : raw25219step2 = -raw25219step1 := by apply Matrix.ext; change ∀ i j, raw25219step2 i j = -(raw25219step1 i j); unfold raw25219step2 raw25219step1; decide +kernel
      have hl : raw25219step2Labels = raw25219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25219step2 raw25219step2Labels = mixedMoment B raw25219step3 raw25219step3Labels := by
      have ha : raw25219step3 = raw25219step2 := by apply Matrix.ext; unfold raw25219step3 raw25219step2; decide +kernel
      have hl : raw25219step2Labels = labelEmbedding1 ∘ raw25219step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25219step2 raw25219step2Labels raw25219step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical25220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25220 raw25220Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw25220 raw25220Labels = mixedMoment B raw25220step0 raw25220step0Labels := by
      have hz : ∀ j, raw25220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25220step0 = (fun i j => raw25220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25220step0 raw25220; decide +kernel
      have hl : raw25220step0Labels = raw25220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25220 raw25220Labels permutation346 hz
    mixedMoment B raw25220step0 raw25220step0Labels = mixedMoment B raw25220step1 raw25220step1Labels := by
      have ha : raw25220step1 = (fun i j => raw25220step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25220step1 raw25220step0; decide +kernel
      have hl : raw25220step1Labels = raw25220step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25220step0 raw25220step0Labels permutation44 permutation7
    mixedMoment B raw25220step1 raw25220step1Labels = mixedMoment B raw25220step2 raw25220step2Labels := by
      have ha : raw25220step2 = -raw25220step1 := by apply Matrix.ext; change ∀ i j, raw25220step2 i j = -(raw25220step1 i j); unfold raw25220step2 raw25220step1; decide +kernel
      have hl : raw25220step2Labels = raw25220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25220step2 raw25220step2Labels = mixedMoment B raw25220step3 raw25220step3Labels := by
      have ha : raw25220step3 = raw25220step2 := by apply Matrix.ext; unfold raw25220step3 raw25220step2; decide +kernel
      have hl : raw25220step2Labels = labelEmbedding1 ∘ raw25220step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25220step2 raw25220step2Labels raw25220step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

theorem canonical25221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25221 raw25221Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw25221 raw25221Labels = mixedMoment B raw25221step0 raw25221step0Labels := by
      have hz : ∀ j, raw25221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25221step0 = (fun i j => raw25221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25221step0 raw25221; decide +kernel
      have hl : raw25221step0Labels = raw25221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25221 raw25221Labels permutation346 hz
    mixedMoment B raw25221step0 raw25221step0Labels = mixedMoment B raw25221step1 raw25221step1Labels := by
      have ha : raw25221step1 = (fun i j => raw25221step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25221step1 raw25221step0; decide +kernel
      have hl : raw25221step1Labels = raw25221step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25221step0 raw25221step0Labels permutation44 permutation7
    mixedMoment B raw25221step1 raw25221step1Labels = mixedMoment B raw25221step2 raw25221step2Labels := by
      have ha : raw25221step2 = -raw25221step1 := by apply Matrix.ext; change ∀ i j, raw25221step2 i j = -(raw25221step1 i j); unfold raw25221step2 raw25221step1; decide +kernel
      have hl : raw25221step2Labels = raw25221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25221step2 raw25221step2Labels = mixedMoment B raw25221step3 raw25221step3Labels := by
      have ha : raw25221step3 = raw25221step2 := by apply Matrix.ext; unfold raw25221step3 raw25221step2; decide +kernel
      have hl : raw25221step2Labels = labelEmbedding1 ∘ raw25221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25221step2 raw25221step2Labels raw25221step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

theorem canonical25222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25222 raw25222Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw25222 raw25222Labels = mixedMoment B raw25222step0 raw25222step0Labels := by
      have ha : raw25222step0 = (fun i j => raw25222 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25222step0 raw25222; decide +kernel
      have hl : raw25222step0Labels = raw25222Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25222 raw25222Labels permutation188 permutation7
    mixedMoment B raw25222step0 raw25222step0Labels = mixedMoment B raw25222step1 raw25222step1Labels := by
      have ha : raw25222step1 = -raw25222step0 := by apply Matrix.ext; change ∀ i j, raw25222step1 i j = -(raw25222step0 i j); unfold raw25222step1 raw25222step0; decide +kernel
      have hl : raw25222step1Labels = raw25222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25222step1 raw25222step1Labels = mixedMoment B raw25222step2 raw25222step2Labels := by
      have ha : raw25222step2 = raw25222step1 := by apply Matrix.ext; unfold raw25222step2 raw25222step1; decide +kernel
      have hl : raw25222step1Labels = labelEmbedding1 ∘ raw25222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25222step1 raw25222step1Labels raw25222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

theorem canonical25223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25223 raw25223Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw25223 raw25223Labels = mixedMoment B raw25223step0 raw25223step0Labels := by
      have hz : ∀ j, raw25223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25223step0 = (fun i j => raw25223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25223step0 raw25223; decide +kernel
      have hl : raw25223step0Labels = raw25223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25223 raw25223Labels permutation346 hz
    mixedMoment B raw25223step0 raw25223step0Labels = mixedMoment B raw25223step1 raw25223step1Labels := by
      have ha : raw25223step1 = (fun i j => raw25223step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25223step1 raw25223step0; decide +kernel
      have hl : raw25223step1Labels = raw25223step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25223step0 raw25223step0Labels permutation44 permutation7
    mixedMoment B raw25223step1 raw25223step1Labels = mixedMoment B raw25223step2 raw25223step2Labels := by
      have ha : raw25223step2 = -raw25223step1 := by apply Matrix.ext; change ∀ i j, raw25223step2 i j = -(raw25223step1 i j); unfold raw25223step2 raw25223step1; decide +kernel
      have hl : raw25223step2Labels = raw25223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25223step2 raw25223step2Labels = mixedMoment B raw25223step3 raw25223step3Labels := by
      have ha : raw25223step3 = raw25223step2 := by apply Matrix.ext; unfold raw25223step3 raw25223step2; decide +kernel
      have hl : raw25223step2Labels = labelEmbedding1 ∘ raw25223step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25223step2 raw25223step2Labels raw25223step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical25224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25224 raw25224Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw25224 raw25224Labels = mixedMoment B raw25224step0 raw25224step0Labels := by
      have hz : ∀ j, raw25224 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25224step0 = (fun i j => raw25224 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25224step0 raw25224; decide +kernel
      have hl : raw25224step0Labels = raw25224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25224 raw25224Labels permutation520 hz
    mixedMoment B raw25224step0 raw25224step0Labels = mixedMoment B raw25224step1 raw25224step1Labels := by
      have hz : ∀ j, raw25224step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25224step1 = (fun i j => raw25224step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25224step1 raw25224step0; decide +kernel
      have hl : raw25224step1Labels = raw25224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25224step0 raw25224step0Labels permutation80 hz
    mixedMoment B raw25224step1 raw25224step1Labels = mixedMoment B raw25224step2 raw25224step2Labels := by
      have ha : raw25224step2 = (fun i j => raw25224step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25224step2 raw25224step1; decide +kernel
      have hl : raw25224step2Labels = raw25224step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25224step1 raw25224step1Labels permutation8 permutation7
    mixedMoment B raw25224step2 raw25224step2Labels = mixedMoment B raw25224step3 raw25224step3Labels := by
      have ha : raw25224step3 = -raw25224step2 := by apply Matrix.ext; change ∀ i j, raw25224step3 i j = -(raw25224step2 i j); unfold raw25224step3 raw25224step2; decide +kernel
      have hl : raw25224step3Labels = raw25224step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25224step3 raw25224step3Labels = mixedMoment B raw25224step4 raw25224step4Labels := by
      have ha : raw25224step4 = raw25224step3 := by apply Matrix.ext; unfold raw25224step4 raw25224step3; decide +kernel
      have hl : raw25224step3Labels = labelEmbedding1 ∘ raw25224step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25224step3 raw25224step3Labels raw25224step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical25225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25225 raw25225Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25225 raw25225Labels = mixedMoment B raw25225step0 raw25225step0Labels := by
      have hz : ∀ j, raw25225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25225step0 = (fun i j => raw25225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25225step0 raw25225; decide +kernel
      have hl : raw25225step0Labels = raw25225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25225 raw25225Labels permutation346 hz
    mixedMoment B raw25225step0 raw25225step0Labels = mixedMoment B raw25225step1 raw25225step1Labels := by
      have ha : raw25225step1 = (fun i j => raw25225step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25225step1 raw25225step0; decide +kernel
      have hl : raw25225step1Labels = raw25225step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25225step0 raw25225step0Labels permutation34 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical25226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25226 raw25226Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw25226 raw25226Labels = mixedMoment B raw25226step0 raw25226step0Labels := by
      have hz : ∀ j, raw25226 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25226step0 = (fun i j => raw25226 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25226step0 raw25226; decide +kernel
      have hl : raw25226step0Labels = raw25226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25226 raw25226Labels permutation346 hz
    mixedMoment B raw25226step0 raw25226step0Labels = mixedMoment B raw25226step1 raw25226step1Labels := by
      have ha : raw25226step1 = (fun i j => raw25226step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25226step1 raw25226step0; decide +kernel
      have hl : raw25226step1Labels = raw25226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25226step0 raw25226step0Labels permutation44 permutation2
    _ = mixedMoment B node603 node603Labels := by rfl

theorem canonical25227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25227 raw25227Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw25227 raw25227Labels = mixedMoment B raw25227step0 raw25227step0Labels := by
      have ha : raw25227step0 = (fun i j => raw25227 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25227step0 raw25227; decide +kernel
      have hl : raw25227step0Labels = raw25227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25227 raw25227Labels permutation154 permutation2
    _ = mixedMoment B node578 node578Labels := by rfl

theorem canonical25228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25228 raw25228Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw25228 raw25228Labels = mixedMoment B raw25228step0 raw25228step0Labels := by
      have hz : ∀ j, raw25228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25228step0 = (fun i j => raw25228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25228step0 raw25228; decide +kernel
      have hl : raw25228step0Labels = raw25228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25228 raw25228Labels permutation346 hz
    mixedMoment B raw25228step0 raw25228step0Labels = mixedMoment B raw25228step1 raw25228step1Labels := by
      have ha : raw25228step1 = (fun i j => raw25228step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25228step1 raw25228step0; decide +kernel
      have hl : raw25228step1Labels = raw25228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25228step0 raw25228step0Labels permutation34 permutation2
    _ = mixedMoment B node583 node583Labels := by rfl

theorem canonical25229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25229 raw25229Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw25229 raw25229Labels = mixedMoment B raw25229step0 raw25229step0Labels := by
      have hz : ∀ j, raw25229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25229step0 = (fun i j => raw25229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25229step0 raw25229; decide +kernel
      have hl : raw25229step0Labels = raw25229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25229 raw25229Labels permutation346 hz
    _ = mixedMoment B node586 node586Labels := by rfl

theorem canonical25230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25230 raw25230Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw25230 raw25230Labels = mixedMoment B raw25230step0 raw25230step0Labels := by
      have hz : ∀ j, raw25230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25230step0 = (fun i j => raw25230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25230step0 raw25230; decide +kernel
      have hl : raw25230step0Labels = raw25230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25230 raw25230Labels permutation346 hz
    mixedMoment B raw25230step0 raw25230step0Labels = mixedMoment B raw25230step1 raw25230step1Labels := by
      have ha : raw25230step1 = (fun i j => raw25230step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25230step1 raw25230step0; decide +kernel
      have hl : raw25230step1Labels = raw25230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25230step0 raw25230step0Labels permutation34 permutation2
    _ = mixedMoment B node581 node581Labels := by rfl

theorem canonical25231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25231 raw25231Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25231 raw25231Labels = mixedMoment B raw25231step0 raw25231step0Labels := by
      have hz : ∀ j, raw25231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25231step0 = (fun i j => raw25231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25231step0 raw25231; decide +kernel
      have hl : raw25231step0Labels = raw25231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25231 raw25231Labels permutation520 hz
    mixedMoment B raw25231step0 raw25231step0Labels = mixedMoment B raw25231step1 raw25231step1Labels := by
      have hz : ∀ j, raw25231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25231step1 = (fun i j => raw25231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25231step1 raw25231step0; decide +kernel
      have hl : raw25231step1Labels = raw25231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25231step0 raw25231step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical25232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25232 raw25232Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw25232 raw25232Labels = mixedMoment B raw25232step0 raw25232step0Labels := by
      have ha : raw25232step0 = (fun i j => raw25232 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25232step0 raw25232; decide +kernel
      have hl : raw25232step0Labels = raw25232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25232 raw25232Labels permutation188 permutation2
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical25233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25233 raw25233Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25233 raw25233Labels = mixedMoment B raw25233step0 raw25233step0Labels := by
      have hz : ∀ j, raw25233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25233step0 = (fun i j => raw25233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25233step0 raw25233; decide +kernel
      have hl : raw25233step0Labels = raw25233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25233 raw25233Labels permutation346 hz
    mixedMoment B raw25233step0 raw25233step0Labels = mixedMoment B raw25233step1 raw25233step1Labels := by
      have ha : raw25233step1 = (fun i j => raw25233step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25233step1 raw25233step0; decide +kernel
      have hl : raw25233step1Labels = raw25233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25233step0 raw25233step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical25234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25234 raw25234Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw25234 raw25234Labels = mixedMoment B raw25234step0 raw25234step0Labels := by
      have hz : ∀ j, raw25234 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25234step0 = (fun i j => raw25234 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25234step0 raw25234; decide +kernel
      have hl : raw25234step0Labels = raw25234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25234 raw25234Labels permutation520 hz
    mixedMoment B raw25234step0 raw25234step0Labels = mixedMoment B raw25234step1 raw25234step1Labels := by
      have hz : ∀ j, raw25234step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25234step1 = (fun i j => raw25234step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25234step1 raw25234step0; decide +kernel
      have hl : raw25234step1Labels = raw25234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25234step0 raw25234step0Labels permutation80 hz
    _ = mixedMoment B node1086 node1086Labels := by rfl

theorem canonical25235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25235 raw25235Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw25235 raw25235Labels = mixedMoment B raw25235step0 raw25235step0Labels := by
      have hz : ∀ j, raw25235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25235step0 = (fun i j => raw25235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25235step0 raw25235; decide +kernel
      have hl : raw25235step0Labels = raw25235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25235 raw25235Labels permutation346 hz
    mixedMoment B raw25235step0 raw25235step0Labels = mixedMoment B raw25235step1 raw25235step1Labels := by
      have ha : raw25235step1 = (fun i j => raw25235step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25235step1 raw25235step0; decide +kernel
      have hl : raw25235step1Labels = raw25235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25235step0 raw25235step0Labels permutation44 permutation2
    _ = mixedMoment B node1081 node1081Labels := by rfl

theorem canonical25236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25236 raw25236Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw25236 raw25236Labels = mixedMoment B raw25236step0 raw25236step0Labels := by
      have hz : ∀ j, raw25236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25236step0 = (fun i j => raw25236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25236step0 raw25236; decide +kernel
      have hl : raw25236step0Labels = raw25236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25236 raw25236Labels permutation346 hz
    mixedMoment B raw25236step0 raw25236step0Labels = mixedMoment B raw25236step1 raw25236step1Labels := by
      have ha : raw25236step1 = (fun i j => raw25236step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25236step1 raw25236step0; decide +kernel
      have hl : raw25236step1Labels = raw25236step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25236step0 raw25236step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical25237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25237 raw25237Labels = mixedMoment B node942 node942Labels := by
  calc
    mixedMoment B raw25237 raw25237Labels = mixedMoment B raw25237step0 raw25237step0Labels := by
      have ha : raw25237step0 = (fun i j => raw25237 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25237step0 raw25237; decide +kernel
      have hl : raw25237step0Labels = raw25237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25237 raw25237Labels permutation154 permutation2
    _ = mixedMoment B node942 node942Labels := by rfl

theorem canonical25238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25238 raw25238Labels = mixedMoment B node947 node947Labels := by
  calc
    mixedMoment B raw25238 raw25238Labels = mixedMoment B raw25238step0 raw25238step0Labels := by
      have hz : ∀ j, raw25238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25238step0 = (fun i j => raw25238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25238step0 raw25238; decide +kernel
      have hl : raw25238step0Labels = raw25238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25238 raw25238Labels permutation346 hz
    mixedMoment B raw25238step0 raw25238step0Labels = mixedMoment B raw25238step1 raw25238step1Labels := by
      have ha : raw25238step1 = (fun i j => raw25238step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25238step1 raw25238step0; decide +kernel
      have hl : raw25238step1Labels = raw25238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25238step0 raw25238step0Labels permutation34 permutation2
    _ = mixedMoment B node947 node947Labels := by rfl

theorem canonical25239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25239 raw25239Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw25239 raw25239Labels = mixedMoment B raw25239step0 raw25239step0Labels := by
      have hz : ∀ j, raw25239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25239step0 = (fun i j => raw25239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25239step0 raw25239; decide +kernel
      have hl : raw25239step0Labels = raw25239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25239 raw25239Labels permutation346 hz
    _ = mixedMoment B node950 node950Labels := by rfl

theorem canonical25240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25240 raw25240Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw25240 raw25240Labels = mixedMoment B raw25240step0 raw25240step0Labels := by
      have hz : ∀ j, raw25240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25240step0 = (fun i j => raw25240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25240step0 raw25240; decide +kernel
      have hl : raw25240step0Labels = raw25240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25240 raw25240Labels permutation346 hz
    mixedMoment B raw25240step0 raw25240step0Labels = mixedMoment B raw25240step1 raw25240step1Labels := by
      have ha : raw25240step1 = (fun i j => raw25240step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25240step1 raw25240step0; decide +kernel
      have hl : raw25240step1Labels = raw25240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25240step0 raw25240step0Labels permutation34 permutation2
    _ = mixedMoment B node945 node945Labels := by rfl

theorem canonical25334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25334 raw25334Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw25334 raw25334Labels = mixedMoment B raw25334step0 raw25334step0Labels := by
      have hz : ∀ j, raw25334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25334step0 = (fun i j => raw25334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25334step0 raw25334; decide +kernel
      have hl : raw25334step0Labels = raw25334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25334 raw25334Labels permutation346 hz
    mixedMoment B raw25334step0 raw25334step0Labels = mixedMoment B raw25334step1 raw25334step1Labels := by
      have ha : raw25334step1 = (fun i j => raw25334step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25334step1 raw25334step0; decide +kernel
      have hl : raw25334step1Labels = raw25334step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25334step0 raw25334step0Labels permutation34 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical25335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25335 raw25335Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw25335 raw25335Labels = mixedMoment B raw25335step0 raw25335step0Labels := by
      have hz : ∀ j, raw25335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25335step0 = (fun i j => raw25335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25335step0 raw25335; decide +kernel
      have hl : raw25335step0Labels = raw25335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25335 raw25335Labels permutation346 hz
    mixedMoment B raw25335step0 raw25335step0Labels = mixedMoment B raw25335step1 raw25335step1Labels := by
      have ha : raw25335step1 = (fun i j => raw25335step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25335step1 raw25335step0; decide +kernel
      have hl : raw25335step1Labels = raw25335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25335step0 raw25335step0Labels permutation34 permutation2
    _ = mixedMoment B node2101 node2101Labels := by rfl

theorem canonical25336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25336 raw25336Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw25336 raw25336Labels = mixedMoment B raw25336step0 raw25336step0Labels := by
      have ha : raw25336step0 = (fun i j => raw25336 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25336step0 raw25336; decide +kernel
      have hl : raw25336step0Labels = raw25336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25336 raw25336Labels permutation178 permutation2
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical25337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25337 raw25337Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw25337 raw25337Labels = mixedMoment B raw25337step0 raw25337step0Labels := by
      have hz : ∀ j, raw25337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25337step0 = (fun i j => raw25337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25337step0 raw25337; decide +kernel
      have hl : raw25337step0Labels = raw25337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25337 raw25337Labels permutation346 hz
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical25338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25338 raw25338Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw25338 raw25338Labels = mixedMoment B raw25338step0 raw25338step0Labels := by
      have hz : ∀ j, raw25338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25338step0 = (fun i j => raw25338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25338step0 raw25338; decide +kernel
      have hl : raw25338step0Labels = raw25338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25338 raw25338Labels permutation346 hz
    mixedMoment B raw25338step0 raw25338step0Labels = mixedMoment B raw25338step1 raw25338step1Labels := by
      have ha : raw25338step1 = (fun i j => raw25338step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25338step1 raw25338step0; decide +kernel
      have hl : raw25338step1Labels = raw25338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25338step0 raw25338step0Labels permutation44 permutation2
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical25339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25339 raw25339Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw25339 raw25339Labels = mixedMoment B raw25339step0 raw25339step0Labels := by
      have hz : ∀ j, raw25339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25339step0 = (fun i j => raw25339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25339step0 raw25339; decide +kernel
      have hl : raw25339step0Labels = raw25339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25339 raw25339Labels permutation346 hz
    mixedMoment B raw25339step0 raw25339step0Labels = mixedMoment B raw25339step1 raw25339step1Labels := by
      have ha : raw25339step1 = (fun i j => raw25339step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25339step1 raw25339step0; decide +kernel
      have hl : raw25339step1Labels = raw25339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25339step0 raw25339step0Labels permutation34 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical25340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25340 raw25340Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25340 raw25340Labels = mixedMoment B raw25340step0 raw25340step0Labels := by
      have hz : ∀ j, raw25340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25340step0 = (fun i j => raw25340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25340step0 raw25340; decide +kernel
      have hl : raw25340step0Labels = raw25340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25340 raw25340Labels permutation346 hz
    mixedMoment B raw25340step0 raw25340step0Labels = mixedMoment B raw25340step1 raw25340step1Labels := by
      have ha : raw25340step1 = (fun i j => raw25340step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25340step1 raw25340step0; decide +kernel
      have hl : raw25340step1Labels = raw25340step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25340step0 raw25340step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

theorem canonical25346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25346 raw25346Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw25346 raw25346Labels = mixedMoment B raw25346step0 raw25346step0Labels := by
      have hz : ∀ j, raw25346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25346step0 = (fun i j => raw25346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25346step0 raw25346; decide +kernel
      have hl : raw25346step0Labels = raw25346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25346 raw25346Labels permutation346 hz
    mixedMoment B raw25346step0 raw25346step0Labels = mixedMoment B raw25346step1 raw25346step1Labels := by
      have ha : raw25346step1 = (fun i j => raw25346step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25346step1 raw25346step0; decide +kernel
      have hl : raw25346step1Labels = raw25346step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25346step0 raw25346step0Labels permutation44 permutation4
    mixedMoment B raw25346step1 raw25346step1Labels = mixedMoment B raw25346step2 raw25346step2Labels := by
      have ha : raw25346step2 = -raw25346step1 := by apply Matrix.ext; change ∀ i j, raw25346step2 i j = -(raw25346step1 i j); unfold raw25346step2 raw25346step1; decide +kernel
      have hl : raw25346step2Labels = raw25346step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1645 node1645Labels := by rfl

theorem canonical25347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25347 raw25347Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw25347 raw25347Labels = mixedMoment B raw25347step0 raw25347step0Labels := by
      have hz : ∀ j, raw25347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25347step0 = (fun i j => raw25347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25347step0 raw25347; decide +kernel
      have hl : raw25347step0Labels = raw25347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25347 raw25347Labels permutation346 hz
    mixedMoment B raw25347step0 raw25347step0Labels = mixedMoment B raw25347step1 raw25347step1Labels := by
      have ha : raw25347step1 = (fun i j => raw25347step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25347step1 raw25347step0; decide +kernel
      have hl : raw25347step1Labels = raw25347step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25347step0 raw25347step0Labels permutation46 permutation4
    mixedMoment B raw25347step1 raw25347step1Labels = mixedMoment B raw25347step2 raw25347step2Labels := by
      have ha : raw25347step2 = -raw25347step1 := by apply Matrix.ext; change ∀ i j, raw25347step2 i j = -(raw25347step1 i j); unfold raw25347step2 raw25347step1; decide +kernel
      have hl : raw25347step2Labels = raw25347step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node738 node738Labels := by rfl

theorem canonical25348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25348 raw25348Labels = mixedMoment B node730 node730Labels := by
  calc
    mixedMoment B raw25348 raw25348Labels = mixedMoment B raw25348step0 raw25348step0Labels := by
      have ha : raw25348step0 = (fun i j => raw25348 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25348step0 raw25348; decide +kernel
      have hl : raw25348step0Labels = raw25348Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25348 raw25348Labels permutation224 permutation4
    mixedMoment B raw25348step0 raw25348step0Labels = mixedMoment B raw25348step1 raw25348step1Labels := by
      have ha : raw25348step1 = -raw25348step0 := by apply Matrix.ext; change ∀ i j, raw25348step1 i j = -(raw25348step0 i j); unfold raw25348step1 raw25348step0; decide +kernel
      have hl : raw25348step1Labels = raw25348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node730 node730Labels := by rfl

theorem canonical25349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25349 raw25349Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw25349 raw25349Labels = mixedMoment B raw25349step0 raw25349step0Labels := by
      have hz : ∀ j, raw25349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25349step0 = (fun i j => raw25349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25349step0 raw25349; decide +kernel
      have hl : raw25349step0Labels = raw25349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25349 raw25349Labels permutation346 hz
    mixedMoment B raw25349step0 raw25349step0Labels = mixedMoment B raw25349step1 raw25349step1Labels := by
      have ha : raw25349step1 = (fun i j => raw25349step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25349step1 raw25349step0; decide +kernel
      have hl : raw25349step1Labels = raw25349step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25349step0 raw25349step0Labels permutation44 permutation4
    mixedMoment B raw25349step1 raw25349step1Labels = mixedMoment B raw25349step2 raw25349step2Labels := by
      have ha : raw25349step2 = -raw25349step1 := by apply Matrix.ext; change ∀ i j, raw25349step2 i j = -(raw25349step1 i j); unfold raw25349step2 raw25349step1; decide +kernel
      have hl : raw25349step2Labels = raw25349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node734 node734Labels := by rfl

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

theorem canonical25351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25351 raw25351Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw25351 raw25351Labels = mixedMoment B raw25351step0 raw25351step0Labels := by
      have hz : ∀ j, raw25351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25351step0 = (fun i j => raw25351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25351step0 raw25351; decide +kernel
      have hl : raw25351step0Labels = raw25351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25351 raw25351Labels permutation346 hz
    mixedMoment B raw25351step0 raw25351step0Labels = mixedMoment B raw25351step1 raw25351step1Labels := by
      have ha : raw25351step1 = (fun i j => raw25351step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25351step1 raw25351step0; decide +kernel
      have hl : raw25351step1Labels = raw25351step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25351step0 raw25351step0Labels permutation44 permutation4
    mixedMoment B raw25351step1 raw25351step1Labels = mixedMoment B raw25351step2 raw25351step2Labels := by
      have ha : raw25351step2 = -raw25351step1 := by apply Matrix.ext; change ∀ i j, raw25351step2 i j = -(raw25351step1 i j); unfold raw25351step2 raw25351step1; decide +kernel
      have hl : raw25351step2Labels = raw25351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node733 node733Labels := by rfl

theorem canonical25352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25352 raw25352Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw25352 raw25352Labels = mixedMoment B raw25352step0 raw25352step0Labels := by
      have hz : ∀ j, raw25352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25352step0 = (fun i j => raw25352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25352step0 raw25352; decide +kernel
      have hl : raw25352step0Labels = raw25352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25352 raw25352Labels permutation346 hz
    mixedMoment B raw25352step0 raw25352step0Labels = mixedMoment B raw25352step1 raw25352step1Labels := by
      have ha : raw25352step1 = (fun i j => raw25352step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25352step1 raw25352step0; decide +kernel
      have hl : raw25352step1Labels = raw25352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25352step0 raw25352step0Labels permutation40 permutation2
    _ = mixedMoment B node4172 node4172Labels := by rfl

theorem canonical25353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25353 raw25353Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25353 raw25353Labels = mixedMoment B raw25353step0 raw25353step0Labels := by
      have ha : raw25353step0 = (fun i j => raw25353 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25353step0 raw25353; decide +kernel
      have hl : raw25353step0Labels = raw25353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25353 raw25353Labels permutation184 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical25354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25354 raw25354Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25354 raw25354Labels = mixedMoment B raw25354step0 raw25354step0Labels := by
      have hz : ∀ j, raw25354 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25354step0 = (fun i j => raw25354 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25354step0 raw25354; decide +kernel
      have hl : raw25354step0Labels = raw25354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25354 raw25354Labels permutation520 hz
    mixedMoment B raw25354step0 raw25354step0Labels = mixedMoment B raw25354step1 raw25354step1Labels := by
      have hz : ∀ j, raw25354step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25354step1 = (fun i j => raw25354step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25354step1 raw25354step0; decide +kernel
      have hl : raw25354step1Labels = raw25354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25354step0 raw25354step0Labels permutation80 hz
    mixedMoment B raw25354step1 raw25354step1Labels = mixedMoment B raw25354step2 raw25354step2Labels := by
      have ha : raw25354step2 = (fun i j => raw25354step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25354step2 raw25354step1; decide +kernel
      have hl : raw25354step2Labels = raw25354step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25354step1 raw25354step1Labels permutation10 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical25355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25355 raw25355Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25355 raw25355Labels = mixedMoment B raw25355step0 raw25355step0Labels := by
      have hz : ∀ j, raw25355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25355step0 = (fun i j => raw25355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25355step0 raw25355; decide +kernel
      have hl : raw25355step0Labels = raw25355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25355 raw25355Labels permutation346 hz
    mixedMoment B raw25355step0 raw25355step0Labels = mixedMoment B raw25355step1 raw25355step1Labels := by
      have ha : raw25355step1 = (fun i j => raw25355step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25355step1 raw25355step0; decide +kernel
      have hl : raw25355step1Labels = raw25355step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25355step0 raw25355step0Labels permutation40 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical25356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25356 raw25356Labels = mixedMoment B node4149 node4149Labels := by
  calc
    _ = mixedMoment B node4149 node4149Labels := by rfl

theorem canonical25357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25357 raw25357Labels = mixedMoment B node4363 node4363Labels := by
  calc
    _ = mixedMoment B node4363 node4363Labels := by rfl

theorem canonical25358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25358 raw25358Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25358 raw25358Labels = mixedMoment B raw25358step0 raw25358step0Labels := by
      have hz : ∀ j, raw25358 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25358step0 = (fun i j => raw25358 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25358step0 raw25358; decide +kernel
      have hl : raw25358step0Labels = raw25358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25358 raw25358Labels permutation520 hz
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical25359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25359 raw25359Labels = mixedMoment B node4455 node4455Labels := by
  calc
    _ = mixedMoment B node4455 node4455Labels := by rfl

theorem canonical25360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25360 raw25360Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw25360 raw25360Labels = mixedMoment B raw25360step0 raw25360step0Labels := by
      have hz : ∀ j, raw25360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25360step0 = (fun i j => raw25360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25360step0 raw25360; decide +kernel
      have hl : raw25360step0Labels = raw25360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25360 raw25360Labels permutation346 hz
    mixedMoment B raw25360step0 raw25360step0Labels = mixedMoment B raw25360step1 raw25360step1Labels := by
      have ha : raw25360step1 = (fun i j => raw25360step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25360step1 raw25360step0; decide +kernel
      have hl : raw25360step1Labels = raw25360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25360step0 raw25360step0Labels permutation34 permutation2
    _ = mixedMoment B node4154 node4154Labels := by rfl

theorem canonical25361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25361 raw25361Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw25361 raw25361Labels = mixedMoment B raw25361step0 raw25361step0Labels := by
      have hz : ∀ j, raw25361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25361step0 = (fun i j => raw25361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25361step0 raw25361; decide +kernel
      have hl : raw25361step0Labels = raw25361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25361 raw25361Labels permutation346 hz
    mixedMoment B raw25361step0 raw25361step0Labels = mixedMoment B raw25361step1 raw25361step1Labels := by
      have ha : raw25361step1 = (fun i j => raw25361step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25361step1 raw25361step0; decide +kernel
      have hl : raw25361step1Labels = raw25361step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25361step0 raw25361step0Labels permutation34 permutation2
    _ = mixedMoment B node4368 node4368Labels := by rfl

theorem canonical25362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25362 raw25362Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw25362 raw25362Labels = mixedMoment B raw25362step0 raw25362step0Labels := by
      have ha : raw25362step0 = (fun i j => raw25362 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25362step0 raw25362; decide +kernel
      have hl : raw25362step0Labels = raw25362Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25362 raw25362Labels permutation178 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

theorem canonical25363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25363 raw25363Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw25363 raw25363Labels = mixedMoment B raw25363step0 raw25363step0Labels := by
      have hz : ∀ j, raw25363 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25363step0 = (fun i j => raw25363 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25363step0 raw25363; decide +kernel
      have hl : raw25363step0Labels = raw25363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25363 raw25363Labels permutation520 hz
    mixedMoment B raw25363step0 raw25363step0Labels = mixedMoment B raw25363step1 raw25363step1Labels := by
      have hz : ∀ j, raw25363step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25363step1 = (fun i j => raw25363step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25363step1 raw25363step0; decide +kernel
      have hl : raw25363step1Labels = raw25363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25363step0 raw25363step0Labels permutation80 hz
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical25364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25364 raw25364Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw25364 raw25364Labels = mixedMoment B raw25364step0 raw25364step0Labels := by
      have hz : ∀ j, raw25364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25364step0 = (fun i j => raw25364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25364step0 raw25364; decide +kernel
      have hl : raw25364step0Labels = raw25364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25364 raw25364Labels permutation346 hz
    mixedMoment B raw25364step0 raw25364step0Labels = mixedMoment B raw25364step1 raw25364step1Labels := by
      have ha : raw25364step1 = (fun i j => raw25364step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25364step1 raw25364step0; decide +kernel
      have hl : raw25364step1Labels = raw25364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25364step0 raw25364step0Labels permutation35 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

theorem canonical25365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25365 raw25365Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw25365 raw25365Labels = mixedMoment B raw25365step0 raw25365step0Labels := by
      have hz : ∀ j, raw25365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25365step0 = (fun i j => raw25365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25365step0 raw25365; decide +kernel
      have hl : raw25365step0Labels = raw25365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25365 raw25365Labels permutation346 hz
    _ = mixedMoment B node4154 node4154Labels := by rfl

theorem canonical25366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25366 raw25366Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw25366 raw25366Labels = mixedMoment B raw25366step0 raw25366step0Labels := by
      have hz : ∀ j, raw25366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25366step0 = (fun i j => raw25366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25366step0 raw25366; decide +kernel
      have hl : raw25366step0Labels = raw25366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25366 raw25366Labels permutation346 hz
    _ = mixedMoment B node4368 node4368Labels := by rfl

theorem canonical25367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25367 raw25367Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw25367 raw25367Labels = mixedMoment B raw25367step0 raw25367step0Labels := by
      have ha : raw25367step0 = (fun i j => raw25367 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25367step0 raw25367; decide +kernel
      have hl : raw25367step0Labels = raw25367Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25367 raw25367Labels permutation176 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

theorem canonical25368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25368 raw25368Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw25368 raw25368Labels = mixedMoment B raw25368step0 raw25368step0Labels := by
      have hz : ∀ j, raw25368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25368step0 = (fun i j => raw25368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25368step0 raw25368; decide +kernel
      have hl : raw25368step0Labels = raw25368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25368 raw25368Labels permutation346 hz
    mixedMoment B raw25368step0 raw25368step0Labels = mixedMoment B raw25368step1 raw25368step1Labels := by
      have ha : raw25368step1 = (fun i j => raw25368step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25368step1 raw25368step0; decide +kernel
      have hl : raw25368step1Labels = raw25368step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25368step0 raw25368step0Labels permutation33 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

theorem canonical25391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25391 raw25391Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw25391 raw25391Labels = mixedMoment B raw25391step0 raw25391step0Labels := by
      have hz : ∀ j, raw25391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25391step0 = (fun i j => raw25391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25391step0 raw25391; decide +kernel
      have hl : raw25391step0Labels = raw25391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25391 raw25391Labels permutation346 hz
    mixedMoment B raw25391step0 raw25391step0Labels = mixedMoment B raw25391step1 raw25391step1Labels := by
      have ha : raw25391step1 = (fun i j => raw25391step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25391step1 raw25391step0; decide +kernel
      have hl : raw25391step1Labels = raw25391step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25391step0 raw25391step0Labels permutation40 permutation7
    mixedMoment B raw25391step1 raw25391step1Labels = mixedMoment B raw25391step2 raw25391step2Labels := by
      have ha : raw25391step2 = -raw25391step1 := by apply Matrix.ext; change ∀ i j, raw25391step2 i j = -(raw25391step1 i j); unfold raw25391step2 raw25391step1; decide +kernel
      have hl : raw25391step2Labels = raw25391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25391step2 raw25391step2Labels = mixedMoment B raw25391step3 raw25391step3Labels := by
      have ha : raw25391step3 = raw25391step2 := by apply Matrix.ext; unfold raw25391step3 raw25391step2; decide +kernel
      have hl : raw25391step2Labels = labelEmbedding1 ∘ raw25391step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25391step2 raw25391step2Labels raw25391step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical25392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25392 raw25392Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw25392 raw25392Labels = mixedMoment B raw25392step0 raw25392step0Labels := by
      have ha : raw25392step0 = (fun i j => raw25392 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25392step0 raw25392; decide +kernel
      have hl : raw25392step0Labels = raw25392Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25392 raw25392Labels permutation184 permutation7
    mixedMoment B raw25392step0 raw25392step0Labels = mixedMoment B raw25392step1 raw25392step1Labels := by
      have ha : raw25392step1 = -raw25392step0 := by apply Matrix.ext; change ∀ i j, raw25392step1 i j = -(raw25392step0 i j); unfold raw25392step1 raw25392step0; decide +kernel
      have hl : raw25392step1Labels = raw25392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25392step1 raw25392step1Labels = mixedMoment B raw25392step2 raw25392step2Labels := by
      have ha : raw25392step2 = raw25392step1 := by apply Matrix.ext; unfold raw25392step2 raw25392step1; decide +kernel
      have hl : raw25392step1Labels = labelEmbedding1 ∘ raw25392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25392step1 raw25392step1Labels raw25392step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical25393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25393 raw25393Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw25393 raw25393Labels = mixedMoment B raw25393step0 raw25393step0Labels := by
      have hz : ∀ j, raw25393 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25393step0 = (fun i j => raw25393 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25393step0 raw25393; decide +kernel
      have hl : raw25393step0Labels = raw25393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25393 raw25393Labels permutation520 hz
    mixedMoment B raw25393step0 raw25393step0Labels = mixedMoment B raw25393step1 raw25393step1Labels := by
      have hz : ∀ j, raw25393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25393step1 = (fun i j => raw25393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25393step1 raw25393step0; decide +kernel
      have hl : raw25393step1Labels = raw25393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25393step0 raw25393step0Labels permutation80 hz
    mixedMoment B raw25393step1 raw25393step1Labels = mixedMoment B raw25393step2 raw25393step2Labels := by
      have ha : raw25393step2 = (fun i j => raw25393step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25393step2 raw25393step1; decide +kernel
      have hl : raw25393step2Labels = raw25393step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25393step1 raw25393step1Labels permutation10 permutation7
    mixedMoment B raw25393step2 raw25393step2Labels = mixedMoment B raw25393step3 raw25393step3Labels := by
      have ha : raw25393step3 = -raw25393step2 := by apply Matrix.ext; change ∀ i j, raw25393step3 i j = -(raw25393step2 i j); unfold raw25393step3 raw25393step2; decide +kernel
      have hl : raw25393step3Labels = raw25393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25393step3 raw25393step3Labels = mixedMoment B raw25393step4 raw25393step4Labels := by
      have ha : raw25393step4 = raw25393step3 := by apply Matrix.ext; unfold raw25393step4 raw25393step3; decide +kernel
      have hl : raw25393step3Labels = labelEmbedding1 ∘ raw25393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25393step3 raw25393step3Labels raw25393step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical25394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25394 raw25394Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw25394 raw25394Labels = mixedMoment B raw25394step0 raw25394step0Labels := by
      have hz : ∀ j, raw25394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25394step0 = (fun i j => raw25394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25394step0 raw25394; decide +kernel
      have hl : raw25394step0Labels = raw25394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25394 raw25394Labels permutation346 hz
    mixedMoment B raw25394step0 raw25394step0Labels = mixedMoment B raw25394step1 raw25394step1Labels := by
      have ha : raw25394step1 = (fun i j => raw25394step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25394step1 raw25394step0; decide +kernel
      have hl : raw25394step1Labels = raw25394step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25394step0 raw25394step0Labels permutation40 permutation7
    mixedMoment B raw25394step1 raw25394step1Labels = mixedMoment B raw25394step2 raw25394step2Labels := by
      have ha : raw25394step2 = -raw25394step1 := by apply Matrix.ext; change ∀ i j, raw25394step2 i j = -(raw25394step1 i j); unfold raw25394step2 raw25394step1; decide +kernel
      have hl : raw25394step2Labels = raw25394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25394step2 raw25394step2Labels = mixedMoment B raw25394step3 raw25394step3Labels := by
      have ha : raw25394step3 = raw25394step2 := by apply Matrix.ext; unfold raw25394step3 raw25394step2; decide +kernel
      have hl : raw25394step2Labels = labelEmbedding1 ∘ raw25394step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25394step2 raw25394step2Labels raw25394step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical25395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25395 raw25395Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw25395 raw25395Labels = mixedMoment B raw25395step0 raw25395step0Labels := by
      have hz : ∀ j, raw25395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25395step0 = (fun i j => raw25395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25395step0 raw25395; decide +kernel
      have hl : raw25395step0Labels = raw25395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25395 raw25395Labels permutation346 hz
    mixedMoment B raw25395step0 raw25395step0Labels = mixedMoment B raw25395step1 raw25395step1Labels := by
      have ha : raw25395step1 = (fun i j => raw25395step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25395step1 raw25395step0; decide +kernel
      have hl : raw25395step1Labels = raw25395step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25395step0 raw25395step0Labels permutation40 permutation7
    mixedMoment B raw25395step1 raw25395step1Labels = mixedMoment B raw25395step2 raw25395step2Labels := by
      have ha : raw25395step2 = -raw25395step1 := by apply Matrix.ext; change ∀ i j, raw25395step2 i j = -(raw25395step1 i j); unfold raw25395step2 raw25395step1; decide +kernel
      have hl : raw25395step2Labels = raw25395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25395step2 raw25395step2Labels = mixedMoment B raw25395step3 raw25395step3Labels := by
      have ha : raw25395step3 = raw25395step2 := by apply Matrix.ext; unfold raw25395step3 raw25395step2; decide +kernel
      have hl : raw25395step2Labels = labelEmbedding1 ∘ raw25395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25395step2 raw25395step2Labels raw25395step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

theorem canonical25396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25396 raw25396Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw25396 raw25396Labels = mixedMoment B raw25396step0 raw25396step0Labels := by
      have ha : raw25396step0 = (fun i j => raw25396 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25396step0 raw25396; decide +kernel
      have hl : raw25396step0Labels = raw25396Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25396 raw25396Labels permutation184 permutation7
    mixedMoment B raw25396step0 raw25396step0Labels = mixedMoment B raw25396step1 raw25396step1Labels := by
      have ha : raw25396step1 = -raw25396step0 := by apply Matrix.ext; change ∀ i j, raw25396step1 i j = -(raw25396step0 i j); unfold raw25396step1 raw25396step0; decide +kernel
      have hl : raw25396step1Labels = raw25396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25396step1 raw25396step1Labels = mixedMoment B raw25396step2 raw25396step2Labels := by
      have ha : raw25396step2 = raw25396step1 := by apply Matrix.ext; unfold raw25396step2 raw25396step1; decide +kernel
      have hl : raw25396step1Labels = labelEmbedding1 ∘ raw25396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25396step1 raw25396step1Labels raw25396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

theorem canonical25397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25397 raw25397Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw25397 raw25397Labels = mixedMoment B raw25397step0 raw25397step0Labels := by
      have hz : ∀ j, raw25397 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25397step0 = (fun i j => raw25397 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25397step0 raw25397; decide +kernel
      have hl : raw25397step0Labels = raw25397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25397 raw25397Labels permutation520 hz
    mixedMoment B raw25397step0 raw25397step0Labels = mixedMoment B raw25397step1 raw25397step1Labels := by
      have hz : ∀ j, raw25397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25397step1 = (fun i j => raw25397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25397step1 raw25397step0; decide +kernel
      have hl : raw25397step1Labels = raw25397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25397step0 raw25397step0Labels permutation80 hz
    mixedMoment B raw25397step1 raw25397step1Labels = mixedMoment B raw25397step2 raw25397step2Labels := by
      have ha : raw25397step2 = (fun i j => raw25397step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25397step2 raw25397step1; decide +kernel
      have hl : raw25397step2Labels = raw25397step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25397step1 raw25397step1Labels permutation10 permutation7
    mixedMoment B raw25397step2 raw25397step2Labels = mixedMoment B raw25397step3 raw25397step3Labels := by
      have ha : raw25397step3 = -raw25397step2 := by apply Matrix.ext; change ∀ i j, raw25397step3 i j = -(raw25397step2 i j); unfold raw25397step3 raw25397step2; decide +kernel
      have hl : raw25397step3Labels = raw25397step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25397step3 raw25397step3Labels = mixedMoment B raw25397step4 raw25397step4Labels := by
      have ha : raw25397step4 = raw25397step3 := by apply Matrix.ext; unfold raw25397step4 raw25397step3; decide +kernel
      have hl : raw25397step3Labels = labelEmbedding1 ∘ raw25397step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25397step3 raw25397step3Labels raw25397step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical25398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25398 raw25398Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25398 raw25398Labels = mixedMoment B raw25398step0 raw25398step0Labels := by
      have hz : ∀ j, raw25398 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25398step0 = (fun i j => raw25398 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25398step0 raw25398; decide +kernel
      have hl : raw25398step0Labels = raw25398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25398 raw25398Labels permutation346 hz
    mixedMoment B raw25398step0 raw25398step0Labels = mixedMoment B raw25398step1 raw25398step1Labels := by
      have ha : raw25398step1 = (fun i j => raw25398step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25398step1 raw25398step0; decide +kernel
      have hl : raw25398step1Labels = raw25398step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25398step0 raw25398step0Labels permutation40 permutation7
    mixedMoment B raw25398step1 raw25398step1Labels = mixedMoment B raw25398step2 raw25398step2Labels := by
      have ha : raw25398step2 = -raw25398step1 := by apply Matrix.ext; change ∀ i j, raw25398step2 i j = -(raw25398step1 i j); unfold raw25398step2 raw25398step1; decide +kernel
      have hl : raw25398step2Labels = raw25398step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25398step2 raw25398step2Labels = mixedMoment B raw25398step3 raw25398step3Labels := by
      have ha : raw25398step3 = raw25398step2 := by apply Matrix.ext; unfold raw25398step3 raw25398step2; decide +kernel
      have hl : raw25398step2Labels = labelEmbedding1 ∘ raw25398step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25398step2 raw25398step2Labels raw25398step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical25399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25399 raw25399Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw25399 raw25399Labels = mixedMoment B raw25399step0 raw25399step0Labels := by
      have ha : raw25399step0 = (fun i j => raw25399 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25399step0 raw25399; decide +kernel
      have hl : raw25399step0Labels = raw25399Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25399 raw25399Labels permutation184 permutation7
    mixedMoment B raw25399step0 raw25399step0Labels = mixedMoment B raw25399step1 raw25399step1Labels := by
      have ha : raw25399step1 = -raw25399step0 := by apply Matrix.ext; change ∀ i j, raw25399step1 i j = -(raw25399step0 i j); unfold raw25399step1 raw25399step0; decide +kernel
      have hl : raw25399step1Labels = raw25399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25399step1 raw25399step1Labels = mixedMoment B raw25399step2 raw25399step2Labels := by
      have ha : raw25399step2 = raw25399step1 := by apply Matrix.ext; unfold raw25399step2 raw25399step1; decide +kernel
      have hl : raw25399step1Labels = labelEmbedding1 ∘ raw25399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25399step1 raw25399step1Labels raw25399step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1501 node1501Labels := by rfl

theorem canonical25400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25400 raw25400Labels = mixedMoment B node1697 node1697Labels := by
  calc
    mixedMoment B raw25400 raw25400Labels = mixedMoment B raw25400step0 raw25400step0Labels := by
      have ha : raw25400step0 = (fun i j => raw25400 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25400step0 raw25400; decide +kernel
      have hl : raw25400step0Labels = raw25400Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25400 raw25400Labels permutation184 permutation7
    mixedMoment B raw25400step0 raw25400step0Labels = mixedMoment B raw25400step1 raw25400step1Labels := by
      have ha : raw25400step1 = -raw25400step0 := by apply Matrix.ext; change ∀ i j, raw25400step1 i j = -(raw25400step0 i j); unfold raw25400step1 raw25400step0; decide +kernel
      have hl : raw25400step1Labels = raw25400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25400step1 raw25400step1Labels = mixedMoment B raw25400step2 raw25400step2Labels := by
      have ha : raw25400step2 = raw25400step1 := by apply Matrix.ext; unfold raw25400step2 raw25400step1; decide +kernel
      have hl : raw25400step1Labels = labelEmbedding1 ∘ raw25400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25400step1 raw25400step1Labels raw25400step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1697 node1697Labels := by rfl

theorem canonical25401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25401 raw25401Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw25401 raw25401Labels = mixedMoment B raw25401step0 raw25401step0Labels := by
      have hz : ∀ j, raw25401 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25401step0 = (fun i j => raw25401 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25401step0 raw25401; decide +kernel
      have hl : raw25401step0Labels = raw25401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25401 raw25401Labels permutation520 hz
    mixedMoment B raw25401step0 raw25401step0Labels = mixedMoment B raw25401step1 raw25401step1Labels := by
      have ha : raw25401step1 = (fun i j => raw25401step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25401step1 raw25401step0; decide +kernel
      have hl : raw25401step1Labels = raw25401step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25401step0 raw25401step0Labels permutation40 permutation7
    mixedMoment B raw25401step1 raw25401step1Labels = mixedMoment B raw25401step2 raw25401step2Labels := by
      have ha : raw25401step2 = -raw25401step1 := by apply Matrix.ext; change ∀ i j, raw25401step2 i j = -(raw25401step1 i j); unfold raw25401step2 raw25401step1; decide +kernel
      have hl : raw25401step2Labels = raw25401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25401step2 raw25401step2Labels = mixedMoment B raw25401step3 raw25401step3Labels := by
      have ha : raw25401step3 = raw25401step2 := by apply Matrix.ext; unfold raw25401step3 raw25401step2; decide +kernel
      have hl : raw25401step2Labels = labelEmbedding1 ∘ raw25401step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25401step2 raw25401step2Labels raw25401step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical25402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25402 raw25402Labels = mixedMoment B node1698 node1698Labels := by
  calc
    mixedMoment B raw25402 raw25402Labels = mixedMoment B raw25402step0 raw25402step0Labels := by
      have ha : raw25402step0 = (fun i j => raw25402 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25402step0 raw25402; decide +kernel
      have hl : raw25402step0Labels = raw25402Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25402 raw25402Labels permutation184 permutation7
    mixedMoment B raw25402step0 raw25402step0Labels = mixedMoment B raw25402step1 raw25402step1Labels := by
      have ha : raw25402step1 = -raw25402step0 := by apply Matrix.ext; change ∀ i j, raw25402step1 i j = -(raw25402step0 i j); unfold raw25402step1 raw25402step0; decide +kernel
      have hl : raw25402step1Labels = raw25402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25402step1 raw25402step1Labels = mixedMoment B raw25402step2 raw25402step2Labels := by
      have ha : raw25402step2 = raw25402step1 := by apply Matrix.ext; unfold raw25402step2 raw25402step1; decide +kernel
      have hl : raw25402step1Labels = labelEmbedding1 ∘ raw25402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25402step1 raw25402step1Labels raw25402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1698 node1698Labels := by rfl

theorem canonical25403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25403 raw25403Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw25403 raw25403Labels = mixedMoment B raw25403step0 raw25403step0Labels := by
      have hz : ∀ j, raw25403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25403step0 = (fun i j => raw25403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25403step0 raw25403; decide +kernel
      have hl : raw25403step0Labels = raw25403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25403 raw25403Labels permutation346 hz
    mixedMoment B raw25403step0 raw25403step0Labels = mixedMoment B raw25403step1 raw25403step1Labels := by
      have ha : raw25403step1 = (fun i j => raw25403step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25403step1 raw25403step0; decide +kernel
      have hl : raw25403step1Labels = raw25403step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25403step0 raw25403step0Labels permutation46 permutation7
    mixedMoment B raw25403step1 raw25403step1Labels = mixedMoment B raw25403step2 raw25403step2Labels := by
      have ha : raw25403step2 = -raw25403step1 := by apply Matrix.ext; change ∀ i j, raw25403step2 i j = -(raw25403step1 i j); unfold raw25403step2 raw25403step1; decide +kernel
      have hl : raw25403step2Labels = raw25403step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25403step2 raw25403step2Labels = mixedMoment B raw25403step3 raw25403step3Labels := by
      have ha : raw25403step3 = raw25403step2 := by apply Matrix.ext; unfold raw25403step3 raw25403step2; decide +kernel
      have hl : raw25403step2Labels = labelEmbedding1 ∘ raw25403step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25403step2 raw25403step2Labels raw25403step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical25404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25404 raw25404Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw25404 raw25404Labels = mixedMoment B raw25404step0 raw25404step0Labels := by
      have hz : ∀ j, raw25404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25404step0 = (fun i j => raw25404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25404step0 raw25404; decide +kernel
      have hl : raw25404step0Labels = raw25404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25404 raw25404Labels permutation346 hz
    mixedMoment B raw25404step0 raw25404step0Labels = mixedMoment B raw25404step1 raw25404step1Labels := by
      have ha : raw25404step1 = (fun i j => raw25404step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25404step1 raw25404step0; decide +kernel
      have hl : raw25404step1Labels = raw25404step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25404step0 raw25404step0Labels permutation46 permutation7
    mixedMoment B raw25404step1 raw25404step1Labels = mixedMoment B raw25404step2 raw25404step2Labels := by
      have ha : raw25404step2 = -raw25404step1 := by apply Matrix.ext; change ∀ i j, raw25404step2 i j = -(raw25404step1 i j); unfold raw25404step2 raw25404step1; decide +kernel
      have hl : raw25404step2Labels = raw25404step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25404step2 raw25404step2Labels = mixedMoment B raw25404step3 raw25404step3Labels := by
      have ha : raw25404step3 = raw25404step2 := by apply Matrix.ext; unfold raw25404step3 raw25404step2; decide +kernel
      have hl : raw25404step2Labels = labelEmbedding1 ∘ raw25404step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25404step2 raw25404step2Labels raw25404step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical25405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25405 raw25405Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw25405 raw25405Labels = mixedMoment B raw25405step0 raw25405step0Labels := by
      have ha : raw25405step0 = (fun i j => raw25405 (permutation190 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25405step0 raw25405; decide +kernel
      have hl : raw25405step0Labels = raw25405Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25405 raw25405Labels permutation190 permutation7
    mixedMoment B raw25405step0 raw25405step0Labels = mixedMoment B raw25405step1 raw25405step1Labels := by
      have ha : raw25405step1 = -raw25405step0 := by apply Matrix.ext; change ∀ i j, raw25405step1 i j = -(raw25405step0 i j); unfold raw25405step1 raw25405step0; decide +kernel
      have hl : raw25405step1Labels = raw25405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25405step1 raw25405step1Labels = mixedMoment B raw25405step2 raw25405step2Labels := by
      have ha : raw25405step2 = raw25405step1 := by apply Matrix.ext; unfold raw25405step2 raw25405step1; decide +kernel
      have hl : raw25405step1Labels = labelEmbedding1 ∘ raw25405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25405step1 raw25405step1Labels raw25405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical25406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25406 raw25406Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw25406 raw25406Labels = mixedMoment B raw25406step0 raw25406step0Labels := by
      have hz : ∀ j, raw25406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25406step0 = (fun i j => raw25406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25406step0 raw25406; decide +kernel
      have hl : raw25406step0Labels = raw25406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25406 raw25406Labels permutation520 hz
    mixedMoment B raw25406step0 raw25406step0Labels = mixedMoment B raw25406step1 raw25406step1Labels := by
      have hz : ∀ j, raw25406step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25406step1 = (fun i j => raw25406step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25406step1 raw25406step0; decide +kernel
      have hl : raw25406step1Labels = raw25406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25406step0 raw25406step0Labels permutation80 hz
    mixedMoment B raw25406step1 raw25406step1Labels = mixedMoment B raw25406step2 raw25406step2Labels := by
      have ha : raw25406step2 = (fun i j => raw25406step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25406step2 raw25406step1; decide +kernel
      have hl : raw25406step2Labels = raw25406step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25406step1 raw25406step1Labels permutation10 permutation7
    mixedMoment B raw25406step2 raw25406step2Labels = mixedMoment B raw25406step3 raw25406step3Labels := by
      have ha : raw25406step3 = -raw25406step2 := by apply Matrix.ext; change ∀ i j, raw25406step3 i j = -(raw25406step2 i j); unfold raw25406step3 raw25406step2; decide +kernel
      have hl : raw25406step3Labels = raw25406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25406step3 raw25406step3Labels = mixedMoment B raw25406step4 raw25406step4Labels := by
      have ha : raw25406step4 = raw25406step3 := by apply Matrix.ext; unfold raw25406step4 raw25406step3; decide +kernel
      have hl : raw25406step3Labels = labelEmbedding1 ∘ raw25406step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25406step3 raw25406step3Labels raw25406step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical25407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25407 raw25407Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw25407 raw25407Labels = mixedMoment B raw25407step0 raw25407step0Labels := by
      have hz : ∀ j, raw25407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25407step0 = (fun i j => raw25407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25407step0 raw25407; decide +kernel
      have hl : raw25407step0Labels = raw25407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25407 raw25407Labels permutation346 hz
    mixedMoment B raw25407step0 raw25407step0Labels = mixedMoment B raw25407step1 raw25407step1Labels := by
      have ha : raw25407step1 = (fun i j => raw25407step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25407step1 raw25407step0; decide +kernel
      have hl : raw25407step1Labels = raw25407step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25407step0 raw25407step0Labels permutation46 permutation7
    mixedMoment B raw25407step1 raw25407step1Labels = mixedMoment B raw25407step2 raw25407step2Labels := by
      have ha : raw25407step2 = -raw25407step1 := by apply Matrix.ext; change ∀ i j, raw25407step2 i j = -(raw25407step1 i j); unfold raw25407step2 raw25407step1; decide +kernel
      have hl : raw25407step2Labels = raw25407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25407step2 raw25407step2Labels = mixedMoment B raw25407step3 raw25407step3Labels := by
      have ha : raw25407step3 = raw25407step2 := by apply Matrix.ext; unfold raw25407step3 raw25407step2; decide +kernel
      have hl : raw25407step2Labels = labelEmbedding1 ∘ raw25407step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25407step2 raw25407step2Labels raw25407step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical25408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25408 raw25408Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw25408 raw25408Labels = mixedMoment B raw25408step0 raw25408step0Labels := by
      have hz : ∀ j, raw25408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25408step0 = (fun i j => raw25408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25408step0 raw25408; decide +kernel
      have hl : raw25408step0Labels = raw25408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25408 raw25408Labels permutation346 hz
    mixedMoment B raw25408step0 raw25408step0Labels = mixedMoment B raw25408step1 raw25408step1Labels := by
      have ha : raw25408step1 = (fun i j => raw25408step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25408step1 raw25408step0; decide +kernel
      have hl : raw25408step1Labels = raw25408step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25408step0 raw25408step0Labels permutation40 permutation7
    mixedMoment B raw25408step1 raw25408step1Labels = mixedMoment B raw25408step2 raw25408step2Labels := by
      have ha : raw25408step2 = -raw25408step1 := by apply Matrix.ext; change ∀ i j, raw25408step2 i j = -(raw25408step1 i j); unfold raw25408step2 raw25408step1; decide +kernel
      have hl : raw25408step2Labels = raw25408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25408step2 raw25408step2Labels = mixedMoment B raw25408step3 raw25408step3Labels := by
      have ha : raw25408step3 = raw25408step2 := by apply Matrix.ext; unfold raw25408step3 raw25408step2; decide +kernel
      have hl : raw25408step2Labels = labelEmbedding1 ∘ raw25408step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25408step2 raw25408step2Labels raw25408step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical25409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25409 raw25409Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw25409 raw25409Labels = mixedMoment B raw25409step0 raw25409step0Labels := by
      have hz : ∀ j, raw25409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25409step0 = (fun i j => raw25409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25409step0 raw25409; decide +kernel
      have hl : raw25409step0Labels = raw25409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25409 raw25409Labels permutation346 hz
    mixedMoment B raw25409step0 raw25409step0Labels = mixedMoment B raw25409step1 raw25409step1Labels := by
      have ha : raw25409step1 = (fun i j => raw25409step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25409step1 raw25409step0; decide +kernel
      have hl : raw25409step1Labels = raw25409step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25409step0 raw25409step0Labels permutation40 permutation7
    mixedMoment B raw25409step1 raw25409step1Labels = mixedMoment B raw25409step2 raw25409step2Labels := by
      have ha : raw25409step2 = -raw25409step1 := by apply Matrix.ext; change ∀ i j, raw25409step2 i j = -(raw25409step1 i j); unfold raw25409step2 raw25409step1; decide +kernel
      have hl : raw25409step2Labels = raw25409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25409step2 raw25409step2Labels = mixedMoment B raw25409step3 raw25409step3Labels := by
      have ha : raw25409step3 = raw25409step2 := by apply Matrix.ext; unfold raw25409step3 raw25409step2; decide +kernel
      have hl : raw25409step2Labels = labelEmbedding1 ∘ raw25409step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25409step2 raw25409step2Labels raw25409step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical25410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25410 raw25410Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw25410 raw25410Labels = mixedMoment B raw25410step0 raw25410step0Labels := by
      have ha : raw25410step0 = (fun i j => raw25410 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25410step0 raw25410; decide +kernel
      have hl : raw25410step0Labels = raw25410Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25410 raw25410Labels permutation184 permutation7
    mixedMoment B raw25410step0 raw25410step0Labels = mixedMoment B raw25410step1 raw25410step1Labels := by
      have ha : raw25410step1 = -raw25410step0 := by apply Matrix.ext; change ∀ i j, raw25410step1 i j = -(raw25410step0 i j); unfold raw25410step1 raw25410step0; decide +kernel
      have hl : raw25410step1Labels = raw25410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25410step1 raw25410step1Labels = mixedMoment B raw25410step2 raw25410step2Labels := by
      have ha : raw25410step2 = raw25410step1 := by apply Matrix.ext; unfold raw25410step2 raw25410step1; decide +kernel
      have hl : raw25410step1Labels = labelEmbedding1 ∘ raw25410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25410step1 raw25410step1Labels raw25410step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical25411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25411 raw25411Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw25411 raw25411Labels = mixedMoment B raw25411step0 raw25411step0Labels := by
      have hz : ∀ j, raw25411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25411step0 = (fun i j => raw25411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25411step0 raw25411; decide +kernel
      have hl : raw25411step0Labels = raw25411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25411 raw25411Labels permutation346 hz
    mixedMoment B raw25411step0 raw25411step0Labels = mixedMoment B raw25411step1 raw25411step1Labels := by
      have ha : raw25411step1 = (fun i j => raw25411step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25411step1 raw25411step0; decide +kernel
      have hl : raw25411step1Labels = raw25411step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25411step0 raw25411step0Labels permutation40 permutation7
    mixedMoment B raw25411step1 raw25411step1Labels = mixedMoment B raw25411step2 raw25411step2Labels := by
      have ha : raw25411step2 = -raw25411step1 := by apply Matrix.ext; change ∀ i j, raw25411step2 i j = -(raw25411step1 i j); unfold raw25411step2 raw25411step1; decide +kernel
      have hl : raw25411step2Labels = raw25411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25411step2 raw25411step2Labels = mixedMoment B raw25411step3 raw25411step3Labels := by
      have ha : raw25411step3 = raw25411step2 := by apply Matrix.ext; unfold raw25411step3 raw25411step2; decide +kernel
      have hl : raw25411step2Labels = labelEmbedding1 ∘ raw25411step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25411step2 raw25411step2Labels raw25411step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical25412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25412 raw25412Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw25412 raw25412Labels = mixedMoment B raw25412step0 raw25412step0Labels := by
      have hz : ∀ j, raw25412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25412step0 = (fun i j => raw25412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25412step0 raw25412; decide +kernel
      have hl : raw25412step0Labels = raw25412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25412 raw25412Labels permutation434 hz
    mixedMoment B raw25412step0 raw25412step0Labels = mixedMoment B raw25412step1 raw25412step1Labels := by
      have hz : ∀ j, raw25412step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25412step1 = (fun i j => raw25412step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25412step1 raw25412step0; decide +kernel
      have hl : raw25412step1Labels = raw25412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25412step0 raw25412step0Labels permutation80 hz
    mixedMoment B raw25412step1 raw25412step1Labels = mixedMoment B raw25412step2 raw25412step2Labels := by
      have ha : raw25412step2 = (fun i j => raw25412step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25412step2 raw25412step1; decide +kernel
      have hl : raw25412step2Labels = raw25412step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25412step1 raw25412step1Labels permutation10 permutation7
    mixedMoment B raw25412step2 raw25412step2Labels = mixedMoment B raw25412step3 raw25412step3Labels := by
      have ha : raw25412step3 = -raw25412step2 := by apply Matrix.ext; change ∀ i j, raw25412step3 i j = -(raw25412step2 i j); unfold raw25412step3 raw25412step2; decide +kernel
      have hl : raw25412step3Labels = raw25412step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25412step3 raw25412step3Labels = mixedMoment B raw25412step4 raw25412step4Labels := by
      have ha : raw25412step4 = raw25412step3 := by apply Matrix.ext; unfold raw25412step4 raw25412step3; decide +kernel
      have hl : raw25412step3Labels = labelEmbedding1 ∘ raw25412step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25412step3 raw25412step3Labels raw25412step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

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

theorem canonical25414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25414 raw25414Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw25414 raw25414Labels = mixedMoment B raw25414step0 raw25414step0Labels := by
      have hz : ∀ j, raw25414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25414step0 = (fun i j => raw25414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25414step0 raw25414; decide +kernel
      have hl : raw25414step0Labels = raw25414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25414 raw25414Labels permutation346 hz
    mixedMoment B raw25414step0 raw25414step0Labels = mixedMoment B raw25414step1 raw25414step1Labels := by
      have ha : raw25414step1 = (fun i j => raw25414step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25414step1 raw25414step0; decide +kernel
      have hl : raw25414step1Labels = raw25414step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25414step0 raw25414step0Labels permutation40 permutation2
    _ = mixedMoment B node600 node600Labels := by rfl

theorem canonical25415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25415 raw25415Labels = mixedMoment B node577 node577Labels := by
  calc
    _ = mixedMoment B node577 node577Labels := by rfl

theorem canonical25416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25416 raw25416Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw25416 raw25416Labels = mixedMoment B raw25416step0 raw25416step0Labels := by
      have hz : ∀ j, raw25416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25416step0 = (fun i j => raw25416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25416step0 raw25416; decide +kernel
      have hl : raw25416step0Labels = raw25416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25416 raw25416Labels permutation346 hz
    mixedMoment B raw25416step0 raw25416step0Labels = mixedMoment B raw25416step1 raw25416step1Labels := by
      have ha : raw25416step1 = (fun i j => raw25416step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25416step1 raw25416step0; decide +kernel
      have hl : raw25416step1Labels = raw25416step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25416step0 raw25416step0Labels permutation34 permutation2
    _ = mixedMoment B node582 node582Labels := by rfl

theorem canonical25417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25417 raw25417Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw25417 raw25417Labels = mixedMoment B raw25417step0 raw25417step0Labels := by
      have hz : ∀ j, raw25417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25417step0 = (fun i j => raw25417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25417step0 raw25417; decide +kernel
      have hl : raw25417step0Labels = raw25417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25417 raw25417Labels permutation346 hz
    _ = mixedMoment B node582 node582Labels := by rfl

theorem canonical25418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25418 raw25418Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw25418 raw25418Labels = mixedMoment B raw25418step0 raw25418step0Labels := by
      have ha : raw25418step0 = (fun i j => raw25418 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25418step0 raw25418; decide +kernel
      have hl : raw25418step0Labels = raw25418Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25418 raw25418Labels permutation184 permutation2
    _ = mixedMoment B node919 node919Labels := by rfl

theorem canonical25419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25419 raw25419Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw25419 raw25419Labels = mixedMoment B raw25419step0 raw25419step0Labels := by
      have hz : ∀ j, raw25419 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25419step0 = (fun i j => raw25419 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25419step0 raw25419; decide +kernel
      have hl : raw25419step0Labels = raw25419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25419 raw25419Labels permutation520 hz
    mixedMoment B raw25419step0 raw25419step0Labels = mixedMoment B raw25419step1 raw25419step1Labels := by
      have hz : ∀ j, raw25419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25419step1 = (fun i j => raw25419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25419step1 raw25419step0; decide +kernel
      have hl : raw25419step1Labels = raw25419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25419step0 raw25419step0Labels permutation80 hz
    mixedMoment B raw25419step1 raw25419step1Labels = mixedMoment B raw25419step2 raw25419step2Labels := by
      have ha : raw25419step2 = (fun i j => raw25419step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25419step2 raw25419step1; decide +kernel
      have hl : raw25419step2Labels = raw25419step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25419step1 raw25419step1Labels permutation10 permutation2
    _ = mixedMoment B node1082 node1082Labels := by rfl

theorem canonical25420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25420 raw25420Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25420 raw25420Labels = mixedMoment B raw25420step0 raw25420step0Labels := by
      have hz : ∀ j, raw25420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25420step0 = (fun i j => raw25420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25420step0 raw25420; decide +kernel
      have hl : raw25420step0Labels = raw25420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25420 raw25420Labels permutation346 hz
    mixedMoment B raw25420step0 raw25420step0Labels = mixedMoment B raw25420step1 raw25420step1Labels := by
      have ha : raw25420step1 = (fun i j => raw25420step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25420step1 raw25420step0; decide +kernel
      have hl : raw25420step1Labels = raw25420step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25420step0 raw25420step0Labels permutation40 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw804 raw804Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw804 raw804Labels = mixedMoment B raw804step0 raw804step0Labels := by
      have ha : raw804step0 = (fun i j => raw804 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw804step0 raw804; decide +kernel
      have hl : raw804step0Labels = raw804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw804 raw804Labels permutation32 permutation4
    mixedMoment B raw804step0 raw804step0Labels = mixedMoment B raw804step1 raw804step1Labels := by
      have ha : raw804step1 = raw804step0 := by apply Matrix.ext; unfold raw804step1 raw804step0; decide +kernel
      have hl : raw804step0Labels = labelEmbedding7 ∘ raw804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw804step0 raw804step0Labels raw804step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

theorem canonical805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw805 raw805Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw805 raw805Labels = mixedMoment B raw805step0 raw805step0Labels := by
      have ha : raw805step0 = (fun i j => raw805 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw805step0 raw805; decide +kernel
      have hl : raw805step0Labels = raw805Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw805 raw805Labels permutation32 permutation4
    _ = mixedMoment B node600 node600Labels := by rfl

theorem canonical806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw806 raw806Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw806 raw806Labels = mixedMoment B raw806step0 raw806step0Labels := by
      have ha : raw806step0 = (fun i j => raw806 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw806step0 raw806; decide +kernel
      have hl : raw806step0Labels = raw806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw806 raw806Labels permutation32 permutation6
    mixedMoment B raw806step0 raw806step0Labels = mixedMoment B raw806step1 raw806step1Labels := by
      have ha : raw806step1 = -raw806step0 := by apply Matrix.ext; change ∀ i j, raw806step1 i j = -(raw806step0 i j); unfold raw806step1 raw806step0; decide +kernel
      have hl : raw806step1Labels = raw806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw806step1 raw806step1Labels = mixedMoment B raw806step2 raw806step2Labels := by
      have ha : raw806step2 = raw806step1 := by apply Matrix.ext; unfold raw806step2 raw806step1; decide +kernel
      have hl : raw806step1Labels = labelEmbedding1 ∘ raw806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw806step1 raw806step1Labels raw806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11476 raw11476Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw11476 raw11476Labels = mixedMoment B raw11476step0 raw11476step0Labels := by
      have hz : ∀ j, raw11476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11476step0 = (fun i j => raw11476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11476step0 raw11476; decide +kernel
      have hl : raw11476step0Labels = raw11476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11476 raw11476Labels permutation434 hz
    mixedMoment B raw11476step0 raw11476step0Labels = mixedMoment B raw11476step1 raw11476step1Labels := by
      have hz : ∀ j, raw11476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11476step1 = (fun i j => raw11476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11476step1 raw11476step0; decide +kernel
      have hl : raw11476step1Labels = raw11476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11476step0 raw11476step0Labels permutation80 hz
    mixedMoment B raw11476step1 raw11476step1Labels = mixedMoment B raw11476step2 raw11476step2Labels := by
      have ha : raw11476step2 = (fun i j => raw11476step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11476step2 raw11476step1; decide +kernel
      have hl : raw11476step2Labels = raw11476step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11476step1 raw11476step1Labels permutation10 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical11481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11481 raw11481Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw11481 raw11481Labels = mixedMoment B raw11481step0 raw11481step0Labels := by
      have hz : ∀ j, raw11481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11481step0 = (fun i j => raw11481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11481step0 raw11481; decide +kernel
      have hl : raw11481step0Labels = raw11481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11481 raw11481Labels permutation434 hz
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical11487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11487 raw11487Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw11487 raw11487Labels = mixedMoment B raw11487step0 raw11487step0Labels := by
      have hz : ∀ j, raw11487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11487step0 = (fun i j => raw11487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11487step0 raw11487; decide +kernel
      have hl : raw11487step0Labels = raw11487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11487 raw11487Labels permutation346 hz
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical11488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11488 raw11488Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw11488 raw11488Labels = mixedMoment B raw11488step0 raw11488step0Labels := by
      have ha : raw11488step0 = (fun i j => raw11488 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11488step0 raw11488; decide +kernel
      have hl : raw11488step0Labels = raw11488Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11488 raw11488Labels permutation176 permutation2
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical11489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11489 raw11489Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw11489 raw11489Labels = mixedMoment B raw11489step0 raw11489step0Labels := by
      have hz : ∀ j, raw11489 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11489step0 = (fun i j => raw11489 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11489step0 raw11489; decide +kernel
      have hl : raw11489step0Labels = raw11489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11489 raw11489Labels permutation520 hz
    mixedMoment B raw11489step0 raw11489step0Labels = mixedMoment B raw11489step1 raw11489step1Labels := by
      have hz : ∀ j, raw11489step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11489step1 = (fun i j => raw11489step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11489step1 raw11489step0; decide +kernel
      have hl : raw11489step1Labels = raw11489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11489step0 raw11489step0Labels permutation80 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical11490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11490 raw11490Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11490 raw11490Labels = mixedMoment B raw11490step0 raw11490step0Labels := by
      have hz : ∀ j, raw11490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11490step0 = (fun i j => raw11490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11490step0 raw11490; decide +kernel
      have hl : raw11490step0Labels = raw11490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11490 raw11490Labels permutation346 hz
    mixedMoment B raw11490step0 raw11490step0Labels = mixedMoment B raw11490step1 raw11490step1Labels := by
      have ha : raw11490step1 = (fun i j => raw11490step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11490step1 raw11490step0; decide +kernel
      have hl : raw11490step1Labels = raw11490step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11490step0 raw11490step0Labels permutation40 permutation7
    mixedMoment B raw11490step1 raw11490step1Labels = mixedMoment B raw11490step2 raw11490step2Labels := by
      have ha : raw11490step2 = -raw11490step1 := by apply Matrix.ext; change ∀ i j, raw11490step2 i j = -(raw11490step1 i j); unfold raw11490step2 raw11490step1; decide +kernel
      have hl : raw11490step2Labels = raw11490step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11490step2 raw11490step2Labels = mixedMoment B raw11490step3 raw11490step3Labels := by
      have ha : raw11490step3 = raw11490step2 := by apply Matrix.ext; unfold raw11490step3 raw11490step2; decide +kernel
      have hl : raw11490step2Labels = labelEmbedding10 ∘ raw11490step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11490step2 raw11490step2Labels raw11490step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11491 raw11491Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw11491 raw11491Labels = mixedMoment B raw11491step0 raw11491step0Labels := by
      have hz : ∀ j, raw11491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11491step0 = (fun i j => raw11491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11491step0 raw11491; decide +kernel
      have hl : raw11491step0Labels = raw11491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11491 raw11491Labels permutation434 hz
    mixedMoment B raw11491step0 raw11491step0Labels = mixedMoment B raw11491step1 raw11491step1Labels := by
      have hz : ∀ j, raw11491step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11491step1 = (fun i j => raw11491step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11491step1 raw11491step0; decide +kernel
      have hl : raw11491step1Labels = raw11491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11491step0 raw11491step0Labels permutation80 hz
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical11496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11496 raw11496Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw11496 raw11496Labels = mixedMoment B raw11496step0 raw11496step0Labels := by
      have hz : ∀ j, raw11496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11496step0 = (fun i j => raw11496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11496step0 raw11496; decide +kernel
      have hl : raw11496step0Labels = raw11496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11496 raw11496Labels permutation434 hz
    mixedMoment B raw11496step0 raw11496step0Labels = mixedMoment B raw11496step1 raw11496step1Labels := by
      have hz : ∀ j, raw11496step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11496step1 = (fun i j => raw11496step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11496step1 raw11496step0; decide +kernel
      have hl : raw11496step1Labels = raw11496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11496step0 raw11496step0Labels permutation80 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

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

theorem canonical1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1263 raw1263Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw1263 raw1263Labels = mixedMoment B raw1263step0 raw1263step0Labels := by
      have ha : raw1263step0 = (fun i j => raw1263 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1263step0 raw1263; decide +kernel
      have hl : raw1263step0Labels = raw1263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1263 raw1263Labels permutation8 permutation4
    mixedMoment B raw1263step0 raw1263step0Labels = mixedMoment B raw1263step1 raw1263step1Labels := by
      have ha : raw1263step1 = raw1263step0 := by apply Matrix.ext; unfold raw1263step1 raw1263step0; decide +kernel
      have hl : raw1263step0Labels = labelEmbedding7 ∘ raw1263step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1263step0 raw1263step0Labels raw1263step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1264 raw1264Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw1264 raw1264Labels = mixedMoment B raw1264step0 raw1264step0Labels := by
      have ha : raw1264step0 = (fun i j => raw1264 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1264step0 raw1264; decide +kernel
      have hl : raw1264step0Labels = raw1264Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1264 raw1264Labels permutation8 permutation4
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical1265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1265 raw1265Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw1265 raw1265Labels = mixedMoment B raw1265step0 raw1265step0Labels := by
      have ha : raw1265step0 = (fun i j => raw1265 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1265step0 raw1265; decide +kernel
      have hl : raw1265step0Labels = raw1265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1265 raw1265Labels permutation10 permutation6
    mixedMoment B raw1265step0 raw1265step0Labels = mixedMoment B raw1265step1 raw1265step1Labels := by
      have ha : raw1265step1 = -raw1265step0 := by apply Matrix.ext; change ∀ i j, raw1265step1 i j = -(raw1265step0 i j); unfold raw1265step1 raw1265step0; decide +kernel
      have hl : raw1265step1Labels = raw1265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1265step1 raw1265step1Labels = mixedMoment B raw1265step2 raw1265step2Labels := by
      have ha : raw1265step2 = raw1265step1 := by apply Matrix.ext; unfold raw1265step2 raw1265step1; decide +kernel
      have hl : raw1265step1Labels = labelEmbedding1 ∘ raw1265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1265step1 raw1265step1Labels raw1265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical1272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1272 raw1272Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw1272 raw1272Labels = mixedMoment B raw1272step0 raw1272step0Labels := by
      have ha : raw1272step0 = (fun i j => raw1272 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1272step0 raw1272; decide +kernel
      have hl : raw1272step0Labels = raw1272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1272 raw1272Labels permutation8 permutation4
    mixedMoment B raw1272step0 raw1272step0Labels = mixedMoment B raw1272step1 raw1272step1Labels := by
      have ha : raw1272step1 = raw1272step0 := by apply Matrix.ext; unfold raw1272step1 raw1272step0; decide +kernel
      have hl : raw1272step0Labels = labelEmbedding7 ∘ raw1272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1272step0 raw1272step0Labels raw1272step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1273 raw1273Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw1273 raw1273Labels = mixedMoment B raw1273step0 raw1273step0Labels := by
      have ha : raw1273step0 = (fun i j => raw1273 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1273step0 raw1273; decide +kernel
      have hl : raw1273step0Labels = raw1273Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1273 raw1273Labels permutation8 permutation4
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical1274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1274 raw1274Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw1274 raw1274Labels = mixedMoment B raw1274step0 raw1274step0Labels := by
      have ha : raw1274step0 = (fun i j => raw1274 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1274step0 raw1274; decide +kernel
      have hl : raw1274step0Labels = raw1274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1274 raw1274Labels permutation10 permutation6
    mixedMoment B raw1274step0 raw1274step0Labels = mixedMoment B raw1274step1 raw1274step1Labels := by
      have ha : raw1274step1 = -raw1274step0 := by apply Matrix.ext; change ∀ i j, raw1274step1 i j = -(raw1274step0 i j); unfold raw1274step1 raw1274step0; decide +kernel
      have hl : raw1274step1Labels = raw1274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1274step1 raw1274step1Labels = mixedMoment B raw1274step2 raw1274step2Labels := by
      have ha : raw1274step2 = raw1274step1 := by apply Matrix.ext; unfold raw1274step2 raw1274step1; decide +kernel
      have hl : raw1274step1Labels = labelEmbedding1 ∘ raw1274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1274step1 raw1274step1Labels raw1274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4172 node4172Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node600 node600Labels + mixedMoment B node1507 node1507Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw804 singletonSmall4172
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4172) = raw804Labels := by decide +kernel
  rw [hl, canonical804 B hB] at h
  have hc0 : mixedMoment B raw804 (Fin.cases (0 : Fin 2) singletonSmall4172) =
      mixedMoment B node600 node600Labels := by
    have ha : raw804 = raw805 := by apply Matrix.ext; unfold raw804 raw805; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4172 = raw805Labels := by decide +kernel
    rw [ha, hj, canonical805 B hB]
  have hc1 : mixedMoment B raw804 (Fin.cases (1 : Fin 2) singletonSmall4172) =
      mixedMoment B node1507 node1507Labels := by
    have ha : raw804 = raw806 := by apply Matrix.ext; unfold raw804 raw806; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4172 = raw806Labels := by decide +kernel
    rw [ha, hj, canonical806 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4460 node4460Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1043 node1043Labels + mixedMoment B node1725 node1725Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1263 singletonSmall4460
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4460) = raw1263Labels := by decide +kernel
  rw [hl, canonical1263 B hB] at h
  have hc0 : mixedMoment B raw1263 (Fin.cases (0 : Fin 2) singletonSmall4460) =
      mixedMoment B node1043 node1043Labels := by
    have ha : raw1263 = raw1264 := by apply Matrix.ext; unfold raw1263 raw1264; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4460 = raw1264Labels := by decide +kernel
    rw [ha, hj, canonical1264 B hB]
  have hc1 : mixedMoment B raw1263 (Fin.cases (1 : Fin 2) singletonSmall4460) =
      mixedMoment B node1725 node1725Labels := by
    have ha : raw1263 = raw1265 := by apply Matrix.ext; unfold raw1263 raw1265; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4460 = raw1265Labels := by decide +kernel
    rw [ha, hj, canonical1265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4466 node4466Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1049 node1049Labels + mixedMoment B node1738 node1738Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1272 singletonSmall4466
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4466) = raw1272Labels := by decide +kernel
  rw [hl, canonical1272 B hB] at h
  have hc0 : mixedMoment B raw1272 (Fin.cases (0 : Fin 2) singletonSmall4466) =
      mixedMoment B node1049 node1049Labels := by
    have ha : raw1272 = raw1273 := by apply Matrix.ext; unfold raw1272 raw1273; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4466 = raw1273Labels := by decide +kernel
    rw [ha, hj, canonical1273 B hB]
  have hc1 : mixedMoment B raw1272 (Fin.cases (1 : Fin 2) singletonSmall4466) =
      mixedMoment B node1738 node1738Labels := by
    have ha : raw1272 = raw1274 := by apply Matrix.ext; unfold raw1272 raw1274; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4466 = raw1274Labels := by decide +kernel
    rw [ha, hj, canonical1274 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4801 node4801Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2019 node2019Labels + mixedMoment B node2190 node2190Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1731 singletonSmall4801
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4801) = raw1731Labels := by decide +kernel
  rw [hl, canonical1731 B hB] at h
  have hc0 : mixedMoment B raw1731 (Fin.cases (0 : Fin 2) singletonSmall4801) =
      mixedMoment B node2019 node2019Labels := by
    have ha : raw1731 = raw1732 := by apply Matrix.ext; unfold raw1731 raw1732; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4801 = raw1732Labels := by decide +kernel
    rw [ha, hj, canonical1732 B hB]
  have hc1 : mixedMoment B raw1731 (Fin.cases (1 : Fin 2) singletonSmall4801) =
      mixedMoment B node2190 node2190Labels := by
    have ha : raw1731 = raw1733 := by apply Matrix.ext; unfold raw1731 raw1733; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4801 = raw1733Labels := by decide +kernel
    rw [ha, hj, canonical1733 B hB]
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

theorem singleton4865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4865 node4865Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2106 node2106Labels + mixedMoment B node2242 node2242Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1791 singletonSmall4865
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4865) = raw1791Labels := by decide +kernel
  rw [hl, canonical1791 B hB] at h
  have hc0 : mixedMoment B raw1791 (Fin.cases (0 : Fin 2) singletonSmall4865) =
      mixedMoment B node2106 node2106Labels := by
    have ha : raw1791 = raw1792 := by apply Matrix.ext; unfold raw1791 raw1792; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4865 = raw1792Labels := by decide +kernel
    rw [ha, hj, canonical1792 B hB]
  have hc1 : mixedMoment B raw1791 (Fin.cases (1 : Fin 2) singletonSmall4865) =
      mixedMoment B node2242 node2242Labels := by
    have ha : raw1791 = raw1793 := by apply Matrix.ext; unfold raw1791 raw1793; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4865 = raw1793Labels := by decide +kernel
    rw [ha, hj, canonical1793 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node730 node730Labels = Sparse.eval nodeValue730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 730) = mixedMoment B node730 node730Labels := rfl
  simpa [nodeValue730, Sparse.eval] using hc.symm

theorem sound733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node733 node733Labels = Sparse.eval nodeValue733 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 733) = mixedMoment B node733 node733Labels := rfl
  simpa [nodeValue733, Sparse.eval] using hc.symm

theorem sound734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node734 node734Labels = Sparse.eval nodeValue734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 734) = mixedMoment B node734 node734Labels := rfl
  simpa [nodeValue734, Sparse.eval] using hc.symm

theorem sound738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node738 node738Labels = Sparse.eval nodeValue738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 738) = mixedMoment B node738 node738Labels := rfl
  simpa [nodeValue738, Sparse.eval] using hc.symm

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

theorem sound922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node922 node922Labels = Sparse.eval nodeValue922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 922) = mixedMoment B node922 node922Labels := rfl
  simpa [nodeValue922, Sparse.eval] using hc.symm

theorem sound942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node942 node942Labels = Sparse.eval nodeValue942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 942) = mixedMoment B node942 node942Labels := rfl
  simpa [nodeValue942, Sparse.eval] using hc.symm

theorem sound945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node945 node945Labels = Sparse.eval nodeValue945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 945) = mixedMoment B node945 node945Labels := rfl
  simpa [nodeValue945, Sparse.eval] using hc.symm

theorem sound947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node947 node947Labels = Sparse.eval nodeValue947 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 947) = mixedMoment B node947 node947Labels := rfl
  simpa [nodeValue947, Sparse.eval] using hc.symm

theorem sound950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node950 node950Labels = Sparse.eval nodeValue950 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 950) = mixedMoment B node950 node950Labels := rfl
  simpa [nodeValue950, Sparse.eval] using hc.symm

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

theorem zero1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = 0 := by
  exact mixedMoment_order_one B hB node1082 node1082Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1086 node1086Labels = 0 := by
  exact mixedMoment_order_one B hB node1086 node1086Labels 1
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

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

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

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

theorem sound1081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = Sparse.eval nodeValue1081 (mixedVector B) := by
  simpa only [nodeValue1081, Sparse.eval_nil] using zero1081 B _hB _hF

theorem sound1082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = Sparse.eval nodeValue1082 (mixedVector B) := by
  simpa only [nodeValue1082, Sparse.eval_nil] using zero1082 B _hB _hF

theorem sound1086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1086 node1086Labels = Sparse.eval nodeValue1086 (mixedVector B) := by
  simpa only [nodeValue1086, Sparse.eval_nil] using zero1086 B _hB _hF

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

theorem sound1501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1501 node1501Labels = Sparse.eval nodeValue1501 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1501) = mixedMoment B node1501 node1501Labels := rfl
  simpa [nodeValue1501, Sparse.eval] using hc.symm

theorem sound1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1504 node1504Labels = Sparse.eval nodeValue1504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1504) = mixedMoment B node1504 node1504Labels := rfl
  simpa [nodeValue1504, Sparse.eval] using hc.symm

theorem sound1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1505 node1505Labels = Sparse.eval nodeValue1505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1505) = mixedMoment B node1505 node1505Labels := rfl
  simpa [nodeValue1505, Sparse.eval] using hc.symm

theorem sound1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1507 node1507Labels = Sparse.eval nodeValue1507 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1507) = mixedMoment B node1507 node1507Labels := rfl
  simpa [nodeValue1507, Sparse.eval] using hc.symm

theorem sound1511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1511 node1511Labels = Sparse.eval nodeValue1511 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1511) = mixedMoment B node1511 node1511Labels := rfl
  simpa [nodeValue1511, Sparse.eval] using hc.symm

theorem sound1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1514 node1514Labels = Sparse.eval nodeValue1514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1514) = mixedMoment B node1514 node1514Labels := rfl
  simpa [nodeValue1514, Sparse.eval] using hc.symm

theorem sound1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1515 node1515Labels = Sparse.eval nodeValue1515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1515) = mixedMoment B node1515 node1515Labels := rfl
  simpa [nodeValue1515, Sparse.eval] using hc.symm

theorem sound1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1517 node1517Labels = Sparse.eval nodeValue1517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1517) = mixedMoment B node1517 node1517Labels := rfl
  simpa [nodeValue1517, Sparse.eval] using hc.symm

theorem sound1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1522 node1522Labels = Sparse.eval nodeValue1522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1522) = mixedMoment B node1522 node1522Labels := rfl
  simpa [nodeValue1522, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = 0 := by
  exact mixedMoment_alpha B hF node1663 node1663Labels 1 permutation485
    (by decide +kernel)

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

theorem sound1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1645 node1645Labels = Sparse.eval nodeValue1645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1645) = mixedMoment B node1645 node1645Labels := rfl
  simpa [nodeValue1645, Sparse.eval] using hc.symm

theorem sound1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1663 node1663Labels = Sparse.eval nodeValue1663 (mixedVector B) := by
  simpa only [nodeValue1663, Sparse.eval_nil] using zero1663 B _hB _hF

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

theorem zero1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1671 node1671Labels = 0 := by
  exact mixedMoment_alpha B hF node1671 node1671Labels 1 permutation487
    (by decide +kernel)

theorem zero1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = 0 := by
  exact mixedMoment_alpha B hF node1698 node1698Labels 1 permutation434
    (by decide +kernel)

theorem zero1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = 0 := by
  exact mixedMoment_alpha B hF node1705 node1705Labels 1 permutation437
    (by decide +kernel)

theorem zero1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1726 node1726Labels = 0 := by
  exact mixedMoment_order_one B hB node1726 node1726Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = 0 := by
  exact mixedMoment_order_one B hB node1727 node1727Labels 1
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

theorem sound1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1664 node1664Labels = Sparse.eval nodeValue1664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1664) = mixedMoment B node1664 node1664Labels := rfl
  simpa [nodeValue1664, Sparse.eval] using hc.symm

theorem sound1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1667 node1667Labels = Sparse.eval nodeValue1667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1667) = mixedMoment B node1667 node1667Labels := rfl
  simpa [nodeValue1667, Sparse.eval] using hc.symm

theorem sound1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1670 node1670Labels = Sparse.eval nodeValue1670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1670) = mixedMoment B node1670 node1670Labels := rfl
  simpa [nodeValue1670, Sparse.eval] using hc.symm

theorem sound1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1671 node1671Labels = Sparse.eval nodeValue1671 (mixedVector B) := by
  simpa only [nodeValue1671, Sparse.eval_nil] using zero1671 B _hB _hF

theorem sound1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1673 node1673Labels = Sparse.eval nodeValue1673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1673) = mixedMoment B node1673 node1673Labels := rfl
  simpa [nodeValue1673, Sparse.eval] using hc.symm

theorem sound1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1678 node1678Labels = Sparse.eval nodeValue1678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1678) = mixedMoment B node1678 node1678Labels := rfl
  simpa [nodeValue1678, Sparse.eval] using hc.symm

theorem sound1697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1697 node1697Labels = Sparse.eval nodeValue1697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1697) = mixedMoment B node1697 node1697Labels := rfl
  simpa [nodeValue1697, Sparse.eval] using hc.symm

theorem sound1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = Sparse.eval nodeValue1698 (mixedVector B) := by
  simpa only [nodeValue1698, Sparse.eval_nil] using zero1698 B _hB _hF

theorem sound1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1703 node1703Labels = Sparse.eval nodeValue1703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1703) = mixedMoment B node1703 node1703Labels := rfl
  simpa [nodeValue1703, Sparse.eval] using hc.symm

theorem sound1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1704 node1704Labels = Sparse.eval nodeValue1704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1704) = mixedMoment B node1704 node1704Labels := rfl
  simpa [nodeValue1704, Sparse.eval] using hc.symm

theorem sound1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = Sparse.eval nodeValue1705 (mixedVector B) := by
  simpa only [nodeValue1705, Sparse.eval_nil] using zero1705 B _hB _hF

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1712 node1712Labels = Sparse.eval nodeValue1712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1712) = mixedMoment B node1712 node1712Labels := rfl
  simpa [nodeValue1712, Sparse.eval] using hc.symm

theorem sound1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1714 node1714Labels = Sparse.eval nodeValue1714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1714) = mixedMoment B node1714 node1714Labels := rfl
  simpa [nodeValue1714, Sparse.eval] using hc.symm

theorem sound1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1720 node1720Labels = Sparse.eval nodeValue1720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1720) = mixedMoment B node1720 node1720Labels := rfl
  simpa [nodeValue1720, Sparse.eval] using hc.symm

theorem sound1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1721 node1721Labels = Sparse.eval nodeValue1721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1721) = mixedMoment B node1721 node1721Labels := rfl
  simpa [nodeValue1721, Sparse.eval] using hc.symm

theorem sound1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1723 node1723Labels = Sparse.eval nodeValue1723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1723) = mixedMoment B node1723 node1723Labels := rfl
  simpa [nodeValue1723, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

theorem sound1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1726 node1726Labels = Sparse.eval nodeValue1726 (mixedVector B) := by
  simpa only [nodeValue1726, Sparse.eval_nil] using zero1726 B _hB _hF

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1753 node1753Labels = 0 := by
  exact mixedMoment_order_one B hB node1753 node1753Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1734 node1734Labels = Sparse.eval nodeValue1734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1734) = mixedMoment B node1734 node1734Labels := rfl
  simpa [nodeValue1734, Sparse.eval] using hc.symm

theorem sound1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1736 node1736Labels = Sparse.eval nodeValue1736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1736) = mixedMoment B node1736 node1736Labels := rfl
  simpa [nodeValue1736, Sparse.eval] using hc.symm

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

theorem sound1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1753 node1753Labels = Sparse.eval nodeValue1753 (mixedVector B) := by
  simpa only [nodeValue1753, Sparse.eval_nil] using zero1753 B _hB _hF

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

theorem sound2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2016 node2016Labels = Sparse.eval nodeValue2016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2016) = mixedMoment B node2016 node2016Labels := rfl
  simpa [nodeValue2016, Sparse.eval] using hc.symm

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

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

theorem sound2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2101 node2101Labels = Sparse.eval nodeValue2101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2101) = mixedMoment B node2101 node2101Labels := rfl
  simpa [nodeValue2101, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

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

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

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

theorem zero2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = 0 := by
  exact mixedMoment_order_one B hB node2263 node2263Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

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

theorem sound578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node578 node578Labels = Sparse.eval nodeValue578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 578) = mixedMoment B node578 node578Labels := rfl
  simpa [nodeValue578, Sparse.eval] using hc.symm

theorem sound579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node579 node579Labels = Sparse.eval nodeValue579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 579) = mixedMoment B node579 node579Labels := rfl
  simpa [nodeValue579, Sparse.eval] using hc.symm

theorem sound581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node581 node581Labels = Sparse.eval nodeValue581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 581) = mixedMoment B node581 node581Labels := rfl
  simpa [nodeValue581, Sparse.eval] using hc.symm

theorem sound582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node582 node582Labels = Sparse.eval nodeValue582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 582) = mixedMoment B node582 node582Labels := rfl
  simpa [nodeValue582, Sparse.eval] using hc.symm

theorem sound583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node583 node583Labels = Sparse.eval nodeValue583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 583) = mixedMoment B node583 node583Labels := rfl
  simpa [nodeValue583, Sparse.eval] using hc.symm

theorem sound586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node586 node586Labels = Sparse.eval nodeValue586 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 586) = mixedMoment B node586 node586Labels := rfl
  simpa [nodeValue586, Sparse.eval] using hc.symm

theorem sound600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node600 node600Labels = Sparse.eval nodeValue600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 600) = mixedMoment B node600 node600Labels := rfl
  simpa [nodeValue600, Sparse.eval] using hc.symm

theorem sound603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node603 node603Labels = Sparse.eval nodeValue603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 603) = mixedMoment B node603 node603Labels := rfl
  simpa [nodeValue603, Sparse.eval] using hc.symm

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

theorem sound4149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4149 node4149Labels = Sparse.eval nodeValue4149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4149) = mixedMoment B node4149 node4149Labels := rfl
  simpa [nodeValue4149, Sparse.eval] using hc.symm

theorem sound4151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4151 node4151Labels = Sparse.eval nodeValue4151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4151) = mixedMoment B node4151 node4151Labels := rfl
  simpa [nodeValue4151, Sparse.eval] using hc.symm

theorem sound4154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4154 node4154Labels = Sparse.eval nodeValue4154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4154) = mixedMoment B node4154 node4154Labels := rfl
  simpa [nodeValue4154, Sparse.eval] using hc.symm

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

theorem sound4172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4172 node4172Labels = Sparse.eval nodeValue4172 (mixedVector B) := by
  have h := singleton4172 B _hB
  rw [sound600 B _hB _hF, sound1507 B _hB _hF] at h
  norm_num [nodeValue4172, nodeValue600, nodeValue1507, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4326 node4326Labels = 0 := by
  exact mixedMoment_alpha B hF node4326 node4326Labels 1 permutation152
    (by decide +kernel)

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

theorem sound4326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4326 node4326Labels = Sparse.eval nodeValue4326 (mixedVector B) := by
  simpa only [nodeValue4326, Sparse.eval_nil] using zero4326 B _hB _hF

theorem sound4328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4328 node4328Labels = Sparse.eval nodeValue4328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4328) = mixedMoment B node4328 node4328Labels := rfl
  simpa [nodeValue4328, Sparse.eval] using hc.symm

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

theorem sound4363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4363 node4363Labels = Sparse.eval nodeValue4363 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4363) = mixedMoment B node4363 node4363Labels := rfl
  simpa [nodeValue4363, Sparse.eval] using hc.symm

theorem sound4365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4365 node4365Labels = Sparse.eval nodeValue4365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4365) = mixedMoment B node4365 node4365Labels := rfl
  simpa [nodeValue4365, Sparse.eval] using hc.symm

theorem sound4368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4368 node4368Labels = Sparse.eval nodeValue4368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4368) = mixedMoment B node4368 node4368Labels := rfl
  simpa [nodeValue4368, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4455 node4455Labels = 0 := by
  exact mixedMoment_alpha B hF node4455 node4455Labels 1 permutation161
    (by decide +kernel)

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

theorem sound4455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4455 node4455Labels = Sparse.eval nodeValue4455 (mixedVector B) := by
  simpa only [nodeValue4455, Sparse.eval_nil] using zero4455 B _hB _hF

theorem sound4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4457 node4457Labels = Sparse.eval nodeValue4457 (mixedVector B) := by
  have h := singleton4457 B _hB
  rw [sound1040 B _hB _hF, sound1707 B _hB _hF] at h
  norm_num [nodeValue4457, nodeValue1040, nodeValue1707, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4459 node4459Labels = Sparse.eval nodeValue4459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4459) = mixedMoment B node4459 node4459Labels := rfl
  simpa [nodeValue4459, Sparse.eval] using hc.symm

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4466 node4466Labels = Sparse.eval nodeValue4466 (mixedVector B) := by
  have h := singleton4466 B _hB
  rw [sound1049 B _hB _hF, sound1738 B _hB _hF] at h
  norm_num [nodeValue4466, nodeValue1049, nodeValue1738, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = 0 := by
  exact mixedMoment_order_one B hB node4498 node4498Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = Sparse.eval nodeValue4498 (mixedVector B) := by
  simpa only [nodeValue4498, Sparse.eval_nil] using zero4498 B _hB _hF

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

theorem sound4801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4801 node4801Labels = Sparse.eval nodeValue4801 (mixedVector B) := by
  have h := singleton4801 B _hB
  rw [sound2019 B _hB _hF, sound2190 B _hB _hF] at h
  norm_num [nodeValue4801, nodeValue2019, nodeValue2190, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero4894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = 0 := by
  exact mixedMoment_order_one B hB node4894 node4894Labels 1
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

theorem sound4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4865 node4865Labels = Sparse.eval nodeValue4865 (mixedVector B) := by
  have h := singleton4865 B _hB
  rw [sound2106 B _hB _hF, sound2242 B _hB _hF] at h
  norm_num [nodeValue4865, nodeValue2106, nodeValue2242, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources53
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1726 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 1) (sourceB1726 + difference 1 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 1) (sourceB1726 + difference 1 0) sourceC1726) = raw25195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25195; decide +kernel
    rw [ha]
    exact (canonical25195 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 2) (sourceB1726 + difference 2 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 2) (sourceB1726 + difference 2 0) sourceC1726) = raw25196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25196; decide +kernel
    rw [ha]
    exact (canonical25196 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 3) (sourceB1726 + difference 3 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 3) (sourceB1726 + difference 3 0) sourceC1726) = raw25197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25197; decide +kernel
    rw [ha]
    exact (canonical25197 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 4) (sourceB1726 + difference 4 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 4) (sourceB1726 + difference 4 0) sourceC1726) = raw25198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25198; decide +kernel
    rw [ha]
    exact (canonical25198 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 5) (sourceB1726 + difference 5 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 5) (sourceB1726 + difference 5 0) sourceC1726) = raw25199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25199; decide +kernel
    rw [ha]
    exact (canonical25199 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 0) (sourceB1726 + difference 0 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 0) (sourceB1726 + difference 0 1) sourceC1726) = raw25200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25200; decide +kernel
    rw [ha]
    exact (canonical25200 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 2) (sourceB1726 + difference 2 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1673) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 2) (sourceB1726 + difference 2 1) sourceC1726) = raw25201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25201; decide +kernel
    rw [ha]
    exact (canonical25201 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 3) (sourceB1726 + difference 3 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 3) (sourceB1726 + difference 3 1) sourceC1726) = raw25202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25202; decide +kernel
    rw [ha]
    exact (canonical25202 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 4) (sourceB1726 + difference 4 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 4) (sourceB1726 + difference 4 1) sourceC1726) = raw25203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25203; decide +kernel
    rw [ha]
    exact (canonical25203 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 5) (sourceB1726 + difference 5 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 5) (sourceB1726 + difference 5 1) sourceC1726) = raw25204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25204; decide +kernel
    rw [ha]
    exact (canonical25204 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 0) (sourceB1726 + difference 0 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 0) (sourceB1726 + difference 0 2) sourceC1726) = raw25205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25205; decide +kernel
    rw [ha]
    exact (canonical25205 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 1) (sourceB1726 + difference 1 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 1) (sourceB1726 + difference 1 2) sourceC1726) = raw25206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25206; decide +kernel
    rw [ha]
    exact (canonical25206 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 3) (sourceB1726 + difference 3 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 3) (sourceB1726 + difference 3 2) sourceC1726) = raw25207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25207; decide +kernel
    rw [ha]
    exact (canonical25207 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 4) (sourceB1726 + difference 4 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 4) (sourceB1726 + difference 4 2) sourceC1726) = raw25208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25208; decide +kernel
    rw [ha]
    exact (canonical25208 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 5) (sourceB1726 + difference 5 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 5) (sourceB1726 + difference 5 2) sourceC1726) = raw25209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25209; decide +kernel
    rw [ha]
    exact (canonical25209 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 0) (sourceB1726 + difference 0 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 0) (sourceB1726 + difference 0 3) sourceC1726) = raw25210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25210; decide +kernel
    rw [ha]
    exact (canonical25210 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 1) (sourceB1726 + difference 1 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 1) (sourceB1726 + difference 1 3) sourceC1726) = raw25211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25211; decide +kernel
    rw [ha]
    exact (canonical25211 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 2) (sourceB1726 + difference 2 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 2) (sourceB1726 + difference 2 3) sourceC1726) = raw25212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25212; decide +kernel
    rw [ha]
    exact (canonical25212 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 4) (sourceB1726 + difference 4 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 4) (sourceB1726 + difference 4 3) sourceC1726) = raw25213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25213; decide +kernel
    rw [ha]
    exact (canonical25213 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 5) (sourceB1726 + difference 5 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 5) (sourceB1726 + difference 5 3) sourceC1726) = raw25214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25214; decide +kernel
    rw [ha]
    exact (canonical25214 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 0) (sourceB1726 + difference 0 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 0) (sourceB1726 + difference 0 4) sourceC1726) = raw25215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25215; decide +kernel
    rw [ha]
    exact (canonical25215 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 1) (sourceB1726 + difference 1 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 1) (sourceB1726 + difference 1 4) sourceC1726) = raw25216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25216; decide +kernel
    rw [ha]
    exact (canonical25216 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 2) (sourceB1726 + difference 2 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 2) (sourceB1726 + difference 2 4) sourceC1726) = raw25217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25217; decide +kernel
    rw [ha]
    exact (canonical25217 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 3) (sourceB1726 + difference 3 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 3) (sourceB1726 + difference 3 4) sourceC1726) = raw25218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25218; decide +kernel
    rw [ha]
    exact (canonical25218 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 5) (sourceB1726 + difference 5 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 5) (sourceB1726 + difference 5 4) sourceC1726) = raw25219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25219; decide +kernel
    rw [ha]
    exact (canonical25219 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 0) (sourceB1726 + difference 0 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 0) (sourceB1726 + difference 0 5) sourceC1726) = raw25220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25220; decide +kernel
    rw [ha]
    exact (canonical25220 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 1) (sourceB1726 + difference 1 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 1) (sourceB1726 + difference 1 5) sourceC1726) = raw25221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25221; decide +kernel
    rw [ha]
    exact (canonical25221 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 2) (sourceB1726 + difference 2 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 2) (sourceB1726 + difference 2 5) sourceC1726) = raw25222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25222; decide +kernel
    rw [ha]
    exact (canonical25222 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 3) (sourceB1726 + difference 3 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 3) (sourceB1726 + difference 3 5) sourceC1726) = raw25223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25223; decide +kernel
    rw [ha]
    exact (canonical25223 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 4) (sourceB1726 + difference 4 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 4) (sourceB1726 + difference 4 5) sourceC1726) = raw25224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25224; decide +kernel
    rw [ha]
    exact (canonical25224 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1726 sourceB1726 sourceC1726
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1726, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1727 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1727 + difference 0 0) (sourceB1727 + difference 0 0) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1727 + difference 0 0) (sourceB1727 + difference 0 0) sourceC1727) = raw25225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25225; decide +kernel
    rw [ha]
    exact (canonical25225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1727 + difference 1 0) (sourceB1727 + difference 0 1) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1727 + difference 1 0) (sourceB1727 + difference 0 1) sourceC1727) = raw25226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25226; decide +kernel
    rw [ha]
    exact (canonical25226 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1727 + difference 2 0) (sourceB1727 + difference 0 2) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 578) := by
    have ha : (tripleCharges (sourceA1727 + difference 2 0) (sourceB1727 + difference 0 2) sourceC1727) = raw25227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25227; decide +kernel
    rw [ha]
    exact (canonical25227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1727 + difference 3 0) (sourceB1727 + difference 0 3) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1727 + difference 3 0) (sourceB1727 + difference 0 3) sourceC1727) = raw25228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25228; decide +kernel
    rw [ha]
    exact (canonical25228 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1727 + difference 4 0) (sourceB1727 + difference 0 4) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 586) := by
    have ha : (tripleCharges (sourceA1727 + difference 4 0) (sourceB1727 + difference 0 4) sourceC1727) = raw25229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25229; decide +kernel
    rw [ha]
    exact (canonical25229 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1727 + difference 5 0) (sourceB1727 + difference 0 5) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1727 + difference 5 0) (sourceB1727 + difference 0 5) sourceC1727) = raw25230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25230; decide +kernel
    rw [ha]
    exact (canonical25230 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1727 + sourceB1727) sourceC1727) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1727 + sourceB1727) sourceC1727) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA1727 sourceB1727 sourceC1727 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1727 sourceB1727 sourceC1727
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1727, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

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

theorem sourceEq1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1728 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 0) (sourceB1728 + difference 0 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 0) (sourceB1728 + difference 0 1) sourceC1728) = raw25226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25226; decide +kernel
    rw [ha]
    exact (canonical25226 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 1) (sourceB1728 + difference 1 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 1) (sourceB1728 + difference 1 1) sourceC1728) = raw25225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25225; decide +kernel
    rw [ha]
    exact (canonical25225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 2) (sourceB1728 + difference 2 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 922) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 2) (sourceB1728 + difference 2 1) sourceC1728) = raw25232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25232; decide +kernel
    rw [ha]
    exact (canonical25232 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 3) (sourceB1728 + difference 3 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 3) (sourceB1728 + difference 3 1) sourceC1728) = raw25233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25233; decide +kernel
    rw [ha]
    exact (canonical25233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 4) (sourceB1728 + difference 4 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 4) (sourceB1728 + difference 4 1) sourceC1728) = raw25234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25234; decide +kernel
    rw [ha]
    exact (canonical25234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 5) (sourceB1728 + difference 5 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 5) (sourceB1728 + difference 5 1) sourceC1728) = raw25235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25235; decide +kernel
    rw [ha]
    exact (canonical25235 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1728 + sourceB1728) sourceC1728) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1728 + sourceB1728) sourceC1728) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA1728 sourceB1728 sourceC1728 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1728 sourceB1728 sourceC1728
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1728, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1729 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1729 + difference 0 1) (sourceB1729 + difference 1 0) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA1729 + difference 0 1) (sourceB1729 + difference 1 0) sourceC1729) = raw25236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25236; decide +kernel
    rw [ha]
    exact (canonical25236 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1729 + difference 1 1) (sourceB1729 + difference 1 1) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1729 + difference 1 1) (sourceB1729 + difference 1 1) sourceC1729) = raw25225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25225; decide +kernel
    rw [ha]
    exact (canonical25225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1729 + difference 2 1) (sourceB1729 + difference 1 2) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 942) := by
    have ha : (tripleCharges (sourceA1729 + difference 2 1) (sourceB1729 + difference 1 2) sourceC1729) = raw25237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25237; decide +kernel
    rw [ha]
    exact (canonical25237 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1729 + difference 3 1) (sourceB1729 + difference 1 3) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA1729 + difference 3 1) (sourceB1729 + difference 1 3) sourceC1729) = raw25238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25238; decide +kernel
    rw [ha]
    exact (canonical25238 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1729 + difference 4 1) (sourceB1729 + difference 1 4) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA1729 + difference 4 1) (sourceB1729 + difference 1 4) sourceC1729) = raw25239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25239; decide +kernel
    rw [ha]
    exact (canonical25239 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1729 + difference 5 1) (sourceB1729 + difference 1 5) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1729 + difference 5 1) (sourceB1729 + difference 1 5) sourceC1729) = raw25240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25240; decide +kernel
    rw [ha]
    exact (canonical25240 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1729 + sourceB1729) sourceC1729) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1729 + sourceB1729) sourceC1729) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA1729 sourceB1729 sourceC1729 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1729 sourceB1729 sourceC1729
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1729, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1735 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 0) (sourceB1735 + difference 0 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 0) (sourceB1735 + difference 0 0) sourceC1735) = raw25334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25334; decide +kernel
    rw [ha]
    exact (canonical25334 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 1) (sourceB1735 + difference 1 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 1) (sourceB1735 + difference 1 0) sourceC1735) = raw25335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25335; decide +kernel
    rw [ha]
    exact (canonical25335 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 2) (sourceB1735 + difference 2 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2016) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 2) (sourceB1735 + difference 2 0) sourceC1735) = raw25336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25336; decide +kernel
    rw [ha]
    exact (canonical25336 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 3) (sourceB1735 + difference 3 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 3) (sourceB1735 + difference 3 0) sourceC1735) = raw25337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25337; decide +kernel
    rw [ha]
    exact (canonical25337 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 4) (sourceB1735 + difference 4 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 4) (sourceB1735 + difference 4 0) sourceC1735) = raw25338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25338; decide +kernel
    rw [ha]
    exact (canonical25338 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 5) (sourceB1735 + difference 5 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 5) (sourceB1735 + difference 5 0) sourceC1735) = raw25339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25339; decide +kernel
    rw [ha]
    exact (canonical25339 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1735 + sourceB1735) sourceC1735) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1735 + sourceB1735) sourceC1735) = raw25340 := by
      apply Matrix.ext; unfold doubleCharges sourceA1735 sourceB1735 sourceC1735 raw25340; decide +kernel
    rw [ha]
    exact (canonical25340 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1735 sourceB1735 sourceC1735
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1735, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1737 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1737 + difference 0 0) (sourceB1737 + difference 0 0) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1645) := by
    have ha : (tripleCharges (sourceA1737 + difference 0 0) (sourceB1737 + difference 0 0) sourceC1737) = raw25346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25346; decide +kernel
    rw [ha]
    exact (canonical25346 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1737 + difference 1 0) (sourceB1737 + difference 0 1) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 738) := by
    have ha : (tripleCharges (sourceA1737 + difference 1 0) (sourceB1737 + difference 0 1) sourceC1737) = raw25347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25347; decide +kernel
    rw [ha]
    exact (canonical25347 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1737 + difference 2 0) (sourceB1737 + difference 0 2) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 730) := by
    have ha : (tripleCharges (sourceA1737 + difference 2 0) (sourceB1737 + difference 0 2) sourceC1737) = raw25348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25348; decide +kernel
    rw [ha]
    exact (canonical25348 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1737 + difference 3 0) (sourceB1737 + difference 0 3) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA1737 + difference 3 0) (sourceB1737 + difference 0 3) sourceC1737) = raw25349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25349; decide +kernel
    rw [ha]
    exact (canonical25349 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1737 + difference 4 0) (sourceB1737 + difference 0 4) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1737 + difference 4 0) (sourceB1737 + difference 0 4) sourceC1737) = raw25350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25350; decide +kernel
    rw [ha]
    exact (canonical25350 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1737 + difference 5 0) (sourceB1737 + difference 0 5) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA1737 + difference 5 0) (sourceB1737 + difference 0 5) sourceC1737) = raw25351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25351; decide +kernel
    rw [ha]
    exact (canonical25351 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1737 + sourceB1737) sourceC1737) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1737 + sourceB1737) sourceC1737) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1737 sourceB1737 sourceC1737 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1737 sourceB1737 sourceC1737
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1737, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1738 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 1) (sourceB1738 + difference 1 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 1) (sourceB1738 + difference 1 0) sourceC1738) = raw11487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11487; decide +kernel
    rw [ha]
    exact (canonical11487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 2) (sourceB1738 + difference 2 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 2) (sourceB1738 + difference 2 0) sourceC1738) = raw11488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11488; decide +kernel
    rw [ha]
    exact (canonical11488 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 3) (sourceB1738 + difference 3 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 3) (sourceB1738 + difference 3 0) sourceC1738) = raw21373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21373; decide +kernel
    rw [ha]
    exact (canonical21373 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 4) (sourceB1738 + difference 4 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 4) (sourceB1738 + difference 4 0) sourceC1738) = raw11489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11489; decide +kernel
    rw [ha]
    exact (canonical11489 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 5) (sourceB1738 + difference 5 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 5) (sourceB1738 + difference 5 0) sourceC1738) = raw11490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11490; decide +kernel
    rw [ha]
    exact (canonical11490 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 0) (sourceB1738 + difference 0 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 0) (sourceB1738 + difference 0 1) sourceC1738) = raw25352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25352; decide +kernel
    rw [ha]
    exact (canonical25352 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 2) (sourceB1738 + difference 2 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 2) (sourceB1738 + difference 2 1) sourceC1738) = raw25353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25353; decide +kernel
    rw [ha]
    exact (canonical25353 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 3) (sourceB1738 + difference 3 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 3) (sourceB1738 + difference 3 1) sourceC1738) = raw11476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11476; decide +kernel
    rw [ha]
    exact (canonical11476 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 4) (sourceB1738 + difference 4 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 4) (sourceB1738 + difference 4 1) sourceC1738) = raw25354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25354; decide +kernel
    rw [ha]
    exact (canonical25354 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 5) (sourceB1738 + difference 5 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 5) (sourceB1738 + difference 5 1) sourceC1738) = raw25355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25355; decide +kernel
    rw [ha]
    exact (canonical25355 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 0) (sourceB1738 + difference 0 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4149) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 0) (sourceB1738 + difference 0 2) sourceC1738) = raw25356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25356; decide +kernel
    rw [ha]
    exact (canonical25356 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 1) (sourceB1738 + difference 1 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4363) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 1) (sourceB1738 + difference 1 2) sourceC1738) = raw25357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25357; decide +kernel
    rw [ha]
    exact (canonical25357 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 3) (sourceB1738 + difference 3 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 3) (sourceB1738 + difference 3 2) sourceC1738) = raw11481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11481; decide +kernel
    rw [ha]
    exact (canonical11481 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 4) (sourceB1738 + difference 4 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 4) (sourceB1738 + difference 4 2) sourceC1738) = raw25358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25358; decide +kernel
    rw [ha]
    exact (canonical25358 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 5) (sourceB1738 + difference 5 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 5) (sourceB1738 + difference 5 2) sourceC1738) = raw25359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25359; decide +kernel
    rw [ha]
    exact (canonical25359 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 0) (sourceB1738 + difference 0 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 0) (sourceB1738 + difference 0 3) sourceC1738) = raw25360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25360; decide +kernel
    rw [ha]
    exact (canonical25360 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 1) (sourceB1738 + difference 1 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 1) (sourceB1738 + difference 1 3) sourceC1738) = raw25361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25361; decide +kernel
    rw [ha]
    exact (canonical25361 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 2) (sourceB1738 + difference 2 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 2) (sourceB1738 + difference 2 3) sourceC1738) = raw25362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25362; decide +kernel
    rw [ha]
    exact (canonical25362 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 4) (sourceB1738 + difference 4 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 4) (sourceB1738 + difference 4 3) sourceC1738) = raw25363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25363; decide +kernel
    rw [ha]
    exact (canonical25363 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 5) (sourceB1738 + difference 5 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 5) (sourceB1738 + difference 5 3) sourceC1738) = raw25364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25364; decide +kernel
    rw [ha]
    exact (canonical25364 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 0) (sourceB1738 + difference 0 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 0) (sourceB1738 + difference 0 4) sourceC1738) = raw25365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25365; decide +kernel
    rw [ha]
    exact (canonical25365 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 1) (sourceB1738 + difference 1 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 1) (sourceB1738 + difference 1 4) sourceC1738) = raw25366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25366; decide +kernel
    rw [ha]
    exact (canonical25366 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 2) (sourceB1738 + difference 2 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 2) (sourceB1738 + difference 2 4) sourceC1738) = raw25367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25367; decide +kernel
    rw [ha]
    exact (canonical25367 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 3) (sourceB1738 + difference 3 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 3) (sourceB1738 + difference 3 4) sourceC1738) = raw11491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11491; decide +kernel
    rw [ha]
    exact (canonical11491 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 5) (sourceB1738 + difference 5 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 5) (sourceB1738 + difference 5 4) sourceC1738) = raw25368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25368; decide +kernel
    rw [ha]
    exact (canonical25368 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 0) (sourceB1738 + difference 0 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4151) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 0) (sourceB1738 + difference 0 5) sourceC1738) = raw21382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21382; decide +kernel
    rw [ha]
    exact (canonical21382 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 1) (sourceB1738 + difference 1 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 1) (sourceB1738 + difference 1 5) sourceC1738) = raw21383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21383; decide +kernel
    rw [ha]
    exact (canonical21383 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 2) (sourceB1738 + difference 2 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4326) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 2) (sourceB1738 + difference 2 5) sourceC1738) = raw21384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21384; decide +kernel
    rw [ha]
    exact (canonical21384 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 3) (sourceB1738 + difference 3 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 3) (sourceB1738 + difference 3 5) sourceC1738) = raw11496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11496; decide +kernel
    rw [ha]
    exact (canonical11496 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 4) (sourceB1738 + difference 4 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 4) (sourceB1738 + difference 4 5) sourceC1738) = raw21385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21385; decide +kernel
    rw [ha]
    exact (canonical21385 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1738 sourceB1738 sourceC1738
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1738, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1740 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 1) (sourceB1740 + difference 1 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 1) (sourceB1740 + difference 1 0) sourceC1740) = raw25391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25391; decide +kernel
    rw [ha]
    exact (canonical25391 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 2) (sourceB1740 + difference 2 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 2) (sourceB1740 + difference 2 0) sourceC1740) = raw25392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25392; decide +kernel
    rw [ha]
    exact (canonical25392 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 3) (sourceB1740 + difference 3 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 3) (sourceB1740 + difference 3 0) sourceC1740) = raw21429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21429; decide +kernel
    rw [ha]
    exact (canonical21429 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 4) (sourceB1740 + difference 4 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 4) (sourceB1740 + difference 4 0) sourceC1740) = raw25393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25393; decide +kernel
    rw [ha]
    exact (canonical25393 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 5) (sourceB1740 + difference 5 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 5) (sourceB1740 + difference 5 0) sourceC1740) = raw25394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25394; decide +kernel
    rw [ha]
    exact (canonical25394 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 0) (sourceB1740 + difference 0 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 0) (sourceB1740 + difference 0 1) sourceC1740) = raw25395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25395; decide +kernel
    rw [ha]
    exact (canonical25395 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 2) (sourceB1740 + difference 2 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1664) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 2) (sourceB1740 + difference 2 1) sourceC1740) = raw25396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25396; decide +kernel
    rw [ha]
    exact (canonical25396 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 3) (sourceB1740 + difference 3 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 3) (sourceB1740 + difference 3 1) sourceC1740) = raw21434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21434; decide +kernel
    rw [ha]
    exact (canonical21434 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 4) (sourceB1740 + difference 4 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 4) (sourceB1740 + difference 4 1) sourceC1740) = raw25397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25397; decide +kernel
    rw [ha]
    exact (canonical25397 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 5) (sourceB1740 + difference 5 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 5) (sourceB1740 + difference 5 1) sourceC1740) = raw25398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25398; decide +kernel
    rw [ha]
    exact (canonical25398 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 0) (sourceB1740 + difference 0 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1501) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 0) (sourceB1740 + difference 0 2) sourceC1740) = raw25399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25399; decide +kernel
    rw [ha]
    exact (canonical25399 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 1) (sourceB1740 + difference 1 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1697) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 1) (sourceB1740 + difference 1 2) sourceC1740) = raw25400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25400; decide +kernel
    rw [ha]
    exact (canonical25400 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 3) (sourceB1740 + difference 3 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 3) (sourceB1740 + difference 3 2) sourceC1740) = raw21439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21439; decide +kernel
    rw [ha]
    exact (canonical21439 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 4) (sourceB1740 + difference 4 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 4) (sourceB1740 + difference 4 2) sourceC1740) = raw25401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25401; decide +kernel
    rw [ha]
    exact (canonical25401 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 5) (sourceB1740 + difference 5 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 5) (sourceB1740 + difference 5 2) sourceC1740) = raw25402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25402; decide +kernel
    rw [ha]
    exact (canonical25402 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 0) (sourceB1740 + difference 0 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 0) (sourceB1740 + difference 0 3) sourceC1740) = raw25403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25403; decide +kernel
    rw [ha]
    exact (canonical25403 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 1) (sourceB1740 + difference 1 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 1) (sourceB1740 + difference 1 3) sourceC1740) = raw25404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25404; decide +kernel
    rw [ha]
    exact (canonical25404 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 2) (sourceB1740 + difference 2 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 2) (sourceB1740 + difference 2 3) sourceC1740) = raw25405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25405; decide +kernel
    rw [ha]
    exact (canonical25405 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 4) (sourceB1740 + difference 4 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 4) (sourceB1740 + difference 4 3) sourceC1740) = raw25406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25406; decide +kernel
    rw [ha]
    exact (canonical25406 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 5) (sourceB1740 + difference 5 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 5) (sourceB1740 + difference 5 3) sourceC1740) = raw25407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25407; decide +kernel
    rw [ha]
    exact (canonical25407 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 0) (sourceB1740 + difference 0 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 0) (sourceB1740 + difference 0 4) sourceC1740) = raw25408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25408; decide +kernel
    rw [ha]
    exact (canonical25408 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 1) (sourceB1740 + difference 1 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 1) (sourceB1740 + difference 1 4) sourceC1740) = raw25409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25409; decide +kernel
    rw [ha]
    exact (canonical25409 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 2) (sourceB1740 + difference 2 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 2) (sourceB1740 + difference 2 4) sourceC1740) = raw25410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25410; decide +kernel
    rw [ha]
    exact (canonical25410 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 3) (sourceB1740 + difference 3 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 3) (sourceB1740 + difference 3 4) sourceC1740) = raw21449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21449; decide +kernel
    rw [ha]
    exact (canonical21449 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 5) (sourceB1740 + difference 5 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 5) (sourceB1740 + difference 5 4) sourceC1740) = raw25411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25411; decide +kernel
    rw [ha]
    exact (canonical25411 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 0) (sourceB1740 + difference 0 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 0) (sourceB1740 + difference 0 5) sourceC1740) = raw21440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21440; decide +kernel
    rw [ha]
    exact (canonical21440 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 1) (sourceB1740 + difference 1 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 1) (sourceB1740 + difference 1 5) sourceC1740) = raw21441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21441; decide +kernel
    rw [ha]
    exact (canonical21441 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 2) (sourceB1740 + difference 2 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 2) (sourceB1740 + difference 2 5) sourceC1740) = raw21442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21442; decide +kernel
    rw [ha]
    exact (canonical21442 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 3) (sourceB1740 + difference 3 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 3) (sourceB1740 + difference 3 5) sourceC1740) = raw25412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25412; decide +kernel
    rw [ha]
    exact (canonical25412 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 4) (sourceB1740 + difference 4 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 4) (sourceB1740 + difference 4 5) sourceC1740) = raw21443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21443; decide +kernel
    rw [ha]
    exact (canonical21443 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1740 sourceB1740 sourceC1740
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1740, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1741 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1741 + difference 0 0) (sourceB1741 + difference 0 0) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1741 + difference 0 0) (sourceB1741 + difference 0 0) sourceC1741) = raw25413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25413; decide +kernel
    rw [ha]
    exact (canonical25413 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1741 + difference 1 0) (sourceB1741 + difference 0 1) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1741 + difference 1 0) (sourceB1741 + difference 0 1) sourceC1741) = raw25414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25414; decide +kernel
    rw [ha]
    exact (canonical25414 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1741 + difference 2 0) (sourceB1741 + difference 0 2) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 577) := by
    have ha : (tripleCharges (sourceA1741 + difference 2 0) (sourceB1741 + difference 0 2) sourceC1741) = raw25415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25415; decide +kernel
    rw [ha]
    exact (canonical25415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1741 + difference 3 0) (sourceB1741 + difference 0 3) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1741 + difference 3 0) (sourceB1741 + difference 0 3) sourceC1741) = raw25416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25416; decide +kernel
    rw [ha]
    exact (canonical25416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1741 + difference 4 0) (sourceB1741 + difference 0 4) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1741 + difference 4 0) (sourceB1741 + difference 0 4) sourceC1741) = raw25417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25417; decide +kernel
    rw [ha]
    exact (canonical25417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1741 + difference 5 0) (sourceB1741 + difference 0 5) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1741 + difference 5 0) (sourceB1741 + difference 0 5) sourceC1741) = raw21458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw21458; decide +kernel
    rw [ha]
    exact (canonical21458 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1741 + sourceB1741) sourceC1741) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1741 + sourceB1741) sourceC1741) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1741 sourceB1741 sourceC1741 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1741 sourceB1741 sourceC1741
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1741, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1742 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 0) (sourceB1742 + difference 0 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 0) (sourceB1742 + difference 0 1) sourceC1742) = raw25414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25414; decide +kernel
    rw [ha]
    exact (canonical25414 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 1) (sourceB1742 + difference 1 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 1) (sourceB1742 + difference 1 1) sourceC1742) = raw25413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25413; decide +kernel
    rw [ha]
    exact (canonical25413 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 2) (sourceB1742 + difference 2 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 2) (sourceB1742 + difference 2 1) sourceC1742) = raw25418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25418; decide +kernel
    rw [ha]
    exact (canonical25418 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 3) (sourceB1742 + difference 3 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 3) (sourceB1742 + difference 3 1) sourceC1742) = raw21465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw21465; decide +kernel
    rw [ha]
    exact (canonical21465 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 4) (sourceB1742 + difference 4 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 4) (sourceB1742 + difference 4 1) sourceC1742) = raw25419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25419; decide +kernel
    rw [ha]
    exact (canonical25419 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 5) (sourceB1742 + difference 5 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 5) (sourceB1742 + difference 5 1) sourceC1742) = raw25420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25420; decide +kernel
    rw [ha]
    exact (canonical25420 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1742 + sourceB1742) sourceC1742) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1742 + sourceB1742) sourceC1742) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1742 sourceB1742 sourceC1742 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1742 sourceB1742 sourceC1742
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1742, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1472 : Integer.Sparse.reindex keyMap MixedData.row1472 = numericRow1472 := by decide +kernel

theorem numericCheck1472 (x : Master → ℝ) : Integer.Sparse.eval numericRow1472 x =
    (4320 : ℝ) * reducedSource1472 x := by
  norm_num [numericRow1472, reducedSource1472, Integer.Sparse.eval, Sparse.eval, nodeValue625, nodeValue626, nodeValue627, nodeValue632, nodeValue644, nodeValue1316, nodeValue1317, nodeValue1318, nodeValue1322, nodeValue1327, nodeValue1328, nodeValue1331, nodeValue1339, nodeValue1386, nodeValue1388, nodeValue1391, nodeValue1409, nodeValue1410, nodeValue1411, nodeValue1413, nodeValue1420, nodeValue1446, nodeValue1447, nodeValue3184, nodeValue3204, nodeValue3227, nodeValue3228, nodeValue3229]
  ring

theorem reindexCheck1473 : Integer.Sparse.reindex keyMap MixedData.row1473 = numericRow1473 := by decide +kernel

theorem numericCheck1473 (x : Master → ℝ) : Integer.Sparse.eval numericRow1473 x =
    (1 : ℝ) * reducedSource1473 x := by
  norm_num [numericRow1473, reducedSource1473, Integer.Sparse.eval, Sparse.eval, nodeValue1504, nodeValue1514, nodeValue1515, nodeValue1517, nodeValue1522, nodeValue1670, nodeValue1671, nodeValue1673, nodeValue1678, nodeValue1703, nodeValue1705, nodeValue1706, nodeValue1720, nodeValue1721, nodeValue1723, nodeValue1724, nodeValue1726, nodeValue1734, nodeValue1736, nodeValue1737, nodeValue1750, nodeValue1751, nodeValue1753, nodeValue2202, nodeValue2260, nodeValue2262, nodeValue2263, nodeValue2291]

theorem reindexCheck1474 : Integer.Sparse.reindex keyMap MixedData.row1474 = numericRow1474 := by decide +kernel

theorem numericCheck1474 (x : Master → ℝ) : Integer.Sparse.eval numericRow1474 x =
    (1 : ℝ) * reducedSource1474 x := by
  norm_num [numericRow1474, reducedSource1474, Integer.Sparse.eval, Sparse.eval, nodeValue578, nodeValue581, nodeValue583, nodeValue586, nodeValue603, nodeValue1041, nodeValue4083]

theorem reindexCheck1475 : Integer.Sparse.reindex keyMap MixedData.row1475 = numericRow1475 := by decide +kernel

theorem numericCheck1475 (x : Master → ℝ) : Integer.Sparse.eval numericRow1475 x =
    (1 : ℝ) * reducedSource1475 x := by
  norm_num [numericRow1475, reducedSource1475, Integer.Sparse.eval, Sparse.eval, nodeValue603, nodeValue922, nodeValue1041, nodeValue1081, nodeValue1086, nodeValue4083]

theorem reindexCheck1476 : Integer.Sparse.reindex keyMap MixedData.row1476 = numericRow1476 := by decide +kernel

theorem numericCheck1476 (x : Master → ℝ) : Integer.Sparse.eval numericRow1476 x =
    (1 : ℝ) * reducedSource1476 x := by
  norm_num [numericRow1476, reducedSource1476, Integer.Sparse.eval, Sparse.eval, nodeValue942, nodeValue945, nodeValue947, nodeValue950, nodeValue1041, nodeValue2107, nodeValue4083]

theorem reindexCheck1481 : Integer.Sparse.reindex keyMap MixedData.row1481 = numericRow1481 := by decide +kernel

theorem numericCheck1481 (x : Master → ℝ) : Integer.Sparse.eval numericRow1481 x =
    (1 : ℝ) * reducedSource1481 x := by
  norm_num [numericRow1481, reducedSource1481, Integer.Sparse.eval, Sparse.eval, nodeValue1035, nodeValue2016, nodeValue2101, nodeValue2205, nodeValue2242, nodeValue2260, nodeValue4080]

theorem reindexCheck1482 : Integer.Sparse.reindex keyMap MixedData.row1482 = numericRow1482 := by decide +kernel

theorem numericCheck1482 (x : Master → ℝ) : Integer.Sparse.eval numericRow1482 x =
    (1 : ℝ) * reducedSource1482 x := by
  norm_num [numericRow1482, reducedSource1482, Integer.Sparse.eval, Sparse.eval, nodeValue730, nodeValue733, nodeValue734, nodeValue738, nodeValue806, nodeValue1645, nodeValue4069]

theorem reindexCheck1483 : Integer.Sparse.reindex keyMap MixedData.row1483 = numericRow1483 := by decide +kernel

theorem numericCheck1483 (x : Master → ℝ) : Integer.Sparse.eval numericRow1483 x =
    (4 : ℝ) * reducedSource1483 x := by
  norm_num [numericRow1483, reducedSource1483, Integer.Sparse.eval, Sparse.eval, nodeValue4149, nodeValue4151, nodeValue4154, nodeValue4172, nodeValue4326, nodeValue4328, nodeValue4341, nodeValue4363, nodeValue4365, nodeValue4368, nodeValue4455, nodeValue4457, nodeValue4459, nodeValue4460, nodeValue4466, nodeValue4495, nodeValue4498, nodeValue4801, nodeValue4865, nodeValue4888, nodeValue4894]
  ring

theorem reindexCheck1485 : Integer.Sparse.reindex keyMap MixedData.row1485 = numericRow1485 := by decide +kernel

theorem numericCheck1485 (x : Master → ℝ) : Integer.Sparse.eval numericRow1485 x =
    (1 : ℝ) * reducedSource1485 x := by
  norm_num [numericRow1485, reducedSource1485, Integer.Sparse.eval, Sparse.eval, nodeValue1501, nodeValue1505, nodeValue1507, nodeValue1511, nodeValue1663, nodeValue1664, nodeValue1667, nodeValue1697, nodeValue1698, nodeValue1704, nodeValue1707, nodeValue1708, nodeValue1712, nodeValue1714, nodeValue1725, nodeValue1727, nodeValue1738, nodeValue2190, nodeValue2242, nodeValue2244, nodeValue2264]

theorem reindexCheck1486 : Integer.Sparse.reindex keyMap MixedData.row1486 = numericRow1486 := by decide +kernel

theorem numericCheck1486 (x : Master → ℝ) : Integer.Sparse.eval numericRow1486 x =
    (1 : ℝ) * reducedSource1486 x := by
  norm_num [numericRow1486, reducedSource1486, Integer.Sparse.eval, Sparse.eval, nodeValue577, nodeValue579, nodeValue582, nodeValue600, nodeValue1040, nodeValue4084]

theorem reindexCheck1487 : Integer.Sparse.reindex keyMap MixedData.row1487 = numericRow1487 := by decide +kernel

theorem numericCheck1487 (x : Master → ℝ) : Integer.Sparse.eval numericRow1487 x =
    (1 : ℝ) * reducedSource1487 x := by
  norm_num [numericRow1487, reducedSource1487, Integer.Sparse.eval, Sparse.eval, nodeValue600, nodeValue919, nodeValue1040, nodeValue1079, nodeValue1082, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound1472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1472 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1472, numericCheck1472, reducedZero1472_e B hB hF, mul_zero]

theorem reducedZero1473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1473 (mixedVector B) = 0 := by
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h1514 : mixedVector B (Sum.inr 1514) = Sparse.eval nodeValue1514 (mixedVector B) := by
    change mixedMoment B node1514 node1514Labels = _
    exact sound1514 B hB hF
  have h1515 : mixedVector B (Sum.inr 1515) = Sparse.eval nodeValue1515 (mixedVector B) := by
    change mixedMoment B node1515 node1515Labels = _
    exact sound1515 B hB hF
  have h1517 : mixedVector B (Sum.inr 1517) = Sparse.eval nodeValue1517 (mixedVector B) := by
    change mixedMoment B node1517 node1517Labels = _
    exact sound1517 B hB hF
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h1670 : mixedVector B (Sum.inr 1670) = Sparse.eval nodeValue1670 (mixedVector B) := by
    change mixedMoment B node1670 node1670Labels = _
    exact sound1670 B hB hF
  have h1671 : mixedVector B (Sum.inr 1671) = Sparse.eval nodeValue1671 (mixedVector B) := by
    change mixedMoment B node1671 node1671Labels = _
    exact sound1671 B hB hF
  have h1673 : mixedVector B (Sum.inr 1673) = Sparse.eval nodeValue1673 (mixedVector B) := by
    change mixedMoment B node1673 node1673Labels = _
    exact sound1673 B hB hF
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1703 : mixedVector B (Sum.inr 1703) = Sparse.eval nodeValue1703 (mixedVector B) := by
    change mixedMoment B node1703 node1703Labels = _
    exact sound1703 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1720 : mixedVector B (Sum.inr 1720) = Sparse.eval nodeValue1720 (mixedVector B) := by
    change mixedMoment B node1720 node1720Labels = _
    exact sound1720 B hB hF
  have h1721 : mixedVector B (Sum.inr 1721) = Sparse.eval nodeValue1721 (mixedVector B) := by
    change mixedMoment B node1721 node1721Labels = _
    exact sound1721 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1726 : mixedVector B (Sum.inr 1726) = Sparse.eval nodeValue1726 (mixedVector B) := by
    change mixedMoment B node1726 node1726Labels = _
    exact sound1726 B hB hF
  have h1734 : mixedVector B (Sum.inr 1734) = Sparse.eval nodeValue1734 (mixedVector B) := by
    change mixedMoment B node1734 node1734Labels = _
    exact sound1734 B hB hF
  have h1736 : mixedVector B (Sum.inr 1736) = Sparse.eval nodeValue1736 (mixedVector B) := by
    change mixedMoment B node1736 node1736Labels = _
    exact sound1736 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h1753 : mixedVector B (Sum.inr 1753) = Sparse.eval nodeValue1753 (mixedVector B) := by
    change mixedMoment B node1753 node1753Labels = _
    exact sound1753 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  simpa only [sourceForm1726, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1504, h1514, h1515, h1517, h1522, h1670, h1671, h1673, h1678, h1703, h1705, h1706, h1720, h1721, h1723, h1724, h1726, h1734, h1736, h1737, h1750, h1751, h1753, h2202, h2260, h2262, h2263, h2291, reducedSource1473] using sourceEq1726 B hB

theorem rowSound1473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1473 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1473, numericCheck1473, reducedZero1473 B hB hF, mul_zero]

theorem reducedZero1474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1474 (mixedVector B) = 0 := by
  have h578 : mixedVector B (Sum.inr 578) = Sparse.eval nodeValue578 (mixedVector B) := by
    change mixedMoment B node578 node578Labels = _
    exact sound578 B hB hF
  have h581 : mixedVector B (Sum.inr 581) = Sparse.eval nodeValue581 (mixedVector B) := by
    change mixedMoment B node581 node581Labels = _
    exact sound581 B hB hF
  have h583 : mixedVector B (Sum.inr 583) = Sparse.eval nodeValue583 (mixedVector B) := by
    change mixedMoment B node583 node583Labels = _
    exact sound583 B hB hF
  have h586 : mixedVector B (Sum.inr 586) = Sparse.eval nodeValue586 (mixedVector B) := by
    change mixedMoment B node586 node586Labels = _
    exact sound586 B hB hF
  have h603 : mixedVector B (Sum.inr 603) = Sparse.eval nodeValue603 (mixedVector B) := by
    change mixedMoment B node603 node603Labels = _
    exact sound603 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1727, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h578, h581, h583, h586, h603, h1041, h4083, reducedSource1474] using sourceEq1727 B hB

theorem rowSound1474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1474 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1474, numericCheck1474, reducedZero1474 B hB hF, mul_zero]

theorem reducedZero1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1475 (mixedVector B) = 0 := by
  have h603 : mixedVector B (Sum.inr 603) = Sparse.eval nodeValue603 (mixedVector B) := by
    change mixedMoment B node603 node603Labels = _
    exact sound603 B hB hF
  have h922 : mixedVector B (Sum.inr 922) = Sparse.eval nodeValue922 (mixedVector B) := by
    change mixedMoment B node922 node922Labels = _
    exact sound922 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1728, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h603, h922, h1041, h1081, h1086, h4083, reducedSource1475] using sourceEq1728 B hB

theorem rowSound1475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1475 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1475, numericCheck1475, reducedZero1475 B hB hF, mul_zero]

theorem reducedZero1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1476 (mixedVector B) = 0 := by
  have h942 : mixedVector B (Sum.inr 942) = Sparse.eval nodeValue942 (mixedVector B) := by
    change mixedMoment B node942 node942Labels = _
    exact sound942 B hB hF
  have h945 : mixedVector B (Sum.inr 945) = Sparse.eval nodeValue945 (mixedVector B) := by
    change mixedMoment B node945 node945Labels = _
    exact sound945 B hB hF
  have h947 : mixedVector B (Sum.inr 947) = Sparse.eval nodeValue947 (mixedVector B) := by
    change mixedMoment B node947 node947Labels = _
    exact sound947 B hB hF
  have h950 : mixedVector B (Sum.inr 950) = Sparse.eval nodeValue950 (mixedVector B) := by
    change mixedMoment B node950 node950Labels = _
    exact sound950 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1729, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h942, h945, h947, h950, h1041, h2107, h4083, reducedSource1476] using sourceEq1729 B hB

theorem rowSound1476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1476 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1476, numericCheck1476, reducedZero1476 B hB hF, mul_zero]

theorem reducedZero1481 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1481 (mixedVector B) = 0 := by
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h2016 : mixedVector B (Sum.inr 2016) = Sparse.eval nodeValue2016 (mixedVector B) := by
    change mixedMoment B node2016 node2016Labels = _
    exact sound2016 B hB hF
  have h2101 : mixedVector B (Sum.inr 2101) = Sparse.eval nodeValue2101 (mixedVector B) := by
    change mixedMoment B node2101 node2101Labels = _
    exact sound2101 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1735, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1035, h2016, h2101, h2205, h2242, h2260, h4080, reducedSource1481] using sourceEq1735 B hB

theorem rowSound1481 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1481 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1481, numericCheck1481, reducedZero1481 B hB hF, mul_zero]

theorem reducedZero1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1482 (mixedVector B) = 0 := by
  have h730 : mixedVector B (Sum.inr 730) = Sparse.eval nodeValue730 (mixedVector B) := by
    change mixedMoment B node730 node730Labels = _
    exact sound730 B hB hF
  have h733 : mixedVector B (Sum.inr 733) = Sparse.eval nodeValue733 (mixedVector B) := by
    change mixedMoment B node733 node733Labels = _
    exact sound733 B hB hF
  have h734 : mixedVector B (Sum.inr 734) = Sparse.eval nodeValue734 (mixedVector B) := by
    change mixedMoment B node734 node734Labels = _
    exact sound734 B hB hF
  have h738 : mixedVector B (Sum.inr 738) = Sparse.eval nodeValue738 (mixedVector B) := by
    change mixedMoment B node738 node738Labels = _
    exact sound738 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h1645 : mixedVector B (Sum.inr 1645) = Sparse.eval nodeValue1645 (mixedVector B) := by
    change mixedMoment B node1645 node1645Labels = _
    exact sound1645 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1737, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h730, h733, h734, h738, h806, h1645, h4069, reducedSource1482] using sourceEq1737 B hB

theorem rowSound1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1482 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1482, numericCheck1482, reducedZero1482 B hB hF, mul_zero]

theorem reducedZero1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1483 (mixedVector B) = 0 := by
  have h4149 : mixedVector B (Sum.inr 4149) = Sparse.eval nodeValue4149 (mixedVector B) := by
    change mixedMoment B node4149 node4149Labels = _
    exact sound4149 B hB hF
  have h4151 : mixedVector B (Sum.inr 4151) = Sparse.eval nodeValue4151 (mixedVector B) := by
    change mixedMoment B node4151 node4151Labels = _
    exact sound4151 B hB hF
  have h4154 : mixedVector B (Sum.inr 4154) = Sparse.eval nodeValue4154 (mixedVector B) := by
    change mixedMoment B node4154 node4154Labels = _
    exact sound4154 B hB hF
  have h4172 : mixedVector B (Sum.inr 4172) = Sparse.eval nodeValue4172 (mixedVector B) := by
    change mixedMoment B node4172 node4172Labels = _
    exact sound4172 B hB hF
  have h4326 : mixedVector B (Sum.inr 4326) = Sparse.eval nodeValue4326 (mixedVector B) := by
    change mixedMoment B node4326 node4326Labels = _
    exact sound4326 B hB hF
  have h4328 : mixedVector B (Sum.inr 4328) = Sparse.eval nodeValue4328 (mixedVector B) := by
    change mixedMoment B node4328 node4328Labels = _
    exact sound4328 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4363 : mixedVector B (Sum.inr 4363) = Sparse.eval nodeValue4363 (mixedVector B) := by
    change mixedMoment B node4363 node4363Labels = _
    exact sound4363 B hB hF
  have h4365 : mixedVector B (Sum.inr 4365) = Sparse.eval nodeValue4365 (mixedVector B) := by
    change mixedMoment B node4365 node4365Labels = _
    exact sound4365 B hB hF
  have h4368 : mixedVector B (Sum.inr 4368) = Sparse.eval nodeValue4368 (mixedVector B) := by
    change mixedMoment B node4368 node4368Labels = _
    exact sound4368 B hB hF
  have h4455 : mixedVector B (Sum.inr 4455) = Sparse.eval nodeValue4455 (mixedVector B) := by
    change mixedMoment B node4455 node4455Labels = _
    exact sound4455 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4459 : mixedVector B (Sum.inr 4459) = Sparse.eval nodeValue4459 (mixedVector B) := by
    change mixedMoment B node4459 node4459Labels = _
    exact sound4459 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  simpa only [sourceForm1738, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4149, h4151, h4154, h4172, h4326, h4328, h4341, h4363, h4365, h4368, h4455, h4457, h4459, h4460, h4466, h4495, h4498, h4801, h4865, h4888, h4894, reducedSource1483] using sourceEq1738 B hB

theorem rowSound1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1483 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1483, numericCheck1483, reducedZero1483 B hB hF, mul_zero]

theorem reducedZero1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1485 (mixedVector B) = 0 := by
  have h1501 : mixedVector B (Sum.inr 1501) = Sparse.eval nodeValue1501 (mixedVector B) := by
    change mixedMoment B node1501 node1501Labels = _
    exact sound1501 B hB hF
  have h1505 : mixedVector B (Sum.inr 1505) = Sparse.eval nodeValue1505 (mixedVector B) := by
    change mixedMoment B node1505 node1505Labels = _
    exact sound1505 B hB hF
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1511 : mixedVector B (Sum.inr 1511) = Sparse.eval nodeValue1511 (mixedVector B) := by
    change mixedMoment B node1511 node1511Labels = _
    exact sound1511 B hB hF
  have h1663 : mixedVector B (Sum.inr 1663) = Sparse.eval nodeValue1663 (mixedVector B) := by
    change mixedMoment B node1663 node1663Labels = _
    exact sound1663 B hB hF
  have h1664 : mixedVector B (Sum.inr 1664) = Sparse.eval nodeValue1664 (mixedVector B) := by
    change mixedMoment B node1664 node1664Labels = _
    exact sound1664 B hB hF
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1697 : mixedVector B (Sum.inr 1697) = Sparse.eval nodeValue1697 (mixedVector B) := by
    change mixedMoment B node1697 node1697Labels = _
    exact sound1697 B hB hF
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1704 : mixedVector B (Sum.inr 1704) = Sparse.eval nodeValue1704 (mixedVector B) := by
    change mixedMoment B node1704 node1704Labels = _
    exact sound1704 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  simpa only [sourceForm1740, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1501, h1505, h1507, h1511, h1663, h1664, h1667, h1697, h1698, h1704, h1707, h1708, h1712, h1714, h1725, h1727, h1738, h2190, h2242, h2244, h2264, reducedSource1485] using sourceEq1740 B hB

theorem rowSound1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1485 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1485, numericCheck1485, reducedZero1485 B hB hF, mul_zero]

theorem reducedZero1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1486 (mixedVector B) = 0 := by
  have h577 : mixedVector B (Sum.inr 577) = Sparse.eval nodeValue577 (mixedVector B) := by
    change mixedMoment B node577 node577Labels = _
    exact sound577 B hB hF
  have h579 : mixedVector B (Sum.inr 579) = Sparse.eval nodeValue579 (mixedVector B) := by
    change mixedMoment B node579 node579Labels = _
    exact sound579 B hB hF
  have h582 : mixedVector B (Sum.inr 582) = Sparse.eval nodeValue582 (mixedVector B) := by
    change mixedMoment B node582 node582Labels = _
    exact sound582 B hB hF
  have h600 : mixedVector B (Sum.inr 600) = Sparse.eval nodeValue600 (mixedVector B) := by
    change mixedMoment B node600 node600Labels = _
    exact sound600 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1741, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h577, h579, h582, h600, h1040, h4084, reducedSource1486] using sourceEq1741 B hB

theorem rowSound1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1486 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1486, numericCheck1486, reducedZero1486 B hB hF, mul_zero]

theorem reducedZero1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1487 (mixedVector B) = 0 := by
  have h600 : mixedVector B (Sum.inr 600) = Sparse.eval nodeValue600 (mixedVector B) := by
    change mixedMoment B node600 node600Labels = _
    exact sound600 B hB hF
  have h919 : mixedVector B (Sum.inr 919) = Sparse.eval nodeValue919 (mixedVector B) := by
    change mixedMoment B node919 node919Labels = _
    exact sound919 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1742, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h600, h919, h1040, h1079, h1082, h4084, reducedSource1487] using sourceEq1742 B hB

theorem rowSound1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1487 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1487, numericCheck1487, reducedZero1487 B hB hF, mul_zero]

theorem sourceRowsAt1472 : MixedData.sourceRows (1472 : Fin 2425) =
    MixedData.row1472 := by decide +kernel

theorem sourceRowsAt1473 : MixedData.sourceRows (1473 : Fin 2425) =
    MixedData.row1473 := by decide +kernel

theorem sourceRowsAt1474 : MixedData.sourceRows (1474 : Fin 2425) =
    MixedData.row1474 := by decide +kernel

theorem sourceRowsAt1475 : MixedData.sourceRows (1475 : Fin 2425) =
    MixedData.row1475 := by decide +kernel

theorem sourceRowsAt1476 : MixedData.sourceRows (1476 : Fin 2425) =
    MixedData.row1476 := by decide +kernel

theorem sourceRowsAt1477 : MixedData.sourceRows (1477 : Fin 2425) =
    MixedData.row1477 := by decide +kernel

theorem sourceRowsAt1478 : MixedData.sourceRows (1478 : Fin 2425) =
    MixedData.row1478 := by decide +kernel

theorem sourceRowsAt1479 : MixedData.sourceRows (1479 : Fin 2425) =
    MixedData.row1479 := by decide +kernel

theorem sourceRowsAt1480 : MixedData.sourceRows (1480 : Fin 2425) =
    MixedData.row1480 := by decide +kernel

theorem sourceRowsAt1481 : MixedData.sourceRows (1481 : Fin 2425) =
    MixedData.row1481 := by decide +kernel

theorem sourceRowsAt1482 : MixedData.sourceRows (1482 : Fin 2425) =
    MixedData.row1482 := by decide +kernel

theorem sourceRowsAt1483 : MixedData.sourceRows (1483 : Fin 2425) =
    MixedData.row1483 := by decide +kernel

theorem sourceRowsAt1484 : MixedData.sourceRows (1484 : Fin 2425) =
    MixedData.row1484 := by decide +kernel

theorem sourceRowsAt1485 : MixedData.sourceRows (1485 : Fin 2425) =
    MixedData.row1485 := by decide +kernel

theorem sourceRowsAt1486 : MixedData.sourceRows (1486 : Fin 2425) =
    MixedData.row1486 := by decide +kernel

theorem sourceRowsAt1487 : MixedData.sourceRows (1487 : Fin 2425) =
    MixedData.row1487 := by decide +kernel

theorem chunkSound92_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 92) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1472 ∨ k.val = 1473 ∨ k.val = 1474 ∨ k.val = 1475 ∨ k.val = 1476 ∨ k.val = 1477 ∨ k.val = 1478 ∨ k.val = 1479 ∨ k.val = 1480 ∨ k.val = 1481 ∨ k.val = 1482 ∨ k.val = 1483 ∨ k.val = 1484 ∨ k.val = 1485 ∨ k.val = 1486 ∨ k.val = 1487 := by omega
  rcases heq with h1472 | h1473 | h1474 | h1475 | h1476 | h1477 | h1478 | h1479 | h1480 | h1481 | h1482 | h1483 | h1484 | h1485 | h1486 | h1487
  · have he : k = (1472 : Fin 2425) := Fin.ext h1472
    subst k
    rw [sourceRowsAt1472]
    exact rowSound1472 B hB hF
  · have he : k = (1473 : Fin 2425) := Fin.ext h1473
    subst k
    rw [sourceRowsAt1473]
    exact rowSound1473 B hB hF
  · have he : k = (1474 : Fin 2425) := Fin.ext h1474
    subst k
    rw [sourceRowsAt1474]
    exact rowSound1474 B hB hF
  · have he : k = (1475 : Fin 2425) := Fin.ext h1475
    subst k
    rw [sourceRowsAt1475]
    exact rowSound1475 B hB hF
  · have he : k = (1476 : Fin 2425) := Fin.ext h1476
    subst k
    rw [sourceRowsAt1476]
    exact rowSound1476 B hB hF
  · have he : k = (1477 : Fin 2425) := Fin.ext h1477
    subst k
    rw [sourceRowsAt1477]
    exact rowSound1477_e B hB hF
  · have he : k = (1478 : Fin 2425) := Fin.ext h1478
    subst k
    rw [sourceRowsAt1478]
    exact rowSound1478_e B hB hF
  · have he : k = (1479 : Fin 2425) := Fin.ext h1479
    subst k
    rw [sourceRowsAt1479]
    exact rowSound1479_e B hB hF
  · have he : k = (1480 : Fin 2425) := Fin.ext h1480
    subst k
    rw [sourceRowsAt1480]
    exact rowSound1480_e B hB hF
  · have he : k = (1481 : Fin 2425) := Fin.ext h1481
    subst k
    rw [sourceRowsAt1481]
    exact rowSound1481 B hB hF
  · have he : k = (1482 : Fin 2425) := Fin.ext h1482
    subst k
    rw [sourceRowsAt1482]
    exact rowSound1482 B hB hF
  · have he : k = (1483 : Fin 2425) := Fin.ext h1483
    subst k
    rw [sourceRowsAt1483]
    exact rowSound1483 B hB hF
  · have he : k = (1484 : Fin 2425) := Fin.ext h1484
    subst k
    rw [sourceRowsAt1484]
    exact rowSound1484_e B hB hF
  · have he : k = (1485 : Fin 2425) := Fin.ext h1485
    subst k
    rw [sourceRowsAt1485]
    exact rowSound1485 B hB hF
  · have he : k = (1486 : Fin 2425) := Fin.ext h1486
    subst k
    rw [sourceRowsAt1486]
    exact rowSound1486 B hB hF
  · have he : k = (1487 : Fin 2425) := Fin.ext h1487
    subst k
    rw [sourceRowsAt1487]
    exact rowSound1487 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e_oai
