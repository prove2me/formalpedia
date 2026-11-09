-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:31:46.473216+00:00
-- url     : https://prove2.me/submissions/de0a3eff-57dc-45e2-9d1b-c0b1fe164831

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E112
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound113_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound114_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound115_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound116_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound125_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound126_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound127_e

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

theorem canonical282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw282 raw282Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw282 raw282Labels = mixedMoment B raw282step0 raw282step0Labels := by
      have ha : raw282step0 = (fun i j => raw282 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw282step0 raw282; decide +kernel
      have hl : raw282step0Labels = raw282Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw282 raw282Labels permutation8 permutation5
    mixedMoment B raw282step0 raw282step0Labels = mixedMoment B raw282step1 raw282step1Labels := by
      have ha : raw282step1 = raw282step0 := by apply Matrix.ext; unfold raw282step1 raw282step0; decide +kernel
      have hl : raw282step0Labels = labelEmbedding1 ∘ raw282step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw282step0 raw282step0Labels raw282step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

theorem canonical283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw283 raw283Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw283 raw283Labels = mixedMoment B raw283step0 raw283step0Labels := by
      have ha : raw283step0 = (fun i j => raw283 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw283step0 raw283; decide +kernel
      have hl : raw283step0Labels = raw283Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw283 raw283Labels permutation8 permutation5
    _ = mixedMoment B node416 node416Labels := by rfl

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

theorem canonical3718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3718 raw3718Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw3718 raw3718Labels = mixedMoment B raw3718step0 raw3718step0Labels := by
      have hz : ∀ j, raw3718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3718step0 = (fun i j => raw3718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3718step0 raw3718; decide +kernel
      have hl : raw3718step0Labels = raw3718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718 raw3718Labels permutation434 hz
    mixedMoment B raw3718step0 raw3718step0Labels = mixedMoment B raw3718step1 raw3718step1Labels := by
      have hz : ∀ j, raw3718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3718step1 = (fun i j => raw3718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3718step1 raw3718step0; decide +kernel
      have hl : raw3718step1Labels = raw3718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718step0 raw3718step0Labels permutation80 hz
    mixedMoment B raw3718step1 raw3718step1Labels = mixedMoment B raw3718step2 raw3718step2Labels := by
      have hz : ∀ j, raw3718step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3718step2 = (fun i j => raw3718step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3718step2 raw3718step1; decide +kernel
      have hl : raw3718step2Labels = raw3718step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718step1 raw3718step1Labels permutation14 hz
    mixedMoment B raw3718step2 raw3718step2Labels = mixedMoment B raw3718step3 raw3718step3Labels := by
      have ha : raw3718step3 = (fun i j => raw3718step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3718step3 raw3718step2; decide +kernel
      have hl : raw3718step3Labels = raw3718step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3718step2 raw3718step2Labels permutation6 permutation2
    _ = mixedMoment B node2294 node2294Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4090 raw4090Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4090 raw4090Labels = mixedMoment B raw4090step0 raw4090step0Labels := by
      have hz : ∀ j, raw4090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4090step0 = (fun i j => raw4090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4090step0 raw4090; decide +kernel
      have hl : raw4090step0Labels = raw4090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4090 raw4090Labels permutation434 hz
    mixedMoment B raw4090step0 raw4090step0Labels = mixedMoment B raw4090step1 raw4090step1Labels := by
      have hz : ∀ j, raw4090step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4090step1 = (fun i j => raw4090step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4090step1 raw4090step0; decide +kernel
      have hl : raw4090step1Labels = raw4090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4090step0 raw4090step0Labels permutation80 hz
    mixedMoment B raw4090step1 raw4090step1Labels = mixedMoment B raw4090step2 raw4090step2Labels := by
      have ha : raw4090step2 = (fun i j => raw4090step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4090step2 raw4090step1; decide +kernel
      have hl : raw4090step2Labels = raw4090step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4090step1 raw4090step1Labels permutation29 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

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

theorem canonical4375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4375 raw4375Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw4375 raw4375Labels = mixedMoment B raw4375step0 raw4375step0Labels := by
      have hz : ∀ j, raw4375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4375step0 = (fun i j => raw4375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4375step0 raw4375; decide +kernel
      have hl : raw4375step0Labels = raw4375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375 raw4375Labels permutation434 hz
    mixedMoment B raw4375step0 raw4375step0Labels = mixedMoment B raw4375step1 raw4375step1Labels := by
      have hz : ∀ j, raw4375step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4375step1 = (fun i j => raw4375step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4375step1 raw4375step0; decide +kernel
      have hl : raw4375step1Labels = raw4375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375step0 raw4375step0Labels permutation80 hz
    mixedMoment B raw4375step1 raw4375step1Labels = mixedMoment B raw4375step2 raw4375step2Labels := by
      have hz : ∀ j, raw4375step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4375step2 = (fun i j => raw4375step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4375step2 raw4375step1; decide +kernel
      have hl : raw4375step2Labels = raw4375step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4375step1 raw4375step1Labels permutation14 hz
    mixedMoment B raw4375step2 raw4375step2Labels = mixedMoment B raw4375step3 raw4375step3Labels := by
      have ha : raw4375step3 = (fun i j => raw4375step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4375step3 raw4375step2; decide +kernel
      have hl : raw4375step3Labels = raw4375step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4375step2 raw4375step2Labels permutation7 permutation2
    _ = mixedMoment B node2292 node2292Labels := by rfl

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

theorem canonical4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4601 raw4601Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4601 raw4601Labels = mixedMoment B raw4601step0 raw4601step0Labels := by
      have hz : ∀ j, raw4601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4601step0 = (fun i j => raw4601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4601step0 raw4601; decide +kernel
      have hl : raw4601step0Labels = raw4601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4601 raw4601Labels permutation434 hz
    mixedMoment B raw4601step0 raw4601step0Labels = mixedMoment B raw4601step1 raw4601step1Labels := by
      have hz : ∀ j, raw4601step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4601step1 = (fun i j => raw4601step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4601step1 raw4601step0; decide +kernel
      have hl : raw4601step1Labels = raw4601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4601step0 raw4601step0Labels permutation56 hz
    mixedMoment B raw4601step1 raw4601step1Labels = mixedMoment B raw4601step2 raw4601step2Labels := by
      have ha : raw4601step2 = (fun i j => raw4601step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4601step2 raw4601step1; decide +kernel
      have hl : raw4601step2Labels = raw4601step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4601step1 raw4601step1Labels permutation29 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4602 raw4602Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4602 raw4602Labels = mixedMoment B raw4602step0 raw4602step0Labels := by
      have hz : ∀ j, raw4602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4602step0 = (fun i j => raw4602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4602step0 raw4602; decide +kernel
      have hl : raw4602step0Labels = raw4602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4602 raw4602Labels permutation346 hz
    mixedMoment B raw4602step0 raw4602step0Labels = mixedMoment B raw4602step1 raw4602step1Labels := by
      have hz : ∀ j, raw4602step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4602step1 = (fun i j => raw4602step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4602step1 raw4602step0; decide +kernel
      have hl : raw4602step1Labels = raw4602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4602step0 raw4602step0Labels permutation56 hz
    mixedMoment B raw4602step1 raw4602step1Labels = mixedMoment B raw4602step2 raw4602step2Labels := by
      have ha : raw4602step2 = (fun i j => raw4602step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4602step2 raw4602step1; decide +kernel
      have hl : raw4602step2Labels = raw4602step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4602step1 raw4602step1Labels permutation29 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical4603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4603 raw4603Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw4603 raw4603Labels = mixedMoment B raw4603step0 raw4603step0Labels := by
      have hz : ∀ j, raw4603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4603step0 = (fun i j => raw4603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4603step0 raw4603; decide +kernel
      have hl : raw4603step0Labels = raw4603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4603 raw4603Labels permutation434 hz
    mixedMoment B raw4603step0 raw4603step0Labels = mixedMoment B raw4603step1 raw4603step1Labels := by
      have hz : ∀ j, raw4603step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4603step1 = (fun i j => raw4603step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4603step1 raw4603step0; decide +kernel
      have hl : raw4603step1Labels = raw4603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4603step0 raw4603step0Labels permutation80 hz
    mixedMoment B raw4603step1 raw4603step1Labels = mixedMoment B raw4603step2 raw4603step2Labels := by
      have hz : ∀ j, raw4603step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4603step2 = (fun i j => raw4603step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4603step2 raw4603step1; decide +kernel
      have hl : raw4603step2Labels = raw4603step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4603step1 raw4603step1Labels permutation14 hz
    mixedMoment B raw4603step2 raw4603step2Labels = mixedMoment B raw4603step3 raw4603step3Labels := by
      have ha : raw4603step3 = (fun i j => raw4603step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4603step3 raw4603step2; decide +kernel
      have hl : raw4603step3Labels = raw4603step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4603step2 raw4603step2Labels permutation7 permutation2
    _ = mixedMoment B node1094 node1094Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4708 raw4708Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw4708 raw4708Labels = mixedMoment B raw4708step0 raw4708step0Labels := by
      have hz : ∀ j, raw4708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4708step0 = (fun i j => raw4708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4708step0 raw4708; decide +kernel
      have hl : raw4708step0Labels = raw4708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4708 raw4708Labels permutation346 hz
    mixedMoment B raw4708step0 raw4708step0Labels = mixedMoment B raw4708step1 raw4708step1Labels := by
      have ha : raw4708step1 = (fun i j => raw4708step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4708step1 raw4708step0; decide +kernel
      have hl : raw4708step1Labels = raw4708step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4708step0 raw4708step0Labels permutation137 permutation7
    mixedMoment B raw4708step1 raw4708step1Labels = mixedMoment B raw4708step2 raw4708step2Labels := by
      have ha : raw4708step2 = raw4708step1 := by apply Matrix.ext; unfold raw4708step2 raw4708step1; decide +kernel
      have hl : raw4708step1Labels = labelEmbedding1 ∘ raw4708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4708step1 raw4708step1Labels raw4708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical4709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4709 raw4709Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw4709 raw4709Labels = mixedMoment B raw4709step0 raw4709step0Labels := by
      have hz : ∀ j, raw4709 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4709step0 = (fun i j => raw4709 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4709step0 raw4709; decide +kernel
      have hl : raw4709step0Labels = raw4709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4709 raw4709Labels permutation265 hz
    mixedMoment B raw4709step0 raw4709step0Labels = mixedMoment B raw4709step1 raw4709step1Labels := by
      have ha : raw4709step1 = (fun i j => raw4709step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4709step1 raw4709step0; decide +kernel
      have hl : raw4709step1Labels = raw4709step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4709step0 raw4709step0Labels permutation137 permutation7
    mixedMoment B raw4709step1 raw4709step1Labels = mixedMoment B raw4709step2 raw4709step2Labels := by
      have ha : raw4709step2 = raw4709step1 := by apply Matrix.ext; unfold raw4709step2 raw4709step1; decide +kernel
      have hl : raw4709step1Labels = labelEmbedding1 ∘ raw4709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4709step1 raw4709step1Labels raw4709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical4710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4710 raw4710Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw4710 raw4710Labels = mixedMoment B raw4710step0 raw4710step0Labels := by
      have hz : ∀ j, raw4710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4710step0 = (fun i j => raw4710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4710step0 raw4710; decide +kernel
      have hl : raw4710step0Labels = raw4710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4710 raw4710Labels permutation346 hz
    mixedMoment B raw4710step0 raw4710step0Labels = mixedMoment B raw4710step1 raw4710step1Labels := by
      have hz : ∀ j, raw4710step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4710step1 = (fun i j => raw4710step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4710step1 raw4710step0; decide +kernel
      have hl : raw4710step1Labels = raw4710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4710step0 raw4710step0Labels permutation56 hz
    mixedMoment B raw4710step1 raw4710step1Labels = mixedMoment B raw4710step2 raw4710step2Labels := by
      have ha : raw4710step2 = (fun i j => raw4710step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4710step2 raw4710step1; decide +kernel
      have hl : raw4710step2Labels = raw4710step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4710step1 raw4710step1Labels permutation31 permutation7
    mixedMoment B raw4710step2 raw4710step2Labels = mixedMoment B raw4710step3 raw4710step3Labels := by
      have ha : raw4710step3 = raw4710step2 := by apply Matrix.ext; unfold raw4710step3 raw4710step2; decide +kernel
      have hl : raw4710step2Labels = labelEmbedding1 ∘ raw4710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4710step2 raw4710step2Labels raw4710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical4711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4711 raw4711Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw4711 raw4711Labels = mixedMoment B raw4711step0 raw4711step0Labels := by
      have hz : ∀ j, raw4711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4711step0 = (fun i j => raw4711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4711step0 raw4711; decide +kernel
      have hl : raw4711step0Labels = raw4711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4711 raw4711Labels permutation346 hz
    mixedMoment B raw4711step0 raw4711step0Labels = mixedMoment B raw4711step1 raw4711step1Labels := by
      have hz : ∀ j, raw4711step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4711step1 = (fun i j => raw4711step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4711step1 raw4711step0; decide +kernel
      have hl : raw4711step1Labels = raw4711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4711step0 raw4711step0Labels permutation56 hz
    mixedMoment B raw4711step1 raw4711step1Labels = mixedMoment B raw4711step2 raw4711step2Labels := by
      have ha : raw4711step2 = (fun i j => raw4711step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4711step2 raw4711step1; decide +kernel
      have hl : raw4711step2Labels = raw4711step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4711step1 raw4711step1Labels permutation29 permutation7
    mixedMoment B raw4711step2 raw4711step2Labels = mixedMoment B raw4711step3 raw4711step3Labels := by
      have ha : raw4711step3 = raw4711step2 := by apply Matrix.ext; unfold raw4711step3 raw4711step2; decide +kernel
      have hl : raw4711step2Labels = labelEmbedding1 ∘ raw4711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4711step2 raw4711step2Labels raw4711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical4712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4712 raw4712Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw4712 raw4712Labels = mixedMoment B raw4712step0 raw4712step0Labels := by
      have hz : ∀ j, raw4712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4712step0 = (fun i j => raw4712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4712step0 raw4712; decide +kernel
      have hl : raw4712step0Labels = raw4712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4712 raw4712Labels permutation346 hz
    mixedMoment B raw4712step0 raw4712step0Labels = mixedMoment B raw4712step1 raw4712step1Labels := by
      have hz : ∀ j, raw4712step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4712step1 = (fun i j => raw4712step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4712step1 raw4712step0; decide +kernel
      have hl : raw4712step1Labels = raw4712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4712step0 raw4712step0Labels permutation56 hz
    mixedMoment B raw4712step1 raw4712step1Labels = mixedMoment B raw4712step2 raw4712step2Labels := by
      have ha : raw4712step2 = (fun i j => raw4712step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4712step2 raw4712step1; decide +kernel
      have hl : raw4712step2Labels = raw4712step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4712step1 raw4712step1Labels permutation29 permutation7
    mixedMoment B raw4712step2 raw4712step2Labels = mixedMoment B raw4712step3 raw4712step3Labels := by
      have ha : raw4712step3 = raw4712step2 := by apply Matrix.ext; unfold raw4712step3 raw4712step2; decide +kernel
      have hl : raw4712step2Labels = labelEmbedding1 ∘ raw4712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4712step2 raw4712step2Labels raw4712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

theorem canonical4713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4713 raw4713Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw4713 raw4713Labels = mixedMoment B raw4713step0 raw4713step0Labels := by
      have hz : ∀ j, raw4713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4713step0 = (fun i j => raw4713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4713step0 raw4713; decide +kernel
      have hl : raw4713step0Labels = raw4713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4713 raw4713Labels permutation346 hz
    mixedMoment B raw4713step0 raw4713step0Labels = mixedMoment B raw4713step1 raw4713step1Labels := by
      have ha : raw4713step1 = (fun i j => raw4713step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4713step1 raw4713step0; decide +kernel
      have hl : raw4713step1Labels = raw4713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4713step0 raw4713step0Labels permutation53 permutation5
    mixedMoment B raw4713step1 raw4713step1Labels = mixedMoment B raw4713step2 raw4713step2Labels := by
      have ha : raw4713step2 = -raw4713step1 := by apply Matrix.ext; change ∀ i j, raw4713step2 i j = -(raw4713step1 i j); unfold raw4713step2 raw4713step1; decide +kernel
      have hl : raw4713step2Labels = raw4713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4713step2 raw4713step2Labels = mixedMoment B raw4713step3 raw4713step3Labels := by
      have ha : raw4713step3 = raw4713step2 := by apply Matrix.ext; unfold raw4713step3 raw4713step2; decide +kernel
      have hl : raw4713step2Labels = labelEmbedding1 ∘ raw4713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4713step2 raw4713step2Labels raw4713step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical4714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4714 raw4714Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw4714 raw4714Labels = mixedMoment B raw4714step0 raw4714step0Labels := by
      have ha : raw4714step0 = (fun i j => raw4714 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4714step0 raw4714; decide +kernel
      have hl : raw4714step0Labels = raw4714Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4714 raw4714Labels permutation609 permutation7
    mixedMoment B raw4714step0 raw4714step0Labels = mixedMoment B raw4714step1 raw4714step1Labels := by
      have ha : raw4714step1 = raw4714step0 := by apply Matrix.ext; unfold raw4714step1 raw4714step0; decide +kernel
      have hl : raw4714step0Labels = labelEmbedding1 ∘ raw4714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4714step0 raw4714step0Labels raw4714step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical4715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4715 raw4715Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw4715 raw4715Labels = mixedMoment B raw4715step0 raw4715step0Labels := by
      have hz : ∀ j, raw4715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4715step0 = (fun i j => raw4715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4715step0 raw4715; decide +kernel
      have hl : raw4715step0Labels = raw4715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4715 raw4715Labels permutation346 hz
    mixedMoment B raw4715step0 raw4715step0Labels = mixedMoment B raw4715step1 raw4715step1Labels := by
      have ha : raw4715step1 = (fun i j => raw4715step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4715step1 raw4715step0; decide +kernel
      have hl : raw4715step1Labels = raw4715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4715step0 raw4715step0Labels permutation139 permutation7
    mixedMoment B raw4715step1 raw4715step1Labels = mixedMoment B raw4715step2 raw4715step2Labels := by
      have ha : raw4715step2 = raw4715step1 := by apply Matrix.ext; unfold raw4715step2 raw4715step1; decide +kernel
      have hl : raw4715step1Labels = labelEmbedding1 ∘ raw4715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4715step1 raw4715step1Labels raw4715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical4716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4716 raw4716Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw4716 raw4716Labels = mixedMoment B raw4716step0 raw4716step0Labels := by
      have hz : ∀ j, raw4716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4716step0 = (fun i j => raw4716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4716step0 raw4716; decide +kernel
      have hl : raw4716step0Labels = raw4716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4716 raw4716Labels permutation346 hz
    mixedMoment B raw4716step0 raw4716step0Labels = mixedMoment B raw4716step1 raw4716step1Labels := by
      have ha : raw4716step1 = (fun i j => raw4716step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4716step1 raw4716step0; decide +kernel
      have hl : raw4716step1Labels = raw4716step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4716step0 raw4716step0Labels permutation137 permutation7
    mixedMoment B raw4716step1 raw4716step1Labels = mixedMoment B raw4716step2 raw4716step2Labels := by
      have ha : raw4716step2 = raw4716step1 := by apply Matrix.ext; unfold raw4716step2 raw4716step1; decide +kernel
      have hl : raw4716step1Labels = labelEmbedding1 ∘ raw4716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4716step1 raw4716step1Labels raw4716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical4717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4717 raw4717Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw4717 raw4717Labels = mixedMoment B raw4717step0 raw4717step0Labels := by
      have hz : ∀ j, raw4717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4717step0 = (fun i j => raw4717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4717step0 raw4717; decide +kernel
      have hl : raw4717step0Labels = raw4717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4717 raw4717Labels permutation346 hz
    mixedMoment B raw4717step0 raw4717step0Labels = mixedMoment B raw4717step1 raw4717step1Labels := by
      have ha : raw4717step1 = (fun i j => raw4717step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4717step1 raw4717step0; decide +kernel
      have hl : raw4717step1Labels = raw4717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4717step0 raw4717step0Labels permutation137 permutation7
    mixedMoment B raw4717step1 raw4717step1Labels = mixedMoment B raw4717step2 raw4717step2Labels := by
      have ha : raw4717step2 = raw4717step1 := by apply Matrix.ext; unfold raw4717step2 raw4717step1; decide +kernel
      have hl : raw4717step1Labels = labelEmbedding1 ∘ raw4717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4717step1 raw4717step1Labels raw4717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical4718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4718 raw4718Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw4718 raw4718Labels = mixedMoment B raw4718step0 raw4718step0Labels := by
      have hz : ∀ j, raw4718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4718step0 = (fun i j => raw4718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4718step0 raw4718; decide +kernel
      have hl : raw4718step0Labels = raw4718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4718 raw4718Labels permutation265 hz
    mixedMoment B raw4718step0 raw4718step0Labels = mixedMoment B raw4718step1 raw4718step1Labels := by
      have ha : raw4718step1 = (fun i j => raw4718step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4718step1 raw4718step0; decide +kernel
      have hl : raw4718step1Labels = raw4718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4718step0 raw4718step0Labels permutation53 permutation5
    mixedMoment B raw4718step1 raw4718step1Labels = mixedMoment B raw4718step2 raw4718step2Labels := by
      have ha : raw4718step2 = -raw4718step1 := by apply Matrix.ext; change ∀ i j, raw4718step2 i j = -(raw4718step1 i j); unfold raw4718step2 raw4718step1; decide +kernel
      have hl : raw4718step2Labels = raw4718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4718step2 raw4718step2Labels = mixedMoment B raw4718step3 raw4718step3Labels := by
      have ha : raw4718step3 = raw4718step2 := by apply Matrix.ext; unfold raw4718step3 raw4718step2; decide +kernel
      have hl : raw4718step2Labels = labelEmbedding1 ∘ raw4718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4718step2 raw4718step2Labels raw4718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical4719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4719 raw4719Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw4719 raw4719Labels = mixedMoment B raw4719step0 raw4719step0Labels := by
      have ha : raw4719step0 = (fun i j => raw4719 (permutation632 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4719step0 raw4719; decide +kernel
      have hl : raw4719step0Labels = raw4719Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4719 raw4719Labels permutation632 permutation7
    mixedMoment B raw4719step0 raw4719step0Labels = mixedMoment B raw4719step1 raw4719step1Labels := by
      have ha : raw4719step1 = raw4719step0 := by apply Matrix.ext; unfold raw4719step1 raw4719step0; decide +kernel
      have hl : raw4719step0Labels = labelEmbedding1 ∘ raw4719step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4719step0 raw4719step0Labels raw4719step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical4720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4720 raw4720Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw4720 raw4720Labels = mixedMoment B raw4720step0 raw4720step0Labels := by
      have hz : ∀ j, raw4720 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4720step0 = (fun i j => raw4720 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4720step0 raw4720; decide +kernel
      have hl : raw4720step0Labels = raw4720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4720 raw4720Labels permutation265 hz
    mixedMoment B raw4720step0 raw4720step0Labels = mixedMoment B raw4720step1 raw4720step1Labels := by
      have ha : raw4720step1 = (fun i j => raw4720step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4720step1 raw4720step0; decide +kernel
      have hl : raw4720step1Labels = raw4720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4720step0 raw4720step0Labels permutation139 permutation7
    mixedMoment B raw4720step1 raw4720step1Labels = mixedMoment B raw4720step2 raw4720step2Labels := by
      have ha : raw4720step2 = raw4720step1 := by apply Matrix.ext; unfold raw4720step2 raw4720step1; decide +kernel
      have hl : raw4720step1Labels = labelEmbedding1 ∘ raw4720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4720step1 raw4720step1Labels raw4720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical4721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4721 raw4721Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw4721 raw4721Labels = mixedMoment B raw4721step0 raw4721step0Labels := by
      have hz : ∀ j, raw4721 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4721step0 = (fun i j => raw4721 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4721step0 raw4721; decide +kernel
      have hl : raw4721step0Labels = raw4721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4721 raw4721Labels permutation265 hz
    mixedMoment B raw4721step0 raw4721step0Labels = mixedMoment B raw4721step1 raw4721step1Labels := by
      have ha : raw4721step1 = (fun i j => raw4721step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4721step1 raw4721step0; decide +kernel
      have hl : raw4721step1Labels = raw4721step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4721step0 raw4721step0Labels permutation137 permutation7
    mixedMoment B raw4721step1 raw4721step1Labels = mixedMoment B raw4721step2 raw4721step2Labels := by
      have ha : raw4721step2 = raw4721step1 := by apply Matrix.ext; unfold raw4721step2 raw4721step1; decide +kernel
      have hl : raw4721step1Labels = labelEmbedding1 ∘ raw4721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4721step1 raw4721step1Labels raw4721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical4722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4722 raw4722Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw4722 raw4722Labels = mixedMoment B raw4722step0 raw4722step0Labels := by
      have hz : ∀ j, raw4722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4722step0 = (fun i j => raw4722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4722step0 raw4722; decide +kernel
      have hl : raw4722step0Labels = raw4722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4722 raw4722Labels permutation265 hz
    mixedMoment B raw4722step0 raw4722step0Labels = mixedMoment B raw4722step1 raw4722step1Labels := by
      have ha : raw4722step1 = (fun i j => raw4722step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4722step1 raw4722step0; decide +kernel
      have hl : raw4722step1Labels = raw4722step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4722step0 raw4722step0Labels permutation137 permutation7
    mixedMoment B raw4722step1 raw4722step1Labels = mixedMoment B raw4722step2 raw4722step2Labels := by
      have ha : raw4722step2 = raw4722step1 := by apply Matrix.ext; unfold raw4722step2 raw4722step1; decide +kernel
      have hl : raw4722step1Labels = labelEmbedding1 ∘ raw4722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4722step1 raw4722step1Labels raw4722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

theorem canonical4723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4723 raw4723Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw4723 raw4723Labels = mixedMoment B raw4723step0 raw4723step0Labels := by
      have hz : ∀ j, raw4723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4723step0 = (fun i j => raw4723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4723step0 raw4723; decide +kernel
      have hl : raw4723step0Labels = raw4723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4723 raw4723Labels permutation346 hz
    mixedMoment B raw4723step0 raw4723step0Labels = mixedMoment B raw4723step1 raw4723step1Labels := by
      have hz : ∀ j, raw4723step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4723step1 = (fun i j => raw4723step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4723step1 raw4723step0; decide +kernel
      have hl : raw4723step1Labels = raw4723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4723step0 raw4723step0Labels permutation56 hz
    mixedMoment B raw4723step1 raw4723step1Labels = mixedMoment B raw4723step2 raw4723step2Labels := by
      have ha : raw4723step2 = (fun i j => raw4723step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4723step2 raw4723step1; decide +kernel
      have hl : raw4723step2Labels = raw4723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4723step1 raw4723step1Labels permutation13 permutation5
    mixedMoment B raw4723step2 raw4723step2Labels = mixedMoment B raw4723step3 raw4723step3Labels := by
      have ha : raw4723step3 = -raw4723step2 := by apply Matrix.ext; change ∀ i j, raw4723step3 i j = -(raw4723step2 i j); unfold raw4723step3 raw4723step2; decide +kernel
      have hl : raw4723step3Labels = raw4723step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4723step3 raw4723step3Labels = mixedMoment B raw4723step4 raw4723step4Labels := by
      have ha : raw4723step4 = raw4723step3 := by apply Matrix.ext; unfold raw4723step4 raw4723step3; decide +kernel
      have hl : raw4723step3Labels = labelEmbedding1 ∘ raw4723step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4723step3 raw4723step3Labels raw4723step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

theorem canonical4724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4724 raw4724Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw4724 raw4724Labels = mixedMoment B raw4724step0 raw4724step0Labels := by
      have hz : ∀ j, raw4724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4724step0 = (fun i j => raw4724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4724step0 raw4724; decide +kernel
      have hl : raw4724step0Labels = raw4724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4724 raw4724Labels permutation346 hz
    mixedMoment B raw4724step0 raw4724step0Labels = mixedMoment B raw4724step1 raw4724step1Labels := by
      have ha : raw4724step1 = (fun i j => raw4724step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4724step1 raw4724step0; decide +kernel
      have hl : raw4724step1Labels = raw4724step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4724step0 raw4724step0Labels permutation137 permutation7
    mixedMoment B raw4724step1 raw4724step1Labels = mixedMoment B raw4724step2 raw4724step2Labels := by
      have ha : raw4724step2 = raw4724step1 := by apply Matrix.ext; unfold raw4724step2 raw4724step1; decide +kernel
      have hl : raw4724step1Labels = labelEmbedding1 ∘ raw4724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4724step1 raw4724step1Labels raw4724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical4725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4725 raw4725Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw4725 raw4725Labels = mixedMoment B raw4725step0 raw4725step0Labels := by
      have hz : ∀ j, raw4725 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4725step0 = (fun i j => raw4725 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4725step0 raw4725; decide +kernel
      have hl : raw4725step0Labels = raw4725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4725 raw4725Labels permutation265 hz
    mixedMoment B raw4725step0 raw4725step0Labels = mixedMoment B raw4725step1 raw4725step1Labels := by
      have ha : raw4725step1 = (fun i j => raw4725step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4725step1 raw4725step0; decide +kernel
      have hl : raw4725step1Labels = raw4725step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4725step0 raw4725step0Labels permutation137 permutation7
    mixedMoment B raw4725step1 raw4725step1Labels = mixedMoment B raw4725step2 raw4725step2Labels := by
      have ha : raw4725step2 = raw4725step1 := by apply Matrix.ext; unfold raw4725step2 raw4725step1; decide +kernel
      have hl : raw4725step1Labels = labelEmbedding1 ∘ raw4725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4725step1 raw4725step1Labels raw4725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical4726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4726 raw4726Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw4726 raw4726Labels = mixedMoment B raw4726step0 raw4726step0Labels := by
      have hz : ∀ j, raw4726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4726step0 = (fun i j => raw4726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4726step0 raw4726; decide +kernel
      have hl : raw4726step0Labels = raw4726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4726 raw4726Labels permutation346 hz
    mixedMoment B raw4726step0 raw4726step0Labels = mixedMoment B raw4726step1 raw4726step1Labels := by
      have hz : ∀ j, raw4726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4726step1 = (fun i j => raw4726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4726step1 raw4726step0; decide +kernel
      have hl : raw4726step1Labels = raw4726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4726step0 raw4726step0Labels permutation56 hz
    mixedMoment B raw4726step1 raw4726step1Labels = mixedMoment B raw4726step2 raw4726step2Labels := by
      have ha : raw4726step2 = (fun i j => raw4726step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4726step2 raw4726step1; decide +kernel
      have hl : raw4726step2Labels = raw4726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4726step1 raw4726step1Labels permutation29 permutation7
    mixedMoment B raw4726step2 raw4726step2Labels = mixedMoment B raw4726step3 raw4726step3Labels := by
      have ha : raw4726step3 = raw4726step2 := by apply Matrix.ext; unfold raw4726step3 raw4726step2; decide +kernel
      have hl : raw4726step2Labels = labelEmbedding1 ∘ raw4726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4726step2 raw4726step2Labels raw4726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical4727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4727 raw4727Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw4727 raw4727Labels = mixedMoment B raw4727step0 raw4727step0Labels := by
      have hz : ∀ j, raw4727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4727step0 = (fun i j => raw4727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4727step0 raw4727; decide +kernel
      have hl : raw4727step0Labels = raw4727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4727 raw4727Labels permutation346 hz
    mixedMoment B raw4727step0 raw4727step0Labels = mixedMoment B raw4727step1 raw4727step1Labels := by
      have hz : ∀ j, raw4727step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4727step1 = (fun i j => raw4727step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4727step1 raw4727step0; decide +kernel
      have hl : raw4727step1Labels = raw4727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4727step0 raw4727step0Labels permutation56 hz
    mixedMoment B raw4727step1 raw4727step1Labels = mixedMoment B raw4727step2 raw4727step2Labels := by
      have ha : raw4727step2 = (fun i j => raw4727step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4727step2 raw4727step1; decide +kernel
      have hl : raw4727step2Labels = raw4727step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4727step1 raw4727step1Labels permutation29 permutation7
    mixedMoment B raw4727step2 raw4727step2Labels = mixedMoment B raw4727step3 raw4727step3Labels := by
      have ha : raw4727step3 = raw4727step2 := by apply Matrix.ext; unfold raw4727step3 raw4727step2; decide +kernel
      have hl : raw4727step2Labels = labelEmbedding1 ∘ raw4727step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4727step2 raw4727step2Labels raw4727step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical4728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4728 raw4728Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw4728 raw4728Labels = mixedMoment B raw4728step0 raw4728step0Labels := by
      have hz : ∀ j, raw4728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4728step0 = (fun i j => raw4728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4728step0 raw4728; decide +kernel
      have hl : raw4728step0Labels = raw4728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4728 raw4728Labels permutation346 hz
    mixedMoment B raw4728step0 raw4728step0Labels = mixedMoment B raw4728step1 raw4728step1Labels := by
      have hz : ∀ j, raw4728step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4728step1 = (fun i j => raw4728step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4728step1 raw4728step0; decide +kernel
      have hl : raw4728step1Labels = raw4728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4728step0 raw4728step0Labels permutation56 hz
    mixedMoment B raw4728step1 raw4728step1Labels = mixedMoment B raw4728step2 raw4728step2Labels := by
      have ha : raw4728step2 = (fun i j => raw4728step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4728step2 raw4728step1; decide +kernel
      have hl : raw4728step2Labels = raw4728step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4728step1 raw4728step1Labels permutation12 permutation5
    mixedMoment B raw4728step2 raw4728step2Labels = mixedMoment B raw4728step3 raw4728step3Labels := by
      have ha : raw4728step3 = -raw4728step2 := by apply Matrix.ext; change ∀ i j, raw4728step3 i j = -(raw4728step2 i j); unfold raw4728step3 raw4728step2; decide +kernel
      have hl : raw4728step3Labels = raw4728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4728step3 raw4728step3Labels = mixedMoment B raw4728step4 raw4728step4Labels := by
      have ha : raw4728step4 = raw4728step3 := by apply Matrix.ext; unfold raw4728step4 raw4728step3; decide +kernel
      have hl : raw4728step3Labels = labelEmbedding1 ∘ raw4728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4728step3 raw4728step3Labels raw4728step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

theorem canonical4729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4729 raw4729Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw4729 raw4729Labels = mixedMoment B raw4729step0 raw4729step0Labels := by
      have hz : ∀ j, raw4729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4729step0 = (fun i j => raw4729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4729step0 raw4729; decide +kernel
      have hl : raw4729step0Labels = raw4729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4729 raw4729Labels permutation346 hz
    mixedMoment B raw4729step0 raw4729step0Labels = mixedMoment B raw4729step1 raw4729step1Labels := by
      have ha : raw4729step1 = (fun i j => raw4729step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4729step1 raw4729step0; decide +kernel
      have hl : raw4729step1Labels = raw4729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4729step0 raw4729step0Labels permutation139 permutation7
    mixedMoment B raw4729step1 raw4729step1Labels = mixedMoment B raw4729step2 raw4729step2Labels := by
      have ha : raw4729step2 = raw4729step1 := by apply Matrix.ext; unfold raw4729step2 raw4729step1; decide +kernel
      have hl : raw4729step1Labels = labelEmbedding1 ∘ raw4729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4729step1 raw4729step1Labels raw4729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical4730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4730 raw4730Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw4730 raw4730Labels = mixedMoment B raw4730step0 raw4730step0Labels := by
      have hz : ∀ j, raw4730 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4730step0 = (fun i j => raw4730 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4730step0 raw4730; decide +kernel
      have hl : raw4730step0Labels = raw4730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4730 raw4730Labels permutation265 hz
    mixedMoment B raw4730step0 raw4730step0Labels = mixedMoment B raw4730step1 raw4730step1Labels := by
      have ha : raw4730step1 = (fun i j => raw4730step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4730step1 raw4730step0; decide +kernel
      have hl : raw4730step1Labels = raw4730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4730step0 raw4730step0Labels permutation139 permutation7
    mixedMoment B raw4730step1 raw4730step1Labels = mixedMoment B raw4730step2 raw4730step2Labels := by
      have ha : raw4730step2 = raw4730step1 := by apply Matrix.ext; unfold raw4730step2 raw4730step1; decide +kernel
      have hl : raw4730step1Labels = labelEmbedding1 ∘ raw4730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4730step1 raw4730step1Labels raw4730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical4731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4731 raw4731Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw4731 raw4731Labels = mixedMoment B raw4731step0 raw4731step0Labels := by
      have hz : ∀ j, raw4731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4731step0 = (fun i j => raw4731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4731step0 raw4731; decide +kernel
      have hl : raw4731step0Labels = raw4731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4731 raw4731Labels permutation346 hz
    mixedMoment B raw4731step0 raw4731step0Labels = mixedMoment B raw4731step1 raw4731step1Labels := by
      have hz : ∀ j, raw4731step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4731step1 = (fun i j => raw4731step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4731step1 raw4731step0; decide +kernel
      have hl : raw4731step1Labels = raw4731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4731step0 raw4731step0Labels permutation56 hz
    mixedMoment B raw4731step1 raw4731step1Labels = mixedMoment B raw4731step2 raw4731step2Labels := by
      have ha : raw4731step2 = (fun i j => raw4731step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4731step2 raw4731step1; decide +kernel
      have hl : raw4731step2Labels = raw4731step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4731step1 raw4731step1Labels permutation31 permutation7
    mixedMoment B raw4731step2 raw4731step2Labels = mixedMoment B raw4731step3 raw4731step3Labels := by
      have ha : raw4731step3 = raw4731step2 := by apply Matrix.ext; unfold raw4731step3 raw4731step2; decide +kernel
      have hl : raw4731step2Labels = labelEmbedding1 ∘ raw4731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4731step2 raw4731step2Labels raw4731step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical4732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4732 raw4732Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw4732 raw4732Labels = mixedMoment B raw4732step0 raw4732step0Labels := by
      have hz : ∀ j, raw4732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4732step0 = (fun i j => raw4732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4732step0 raw4732; decide +kernel
      have hl : raw4732step0Labels = raw4732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4732 raw4732Labels permutation346 hz
    mixedMoment B raw4732step0 raw4732step0Labels = mixedMoment B raw4732step1 raw4732step1Labels := by
      have hz : ∀ j, raw4732step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4732step1 = (fun i j => raw4732step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4732step1 raw4732step0; decide +kernel
      have hl : raw4732step1Labels = raw4732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4732step0 raw4732step0Labels permutation56 hz
    mixedMoment B raw4732step1 raw4732step1Labels = mixedMoment B raw4732step2 raw4732step2Labels := by
      have ha : raw4732step2 = (fun i j => raw4732step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4732step2 raw4732step1; decide +kernel
      have hl : raw4732step2Labels = raw4732step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4732step1 raw4732step1Labels permutation31 permutation7
    mixedMoment B raw4732step2 raw4732step2Labels = mixedMoment B raw4732step3 raw4732step3Labels := by
      have ha : raw4732step3 = raw4732step2 := by apply Matrix.ext; unfold raw4732step3 raw4732step2; decide +kernel
      have hl : raw4732step2Labels = labelEmbedding1 ∘ raw4732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4732step2 raw4732step2Labels raw4732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

theorem canonical4733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4733 raw4733Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw4733 raw4733Labels = mixedMoment B raw4733step0 raw4733step0Labels := by
      have hz : ∀ j, raw4733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4733step0 = (fun i j => raw4733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4733step0 raw4733; decide +kernel
      have hl : raw4733step0Labels = raw4733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4733 raw4733Labels permutation346 hz
    mixedMoment B raw4733step0 raw4733step0Labels = mixedMoment B raw4733step1 raw4733step1Labels := by
      have hz : ∀ j, raw4733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4733step1 = (fun i j => raw4733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4733step1 raw4733step0; decide +kernel
      have hl : raw4733step1Labels = raw4733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4733step0 raw4733step0Labels permutation56 hz
    mixedMoment B raw4733step1 raw4733step1Labels = mixedMoment B raw4733step2 raw4733step2Labels := by
      have ha : raw4733step2 = (fun i j => raw4733step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4733step2 raw4733step1; decide +kernel
      have hl : raw4733step2Labels = raw4733step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4733step1 raw4733step1Labels permutation8 permutation5
    mixedMoment B raw4733step2 raw4733step2Labels = mixedMoment B raw4733step3 raw4733step3Labels := by
      have ha : raw4733step3 = -raw4733step2 := by apply Matrix.ext; change ∀ i j, raw4733step3 i j = -(raw4733step2 i j); unfold raw4733step3 raw4733step2; decide +kernel
      have hl : raw4733step3Labels = raw4733step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4733step3 raw4733step3Labels = mixedMoment B raw4733step4 raw4733step4Labels := by
      have ha : raw4733step4 = raw4733step3 := by apply Matrix.ext; unfold raw4733step4 raw4733step3; decide +kernel
      have hl : raw4733step3Labels = labelEmbedding1 ∘ raw4733step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4733step3 raw4733step3Labels raw4733step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1749 node1749Labels := by rfl

theorem canonical4734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4734 raw4734Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw4734 raw4734Labels = mixedMoment B raw4734step0 raw4734step0Labels := by
      have hz : ∀ j, raw4734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4734step0 = (fun i j => raw4734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4734step0 raw4734; decide +kernel
      have hl : raw4734step0Labels = raw4734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4734 raw4734Labels permutation346 hz
    mixedMoment B raw4734step0 raw4734step0Labels = mixedMoment B raw4734step1 raw4734step1Labels := by
      have ha : raw4734step1 = (fun i j => raw4734step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4734step1 raw4734step0; decide +kernel
      have hl : raw4734step1Labels = raw4734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4734step0 raw4734step0Labels permutation137 permutation7
    mixedMoment B raw4734step1 raw4734step1Labels = mixedMoment B raw4734step2 raw4734step2Labels := by
      have ha : raw4734step2 = raw4734step1 := by apply Matrix.ext; unfold raw4734step2 raw4734step1; decide +kernel
      have hl : raw4734step1Labels = labelEmbedding1 ∘ raw4734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4734step1 raw4734step1Labels raw4734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical4735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4735 raw4735Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw4735 raw4735Labels = mixedMoment B raw4735step0 raw4735step0Labels := by
      have hz : ∀ j, raw4735 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4735step0 = (fun i j => raw4735 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4735step0 raw4735; decide +kernel
      have hl : raw4735step0Labels = raw4735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4735 raw4735Labels permutation265 hz
    mixedMoment B raw4735step0 raw4735step0Labels = mixedMoment B raw4735step1 raw4735step1Labels := by
      have ha : raw4735step1 = (fun i j => raw4735step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4735step1 raw4735step0; decide +kernel
      have hl : raw4735step1Labels = raw4735step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4735step0 raw4735step0Labels permutation137 permutation7
    mixedMoment B raw4735step1 raw4735step1Labels = mixedMoment B raw4735step2 raw4735step2Labels := by
      have ha : raw4735step2 = raw4735step1 := by apply Matrix.ext; unfold raw4735step2 raw4735step1; decide +kernel
      have hl : raw4735step1Labels = labelEmbedding1 ∘ raw4735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4735step1 raw4735step1Labels raw4735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4736 raw4736Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw4736 raw4736Labels = mixedMoment B raw4736step0 raw4736step0Labels := by
      have hz : ∀ j, raw4736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4736step0 = (fun i j => raw4736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4736step0 raw4736; decide +kernel
      have hl : raw4736step0Labels = raw4736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4736 raw4736Labels permutation346 hz
    mixedMoment B raw4736step0 raw4736step0Labels = mixedMoment B raw4736step1 raw4736step1Labels := by
      have hz : ∀ j, raw4736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4736step1 = (fun i j => raw4736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4736step1 raw4736step0; decide +kernel
      have hl : raw4736step1Labels = raw4736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4736step0 raw4736step0Labels permutation56 hz
    mixedMoment B raw4736step1 raw4736step1Labels = mixedMoment B raw4736step2 raw4736step2Labels := by
      have ha : raw4736step2 = (fun i j => raw4736step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4736step2 raw4736step1; decide +kernel
      have hl : raw4736step2Labels = raw4736step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4736step1 raw4736step1Labels permutation31 permutation7
    mixedMoment B raw4736step2 raw4736step2Labels = mixedMoment B raw4736step3 raw4736step3Labels := by
      have ha : raw4736step3 = raw4736step2 := by apply Matrix.ext; unfold raw4736step3 raw4736step2; decide +kernel
      have hl : raw4736step2Labels = labelEmbedding1 ∘ raw4736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4736step2 raw4736step2Labels raw4736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical4737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4737 raw4737Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw4737 raw4737Labels = mixedMoment B raw4737step0 raw4737step0Labels := by
      have hz : ∀ j, raw4737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4737step0 = (fun i j => raw4737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4737step0 raw4737; decide +kernel
      have hl : raw4737step0Labels = raw4737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4737 raw4737Labels permutation346 hz
    mixedMoment B raw4737step0 raw4737step0Labels = mixedMoment B raw4737step1 raw4737step1Labels := by
      have hz : ∀ j, raw4737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4737step1 = (fun i j => raw4737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4737step1 raw4737step0; decide +kernel
      have hl : raw4737step1Labels = raw4737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4737step0 raw4737step0Labels permutation56 hz
    mixedMoment B raw4737step1 raw4737step1Labels = mixedMoment B raw4737step2 raw4737step2Labels := by
      have ha : raw4737step2 = (fun i j => raw4737step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4737step2 raw4737step1; decide +kernel
      have hl : raw4737step2Labels = raw4737step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4737step1 raw4737step1Labels permutation29 permutation7
    mixedMoment B raw4737step2 raw4737step2Labels = mixedMoment B raw4737step3 raw4737step3Labels := by
      have ha : raw4737step3 = raw4737step2 := by apply Matrix.ext; unfold raw4737step3 raw4737step2; decide +kernel
      have hl : raw4737step2Labels = labelEmbedding1 ∘ raw4737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4737step2 raw4737step2Labels raw4737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical4738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4738 raw4738Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw4738 raw4738Labels = mixedMoment B raw4738step0 raw4738step0Labels := by
      have hz : ∀ j, raw4738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4738step0 = (fun i j => raw4738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4738step0 raw4738; decide +kernel
      have hl : raw4738step0Labels = raw4738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4738 raw4738Labels permutation346 hz
    mixedMoment B raw4738step0 raw4738step0Labels = mixedMoment B raw4738step1 raw4738step1Labels := by
      have hz : ∀ j, raw4738step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4738step1 = (fun i j => raw4738step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4738step1 raw4738step0; decide +kernel
      have hl : raw4738step1Labels = raw4738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4738step0 raw4738step0Labels permutation56 hz
    mixedMoment B raw4738step1 raw4738step1Labels = mixedMoment B raw4738step2 raw4738step2Labels := by
      have ha : raw4738step2 = (fun i j => raw4738step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4738step2 raw4738step1; decide +kernel
      have hl : raw4738step2Labels = raw4738step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4738step1 raw4738step1Labels permutation29 permutation2
    mixedMoment B raw4738step2 raw4738step2Labels = mixedMoment B raw4738step3 raw4738step3Labels := by
      have ha : raw4738step3 = -raw4738step2 := by apply Matrix.ext; change ∀ i j, raw4738step3 i j = -(raw4738step2 i j); unfold raw4738step3 raw4738step2; decide +kernel
      have hl : raw4738step3Labels = raw4738step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical4739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4739 raw4739Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw4739 raw4739Labels = mixedMoment B raw4739step0 raw4739step0Labels := by
      have hz : ∀ j, raw4739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4739step0 = (fun i j => raw4739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4739step0 raw4739; decide +kernel
      have hl : raw4739step0Labels = raw4739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4739 raw4739Labels permutation346 hz
    mixedMoment B raw4739step0 raw4739step0Labels = mixedMoment B raw4739step1 raw4739step1Labels := by
      have ha : raw4739step1 = (fun i j => raw4739step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4739step1 raw4739step0; decide +kernel
      have hl : raw4739step1Labels = raw4739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4739step0 raw4739step0Labels permutation145 permutation2
    mixedMoment B raw4739step1 raw4739step1Labels = mixedMoment B raw4739step2 raw4739step2Labels := by
      have ha : raw4739step2 = -raw4739step1 := by apply Matrix.ext; change ∀ i j, raw4739step2 i j = -(raw4739step1 i j); unfold raw4739step2 raw4739step1; decide +kernel
      have hl : raw4739step2Labels = raw4739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical4740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4740 raw4740Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw4740 raw4740Labels = mixedMoment B raw4740step0 raw4740step0Labels := by
      have hz : ∀ j, raw4740 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4740step0 = (fun i j => raw4740 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4740step0 raw4740; decide +kernel
      have hl : raw4740step0Labels = raw4740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4740 raw4740Labels permutation265 hz
    mixedMoment B raw4740step0 raw4740step0Labels = mixedMoment B raw4740step1 raw4740step1Labels := by
      have ha : raw4740step1 = (fun i j => raw4740step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4740step1 raw4740step0; decide +kernel
      have hl : raw4740step1Labels = raw4740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4740step0 raw4740step0Labels permutation145 permutation2
    mixedMoment B raw4740step1 raw4740step1Labels = mixedMoment B raw4740step2 raw4740step2Labels := by
      have ha : raw4740step2 = -raw4740step1 := by apply Matrix.ext; change ∀ i j, raw4740step2 i j = -(raw4740step1 i j); unfold raw4740step2 raw4740step1; decide +kernel
      have hl : raw4740step2Labels = raw4740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical4741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4741 raw4741Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw4741 raw4741Labels = mixedMoment B raw4741step0 raw4741step0Labels := by
      have hz : ∀ j, raw4741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4741step0 = (fun i j => raw4741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4741step0 raw4741; decide +kernel
      have hl : raw4741step0Labels = raw4741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4741 raw4741Labels permutation346 hz
    mixedMoment B raw4741step0 raw4741step0Labels = mixedMoment B raw4741step1 raw4741step1Labels := by
      have hz : ∀ j, raw4741step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4741step1 = (fun i j => raw4741step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4741step1 raw4741step0; decide +kernel
      have hl : raw4741step1Labels = raw4741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4741step0 raw4741step0Labels permutation56 hz
    mixedMoment B raw4741step1 raw4741step1Labels = mixedMoment B raw4741step2 raw4741step2Labels := by
      have ha : raw4741step2 = (fun i j => raw4741step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4741step2 raw4741step1; decide +kernel
      have hl : raw4741step2Labels = raw4741step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4741step1 raw4741step1Labels permutation31 permutation2
    mixedMoment B raw4741step2 raw4741step2Labels = mixedMoment B raw4741step3 raw4741step3Labels := by
      have ha : raw4741step3 = -raw4741step2 := by apply Matrix.ext; change ∀ i j, raw4741step3 i j = -(raw4741step2 i j); unfold raw4741step3 raw4741step2; decide +kernel
      have hl : raw4741step3Labels = raw4741step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical4742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4742 raw4742Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw4742 raw4742Labels = mixedMoment B raw4742step0 raw4742step0Labels := by
      have hz : ∀ j, raw4742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4742step0 = (fun i j => raw4742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4742step0 raw4742; decide +kernel
      have hl : raw4742step0Labels = raw4742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4742 raw4742Labels permutation346 hz
    mixedMoment B raw4742step0 raw4742step0Labels = mixedMoment B raw4742step1 raw4742step1Labels := by
      have hz : ∀ j, raw4742step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4742step1 = (fun i j => raw4742step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4742step1 raw4742step0; decide +kernel
      have hl : raw4742step1Labels = raw4742step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4742step0 raw4742step0Labels permutation56 hz
    mixedMoment B raw4742step1 raw4742step1Labels = mixedMoment B raw4742step2 raw4742step2Labels := by
      have ha : raw4742step2 = (fun i j => raw4742step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4742step2 raw4742step1; decide +kernel
      have hl : raw4742step2Labels = raw4742step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4742step1 raw4742step1Labels permutation29 permutation2
    mixedMoment B raw4742step2 raw4742step2Labels = mixedMoment B raw4742step3 raw4742step3Labels := by
      have ha : raw4742step3 = -raw4742step2 := by apply Matrix.ext; change ∀ i j, raw4742step3 i j = -(raw4742step2 i j); unfold raw4742step3 raw4742step2; decide +kernel
      have hl : raw4742step3Labels = raw4742step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical4743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4743 raw4743Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw4743 raw4743Labels = mixedMoment B raw4743step0 raw4743step0Labels := by
      have hz : ∀ j, raw4743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4743step0 = (fun i j => raw4743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4743step0 raw4743; decide +kernel
      have hl : raw4743step0Labels = raw4743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4743 raw4743Labels permutation346 hz
    mixedMoment B raw4743step0 raw4743step0Labels = mixedMoment B raw4743step1 raw4743step1Labels := by
      have hz : ∀ j, raw4743step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4743step1 = (fun i j => raw4743step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4743step1 raw4743step0; decide +kernel
      have hl : raw4743step1Labels = raw4743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4743step0 raw4743step0Labels permutation56 hz
    mixedMoment B raw4743step1 raw4743step1Labels = mixedMoment B raw4743step2 raw4743step2Labels := by
      have ha : raw4743step2 = (fun i j => raw4743step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4743step2 raw4743step1; decide +kernel
      have hl : raw4743step2Labels = raw4743step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4743step1 raw4743step1Labels permutation29 permutation2
    mixedMoment B raw4743step2 raw4743step2Labels = mixedMoment B raw4743step3 raw4743step3Labels := by
      have ha : raw4743step3 = -raw4743step2 := by apply Matrix.ext; change ∀ i j, raw4743step3 i j = -(raw4743step2 i j); unfold raw4743step3 raw4743step2; decide +kernel
      have hl : raw4743step3Labels = raw4743step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical4744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4744 raw4744Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw4744 raw4744Labels = mixedMoment B raw4744step0 raw4744step0Labels := by
      have hz : ∀ j, raw4744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4744step0 = (fun i j => raw4744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4744step0 raw4744; decide +kernel
      have hl : raw4744step0Labels = raw4744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744 raw4744Labels permutation346 hz
    mixedMoment B raw4744step0 raw4744step0Labels = mixedMoment B raw4744step1 raw4744step1Labels := by
      have hz : ∀ j, raw4744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4744step1 = (fun i j => raw4744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4744step1 raw4744step0; decide +kernel
      have hl : raw4744step1Labels = raw4744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744step0 raw4744step0Labels permutation56 hz
    mixedMoment B raw4744step1 raw4744step1Labels = mixedMoment B raw4744step2 raw4744step2Labels := by
      have ha : raw4744step2 = (fun i j => raw4744step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4744step2 raw4744step1; decide +kernel
      have hl : raw4744step2Labels = raw4744step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4744step1 raw4744step1Labels permutation26 permutation0
    mixedMoment B raw4744step2 raw4744step2Labels = mixedMoment B raw4744step3 raw4744step3Labels := by
      have ha : raw4744step3 = -raw4744step2 := by apply Matrix.ext; change ∀ i j, raw4744step3 i j = -(raw4744step2 i j); unfold raw4744step3 raw4744step2; decide +kernel
      have hl : raw4744step3Labels = raw4744step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical4745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4745 raw4745Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw4745 raw4745Labels = mixedMoment B raw4745step0 raw4745step0Labels := by
      have hz : ∀ j, raw4745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4745step0 = (fun i j => raw4745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4745step0 raw4745; decide +kernel
      have hl : raw4745step0Labels = raw4745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4745 raw4745Labels permutation346 hz
    mixedMoment B raw4745step0 raw4745step0Labels = mixedMoment B raw4745step1 raw4745step1Labels := by
      have ha : raw4745step1 = (fun i j => raw4745step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4745step1 raw4745step0; decide +kernel
      have hl : raw4745step1Labels = raw4745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4745step0 raw4745step0Labels permutation40 permutation2
    _ = mixedMoment B node1385 node1385Labels := by rfl

theorem canonical4746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4746 raw4746Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw4746 raw4746Labels = mixedMoment B raw4746step0 raw4746step0Labels := by
      have hz : ∀ j, raw4746 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4746step0 = (fun i j => raw4746 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4746step0 raw4746; decide +kernel
      have hl : raw4746step0Labels = raw4746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4746 raw4746Labels permutation265 hz
    mixedMoment B raw4746step0 raw4746step0Labels = mixedMoment B raw4746step1 raw4746step1Labels := by
      have ha : raw4746step1 = (fun i j => raw4746step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4746step1 raw4746step0; decide +kernel
      have hl : raw4746step1Labels = raw4746step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4746step0 raw4746step0Labels permutation40 permutation2
    _ = mixedMoment B node1385 node1385Labels := by rfl

theorem canonical4747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4747 raw4747Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw4747 raw4747Labels = mixedMoment B raw4747step0 raw4747step0Labels := by
      have hz : ∀ j, raw4747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4747step0 = (fun i j => raw4747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4747step0 raw4747; decide +kernel
      have hl : raw4747step0Labels = raw4747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4747 raw4747Labels permutation346 hz
    mixedMoment B raw4747step0 raw4747step0Labels = mixedMoment B raw4747step1 raw4747step1Labels := by
      have hz : ∀ j, raw4747step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4747step1 = (fun i j => raw4747step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4747step1 raw4747step0; decide +kernel
      have hl : raw4747step1Labels = raw4747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4747step0 raw4747step0Labels permutation56 hz
    mixedMoment B raw4747step1 raw4747step1Labels = mixedMoment B raw4747step2 raw4747step2Labels := by
      have ha : raw4747step2 = (fun i j => raw4747step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4747step2 raw4747step1; decide +kernel
      have hl : raw4747step2Labels = raw4747step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4747step1 raw4747step1Labels permutation10 permutation2
    _ = mixedMoment B node1408 node1408Labels := by rfl

theorem canonical4748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4748 raw4748Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw4748 raw4748Labels = mixedMoment B raw4748step0 raw4748step0Labels := by
      have hz : ∀ j, raw4748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4748step0 = (fun i j => raw4748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4748step0 raw4748; decide +kernel
      have hl : raw4748step0Labels = raw4748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4748 raw4748Labels permutation346 hz
    mixedMoment B raw4748step0 raw4748step0Labels = mixedMoment B raw4748step1 raw4748step1Labels := by
      have hz : ∀ j, raw4748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4748step1 = (fun i j => raw4748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4748step1 raw4748step0; decide +kernel
      have hl : raw4748step1Labels = raw4748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4748step0 raw4748step0Labels permutation56 hz
    _ = mixedMoment B node1408 node1408Labels := by rfl

theorem canonical4749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4749 raw4749Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw4749 raw4749Labels = mixedMoment B raw4749step0 raw4749step0Labels := by
      have hz : ∀ j, raw4749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4749step0 = (fun i j => raw4749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4749step0 raw4749; decide +kernel
      have hl : raw4749step0Labels = raw4749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4749 raw4749Labels permutation346 hz
    mixedMoment B raw4749step0 raw4749step0Labels = mixedMoment B raw4749step1 raw4749step1Labels := by
      have hz : ∀ j, raw4749step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4749step1 = (fun i j => raw4749step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4749step1 raw4749step0; decide +kernel
      have hl : raw4749step1Labels = raw4749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4749step0 raw4749step0Labels permutation56 hz
    mixedMoment B raw4749step1 raw4749step1Labels = mixedMoment B raw4749step2 raw4749step2Labels := by
      have ha : raw4749step2 = (fun i j => raw4749step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4749step2 raw4749step1; decide +kernel
      have hl : raw4749step2Labels = raw4749step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4749step1 raw4749step1Labels permutation29 permutation2
    mixedMoment B raw4749step2 raw4749step2Labels = mixedMoment B raw4749step3 raw4749step3Labels := by
      have ha : raw4749step3 = -raw4749step2 := by apply Matrix.ext; change ∀ i j, raw4749step3 i j = -(raw4749step2 i j); unfold raw4749step3 raw4749step2; decide +kernel
      have hl : raw4749step3Labels = raw4749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1027 node1027Labels := by rfl

theorem canonical4750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4750 raw4750Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw4750 raw4750Labels = mixedMoment B raw4750step0 raw4750step0Labels := by
      have ha : raw4750step0 = (fun i j => raw4750 (permutation616 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4750step0 raw4750; decide +kernel
      have hl : raw4750step0Labels = raw4750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4750 raw4750Labels permutation616 permutation2
    mixedMoment B raw4750step0 raw4750step0Labels = mixedMoment B raw4750step1 raw4750step1Labels := by
      have ha : raw4750step1 = -raw4750step0 := by apply Matrix.ext; change ∀ i j, raw4750step1 i j = -(raw4750step0 i j); unfold raw4750step1 raw4750step0; decide +kernel
      have hl : raw4750step1Labels = raw4750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2009 node2009Labels := by rfl

theorem canonical4751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4751 raw4751Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4751 raw4751Labels = mixedMoment B raw4751step0 raw4751step0Labels := by
      have hz : ∀ j, raw4751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4751step0 = (fun i j => raw4751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4751step0 raw4751; decide +kernel
      have hl : raw4751step0Labels = raw4751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4751 raw4751Labels permutation346 hz
    mixedMoment B raw4751step0 raw4751step0Labels = mixedMoment B raw4751step1 raw4751step1Labels := by
      have ha : raw4751step1 = (fun i j => raw4751step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4751step1 raw4751step0; decide +kernel
      have hl : raw4751step1Labels = raw4751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4751step0 raw4751step0Labels permutation139 permutation2
    mixedMoment B raw4751step1 raw4751step1Labels = mixedMoment B raw4751step2 raw4751step2Labels := by
      have ha : raw4751step2 = -raw4751step1 := by apply Matrix.ext; change ∀ i j, raw4751step2 i j = -(raw4751step1 i j); unfold raw4751step2 raw4751step1; decide +kernel
      have hl : raw4751step2Labels = raw4751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical4752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4752 raw4752Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4752 raw4752Labels = mixedMoment B raw4752step0 raw4752step0Labels := by
      have hz : ∀ j, raw4752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4752step0 = (fun i j => raw4752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4752step0 raw4752; decide +kernel
      have hl : raw4752step0Labels = raw4752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4752 raw4752Labels permutation346 hz
    mixedMoment B raw4752step0 raw4752step0Labels = mixedMoment B raw4752step1 raw4752step1Labels := by
      have ha : raw4752step1 = (fun i j => raw4752step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4752step1 raw4752step0; decide +kernel
      have hl : raw4752step1Labels = raw4752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4752step0 raw4752step0Labels permutation137 permutation2
    mixedMoment B raw4752step1 raw4752step1Labels = mixedMoment B raw4752step2 raw4752step2Labels := by
      have ha : raw4752step2 = -raw4752step1 := by apply Matrix.ext; change ∀ i j, raw4752step2 i j = -(raw4752step1 i j); unfold raw4752step2 raw4752step1; decide +kernel
      have hl : raw4752step2Labels = raw4752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical4753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4753 raw4753Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw4753 raw4753Labels = mixedMoment B raw4753step0 raw4753step0Labels := by
      have hz : ∀ j, raw4753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4753step0 = (fun i j => raw4753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4753step0 raw4753; decide +kernel
      have hl : raw4753step0Labels = raw4753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4753 raw4753Labels permutation346 hz
    mixedMoment B raw4753step0 raw4753step0Labels = mixedMoment B raw4753step1 raw4753step1Labels := by
      have ha : raw4753step1 = (fun i j => raw4753step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4753step1 raw4753step0; decide +kernel
      have hl : raw4753step1Labels = raw4753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4753step0 raw4753step0Labels permutation40 permutation2
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical4754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4754 raw4754Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw4754 raw4754Labels = mixedMoment B raw4754step0 raw4754step0Labels := by
      have ha : raw4754step0 = (fun i j => raw4754 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4754step0 raw4754; decide +kernel
      have hl : raw4754step0Labels = raw4754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4754 raw4754Labels permutation640 permutation2
    mixedMoment B raw4754step0 raw4754step0Labels = mixedMoment B raw4754step1 raw4754step1Labels := by
      have ha : raw4754step1 = -raw4754step0 := by apply Matrix.ext; change ∀ i j, raw4754step1 i j = -(raw4754step0 i j); unfold raw4754step1 raw4754step0; decide +kernel
      have hl : raw4754step1Labels = raw4754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2009 node2009Labels := by rfl

theorem canonical4755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4755 raw4755Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw4755 raw4755Labels = mixedMoment B raw4755step0 raw4755step0Labels := by
      have hz : ∀ j, raw4755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4755step0 = (fun i j => raw4755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4755step0 raw4755; decide +kernel
      have hl : raw4755step0Labels = raw4755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4755 raw4755Labels permutation346 hz
    mixedMoment B raw4755step0 raw4755step0Labels = mixedMoment B raw4755step1 raw4755step1Labels := by
      have ha : raw4755step1 = (fun i j => raw4755step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4755step1 raw4755step0; decide +kernel
      have hl : raw4755step1Labels = raw4755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4755step0 raw4755step0Labels permutation145 permutation2
    mixedMoment B raw4755step1 raw4755step1Labels = mixedMoment B raw4755step2 raw4755step2Labels := by
      have ha : raw4755step2 = -raw4755step1 := by apply Matrix.ext; change ∀ i j, raw4755step2 i j = -(raw4755step1 i j); unfold raw4755step2 raw4755step1; decide +kernel
      have hl : raw4755step2Labels = raw4755step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical4756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4756 raw4756Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw4756 raw4756Labels = mixedMoment B raw4756step0 raw4756step0Labels := by
      have hz : ∀ j, raw4756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4756step0 = (fun i j => raw4756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4756step0 raw4756; decide +kernel
      have hl : raw4756step0Labels = raw4756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4756 raw4756Labels permutation346 hz
    mixedMoment B raw4756step0 raw4756step0Labels = mixedMoment B raw4756step1 raw4756step1Labels := by
      have ha : raw4756step1 = (fun i j => raw4756step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4756step1 raw4756step0; decide +kernel
      have hl : raw4756step1Labels = raw4756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4756step0 raw4756step0Labels permutation151 permutation2
    mixedMoment B raw4756step1 raw4756step1Labels = mixedMoment B raw4756step2 raw4756step2Labels := by
      have ha : raw4756step2 = -raw4756step1 := by apply Matrix.ext; change ∀ i j, raw4756step2 i j = -(raw4756step1 i j); unfold raw4756step2 raw4756step1; decide +kernel
      have hl : raw4756step2Labels = raw4756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical4757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4757 raw4757Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw4757 raw4757Labels = mixedMoment B raw4757step0 raw4757step0Labels := by
      have hz : ∀ j, raw4757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4757step0 = (fun i j => raw4757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4757step0 raw4757; decide +kernel
      have hl : raw4757step0Labels = raw4757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4757 raw4757Labels permutation346 hz
    mixedMoment B raw4757step0 raw4757step0Labels = mixedMoment B raw4757step1 raw4757step1Labels := by
      have ha : raw4757step1 = (fun i j => raw4757step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4757step1 raw4757step0; decide +kernel
      have hl : raw4757step1Labels = raw4757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4757step0 raw4757step0Labels permutation145 permutation2
    mixedMoment B raw4757step1 raw4757step1Labels = mixedMoment B raw4757step2 raw4757step2Labels := by
      have ha : raw4757step2 = -raw4757step1 := by apply Matrix.ext; change ∀ i j, raw4757step2 i j = -(raw4757step1 i j); unfold raw4757step2 raw4757step1; decide +kernel
      have hl : raw4757step2Labels = raw4757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1022 node1022Labels := by rfl

theorem canonical4758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4758 raw4758Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw4758 raw4758Labels = mixedMoment B raw4758step0 raw4758step0Labels := by
      have hz : ∀ j, raw4758 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4758step0 = (fun i j => raw4758 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4758step0 raw4758; decide +kernel
      have hl : raw4758step0Labels = raw4758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4758 raw4758Labels permutation265 hz
    mixedMoment B raw4758step0 raw4758step0Labels = mixedMoment B raw4758step1 raw4758step1Labels := by
      have ha : raw4758step1 = (fun i j => raw4758step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4758step1 raw4758step0; decide +kernel
      have hl : raw4758step1Labels = raw4758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4758step0 raw4758step0Labels permutation145 permutation2
    mixedMoment B raw4758step1 raw4758step1Labels = mixedMoment B raw4758step2 raw4758step2Labels := by
      have ha : raw4758step2 = -raw4758step1 := by apply Matrix.ext; change ∀ i j, raw4758step2 i j = -(raw4758step1 i j); unfold raw4758step2 raw4758step1; decide +kernel
      have hl : raw4758step2Labels = raw4758step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical4759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4759 raw4759Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4759 raw4759Labels = mixedMoment B raw4759step0 raw4759step0Labels := by
      have hz : ∀ j, raw4759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4759step0 = (fun i j => raw4759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4759step0 raw4759; decide +kernel
      have hl : raw4759step0Labels = raw4759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4759 raw4759Labels permutation346 hz
    mixedMoment B raw4759step0 raw4759step0Labels = mixedMoment B raw4759step1 raw4759step1Labels := by
      have hz : ∀ j, raw4759step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4759step1 = (fun i j => raw4759step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4759step1 raw4759step0; decide +kernel
      have hl : raw4759step1Labels = raw4759step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4759step0 raw4759step0Labels permutation56 hz
    mixedMoment B raw4759step1 raw4759step1Labels = mixedMoment B raw4759step2 raw4759step2Labels := by
      have ha : raw4759step2 = (fun i j => raw4759step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4759step2 raw4759step1; decide +kernel
      have hl : raw4759step2Labels = raw4759step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4759step1 raw4759step1Labels permutation29 permutation2
    mixedMoment B raw4759step2 raw4759step2Labels = mixedMoment B raw4759step3 raw4759step3Labels := by
      have ha : raw4759step3 = -raw4759step2 := by apply Matrix.ext; change ∀ i j, raw4759step3 i j = -(raw4759step2 i j); unfold raw4759step3 raw4759step2; decide +kernel
      have hl : raw4759step3Labels = raw4759step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical4760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4760 raw4760Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw4760 raw4760Labels = mixedMoment B raw4760step0 raw4760step0Labels := by
      have hz : ∀ j, raw4760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4760step0 = (fun i j => raw4760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4760step0 raw4760; decide +kernel
      have hl : raw4760step0Labels = raw4760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4760 raw4760Labels permutation346 hz
    mixedMoment B raw4760step0 raw4760step0Labels = mixedMoment B raw4760step1 raw4760step1Labels := by
      have hz : ∀ j, raw4760step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4760step1 = (fun i j => raw4760step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4760step1 raw4760step0; decide +kernel
      have hl : raw4760step1Labels = raw4760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4760step0 raw4760step0Labels permutation56 hz
    mixedMoment B raw4760step1 raw4760step1Labels = mixedMoment B raw4760step2 raw4760step2Labels := by
      have ha : raw4760step2 = (fun i j => raw4760step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4760step2 raw4760step1; decide +kernel
      have hl : raw4760step2Labels = raw4760step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4760step1 raw4760step1Labels permutation10 permutation2
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical4761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4761 raw4761Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4761 raw4761Labels = mixedMoment B raw4761step0 raw4761step0Labels := by
      have hz : ∀ j, raw4761 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4761step0 = (fun i j => raw4761 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4761step0 raw4761; decide +kernel
      have hl : raw4761step0Labels = raw4761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4761 raw4761Labels permutation265 hz
    mixedMoment B raw4761step0 raw4761step0Labels = mixedMoment B raw4761step1 raw4761step1Labels := by
      have ha : raw4761step1 = (fun i j => raw4761step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4761step1 raw4761step0; decide +kernel
      have hl : raw4761step1Labels = raw4761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4761step0 raw4761step0Labels permutation139 permutation2
    mixedMoment B raw4761step1 raw4761step1Labels = mixedMoment B raw4761step2 raw4761step2Labels := by
      have ha : raw4761step2 = -raw4761step1 := by apply Matrix.ext; change ∀ i j, raw4761step2 i j = -(raw4761step1 i j); unfold raw4761step2 raw4761step1; decide +kernel
      have hl : raw4761step2Labels = raw4761step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical4762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4762 raw4762Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4762 raw4762Labels = mixedMoment B raw4762step0 raw4762step0Labels := by
      have hz : ∀ j, raw4762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4762step0 = (fun i j => raw4762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4762step0 raw4762; decide +kernel
      have hl : raw4762step0Labels = raw4762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4762 raw4762Labels permutation346 hz
    mixedMoment B raw4762step0 raw4762step0Labels = mixedMoment B raw4762step1 raw4762step1Labels := by
      have hz : ∀ j, raw4762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4762step1 = (fun i j => raw4762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4762step1 raw4762step0; decide +kernel
      have hl : raw4762step1Labels = raw4762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4762step0 raw4762step0Labels permutation56 hz
    mixedMoment B raw4762step1 raw4762step1Labels = mixedMoment B raw4762step2 raw4762step2Labels := by
      have ha : raw4762step2 = (fun i j => raw4762step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4762step2 raw4762step1; decide +kernel
      have hl : raw4762step2Labels = raw4762step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4762step1 raw4762step1Labels permutation31 permutation2
    mixedMoment B raw4762step2 raw4762step2Labels = mixedMoment B raw4762step3 raw4762step3Labels := by
      have ha : raw4762step3 = -raw4762step2 := by apply Matrix.ext; change ∀ i j, raw4762step3 i j = -(raw4762step2 i j); unfold raw4762step3 raw4762step2; decide +kernel
      have hl : raw4762step3Labels = raw4762step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical4763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4763 raw4763Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw4763 raw4763Labels = mixedMoment B raw4763step0 raw4763step0Labels := by
      have hz : ∀ j, raw4763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4763step0 = (fun i j => raw4763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4763step0 raw4763; decide +kernel
      have hl : raw4763step0Labels = raw4763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4763 raw4763Labels permutation346 hz
    mixedMoment B raw4763step0 raw4763step0Labels = mixedMoment B raw4763step1 raw4763step1Labels := by
      have hz : ∀ j, raw4763step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4763step1 = (fun i j => raw4763step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4763step1 raw4763step0; decide +kernel
      have hl : raw4763step1Labels = raw4763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4763step0 raw4763step0Labels permutation56 hz
    mixedMoment B raw4763step1 raw4763step1Labels = mixedMoment B raw4763step2 raw4763step2Labels := by
      have ha : raw4763step2 = (fun i j => raw4763step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4763step2 raw4763step1; decide +kernel
      have hl : raw4763step2Labels = raw4763step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4763step1 raw4763step1Labels permutation31 permutation2
    mixedMoment B raw4763step2 raw4763step2Labels = mixedMoment B raw4763step3 raw4763step3Labels := by
      have ha : raw4763step3 = -raw4763step2 := by apply Matrix.ext; change ∀ i j, raw4763step3 i j = -(raw4763step2 i j); unfold raw4763step3 raw4763step2; decide +kernel
      have hl : raw4763step3Labels = raw4763step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical4764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4764 raw4764Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw4764 raw4764Labels = mixedMoment B raw4764step0 raw4764step0Labels := by
      have hz : ∀ j, raw4764 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4764step0 = (fun i j => raw4764 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4764step0 raw4764; decide +kernel
      have hl : raw4764step0Labels = raw4764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4764 raw4764Labels permutation265 hz
    mixedMoment B raw4764step0 raw4764step0Labels = mixedMoment B raw4764step1 raw4764step1Labels := by
      have ha : raw4764step1 = (fun i j => raw4764step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4764step1 raw4764step0; decide +kernel
      have hl : raw4764step1Labels = raw4764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4764step0 raw4764step0Labels permutation145 permutation2
    mixedMoment B raw4764step1 raw4764step1Labels = mixedMoment B raw4764step2 raw4764step2Labels := by
      have ha : raw4764step2 = -raw4764step1 := by apply Matrix.ext; change ∀ i j, raw4764step2 i j = -(raw4764step1 i j); unfold raw4764step2 raw4764step1; decide +kernel
      have hl : raw4764step2Labels = raw4764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1022 node1022Labels := by rfl

theorem canonical4765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4765 raw4765Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw4765 raw4765Labels = mixedMoment B raw4765step0 raw4765step0Labels := by
      have hz : ∀ j, raw4765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4765step0 = (fun i j => raw4765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4765step0 raw4765; decide +kernel
      have hl : raw4765step0Labels = raw4765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4765 raw4765Labels permutation346 hz
    mixedMoment B raw4765step0 raw4765step0Labels = mixedMoment B raw4765step1 raw4765step1Labels := by
      have hz : ∀ j, raw4765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4765step1 = (fun i j => raw4765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4765step1 raw4765step0; decide +kernel
      have hl : raw4765step1Labels = raw4765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4765step0 raw4765step0Labels permutation56 hz
    mixedMoment B raw4765step1 raw4765step1Labels = mixedMoment B raw4765step2 raw4765step2Labels := by
      have ha : raw4765step2 = (fun i j => raw4765step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4765step2 raw4765step1; decide +kernel
      have hl : raw4765step2Labels = raw4765step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4765step1 raw4765step1Labels permutation29 permutation2
    mixedMoment B raw4765step2 raw4765step2Labels = mixedMoment B raw4765step3 raw4765step3Labels := by
      have ha : raw4765step3 = -raw4765step2 := by apply Matrix.ext; change ∀ i j, raw4765step3 i j = -(raw4765step2 i j); unfold raw4765step3 raw4765step2; decide +kernel
      have hl : raw4765step3Labels = raw4765step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
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

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

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

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

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

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

theorem canonical7738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7738 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7738 = injectiveMoment H raw7738step0 := by
      have heq : raw7738step0 = (fun i j => raw7738 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7738 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

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

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

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

theorem canonical808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw808 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw808 = injectiveMoment H raw808step0 := by
      have heq : raw808step0 = -raw808 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw808).symm
    injectiveMoment H raw808step0 = injectiveMoment H raw808step1 := by
      have heq : raw808step1 = (fun i j => raw808step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw808step0 permutation9 permutation8
    _ = injectiveMoment H node176 := by rfl

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

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

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

theorem sound26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node26 = Sparse.eval value26 (momentVector H) := by
  have heq : pivotMatrix26 = (fun u v => node26 (pivotPermutation26 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node26 = injectiveMoment H pivotMatrix26 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix26 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix26 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (1 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node26 + (injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value26, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

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

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node416 node416Labels = Sparse.eval singlePairValue416 (familyPairVector B) := by
  have hp := single_label_three B hB node416
  have hl : node416Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node416 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node416 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node416 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 3) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node416 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value176 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 4) = PairSemantics.raw808 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node416 PairSemantics.raw808; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical808 hH).trans (PairSemantics.sound176 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue416, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value65, PairSemantics.value176, Sparse.eval] at hp ⊢
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

theorem singleton2784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2784 node2784Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node416 node416Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw282 singletonSmall2784
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2784) = raw282Labels := by decide +kernel
  rw [hl, canonical282 B hB] at h
  have hc0 : mixedMoment B raw282 (Fin.cases (0 : Fin 1) singletonSmall2784) =
      mixedMoment B node416 node416Labels := by
    have ha : raw282 = raw283 := by apply Matrix.ext; unfold raw282 raw283; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2784 = raw283Labels := by decide +kernel
    rw [ha, hj, canonical283 B hB]
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

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

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

theorem sound1022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1022 node1022Labels = Sparse.eval nodeValue1022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1022) = mixedMoment B node1022 node1022Labels := rfl
  simpa [nodeValue1022, Sparse.eval] using hc.symm

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

theorem sound1027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1027 node1027Labels = Sparse.eval nodeValue1027 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1027) = mixedMoment B node1027 node1027Labels := rfl
  simpa [nodeValue1027, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

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

theorem sound1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1094 node1094Labels = Sparse.eval nodeValue1094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1094) = mixedMoment B node1094 node1094Labels := rfl
  simpa [nodeValue1094, Sparse.eval] using hc.symm

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

theorem sound1385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1385 node1385Labels = Sparse.eval nodeValue1385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1385) = mixedMoment B node1385 node1385Labels := rfl
  simpa [nodeValue1385, Sparse.eval] using hc.symm

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

theorem sound1408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1408 node1408Labels = Sparse.eval nodeValue1408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1408) = mixedMoment B node1408 node1408Labels := rfl
  simpa [nodeValue1408, Sparse.eval] using hc.symm

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

theorem sound1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1723 node1723Labels = Sparse.eval nodeValue1723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1723) = mixedMoment B node1723 node1723Labels := rfl
  simpa [nodeValue1723, Sparse.eval] using hc.symm

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

theorem sound1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1744 node1744Labels = Sparse.eval nodeValue1744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1744) = mixedMoment B node1744 node1744Labels := rfl
  simpa [nodeValue1744, Sparse.eval] using hc.symm

theorem sound1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1745 node1745Labels = Sparse.eval nodeValue1745 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1745) = mixedMoment B node1745 node1745Labels := rfl
  simpa [nodeValue1745, Sparse.eval] using hc.symm

theorem sound1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1749 node1749Labels = Sparse.eval nodeValue1749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1749) = mixedMoment B node1749 node1749Labels := rfl
  simpa [nodeValue1749, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

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

theorem sound2009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2009 node2009Labels = Sparse.eval nodeValue2009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2009) = mixedMoment B node2009 node2009Labels := rfl
  simpa [nodeValue2009, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

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

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

theorem sound2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2090 node2090Labels = Sparse.eval nodeValue2090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2090) = mixedMoment B node2090 node2090Labels := rfl
  simpa [nodeValue2090, Sparse.eval] using hc.symm

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

theorem sound2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2201 node2201Labels = Sparse.eval nodeValue2201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2201) = mixedMoment B node2201 node2201Labels := rfl
  simpa [nodeValue2201, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

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

theorem zero2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = 0 := by
  exact mixedMoment_order_one B hB node2265 node2265Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
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

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = Sparse.eval nodeValue2265 (mixedVector B) := by
  simpa only [nodeValue2265, Sparse.eval_nil] using zero2265 B _hB _hF

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

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

theorem sound2738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2738 node2738Labels = Sparse.eval nodeValue2738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2738) = mixedMoment B node2738 node2738Labels := rfl
  simpa [nodeValue2738, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node416 node416Labels = Sparse.eval nodeValue416 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue416 (familyPairVector B) := singlePair416 B _hB
    _ = _ := by
      norm_num [singlePairValue416, nodeValue416, Sparse.eval, mixedVector]
      ring

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

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

theorem sound2784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2784 node2784Labels = Sparse.eval nodeValue2784 (mixedVector B) := by
  have h := singleton2784 B _hB
  rw [sound416 B _hB _hF] at h
  norm_num [nodeValue2784, nodeValue416, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3075 node3075Labels = Sparse.eval nodeValue3075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3075) = mixedMoment B node3075 node3075Labels := rfl
  simpa [nodeValue3075, Sparse.eval] using hc.symm

theorem sound3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3098 node3098Labels = Sparse.eval nodeValue3098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3098) = mixedMoment B node3098 node3098Labels := rfl
  simpa [nodeValue3098, Sparse.eval] using hc.symm

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

theorem sound3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3623 node3623Labels = Sparse.eval nodeValue3623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3623) = mixedMoment B node3623 node3623Labels := rfl
  simpa [nodeValue3623, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources4
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm132 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA132 + difference 0 0) (sourceB132 + difference 0 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA132 + difference 0 0) (sourceB132 + difference 0 0) sourceC132) = raw3718 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw3718; decide +kernel
    rw [ha]
    exact (canonical3718 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA132 + difference 0 1) (sourceB132 + difference 1 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA132 + difference 0 1) (sourceB132 + difference 1 0) sourceC132) = raw4090 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4090; decide +kernel
    rw [ha]
    exact (canonical4090 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA132 + difference 0 2) (sourceB132 + difference 2 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA132 + difference 0 2) (sourceB132 + difference 2 0) sourceC132) = raw4601 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4601; decide +kernel
    rw [ha]
    exact (canonical4601 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA132 + difference 0 3) (sourceB132 + difference 3 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA132 + difference 0 3) (sourceB132 + difference 3 0) sourceC132) = raw4602 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4602; decide +kernel
    rw [ha]
    exact (canonical4602 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA132 + difference 0 4) (sourceB132 + difference 4 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA132 + difference 0 4) (sourceB132 + difference 4 0) sourceC132) = raw4375 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4375; decide +kernel
    rw [ha]
    exact (canonical4375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA132 + difference 0 5) (sourceB132 + difference 5 0) sourceC132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA132 + difference 0 5) (sourceB132 + difference 5 0) sourceC132) = raw4603 := by
      apply Matrix.ext; unfold tripleCharges sourceA132 sourceB132 sourceC132 difference raw4603; decide +kernel
    rw [ha]
    exact (canonical4603 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA132 + sourceB132) sourceC132) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA132 + sourceB132) sourceC132) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA132 sourceB132 sourceC132 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA132 sourceB132 sourceC132
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm132, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm137 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA137 + difference 0 1) (sourceB137 + difference 1 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA137 + difference 0 1) (sourceB137 + difference 1 0) sourceC137) = raw4708 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4708; decide +kernel
    rw [ha]
    exact (canonical4708 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA137 + difference 0 2) (sourceB137 + difference 2 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA137 + difference 0 2) (sourceB137 + difference 2 0) sourceC137) = raw4709 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4709; decide +kernel
    rw [ha]
    exact (canonical4709 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA137 + difference 0 3) (sourceB137 + difference 3 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA137 + difference 0 3) (sourceB137 + difference 3 0) sourceC137) = raw4710 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4710; decide +kernel
    rw [ha]
    exact (canonical4710 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA137 + difference 0 4) (sourceB137 + difference 4 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA137 + difference 0 4) (sourceB137 + difference 4 0) sourceC137) = raw4711 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4711; decide +kernel
    rw [ha]
    exact (canonical4711 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA137 + difference 0 5) (sourceB137 + difference 5 0) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA137 + difference 0 5) (sourceB137 + difference 5 0) sourceC137) = raw4712 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4712; decide +kernel
    rw [ha]
    exact (canonical4712 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA137 + difference 1 0) (sourceB137 + difference 0 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA137 + difference 1 0) (sourceB137 + difference 0 1) sourceC137) = raw4713 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4713; decide +kernel
    rw [ha]
    exact (canonical4713 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA137 + difference 1 2) (sourceB137 + difference 2 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA137 + difference 1 2) (sourceB137 + difference 2 1) sourceC137) = raw4714 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4714; decide +kernel
    rw [ha]
    exact (canonical4714 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA137 + difference 1 3) (sourceB137 + difference 3 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA137 + difference 1 3) (sourceB137 + difference 3 1) sourceC137) = raw4715 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4715; decide +kernel
    rw [ha]
    exact (canonical4715 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA137 + difference 1 4) (sourceB137 + difference 4 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA137 + difference 1 4) (sourceB137 + difference 4 1) sourceC137) = raw4716 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4716; decide +kernel
    rw [ha]
    exact (canonical4716 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA137 + difference 1 5) (sourceB137 + difference 5 1) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA137 + difference 1 5) (sourceB137 + difference 5 1) sourceC137) = raw4717 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4717; decide +kernel
    rw [ha]
    exact (canonical4717 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA137 + difference 2 0) (sourceB137 + difference 0 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA137 + difference 2 0) (sourceB137 + difference 0 2) sourceC137) = raw4718 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4718; decide +kernel
    rw [ha]
    exact (canonical4718 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA137 + difference 2 1) (sourceB137 + difference 1 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA137 + difference 2 1) (sourceB137 + difference 1 2) sourceC137) = raw4719 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4719; decide +kernel
    rw [ha]
    exact (canonical4719 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA137 + difference 2 3) (sourceB137 + difference 3 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA137 + difference 2 3) (sourceB137 + difference 3 2) sourceC137) = raw4720 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4720; decide +kernel
    rw [ha]
    exact (canonical4720 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA137 + difference 2 4) (sourceB137 + difference 4 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA137 + difference 2 4) (sourceB137 + difference 4 2) sourceC137) = raw4721 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4721; decide +kernel
    rw [ha]
    exact (canonical4721 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA137 + difference 2 5) (sourceB137 + difference 5 2) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA137 + difference 2 5) (sourceB137 + difference 5 2) sourceC137) = raw4722 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4722; decide +kernel
    rw [ha]
    exact (canonical4722 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA137 + difference 3 0) (sourceB137 + difference 0 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA137 + difference 3 0) (sourceB137 + difference 0 3) sourceC137) = raw4723 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4723; decide +kernel
    rw [ha]
    exact (canonical4723 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA137 + difference 3 1) (sourceB137 + difference 1 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA137 + difference 3 1) (sourceB137 + difference 1 3) sourceC137) = raw4724 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4724; decide +kernel
    rw [ha]
    exact (canonical4724 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA137 + difference 3 2) (sourceB137 + difference 2 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA137 + difference 3 2) (sourceB137 + difference 2 3) sourceC137) = raw4725 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4725; decide +kernel
    rw [ha]
    exact (canonical4725 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA137 + difference 3 4) (sourceB137 + difference 4 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA137 + difference 3 4) (sourceB137 + difference 4 3) sourceC137) = raw4726 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4726; decide +kernel
    rw [ha]
    exact (canonical4726 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA137 + difference 3 5) (sourceB137 + difference 5 3) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA137 + difference 3 5) (sourceB137 + difference 5 3) sourceC137) = raw4727 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4727; decide +kernel
    rw [ha]
    exact (canonical4727 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA137 + difference 4 0) (sourceB137 + difference 0 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA137 + difference 4 0) (sourceB137 + difference 0 4) sourceC137) = raw4728 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4728; decide +kernel
    rw [ha]
    exact (canonical4728 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA137 + difference 4 1) (sourceB137 + difference 1 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA137 + difference 4 1) (sourceB137 + difference 1 4) sourceC137) = raw4729 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4729; decide +kernel
    rw [ha]
    exact (canonical4729 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA137 + difference 4 2) (sourceB137 + difference 2 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA137 + difference 4 2) (sourceB137 + difference 2 4) sourceC137) = raw4730 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4730; decide +kernel
    rw [ha]
    exact (canonical4730 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA137 + difference 4 3) (sourceB137 + difference 3 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA137 + difference 4 3) (sourceB137 + difference 3 4) sourceC137) = raw4731 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4731; decide +kernel
    rw [ha]
    exact (canonical4731 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA137 + difference 4 5) (sourceB137 + difference 5 4) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA137 + difference 4 5) (sourceB137 + difference 5 4) sourceC137) = raw4732 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4732; decide +kernel
    rw [ha]
    exact (canonical4732 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA137 + difference 5 0) (sourceB137 + difference 0 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1749) := by
    have ha : (tripleCharges (sourceA137 + difference 5 0) (sourceB137 + difference 0 5) sourceC137) = raw4733 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4733; decide +kernel
    rw [ha]
    exact (canonical4733 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA137 + difference 5 1) (sourceB137 + difference 1 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA137 + difference 5 1) (sourceB137 + difference 1 5) sourceC137) = raw4734 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4734; decide +kernel
    rw [ha]
    exact (canonical4734 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA137 + difference 5 2) (sourceB137 + difference 2 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA137 + difference 5 2) (sourceB137 + difference 2 5) sourceC137) = raw4735 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4735; decide +kernel
    rw [ha]
    exact (canonical4735 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA137 + difference 5 3) (sourceB137 + difference 3 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA137 + difference 5 3) (sourceB137 + difference 3 5) sourceC137) = raw4736 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4736; decide +kernel
    rw [ha]
    exact (canonical4736 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA137 + difference 5 4) (sourceB137 + difference 4 5) sourceC137) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA137 + difference 5 4) (sourceB137 + difference 4 5) sourceC137) = raw4737 := by
      apply Matrix.ext; unfold tripleCharges sourceA137 sourceB137 sourceC137 difference raw4737; decide +kernel
    rw [ha]
    exact (canonical4737 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA137 sourceB137 sourceC137
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm137, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm138 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA138 + difference 0 0) (sourceB138 + difference 0 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA138 + difference 0 0) (sourceB138 + difference 0 0) sourceC138) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA138 + difference 0 1) (sourceB138 + difference 1 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA138 + difference 0 1) (sourceB138 + difference 1 0) sourceC138) = raw4739 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4739; decide +kernel
    rw [ha]
    exact (canonical4739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA138 + difference 0 2) (sourceB138 + difference 2 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA138 + difference 0 2) (sourceB138 + difference 2 0) sourceC138) = raw4740 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4740; decide +kernel
    rw [ha]
    exact (canonical4740 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA138 + difference 0 3) (sourceB138 + difference 3 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA138 + difference 0 3) (sourceB138 + difference 3 0) sourceC138) = raw4741 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4741; decide +kernel
    rw [ha]
    exact (canonical4741 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA138 + difference 0 4) (sourceB138 + difference 4 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA138 + difference 0 4) (sourceB138 + difference 4 0) sourceC138) = raw4742 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4742; decide +kernel
    rw [ha]
    exact (canonical4742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA138 + difference 0 5) (sourceB138 + difference 5 0) sourceC138) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA138 + difference 0 5) (sourceB138 + difference 5 0) sourceC138) = raw4743 := by
      apply Matrix.ext; unfold tripleCharges sourceA138 sourceB138 sourceC138 difference raw4743; decide +kernel
    rw [ha]
    exact (canonical4743 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA138 + sourceB138) sourceC138) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA138 + sourceB138) sourceC138) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA138 sourceB138 sourceC138 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA138 sourceB138 sourceC138
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm138, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm139 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA139 + difference 0 0) (sourceB139 + difference 0 0) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA139 + difference 0 0) (sourceB139 + difference 0 0) sourceC139) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA139 + difference 1 0) (sourceB139 + difference 0 1) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA139 + difference 1 0) (sourceB139 + difference 0 1) sourceC139) = raw4745 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4745; decide +kernel
    rw [ha]
    exact (canonical4745 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA139 + difference 2 0) (sourceB139 + difference 0 2) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA139 + difference 2 0) (sourceB139 + difference 0 2) sourceC139) = raw4746 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4746; decide +kernel
    rw [ha]
    exact (canonical4746 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA139 + difference 3 0) (sourceB139 + difference 0 3) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA139 + difference 3 0) (sourceB139 + difference 0 3) sourceC139) = raw4747 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4747; decide +kernel
    rw [ha]
    exact (canonical4747 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA139 + difference 4 0) (sourceB139 + difference 0 4) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA139 + difference 4 0) (sourceB139 + difference 0 4) sourceC139) = raw4748 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4748; decide +kernel
    rw [ha]
    exact (canonical4748 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA139 + difference 5 0) (sourceB139 + difference 0 5) sourceC139) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA139 + difference 5 0) (sourceB139 + difference 0 5) sourceC139) = raw4749 := by
      apply Matrix.ext; unfold tripleCharges sourceA139 sourceB139 sourceC139 difference raw4749; decide +kernel
    rw [ha]
    exact (canonical4749 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA139 + sourceB139) sourceC139) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA139 + sourceB139) sourceC139) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA139 sourceB139 sourceC139 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA139 sourceB139 sourceC139
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm139, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm140 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA140 + difference 1 0) (sourceB140 + difference 0 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA140 + difference 1 0) (sourceB140 + difference 0 1) sourceC140) = raw4745 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4745; decide +kernel
    rw [ha]
    exact (canonical4745 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA140 + difference 1 1) (sourceB140 + difference 1 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA140 + difference 1 1) (sourceB140 + difference 1 1) sourceC140) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA140 + difference 1 2) (sourceB140 + difference 2 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA140 + difference 1 2) (sourceB140 + difference 2 1) sourceC140) = raw4750 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4750; decide +kernel
    rw [ha]
    exact (canonical4750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA140 + difference 1 3) (sourceB140 + difference 3 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA140 + difference 1 3) (sourceB140 + difference 3 1) sourceC140) = raw4751 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4751; decide +kernel
    rw [ha]
    exact (canonical4751 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA140 + difference 1 4) (sourceB140 + difference 4 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA140 + difference 1 4) (sourceB140 + difference 4 1) sourceC140) = raw4752 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4752; decide +kernel
    rw [ha]
    exact (canonical4752 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA140 + difference 1 5) (sourceB140 + difference 5 1) sourceC140) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA140 + difference 1 5) (sourceB140 + difference 5 1) sourceC140) = raw4753 := by
      apply Matrix.ext; unfold tripleCharges sourceA140 sourceB140 sourceC140 difference raw4753; decide +kernel
    rw [ha]
    exact (canonical4753 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA140 + sourceB140) sourceC140) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA140 + sourceB140) sourceC140) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA140 sourceB140 sourceC140 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA140 sourceB140 sourceC140
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm140, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm141 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA141 + difference 0 1) (sourceB141 + difference 1 0) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA141 + difference 0 1) (sourceB141 + difference 1 0) sourceC141) = raw4739 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4739; decide +kernel
    rw [ha]
    exact (canonical4739 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA141 + difference 1 1) (sourceB141 + difference 1 1) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA141 + difference 1 1) (sourceB141 + difference 1 1) sourceC141) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA141 + difference 2 1) (sourceB141 + difference 1 2) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA141 + difference 2 1) (sourceB141 + difference 1 2) sourceC141) = raw4754 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4754; decide +kernel
    rw [ha]
    exact (canonical4754 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA141 + difference 3 1) (sourceB141 + difference 1 3) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA141 + difference 3 1) (sourceB141 + difference 1 3) sourceC141) = raw4755 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4755; decide +kernel
    rw [ha]
    exact (canonical4755 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA141 + difference 4 1) (sourceB141 + difference 1 4) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA141 + difference 4 1) (sourceB141 + difference 1 4) sourceC141) = raw4756 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4756; decide +kernel
    rw [ha]
    exact (canonical4756 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA141 + difference 5 1) (sourceB141 + difference 1 5) sourceC141) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA141 + difference 5 1) (sourceB141 + difference 1 5) sourceC141) = raw4757 := by
      apply Matrix.ext; unfold tripleCharges sourceA141 sourceB141 sourceC141 difference raw4757; decide +kernel
    rw [ha]
    exact (canonical4757 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA141 + sourceB141) sourceC141) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA141 + sourceB141) sourceC141) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA141 sourceB141 sourceC141 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA141 sourceB141 sourceC141
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm141, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm142 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA142 + difference 3 0) (sourceB142 + difference 0 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA142 + difference 3 0) (sourceB142 + difference 0 3) sourceC142) = raw4747 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4747; decide +kernel
    rw [ha]
    exact (canonical4747 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA142 + difference 3 1) (sourceB142 + difference 1 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA142 + difference 3 1) (sourceB142 + difference 1 3) sourceC142) = raw4755 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4755; decide +kernel
    rw [ha]
    exact (canonical4755 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA142 + difference 3 2) (sourceB142 + difference 2 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA142 + difference 3 2) (sourceB142 + difference 2 3) sourceC142) = raw4758 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4758; decide +kernel
    rw [ha]
    exact (canonical4758 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA142 + difference 3 3) (sourceB142 + difference 3 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA142 + difference 3 3) (sourceB142 + difference 3 3) sourceC142) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA142 + difference 3 4) (sourceB142 + difference 4 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA142 + difference 3 4) (sourceB142 + difference 4 3) sourceC142) = raw4759 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4759; decide +kernel
    rw [ha]
    exact (canonical4759 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA142 + difference 3 5) (sourceB142 + difference 5 3) sourceC142) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA142 + difference 3 5) (sourceB142 + difference 5 3) sourceC142) = raw4760 := by
      apply Matrix.ext; unfold tripleCharges sourceA142 sourceB142 sourceC142 difference raw4760; decide +kernel
    rw [ha]
    exact (canonical4760 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA142 + sourceB142) sourceC142) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA142 + sourceB142) sourceC142) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA142 sourceB142 sourceC142 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA142 sourceB142 sourceC142
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm142, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm143 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA143 + difference 0 3) (sourceB143 + difference 3 0) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA143 + difference 0 3) (sourceB143 + difference 3 0) sourceC143) = raw4741 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4741; decide +kernel
    rw [ha]
    exact (canonical4741 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA143 + difference 1 3) (sourceB143 + difference 3 1) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA143 + difference 1 3) (sourceB143 + difference 3 1) sourceC143) = raw4751 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4751; decide +kernel
    rw [ha]
    exact (canonical4751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA143 + difference 2 3) (sourceB143 + difference 3 2) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA143 + difference 2 3) (sourceB143 + difference 3 2) sourceC143) = raw4761 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4761; decide +kernel
    rw [ha]
    exact (canonical4761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA143 + difference 3 3) (sourceB143 + difference 3 3) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA143 + difference 3 3) (sourceB143 + difference 3 3) sourceC143) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA143 + difference 4 3) (sourceB143 + difference 3 4) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA143 + difference 4 3) (sourceB143 + difference 3 4) sourceC143) = raw4762 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4762; decide +kernel
    rw [ha]
    exact (canonical4762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA143 + difference 5 3) (sourceB143 + difference 3 5) sourceC143) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA143 + difference 5 3) (sourceB143 + difference 3 5) sourceC143) = raw4763 := by
      apply Matrix.ext; unfold tripleCharges sourceA143 sourceB143 sourceC143 difference raw4763; decide +kernel
    rw [ha]
    exact (canonical4763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA143 + sourceB143) sourceC143) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA143 + sourceB143) sourceC143) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA143 sourceB143 sourceC143 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA143 sourceB143 sourceC143
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm143, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm144 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA144 + difference 5 0) (sourceB144 + difference 0 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA144 + difference 5 0) (sourceB144 + difference 0 5) sourceC144) = raw4749 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4749; decide +kernel
    rw [ha]
    exact (canonical4749 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA144 + difference 5 1) (sourceB144 + difference 1 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA144 + difference 5 1) (sourceB144 + difference 1 5) sourceC144) = raw4757 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4757; decide +kernel
    rw [ha]
    exact (canonical4757 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA144 + difference 5 2) (sourceB144 + difference 2 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA144 + difference 5 2) (sourceB144 + difference 2 5) sourceC144) = raw4764 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4764; decide +kernel
    rw [ha]
    exact (canonical4764 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA144 + difference 5 3) (sourceB144 + difference 3 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA144 + difference 5 3) (sourceB144 + difference 3 5) sourceC144) = raw4763 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4763; decide +kernel
    rw [ha]
    exact (canonical4763 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA144 + difference 5 4) (sourceB144 + difference 4 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA144 + difference 5 4) (sourceB144 + difference 4 5) sourceC144) = raw4765 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4765; decide +kernel
    rw [ha]
    exact (canonical4765 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA144 + difference 5 5) (sourceB144 + difference 5 5) sourceC144) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA144 + difference 5 5) (sourceB144 + difference 5 5) sourceC144) = raw4738 := by
      apply Matrix.ext; unfold tripleCharges sourceA144 sourceB144 sourceC144 difference raw4738; decide +kernel
    rw [ha]
    exact (canonical4738 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA144 + sourceB144) sourceC144) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA144 + sourceB144) sourceC144) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA144 sourceB144 sourceC144 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA144 sourceB144 sourceC144
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm144, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck112 : Integer.Sparse.reindex keyMap MixedData.row112 = numericRow112 := by decide +kernel

theorem numericCheck112 (x : Master → ℝ) : Integer.Sparse.eval numericRow112 x =
    (1 : ℝ) * reducedSource112 x := by
  norm_num [numericRow112, reducedSource112, Integer.Sparse.eval, Sparse.eval, nodeValue1094, nodeValue2065, nodeValue2292, nodeValue2294, nodeValue4085]

theorem reindexCheck117 : Integer.Sparse.reindex keyMap MixedData.row117 = numericRow117 := by decide +kernel

theorem numericCheck117 (x : Master → ℝ) : Integer.Sparse.eval numericRow117 x =
    (2160 : ℝ) * reducedSource117 x := by
  norm_num [numericRow117, reducedSource117, Integer.Sparse.eval, Sparse.eval, nodeValue1723, nodeValue1744, nodeValue1745, nodeValue1749, nodeValue1750, nodeValue2201, nodeValue2224, nodeValue2259, nodeValue2262, nodeValue2287, nodeValue2291, nodeValue2738, nodeValue2781, nodeValue2784] <;> ring

theorem reindexCheck118 : Integer.Sparse.reindex keyMap MixedData.row118 = numericRow118 := by decide +kernel

theorem numericCheck118 (x : Master → ℝ) : Integer.Sparse.eval numericRow118 x =
    (1 : ℝ) * reducedSource118 x := by
  norm_num [numericRow118, reducedSource118, Integer.Sparse.eval, Sparse.eval, nodeValue2244, nodeValue2247, nodeValue2265, nodeValue3623, nodeValue4083]

theorem reindexCheck119 : Integer.Sparse.reindex keyMap MixedData.row119 = numericRow119 := by decide +kernel

theorem numericCheck119 (x : Master → ℝ) : Integer.Sparse.eval numericRow119 x =
    (1 : ℝ) * reducedSource119 x := by
  norm_num [numericRow119, reducedSource119, Integer.Sparse.eval, Sparse.eval, nodeValue1027, nodeValue1385, nodeValue1408, nodeValue2247, nodeValue4083]

theorem reindexCheck120 : Integer.Sparse.reindex keyMap MixedData.row120 = numericRow120 := by decide +kernel

theorem numericCheck120 (x : Master → ℝ) : Integer.Sparse.eval numericRow120 x =
    (1 : ℝ) * reducedSource120 x := by
  norm_num [numericRow120, reducedSource120, Integer.Sparse.eval, Sparse.eval, nodeValue1385, nodeValue2009, nodeValue2025, nodeValue2247, nodeValue3075, nodeValue4083]

theorem reindexCheck121 : Integer.Sparse.reindex keyMap MixedData.row121 = numericRow121 := by decide +kernel

theorem numericCheck121 (x : Master → ℝ) : Integer.Sparse.eval numericRow121 x =
    (1 : ℝ) * reducedSource121 x := by
  norm_num [numericRow121, reducedSource121, Integer.Sparse.eval, Sparse.eval, nodeValue1022, nodeValue2009, nodeValue2090, nodeValue2244, nodeValue2247, nodeValue4083]

theorem reindexCheck122 : Integer.Sparse.reindex keyMap MixedData.row122 = numericRow122 := by decide +kernel

theorem numericCheck122 (x : Master → ℝ) : Integer.Sparse.eval numericRow122 x =
    (1 : ℝ) * reducedSource122 x := by
  norm_num [numericRow122, reducedSource122, Integer.Sparse.eval, Sparse.eval, nodeValue1408, nodeValue2090, nodeValue2112, nodeValue2247, nodeValue3098, nodeValue4083]

theorem reindexCheck123 : Integer.Sparse.reindex keyMap MixedData.row123 = numericRow123 := by decide +kernel

theorem numericCheck123 (x : Master → ℝ) : Integer.Sparse.eval numericRow123 x =
    (1 : ℝ) * reducedSource123 x := by
  norm_num [numericRow123, reducedSource123, Integer.Sparse.eval, Sparse.eval, nodeValue1046, nodeValue2025, nodeValue2112, nodeValue2247, nodeValue2265, nodeValue4083]

theorem reindexCheck124 : Integer.Sparse.reindex keyMap MixedData.row124 = numericRow124 := by decide +kernel

theorem numericCheck124 (x : Master → ℝ) : Integer.Sparse.eval numericRow124 x =
    (1 : ℝ) * reducedSource124 x := by
  norm_num [numericRow124, reducedSource124, Integer.Sparse.eval, Sparse.eval, nodeValue1022, nodeValue1027, nodeValue1046, nodeValue2247, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource112 (mixedVector B) = 0 := by
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm132, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1094, h2065, h2292, h2294, h4085, reducedSource112] using sourceEq132 B hB

theorem rowSound112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row112 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck112, numericCheck112, reducedZero112 B hB hF, mul_zero]

theorem reducedZero117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource117 (mixedVector B) = 0 := by
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1749 : mixedVector B (Sum.inr 1749) = Sparse.eval nodeValue1749 (mixedVector B) := by
    change mixedMoment B node1749 node1749Labels = _
    exact sound1749 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2738 : mixedVector B (Sum.inr 2738) = Sparse.eval nodeValue2738 (mixedVector B) := by
    change mixedMoment B node2738 node2738Labels = _
    exact sound2738 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2784 : mixedVector B (Sum.inr 2784) = Sparse.eval nodeValue2784 (mixedVector B) := by
    change mixedMoment B node2784 node2784Labels = _
    exact sound2784 B hB hF
  simpa only [sourceForm137, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1723, h1744, h1745, h1749, h1750, h2201, h2224, h2259, h2262, h2287, h2291, h2738, h2781, h2784, reducedSource117] using sourceEq137 B hB

theorem rowSound117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row117 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck117, numericCheck117, reducedZero117 B hB hF, mul_zero]

theorem reducedZero118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource118 (mixedVector B) = 0 := by
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h3623 : mixedVector B (Sum.inr 3623) = Sparse.eval nodeValue3623 (mixedVector B) := by
    change mixedMoment B node3623 node3623Labels = _
    exact sound3623 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm138, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2244, h2247, h2265, h3623, h4083, reducedSource118] using sourceEq138 B hB

theorem rowSound118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row118 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck118, numericCheck118, reducedZero118 B hB hF, mul_zero]

theorem reducedZero119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource119 (mixedVector B) = 0 := by
  have h1027 : mixedVector B (Sum.inr 1027) = Sparse.eval nodeValue1027 (mixedVector B) := by
    change mixedMoment B node1027 node1027Labels = _
    exact sound1027 B hB hF
  have h1385 : mixedVector B (Sum.inr 1385) = Sparse.eval nodeValue1385 (mixedVector B) := by
    change mixedMoment B node1385 node1385Labels = _
    exact sound1385 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm139, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1027, h1385, h1408, h2247, h4083, reducedSource119] using sourceEq139 B hB

theorem rowSound119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row119 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck119, numericCheck119, reducedZero119 B hB hF, mul_zero]

theorem reducedZero120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource120 (mixedVector B) = 0 := by
  have h1385 : mixedVector B (Sum.inr 1385) = Sparse.eval nodeValue1385 (mixedVector B) := by
    change mixedMoment B node1385 node1385Labels = _
    exact sound1385 B hB hF
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h3075 : mixedVector B (Sum.inr 3075) = Sparse.eval nodeValue3075 (mixedVector B) := by
    change mixedMoment B node3075 node3075Labels = _
    exact sound3075 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm140, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1385, h2009, h2025, h2247, h3075, h4083, reducedSource120] using sourceEq140 B hB

theorem rowSound120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row120 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck120, numericCheck120, reducedZero120 B hB hF, mul_zero]

theorem reducedZero121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource121 (mixedVector B) = 0 := by
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm141, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1022, h2009, h2090, h2244, h2247, h4083, reducedSource121] using sourceEq141 B hB

theorem rowSound121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row121 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck121, numericCheck121, reducedZero121 B hB hF, mul_zero]

theorem reducedZero122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource122 (mixedVector B) = 0 := by
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm142, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1408, h2090, h2112, h2247, h3098, h4083, reducedSource122] using sourceEq142 B hB

theorem rowSound122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row122 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck122, numericCheck122, reducedZero122 B hB hF, mul_zero]

theorem reducedZero123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource123 (mixedVector B) = 0 := by
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm143, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1046, h2025, h2112, h2247, h2265, h4083, reducedSource123] using sourceEq143 B hB

theorem rowSound123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row123 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck123, numericCheck123, reducedZero123 B hB hF, mul_zero]

theorem reducedZero124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource124 (mixedVector B) = 0 := by
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h1027 : mixedVector B (Sum.inr 1027) = Sparse.eval nodeValue1027 (mixedVector B) := by
    change mixedMoment B node1027 node1027Labels = _
    exact sound1027 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h2247 : mixedVector B (Sum.inr 2247) = Sparse.eval nodeValue2247 (mixedVector B) := by
    change mixedMoment B node2247 node2247Labels = _
    exact sound2247 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm144, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1022, h1027, h1046, h2247, h4083, reducedSource124] using sourceEq144 B hB

theorem rowSound124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row124 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck124, numericCheck124, reducedZero124 B hB hF, mul_zero]

theorem sourceRowsAt112 : MixedData.sourceRows (112 : Fin 2425) =
    MixedData.row112 := by decide +kernel

theorem sourceRowsAt113 : MixedData.sourceRows (113 : Fin 2425) =
    MixedData.row113 := by decide +kernel

theorem sourceRowsAt114 : MixedData.sourceRows (114 : Fin 2425) =
    MixedData.row114 := by decide +kernel

theorem sourceRowsAt115 : MixedData.sourceRows (115 : Fin 2425) =
    MixedData.row115 := by decide +kernel

theorem sourceRowsAt116 : MixedData.sourceRows (116 : Fin 2425) =
    MixedData.row116 := by decide +kernel

theorem sourceRowsAt117 : MixedData.sourceRows (117 : Fin 2425) =
    MixedData.row117 := by decide +kernel

theorem sourceRowsAt118 : MixedData.sourceRows (118 : Fin 2425) =
    MixedData.row118 := by decide +kernel

theorem sourceRowsAt119 : MixedData.sourceRows (119 : Fin 2425) =
    MixedData.row119 := by decide +kernel

theorem sourceRowsAt120 : MixedData.sourceRows (120 : Fin 2425) =
    MixedData.row120 := by decide +kernel

theorem sourceRowsAt121 : MixedData.sourceRows (121 : Fin 2425) =
    MixedData.row121 := by decide +kernel

theorem sourceRowsAt122 : MixedData.sourceRows (122 : Fin 2425) =
    MixedData.row122 := by decide +kernel

theorem sourceRowsAt123 : MixedData.sourceRows (123 : Fin 2425) =
    MixedData.row123 := by decide +kernel

theorem sourceRowsAt124 : MixedData.sourceRows (124 : Fin 2425) =
    MixedData.row124 := by decide +kernel

theorem sourceRowsAt125 : MixedData.sourceRows (125 : Fin 2425) =
    MixedData.row125 := by decide +kernel

theorem sourceRowsAt126 : MixedData.sourceRows (126 : Fin 2425) =
    MixedData.row126 := by decide +kernel

theorem sourceRowsAt127 : MixedData.sourceRows (127 : Fin 2425) =
    MixedData.row127 := by decide +kernel

theorem chunkSound7_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 7) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 112 ∨ k.val = 113 ∨ k.val = 114 ∨ k.val = 115 ∨ k.val = 116 ∨ k.val = 117 ∨ k.val = 118 ∨ k.val = 119 ∨ k.val = 120 ∨ k.val = 121 ∨ k.val = 122 ∨ k.val = 123 ∨ k.val = 124 ∨ k.val = 125 ∨ k.val = 126 ∨ k.val = 127 := by omega
  rcases heq with h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127
  · have he : k = (112 : Fin 2425) := Fin.ext h112
    subst k
    rw [sourceRowsAt112]
    exact rowSound112 B hB hF
  · have he : k = (113 : Fin 2425) := Fin.ext h113
    subst k
    rw [sourceRowsAt113]
    exact rowSound113_e B hB hF
  · have he : k = (114 : Fin 2425) := Fin.ext h114
    subst k
    rw [sourceRowsAt114]
    exact rowSound114_e B hB hF
  · have he : k = (115 : Fin 2425) := Fin.ext h115
    subst k
    rw [sourceRowsAt115]
    exact rowSound115_e B hB hF
  · have he : k = (116 : Fin 2425) := Fin.ext h116
    subst k
    rw [sourceRowsAt116]
    exact rowSound116_e B hB hF
  · have he : k = (117 : Fin 2425) := Fin.ext h117
    subst k
    rw [sourceRowsAt117]
    exact rowSound117 B hB hF
  · have he : k = (118 : Fin 2425) := Fin.ext h118
    subst k
    rw [sourceRowsAt118]
    exact rowSound118 B hB hF
  · have he : k = (119 : Fin 2425) := Fin.ext h119
    subst k
    rw [sourceRowsAt119]
    exact rowSound119 B hB hF
  · have he : k = (120 : Fin 2425) := Fin.ext h120
    subst k
    rw [sourceRowsAt120]
    exact rowSound120 B hB hF
  · have he : k = (121 : Fin 2425) := Fin.ext h121
    subst k
    rw [sourceRowsAt121]
    exact rowSound121 B hB hF
  · have he : k = (122 : Fin 2425) := Fin.ext h122
    subst k
    rw [sourceRowsAt122]
    exact rowSound122 B hB hF
  · have he : k = (123 : Fin 2425) := Fin.ext h123
    subst k
    rw [sourceRowsAt123]
    exact rowSound123 B hB hF
  · have he : k = (124 : Fin 2425) := Fin.ext h124
    subst k
    rw [sourceRowsAt124]
    exact rowSound124 B hB hF
  · have he : k = (125 : Fin 2425) := Fin.ext h125
    subst k
    rw [sourceRowsAt125]
    exact rowSound125_e B hB hF
  · have he : k = (126 : Fin 2425) := Fin.ext h126
    subst k
    rw [sourceRowsAt126]
    exact rowSound126_e B hB hF
  · have he : k = (127 : Fin 2425) := Fin.ext h127
    subst k
    rw [sourceRowsAt127]
    exact rowSound127_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e_oai
