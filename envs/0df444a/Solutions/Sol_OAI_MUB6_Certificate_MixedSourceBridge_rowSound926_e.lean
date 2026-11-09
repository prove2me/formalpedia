-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:55:31.001395+00:00
-- url     : https://prove2.me/submissions/857ed89d-a8d3-4d6c-a858-373a4e574264

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5492_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17763 raw17763Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw17763 raw17763Labels = mixedMoment B raw17763step0 raw17763step0Labels := by
      have hz : ∀ j, raw17763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17763step0 = (fun i j => raw17763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17763step0 raw17763; decide +kernel
      have hl : raw17763step0Labels = raw17763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17763 raw17763Labels permutation346 hz
    mixedMoment B raw17763step0 raw17763step0Labels = mixedMoment B raw17763step1 raw17763step1Labels := by
      have ha : raw17763step1 = (fun i j => raw17763step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17763step1 raw17763step0; decide +kernel
      have hl : raw17763step1Labels = raw17763step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17763step0 raw17763step0Labels permutation56 permutation3
    mixedMoment B raw17763step1 raw17763step1Labels = mixedMoment B raw17763step2 raw17763step2Labels := by
      have ha : raw17763step2 = raw17763step1 := by apply Matrix.ext; unfold raw17763step2 raw17763step1; decide +kernel
      have hl : raw17763step1Labels = labelEmbedding6 ∘ raw17763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17763step1 raw17763step1Labels raw17763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical17764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17764 raw17764Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw17764 raw17764Labels = mixedMoment B raw17764step0 raw17764step0Labels := by
      have ha : raw17764step0 = (fun i j => raw17764 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17764step0 raw17764; decide +kernel
      have hl : raw17764step0Labels = raw17764Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17764 raw17764Labels permutation683 permutation3
    mixedMoment B raw17764step0 raw17764step0Labels = mixedMoment B raw17764step1 raw17764step1Labels := by
      have ha : raw17764step1 = -raw17764step0 := by apply Matrix.ext; change ∀ i j, raw17764step1 i j = -(raw17764step0 i j); unfold raw17764step1 raw17764step0; decide +kernel
      have hl : raw17764step1Labels = raw17764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17764step1 raw17764step1Labels = mixedMoment B raw17764step2 raw17764step2Labels := by
      have ha : raw17764step2 = raw17764step1 := by apply Matrix.ext; unfold raw17764step2 raw17764step1; decide +kernel
      have hl : raw17764step1Labels = labelEmbedding6 ∘ raw17764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17764step1 raw17764step1Labels raw17764step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical17765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17765 raw17765Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17765 raw17765Labels = mixedMoment B raw17765step0 raw17765step0Labels := by
      have hz : ∀ j, raw17765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17765step0 = (fun i j => raw17765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17765step0 raw17765; decide +kernel
      have hl : raw17765step0Labels = raw17765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17765 raw17765Labels permutation346 hz
    mixedMoment B raw17765step0 raw17765step0Labels = mixedMoment B raw17765step1 raw17765step1Labels := by
      have ha : raw17765step1 = (fun i j => raw17765step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17765step1 raw17765step0; decide +kernel
      have hl : raw17765step1Labels = raw17765step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17765step0 raw17765step0Labels permutation122 permutation5
    mixedMoment B raw17765step1 raw17765step1Labels = mixedMoment B raw17765step2 raw17765step2Labels := by
      have ha : raw17765step2 = raw17765step1 := by apply Matrix.ext; unfold raw17765step2 raw17765step1; decide +kernel
      have hl : raw17765step1Labels = labelEmbedding8 ∘ raw17765step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17765step1 raw17765step1Labels raw17765step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical17766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17766 raw17766Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17766 raw17766Labels = mixedMoment B raw17766step0 raw17766step0Labels := by
      have hz : ∀ j, raw17766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17766step0 = (fun i j => raw17766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17766step0 raw17766; decide +kernel
      have hl : raw17766step0Labels = raw17766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17766 raw17766Labels permutation346 hz
    mixedMoment B raw17766step0 raw17766step0Labels = mixedMoment B raw17766step1 raw17766step1Labels := by
      have ha : raw17766step1 = (fun i j => raw17766step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17766step1 raw17766step0; decide +kernel
      have hl : raw17766step1Labels = raw17766step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17766step0 raw17766step0Labels permutation145 permutation2
    mixedMoment B raw17766step1 raw17766step1Labels = mixedMoment B raw17766step2 raw17766step2Labels := by
      have ha : raw17766step2 = -raw17766step1 := by apply Matrix.ext; change ∀ i j, raw17766step2 i j = -(raw17766step1 i j); unfold raw17766step2 raw17766step1; decide +kernel
      have hl : raw17766step2Labels = raw17766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical17767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17767 raw17767Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17767 raw17767Labels = mixedMoment B raw17767step0 raw17767step0Labels := by
      have hz : ∀ j, raw17767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17767step0 = (fun i j => raw17767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17767step0 raw17767; decide +kernel
      have hl : raw17767step0Labels = raw17767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17767 raw17767Labels permutation346 hz
    mixedMoment B raw17767step0 raw17767step0Labels = mixedMoment B raw17767step1 raw17767step1Labels := by
      have ha : raw17767step1 = (fun i j => raw17767step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17767step1 raw17767step0; decide +kernel
      have hl : raw17767step1Labels = raw17767step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17767step0 raw17767step0Labels permutation108 permutation4
    mixedMoment B raw17767step1 raw17767step1Labels = mixedMoment B raw17767step2 raw17767step2Labels := by
      have ha : raw17767step2 = raw17767step1 := by apply Matrix.ext; unfold raw17767step2 raw17767step1; decide +kernel
      have hl : raw17767step1Labels = labelEmbedding7 ∘ raw17767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17767step1 raw17767step1Labels raw17767step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical17768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17768 raw17768Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw17768 raw17768Labels = mixedMoment B raw17768step0 raw17768step0Labels := by
      have hz : ∀ j, raw17768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17768step0 = (fun i j => raw17768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17768step0 raw17768; decide +kernel
      have hl : raw17768step0Labels = raw17768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17768 raw17768Labels permutation346 hz
    mixedMoment B raw17768step0 raw17768step0Labels = mixedMoment B raw17768step1 raw17768step1Labels := by
      have hz : ∀ j, raw17768step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17768step1 = (fun i j => raw17768step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17768step1 raw17768step0; decide +kernel
      have hl : raw17768step1Labels = raw17768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17768step0 raw17768step0Labels permutation56 hz
    mixedMoment B raw17768step1 raw17768step1Labels = mixedMoment B raw17768step2 raw17768step2Labels := by
      have ha : raw17768step2 = (fun i j => raw17768step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17768step2 raw17768step1; decide +kernel
      have hl : raw17768step2Labels = raw17768step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17768step1 raw17768step1Labels permutation8 permutation3
    mixedMoment B raw17768step2 raw17768step2Labels = mixedMoment B raw17768step3 raw17768step3Labels := by
      have ha : raw17768step3 = raw17768step2 := by apply Matrix.ext; unfold raw17768step3 raw17768step2; decide +kernel
      have hl : raw17768step2Labels = labelEmbedding6 ∘ raw17768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17768step2 raw17768step2Labels raw17768step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical17769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17769 raw17769Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17769 raw17769Labels = mixedMoment B raw17769step0 raw17769step0Labels := by
      have ha : raw17769step0 = (fun i j => raw17769 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17769step0 raw17769; decide +kernel
      have hl : raw17769step0Labels = raw17769Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17769 raw17769Labels permutation271 permutation3
    mixedMoment B raw17769step0 raw17769step0Labels = mixedMoment B raw17769step1 raw17769step1Labels := by
      have ha : raw17769step1 = raw17769step0 := by apply Matrix.ext; unfold raw17769step1 raw17769step0; decide +kernel
      have hl : raw17769step0Labels = labelEmbedding6 ∘ raw17769step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17769step0 raw17769step0Labels raw17769step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical17770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17770 raw17770Labels = mixedMoment B node5467 node5467Labels := by
  calc
    mixedMoment B raw17770 raw17770Labels = mixedMoment B raw17770step0 raw17770step0Labels := by
      have ha : raw17770step0 = (fun i j => raw17770 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17770step0 raw17770; decide +kernel
      have hl : raw17770step0Labels = raw17770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17770 raw17770Labels permutation200 permutation3
    mixedMoment B raw17770step0 raw17770step0Labels = mixedMoment B raw17770step1 raw17770step1Labels := by
      have ha : raw17770step1 = raw17770step0 := by apply Matrix.ext; unfold raw17770step1 raw17770step0; decide +kernel
      have hl : raw17770step0Labels = labelEmbedding6 ∘ raw17770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17770step0 raw17770step0Labels raw17770step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5467 node5467Labels := by rfl

theorem canonical17771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17771 raw17771Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17771 raw17771Labels = mixedMoment B raw17771step0 raw17771step0Labels := by
      have ha : raw17771step0 = (fun i j => raw17771 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17771step0 raw17771; decide +kernel
      have hl : raw17771step0Labels = raw17771Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17771 raw17771Labels permutation160 permutation3
    mixedMoment B raw17771step0 raw17771step0Labels = mixedMoment B raw17771step1 raw17771step1Labels := by
      have ha : raw17771step1 = raw17771step0 := by apply Matrix.ext; unfold raw17771step1 raw17771step0; decide +kernel
      have hl : raw17771step0Labels = labelEmbedding6 ∘ raw17771step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17771step0 raw17771step0Labels raw17771step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical17772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17772 raw17772Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw17772 raw17772Labels = mixedMoment B raw17772step0 raw17772step0Labels := by
      have ha : raw17772step0 = (fun i j => raw17772 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17772step0 raw17772; decide +kernel
      have hl : raw17772step0Labels = raw17772Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17772 raw17772Labels permutation162 permutation3
    mixedMoment B raw17772step0 raw17772step0Labels = mixedMoment B raw17772step1 raw17772step1Labels := by
      have ha : raw17772step1 = raw17772step0 := by apply Matrix.ext; unfold raw17772step1 raw17772step0; decide +kernel
      have hl : raw17772step0Labels = labelEmbedding6 ∘ raw17772step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17772step0 raw17772step0Labels raw17772step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical17773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17773 raw17773Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17773 raw17773Labels = mixedMoment B raw17773step0 raw17773step0Labels := by
      have hz : ∀ j, raw17773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17773step0 = (fun i j => raw17773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17773step0 raw17773; decide +kernel
      have hl : raw17773step0Labels = raw17773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17773 raw17773Labels permutation346 hz
    mixedMoment B raw17773step0 raw17773step0Labels = mixedMoment B raw17773step1 raw17773step1Labels := by
      have ha : raw17773step1 = (fun i j => raw17773step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17773step1 raw17773step0; decide +kernel
      have hl : raw17773step1Labels = raw17773step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17773step0 raw17773step0Labels permutation56 permutation3
    mixedMoment B raw17773step1 raw17773step1Labels = mixedMoment B raw17773step2 raw17773step2Labels := by
      have ha : raw17773step2 = raw17773step1 := by apply Matrix.ext; unfold raw17773step2 raw17773step1; decide +kernel
      have hl : raw17773step1Labels = labelEmbedding6 ∘ raw17773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17773step1 raw17773step1Labels raw17773step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical17774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17774 raw17774Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw17774 raw17774Labels = mixedMoment B raw17774step0 raw17774step0Labels := by
      have ha : raw17774step0 = (fun i j => raw17774 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17774step0 raw17774; decide +kernel
      have hl : raw17774step0Labels = raw17774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17774 raw17774Labels permutation686 permutation3
    mixedMoment B raw17774step0 raw17774step0Labels = mixedMoment B raw17774step1 raw17774step1Labels := by
      have ha : raw17774step1 = -raw17774step0 := by apply Matrix.ext; change ∀ i j, raw17774step1 i j = -(raw17774step0 i j); unfold raw17774step1 raw17774step0; decide +kernel
      have hl : raw17774step1Labels = raw17774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17774step1 raw17774step1Labels = mixedMoment B raw17774step2 raw17774step2Labels := by
      have ha : raw17774step2 = raw17774step1 := by apply Matrix.ext; unfold raw17774step2 raw17774step1; decide +kernel
      have hl : raw17774step1Labels = labelEmbedding6 ∘ raw17774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17774step1 raw17774step1Labels raw17774step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical17775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17775 raw17775Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17775 raw17775Labels = mixedMoment B raw17775step0 raw17775step0Labels := by
      have hz : ∀ j, raw17775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17775step0 = (fun i j => raw17775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17775step0 raw17775; decide +kernel
      have hl : raw17775step0Labels = raw17775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17775 raw17775Labels permutation346 hz
    mixedMoment B raw17775step0 raw17775step0Labels = mixedMoment B raw17775step1 raw17775step1Labels := by
      have ha : raw17775step1 = (fun i j => raw17775step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17775step1 raw17775step0; decide +kernel
      have hl : raw17775step1Labels = raw17775step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17775step0 raw17775step0Labels permutation145 permutation2
    mixedMoment B raw17775step1 raw17775step1Labels = mixedMoment B raw17775step2 raw17775step2Labels := by
      have ha : raw17775step2 = -raw17775step1 := by apply Matrix.ext; change ∀ i j, raw17775step2 i j = -(raw17775step1 i j); unfold raw17775step2 raw17775step1; decide +kernel
      have hl : raw17775step2Labels = raw17775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical17776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17776 raw17776Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw17776 raw17776Labels = mixedMoment B raw17776step0 raw17776step0Labels := by
      have hz : ∀ j, raw17776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17776step0 = (fun i j => raw17776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17776step0 raw17776; decide +kernel
      have hl : raw17776step0Labels = raw17776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17776 raw17776Labels permutation346 hz
    mixedMoment B raw17776step0 raw17776step0Labels = mixedMoment B raw17776step1 raw17776step1Labels := by
      have ha : raw17776step1 = (fun i j => raw17776step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17776step1 raw17776step0; decide +kernel
      have hl : raw17776step1Labels = raw17776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17776step0 raw17776step0Labels permutation33 permutation3
    mixedMoment B raw17776step1 raw17776step1Labels = mixedMoment B raw17776step2 raw17776step2Labels := by
      have ha : raw17776step2 = raw17776step1 := by apply Matrix.ext; unfold raw17776step2 raw17776step1; decide +kernel
      have hl : raw17776step1Labels = labelEmbedding6 ∘ raw17776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17776step1 raw17776step1Labels raw17776step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical17777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17777 raw17777Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw17777 raw17777Labels = mixedMoment B raw17777step0 raw17777step0Labels := by
      have hz : ∀ j, raw17777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17777step0 = (fun i j => raw17777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17777step0 raw17777; decide +kernel
      have hl : raw17777step0Labels = raw17777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17777 raw17777Labels permutation346 hz
    mixedMoment B raw17777step0 raw17777step0Labels = mixedMoment B raw17777step1 raw17777step1Labels := by
      have ha : raw17777step1 = (fun i j => raw17777step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17777step1 raw17777step0; decide +kernel
      have hl : raw17777step1Labels = raw17777step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17777step0 raw17777step0Labels permutation126 permutation5
    mixedMoment B raw17777step1 raw17777step1Labels = mixedMoment B raw17777step2 raw17777step2Labels := by
      have ha : raw17777step2 = raw17777step1 := by apply Matrix.ext; unfold raw17777step2 raw17777step1; decide +kernel
      have hl : raw17777step1Labels = labelEmbedding8 ∘ raw17777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17777step1 raw17777step1Labels raw17777step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical17778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17778 raw17778Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw17778 raw17778Labels = mixedMoment B raw17778step0 raw17778step0Labels := by
      have ha : raw17778step0 = (fun i j => raw17778 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17778step0 raw17778; decide +kernel
      have hl : raw17778step0Labels = raw17778Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17778 raw17778Labels permutation587 permutation5
    mixedMoment B raw17778step0 raw17778step0Labels = mixedMoment B raw17778step1 raw17778step1Labels := by
      have ha : raw17778step1 = raw17778step0 := by apply Matrix.ext; unfold raw17778step1 raw17778step0; decide +kernel
      have hl : raw17778step0Labels = labelEmbedding8 ∘ raw17778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17778step0 raw17778step0Labels raw17778step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

theorem canonical17779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17779 raw17779Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw17779 raw17779Labels = mixedMoment B raw17779step0 raw17779step0Labels := by
      have hz : ∀ j, raw17779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17779step0 = (fun i j => raw17779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17779step0 raw17779; decide +kernel
      have hl : raw17779step0Labels = raw17779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17779 raw17779Labels permutation346 hz
    mixedMoment B raw17779step0 raw17779step0Labels = mixedMoment B raw17779step1 raw17779step1Labels := by
      have ha : raw17779step1 = (fun i j => raw17779step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17779step1 raw17779step0; decide +kernel
      have hl : raw17779step1Labels = raw17779step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17779step0 raw17779step0Labels permutation124 permutation5
    mixedMoment B raw17779step1 raw17779step1Labels = mixedMoment B raw17779step2 raw17779step2Labels := by
      have ha : raw17779step2 = raw17779step1 := by apply Matrix.ext; unfold raw17779step2 raw17779step1; decide +kernel
      have hl : raw17779step1Labels = labelEmbedding8 ∘ raw17779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17779step1 raw17779step1Labels raw17779step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

theorem canonical17780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17780 raw17780Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw17780 raw17780Labels = mixedMoment B raw17780step0 raw17780step0Labels := by
      have hz : ∀ j, raw17780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17780step0 = (fun i j => raw17780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17780step0 raw17780; decide +kernel
      have hl : raw17780step0Labels = raw17780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17780 raw17780Labels permutation346 hz
    mixedMoment B raw17780step0 raw17780step0Labels = mixedMoment B raw17780step1 raw17780step1Labels := by
      have ha : raw17780step1 = (fun i j => raw17780step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17780step1 raw17780step0; decide +kernel
      have hl : raw17780step1Labels = raw17780step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17780step0 raw17780step0Labels permutation127 permutation5
    mixedMoment B raw17780step1 raw17780step1Labels = mixedMoment B raw17780step2 raw17780step2Labels := by
      have ha : raw17780step2 = raw17780step1 := by apply Matrix.ext; unfold raw17780step2 raw17780step1; decide +kernel
      have hl : raw17780step1Labels = labelEmbedding8 ∘ raw17780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17780step1 raw17780step1Labels raw17780step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical17781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17781 raw17781Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw17781 raw17781Labels = mixedMoment B raw17781step0 raw17781step0Labels := by
      have hz : ∀ j, raw17781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17781step0 = (fun i j => raw17781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17781step0 raw17781; decide +kernel
      have hl : raw17781step0Labels = raw17781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17781 raw17781Labels permutation346 hz
    mixedMoment B raw17781step0 raw17781step0Labels = mixedMoment B raw17781step1 raw17781step1Labels := by
      have ha : raw17781step1 = (fun i j => raw17781step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17781step1 raw17781step0; decide +kernel
      have hl : raw17781step1Labels = raw17781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17781step0 raw17781step0Labels permutation150 permutation3
    mixedMoment B raw17781step1 raw17781step1Labels = mixedMoment B raw17781step2 raw17781step2Labels := by
      have ha : raw17781step2 = -raw17781step1 := by apply Matrix.ext; change ∀ i j, raw17781step2 i j = -(raw17781step1 i j); unfold raw17781step2 raw17781step1; decide +kernel
      have hl : raw17781step2Labels = raw17781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17781step2 raw17781step2Labels = mixedMoment B raw17781step3 raw17781step3Labels := by
      have ha : raw17781step3 = raw17781step2 := by apply Matrix.ext; unfold raw17781step3 raw17781step2; decide +kernel
      have hl : raw17781step2Labels = labelEmbedding6 ∘ raw17781step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17781step2 raw17781step2Labels raw17781step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical17782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17782 raw17782Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw17782 raw17782Labels = mixedMoment B raw17782step0 raw17782step0Labels := by
      have ha : raw17782step0 = (fun i j => raw17782 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17782step0 raw17782; decide +kernel
      have hl : raw17782step0Labels = raw17782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17782 raw17782Labels permutation686 permutation3
    mixedMoment B raw17782step0 raw17782step0Labels = mixedMoment B raw17782step1 raw17782step1Labels := by
      have ha : raw17782step1 = -raw17782step0 := by apply Matrix.ext; change ∀ i j, raw17782step1 i j = -(raw17782step0 i j); unfold raw17782step1 raw17782step0; decide +kernel
      have hl : raw17782step1Labels = raw17782step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17782step1 raw17782step1Labels = mixedMoment B raw17782step2 raw17782step2Labels := by
      have ha : raw17782step2 = raw17782step1 := by apply Matrix.ext; unfold raw17782step2 raw17782step1; decide +kernel
      have hl : raw17782step1Labels = labelEmbedding6 ∘ raw17782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17782step1 raw17782step1Labels raw17782step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

theorem canonical17783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17783 raw17783Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw17783 raw17783Labels = mixedMoment B raw17783step0 raw17783step0Labels := by
      have hz : ∀ j, raw17783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17783step0 = (fun i j => raw17783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17783step0 raw17783; decide +kernel
      have hl : raw17783step0Labels = raw17783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17783 raw17783Labels permutation346 hz
    mixedMoment B raw17783step0 raw17783step0Labels = mixedMoment B raw17783step1 raw17783step1Labels := by
      have ha : raw17783step1 = (fun i j => raw17783step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17783step1 raw17783step0; decide +kernel
      have hl : raw17783step1Labels = raw17783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17783step0 raw17783step0Labels permutation149 permutation3
    mixedMoment B raw17783step1 raw17783step1Labels = mixedMoment B raw17783step2 raw17783step2Labels := by
      have ha : raw17783step2 = -raw17783step1 := by apply Matrix.ext; change ∀ i j, raw17783step2 i j = -(raw17783step1 i j); unfold raw17783step2 raw17783step1; decide +kernel
      have hl : raw17783step2Labels = raw17783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17783step2 raw17783step2Labels = mixedMoment B raw17783step3 raw17783step3Labels := by
      have ha : raw17783step3 = raw17783step2 := by apply Matrix.ext; unfold raw17783step3 raw17783step2; decide +kernel
      have hl : raw17783step2Labels = labelEmbedding6 ∘ raw17783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17783step2 raw17783step2Labels raw17783step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

theorem canonical17784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17784 raw17784Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw17784 raw17784Labels = mixedMoment B raw17784step0 raw17784step0Labels := by
      have hz : ∀ j, raw17784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17784step0 = (fun i j => raw17784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17784step0 raw17784; decide +kernel
      have hl : raw17784step0Labels = raw17784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17784 raw17784Labels permutation346 hz
    mixedMoment B raw17784step0 raw17784step0Labels = mixedMoment B raw17784step1 raw17784step1Labels := by
      have ha : raw17784step1 = (fun i j => raw17784step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17784step1 raw17784step0; decide +kernel
      have hl : raw17784step1Labels = raw17784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17784step0 raw17784step0Labels permutation151 permutation3
    mixedMoment B raw17784step1 raw17784step1Labels = mixedMoment B raw17784step2 raw17784step2Labels := by
      have ha : raw17784step2 = -raw17784step1 := by apply Matrix.ext; change ∀ i j, raw17784step2 i j = -(raw17784step1 i j); unfold raw17784step2 raw17784step1; decide +kernel
      have hl : raw17784step2Labels = raw17784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17784step2 raw17784step2Labels = mixedMoment B raw17784step3 raw17784step3Labels := by
      have ha : raw17784step3 = raw17784step2 := by apply Matrix.ext; unfold raw17784step3 raw17784step2; decide +kernel
      have hl : raw17784step2Labels = labelEmbedding6 ∘ raw17784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17784step2 raw17784step2Labels raw17784step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2010 raw2010Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw2010 raw2010Labels = mixedMoment B raw2010step0 raw2010step0Labels := by
      have ha : raw2010step0 = (fun i j => raw2010 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2010step0 raw2010; decide +kernel
      have hl : raw2010step0Labels = raw2010Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2010 raw2010Labels permutation152 permutation4
    mixedMoment B raw2010step0 raw2010step0Labels = mixedMoment B raw2010step1 raw2010step1Labels := by
      have ha : raw2010step1 = raw2010step0 := by apply Matrix.ext; unfold raw2010step1 raw2010step0; decide +kernel
      have hl : raw2010step0Labels = labelEmbedding7 ∘ raw2010step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2010step0 raw2010step0Labels raw2010step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

theorem canonical2011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2011 raw2011Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw2011 raw2011Labels = mixedMoment B raw2011step0 raw2011step0Labels := by
      have ha : raw2011step0 = (fun i j => raw2011 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2011step0 raw2011; decide +kernel
      have hl : raw2011step0Labels = raw2011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2011 raw2011Labels permutation152 permutation4
    _ = mixedMoment B node2383 node2383Labels := by rfl

theorem canonical2012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2012 raw2012Labels = mixedMoment B node3352 node3352Labels := by
  calc
    mixedMoment B raw2012 raw2012Labels = mixedMoment B raw2012step0 raw2012step0Labels := by
      have ha : raw2012step0 = (fun i j => raw2012 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2012step0 raw2012; decide +kernel
      have hl : raw2012step0Labels = raw2012Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2012 raw2012Labels permutation152 permutation6
    mixedMoment B raw2012step0 raw2012step0Labels = mixedMoment B raw2012step1 raw2012step1Labels := by
      have ha : raw2012step1 = -raw2012step0 := by apply Matrix.ext; change ∀ i j, raw2012step1 i j = -(raw2012step0 i j); unfold raw2012step1 raw2012step0; decide +kernel
      have hl : raw2012step1Labels = raw2012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2012step1 raw2012step1Labels = mixedMoment B raw2012step2 raw2012step2Labels := by
      have ha : raw2012step2 = raw2012step1 := by apply Matrix.ext; unfold raw2012step2 raw2012step1; decide +kernel
      have hl : raw2012step1Labels = labelEmbedding1 ∘ raw2012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2012step1 raw2012step1Labels raw2012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3352 node3352Labels := by rfl

theorem canonical2013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2013 raw2013Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw2013 raw2013Labels = mixedMoment B raw2013step0 raw2013step0Labels := by
      have ha : raw2013step0 = (fun i j => raw2013 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2013step0 raw2013; decide +kernel
      have hl : raw2013step0Labels = raw2013Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2013 raw2013Labels permutation32 permutation4
    mixedMoment B raw2013step0 raw2013step0Labels = mixedMoment B raw2013step1 raw2013step1Labels := by
      have ha : raw2013step1 = raw2013step0 := by apply Matrix.ext; unfold raw2013step1 raw2013step0; decide +kernel
      have hl : raw2013step0Labels = labelEmbedding7 ∘ raw2013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2013step0 raw2013step0Labels raw2013step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical2014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2014 raw2014Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw2014 raw2014Labels = mixedMoment B raw2014step0 raw2014step0Labels := by
      have ha : raw2014step0 = (fun i j => raw2014 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2014step0 raw2014; decide +kernel
      have hl : raw2014step0Labels = raw2014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2014 raw2014Labels permutation32 permutation4
    _ = mixedMoment B node2385 node2385Labels := by rfl

theorem canonical2015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2015 raw2015Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw2015 raw2015Labels = mixedMoment B raw2015step0 raw2015step0Labels := by
      have ha : raw2015step0 = (fun i j => raw2015 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2015step0 raw2015; decide +kernel
      have hl : raw2015step0Labels = raw2015Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2015 raw2015Labels permutation32 permutation6
    mixedMoment B raw2015step0 raw2015step0Labels = mixedMoment B raw2015step1 raw2015step1Labels := by
      have ha : raw2015step1 = -raw2015step0 := by apply Matrix.ext; change ∀ i j, raw2015step1 i j = -(raw2015step0 i j); unfold raw2015step1 raw2015step0; decide +kernel
      have hl : raw2015step1Labels = raw2015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2015step1 raw2015step1Labels = mixedMoment B raw2015step2 raw2015step2Labels := by
      have ha : raw2015step2 = raw2015step1 := by apply Matrix.ext; unfold raw2015step2 raw2015step1; decide +kernel
      have hl : raw2015step1Labels = labelEmbedding1 ∘ raw2015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2015step1 raw2015step1Labels raw2015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3353 node3353Labels := by rfl

theorem canonical2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2016 raw2016Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw2016 raw2016Labels = mixedMoment B raw2016step0 raw2016step0Labels := by
      have ha : raw2016step0 = (fun i j => raw2016 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2016step0 raw2016; decide +kernel
      have hl : raw2016step0Labels = raw2016Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2016 raw2016Labels permutation32 permutation4
    mixedMoment B raw2016step0 raw2016step0Labels = mixedMoment B raw2016step1 raw2016step1Labels := by
      have ha : raw2016step1 = raw2016step0 := by apply Matrix.ext; unfold raw2016step1 raw2016step0; decide +kernel
      have hl : raw2016step0Labels = labelEmbedding7 ∘ raw2016step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2016step0 raw2016step0Labels raw2016step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical2017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2017 raw2017Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw2017 raw2017Labels = mixedMoment B raw2017step0 raw2017step0Labels := by
      have ha : raw2017step0 = (fun i j => raw2017 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2017step0 raw2017; decide +kernel
      have hl : raw2017step0Labels = raw2017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2017 raw2017Labels permutation32 permutation4
    _ = mixedMoment B node2388 node2388Labels := by rfl

theorem canonical2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2018 raw2018Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw2018 raw2018Labels = mixedMoment B raw2018step0 raw2018step0Labels := by
      have ha : raw2018step0 = (fun i j => raw2018 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2018step0 raw2018; decide +kernel
      have hl : raw2018step0Labels = raw2018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2018 raw2018Labels permutation32 permutation6
    mixedMoment B raw2018step0 raw2018step0Labels = mixedMoment B raw2018step1 raw2018step1Labels := by
      have ha : raw2018step1 = -raw2018step0 := by apply Matrix.ext; change ∀ i j, raw2018step1 i j = -(raw2018step0 i j); unfold raw2018step1 raw2018step0; decide +kernel
      have hl : raw2018step1Labels = raw2018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2018step1 raw2018step1Labels = mixedMoment B raw2018step2 raw2018step2Labels := by
      have ha : raw2018step2 = raw2018step1 := by apply Matrix.ext; unfold raw2018step2 raw2018step1; decide +kernel
      have hl : raw2018step1Labels = labelEmbedding1 ∘ raw2018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2018step1 raw2018step1Labels raw2018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3354 node3354Labels := by rfl

theorem canonical2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2019 raw2019Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw2019 raw2019Labels = mixedMoment B raw2019step0 raw2019step0Labels := by
      have ha : raw2019step0 = (fun i j => raw2019 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2019step0 raw2019; decide +kernel
      have hl : raw2019step0Labels = raw2019Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2019 raw2019Labels permutation152 permutation4
    mixedMoment B raw2019step0 raw2019step0Labels = mixedMoment B raw2019step1 raw2019step1Labels := by
      have ha : raw2019step1 = raw2019step0 := by apply Matrix.ext; unfold raw2019step1 raw2019step0; decide +kernel
      have hl : raw2019step0Labels = labelEmbedding7 ∘ raw2019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2019step0 raw2019step0Labels raw2019step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

theorem canonical2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2020 raw2020Labels = mixedMoment B node2398 node2398Labels := by
  calc
    mixedMoment B raw2020 raw2020Labels = mixedMoment B raw2020step0 raw2020step0Labels := by
      have ha : raw2020step0 = (fun i j => raw2020 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2020step0 raw2020; decide +kernel
      have hl : raw2020step0Labels = raw2020Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2020 raw2020Labels permutation152 permutation4
    _ = mixedMoment B node2398 node2398Labels := by rfl

theorem canonical2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2021 raw2021Labels = mixedMoment B node3341 node3341Labels := by
  calc
    mixedMoment B raw2021 raw2021Labels = mixedMoment B raw2021step0 raw2021step0Labels := by
      have ha : raw2021step0 = (fun i j => raw2021 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2021step0 raw2021; decide +kernel
      have hl : raw2021step0Labels = raw2021Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2021 raw2021Labels permutation152 permutation6
    mixedMoment B raw2021step0 raw2021step0Labels = mixedMoment B raw2021step1 raw2021step1Labels := by
      have ha : raw2021step1 = -raw2021step0 := by apply Matrix.ext; change ∀ i j, raw2021step1 i j = -(raw2021step0 i j); unfold raw2021step1 raw2021step0; decide +kernel
      have hl : raw2021step1Labels = raw2021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2021step1 raw2021step1Labels = mixedMoment B raw2021step2 raw2021step2Labels := by
      have ha : raw2021step2 = raw2021step1 := by apply Matrix.ext; unfold raw2021step2 raw2021step1; decide +kernel
      have hl : raw2021step1Labels = labelEmbedding1 ∘ raw2021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2021step1 raw2021step1Labels raw2021step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3341 node3341Labels := by rfl

theorem canonical2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2022 raw2022Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw2022 raw2022Labels = mixedMoment B raw2022step0 raw2022step0Labels := by
      have ha : raw2022step0 = (fun i j => raw2022 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2022step0 raw2022; decide +kernel
      have hl : raw2022step0Labels = raw2022Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2022 raw2022Labels permutation32 permutation4
    mixedMoment B raw2022step0 raw2022step0Labels = mixedMoment B raw2022step1 raw2022step1Labels := by
      have ha : raw2022step1 = raw2022step0 := by apply Matrix.ext; unfold raw2022step1 raw2022step0; decide +kernel
      have hl : raw2022step0Labels = labelEmbedding7 ∘ raw2022step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2022step0 raw2022step0Labels raw2022step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

theorem canonical2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2023 raw2023Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw2023 raw2023Labels = mixedMoment B raw2023step0 raw2023step0Labels := by
      have ha : raw2023step0 = (fun i j => raw2023 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2023step0 raw2023; decide +kernel
      have hl : raw2023step0Labels = raw2023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2023 raw2023Labels permutation32 permutation4
    _ = mixedMoment B node2399 node2399Labels := by rfl

theorem canonical2024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2024 raw2024Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw2024 raw2024Labels = mixedMoment B raw2024step0 raw2024step0Labels := by
      have ha : raw2024step0 = (fun i j => raw2024 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2024step0 raw2024; decide +kernel
      have hl : raw2024step0Labels = raw2024Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2024 raw2024Labels permutation151 permutation6
    mixedMoment B raw2024step0 raw2024step0Labels = mixedMoment B raw2024step1 raw2024step1Labels := by
      have ha : raw2024step1 = raw2024step0 := by apply Matrix.ext; unfold raw2024step1 raw2024step0; decide +kernel
      have hl : raw2024step0Labels = labelEmbedding1 ∘ raw2024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2024step0 raw2024step0Labels raw2024step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2467 node2467Labels := by rfl

theorem canonical2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2025 raw2025Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw2025 raw2025Labels = mixedMoment B raw2025step0 raw2025step0Labels := by
      have ha : raw2025step0 = (fun i j => raw2025 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2025step0 raw2025; decide +kernel
      have hl : raw2025step0Labels = raw2025Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2025 raw2025Labels permutation32 permutation4
    mixedMoment B raw2025step0 raw2025step0Labels = mixedMoment B raw2025step1 raw2025step1Labels := by
      have ha : raw2025step1 = raw2025step0 := by apply Matrix.ext; unfold raw2025step1 raw2025step0; decide +kernel
      have hl : raw2025step0Labels = labelEmbedding7 ∘ raw2025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2025step0 raw2025step0Labels raw2025step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2026 raw2026Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw2026 raw2026Labels = mixedMoment B raw2026step0 raw2026step0Labels := by
      have ha : raw2026step0 = (fun i j => raw2026 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2026step0 raw2026; decide +kernel
      have hl : raw2026step0Labels = raw2026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2026 raw2026Labels permutation32 permutation4
    _ = mixedMoment B node2400 node2400Labels := by rfl

theorem canonical2027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2027 raw2027Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw2027 raw2027Labels = mixedMoment B raw2027step0 raw2027step0Labels := by
      have ha : raw2027step0 = (fun i j => raw2027 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2027step0 raw2027; decide +kernel
      have hl : raw2027step0Labels = raw2027Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2027 raw2027Labels permutation32 permutation6
    mixedMoment B raw2027step0 raw2027step0Labels = mixedMoment B raw2027step1 raw2027step1Labels := by
      have ha : raw2027step1 = -raw2027step0 := by apply Matrix.ext; change ∀ i j, raw2027step1 i j = -(raw2027step0 i j); unfold raw2027step1 raw2027step0; decide +kernel
      have hl : raw2027step1Labels = raw2027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2027step1 raw2027step1Labels = mixedMoment B raw2027step2 raw2027step2Labels := by
      have ha : raw2027step2 = raw2027step1 := by apply Matrix.ext; unfold raw2027step2 raw2027step1; decide +kernel
      have hl : raw2027step1Labels = labelEmbedding1 ∘ raw2027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2027step1 raw2027step1Labels raw2027step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3344 node3344Labels := by rfl

theorem canonical2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2028 raw2028Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw2028 raw2028Labels = mixedMoment B raw2028step0 raw2028step0Labels := by
      have ha : raw2028step0 = (fun i j => raw2028 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2028step0 raw2028; decide +kernel
      have hl : raw2028step0Labels = raw2028Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2028 raw2028Labels permutation32 permutation4
    mixedMoment B raw2028step0 raw2028step0Labels = mixedMoment B raw2028step1 raw2028step1Labels := by
      have ha : raw2028step1 = raw2028step0 := by apply Matrix.ext; unfold raw2028step1 raw2028step0; decide +kernel
      have hl : raw2028step0Labels = labelEmbedding7 ∘ raw2028step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2028step0 raw2028step0Labels raw2028step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

theorem canonical2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2029 raw2029Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw2029 raw2029Labels = mixedMoment B raw2029step0 raw2029step0Labels := by
      have ha : raw2029step0 = (fun i j => raw2029 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2029step0 raw2029; decide +kernel
      have hl : raw2029step0Labels = raw2029Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2029 raw2029Labels permutation32 permutation4
    _ = mixedMoment B node2404 node2404Labels := by rfl

theorem canonical2030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2030 raw2030Labels = mixedMoment B node3357 node3357Labels := by
  calc
    mixedMoment B raw2030 raw2030Labels = mixedMoment B raw2030step0 raw2030step0Labels := by
      have ha : raw2030step0 = (fun i j => raw2030 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2030step0 raw2030; decide +kernel
      have hl : raw2030step0Labels = raw2030Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2030 raw2030Labels permutation33 permutation6
    mixedMoment B raw2030step0 raw2030step0Labels = mixedMoment B raw2030step1 raw2030step1Labels := by
      have ha : raw2030step1 = -raw2030step0 := by apply Matrix.ext; change ∀ i j, raw2030step1 i j = -(raw2030step0 i j); unfold raw2030step1 raw2030step0; decide +kernel
      have hl : raw2030step1Labels = raw2030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2030step1 raw2030step1Labels = mixedMoment B raw2030step2 raw2030step2Labels := by
      have ha : raw2030step2 = raw2030step1 := by apply Matrix.ext; unfold raw2030step2 raw2030step1; decide +kernel
      have hl : raw2030step1Labels = labelEmbedding1 ∘ raw2030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2030step1 raw2030step1Labels raw2030step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3357 node3357Labels := by rfl

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

theorem canonical2085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2085 raw2085Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw2085 raw2085Labels = mixedMoment B raw2085step0 raw2085step0Labels := by
      have ha : raw2085step0 = (fun i j => raw2085 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2085step0 raw2085; decide +kernel
      have hl : raw2085step0Labels = raw2085Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2085 raw2085Labels permutation152 permutation4
    mixedMoment B raw2085step0 raw2085step0Labels = mixedMoment B raw2085step1 raw2085step1Labels := by
      have ha : raw2085step1 = raw2085step0 := by apply Matrix.ext; unfold raw2085step1 raw2085step0; decide +kernel
      have hl : raw2085step0Labels = labelEmbedding7 ∘ raw2085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2085step0 raw2085step0Labels raw2085step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

theorem canonical2086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2086 raw2086Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw2086 raw2086Labels = mixedMoment B raw2086step0 raw2086step0Labels := by
      have ha : raw2086step0 = (fun i j => raw2086 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2086step0 raw2086; decide +kernel
      have hl : raw2086step0Labels = raw2086Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2086 raw2086Labels permutation152 permutation4
    _ = mixedMoment B node2462 node2462Labels := by rfl

theorem canonical2087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2087 raw2087Labels = mixedMoment B node3436 node3436Labels := by
  calc
    mixedMoment B raw2087 raw2087Labels = mixedMoment B raw2087step0 raw2087step0Labels := by
      have ha : raw2087step0 = (fun i j => raw2087 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2087step0 raw2087; decide +kernel
      have hl : raw2087step0Labels = raw2087Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2087 raw2087Labels permutation153 permutation6
    mixedMoment B raw2087step0 raw2087step0Labels = mixedMoment B raw2087step1 raw2087step1Labels := by
      have ha : raw2087step1 = -raw2087step0 := by apply Matrix.ext; change ∀ i j, raw2087step1 i j = -(raw2087step0 i j); unfold raw2087step1 raw2087step0; decide +kernel
      have hl : raw2087step1Labels = raw2087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2087step1 raw2087step1Labels = mixedMoment B raw2087step2 raw2087step2Labels := by
      have ha : raw2087step2 = raw2087step1 := by apply Matrix.ext; unfold raw2087step2 raw2087step1; decide +kernel
      have hl : raw2087step1Labels = labelEmbedding1 ∘ raw2087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2087step1 raw2087step1Labels raw2087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3436 node3436Labels := by rfl

theorem canonical2127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2127 raw2127Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw2127 raw2127Labels = mixedMoment B raw2127step0 raw2127step0Labels := by
      have ha : raw2127step0 = (fun i j => raw2127 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2127step0 raw2127; decide +kernel
      have hl : raw2127step0Labels = raw2127Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2127 raw2127Labels permutation32 permutation4
    mixedMoment B raw2127step0 raw2127step0Labels = mixedMoment B raw2127step1 raw2127step1Labels := by
      have ha : raw2127step1 = raw2127step0 := by apply Matrix.ext; unfold raw2127step1 raw2127step0; decide +kernel
      have hl : raw2127step0Labels = labelEmbedding7 ∘ raw2127step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2127step0 raw2127step0Labels raw2127step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2128 raw2128Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw2128 raw2128Labels = mixedMoment B raw2128step0 raw2128step0Labels := by
      have ha : raw2128step0 = (fun i j => raw2128 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2128step0 raw2128; decide +kernel
      have hl : raw2128step0Labels = raw2128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2128 raw2128Labels permutation32 permutation4
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2129 raw2129Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw2129 raw2129Labels = mixedMoment B raw2129step0 raw2129step0Labels := by
      have ha : raw2129step0 = (fun i j => raw2129 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2129step0 raw2129; decide +kernel
      have hl : raw2129step0Labels = raw2129Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2129 raw2129Labels permutation33 permutation6
    mixedMoment B raw2129step0 raw2129step0Labels = mixedMoment B raw2129step1 raw2129step1Labels := by
      have ha : raw2129step1 = -raw2129step0 := by apply Matrix.ext; change ∀ i j, raw2129step1 i j = -(raw2129step0 i j); unfold raw2129step1 raw2129step0; decide +kernel
      have hl : raw2129step1Labels = raw2129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2129step1 raw2129step1Labels = mixedMoment B raw2129step2 raw2129step2Labels := by
      have ha : raw2129step2 = raw2129step1 := by apply Matrix.ext; unfold raw2129step2 raw2129step1; decide +kernel
      have hl : raw2129step1Labels = labelEmbedding1 ∘ raw2129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2129step1 raw2129step1Labels raw2129step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

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

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2286 raw2286Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2286 raw2286Labels = mixedMoment B raw2286step0 raw2286step0Labels := by
      have ha : raw2286step0 = (fun i j => raw2286 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2286step0 raw2286; decide +kernel
      have hl : raw2286step0Labels = raw2286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2286 raw2286Labels permutation8 permutation4
    mixedMoment B raw2286step0 raw2286step0Labels = mixedMoment B raw2286step1 raw2286step1Labels := by
      have ha : raw2286step1 = raw2286step0 := by apply Matrix.ext; unfold raw2286step1 raw2286step0; decide +kernel
      have hl : raw2286step0Labels = labelEmbedding7 ∘ raw2286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2286step0 raw2286step0Labels raw2286step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2287 raw2287Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2287 raw2287Labels = mixedMoment B raw2287step0 raw2287step0Labels := by
      have ha : raw2287step0 = (fun i j => raw2287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2287step0 raw2287; decide +kernel
      have hl : raw2287step0Labels = raw2287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2287 raw2287Labels permutation8 permutation4
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2288 raw2288Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw2288 raw2288Labels = mixedMoment B raw2288step0 raw2288step0Labels := by
      have ha : raw2288step0 = (fun i j => raw2288 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2288step0 raw2288; decide +kernel
      have hl : raw2288step0Labels = raw2288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2288 raw2288Labels permutation9 permutation6
    mixedMoment B raw2288step0 raw2288step0Labels = mixedMoment B raw2288step1 raw2288step1Labels := by
      have ha : raw2288step1 = -raw2288step0 := by apply Matrix.ext; change ∀ i j, raw2288step1 i j = -(raw2288step0 i j); unfold raw2288step1 raw2288step0; decide +kernel
      have hl : raw2288step1Labels = raw2288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2288step1 raw2288step1Labels = mixedMoment B raw2288step2 raw2288step2Labels := by
      have ha : raw2288step2 = raw2288step1 := by apply Matrix.ext; unfold raw2288step2 raw2288step1; decide +kernel
      have hl : raw2288step1Labels = labelEmbedding1 ∘ raw2288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2288step1 raw2288step1Labels raw2288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

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

theorem canonical2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2385 raw2385Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw2385 raw2385Labels = mixedMoment B raw2385step0 raw2385step0Labels := by
      have ha : raw2385step0 = (fun i j => raw2385 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2385step0 raw2385; decide +kernel
      have hl : raw2385step0Labels = raw2385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2385 raw2385Labels permutation152 permutation4
    mixedMoment B raw2385step0 raw2385step0Labels = mixedMoment B raw2385step1 raw2385step1Labels := by
      have ha : raw2385step1 = raw2385step0 := by apply Matrix.ext; unfold raw2385step1 raw2385step0; decide +kernel
      have hl : raw2385step0Labels = labelEmbedding7 ∘ raw2385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2385step0 raw2385step0Labels raw2385step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical2386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2386 raw2386Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw2386 raw2386Labels = mixedMoment B raw2386step0 raw2386step0Labels := by
      have ha : raw2386step0 = (fun i j => raw2386 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2386step0 raw2386; decide +kernel
      have hl : raw2386step0Labels = raw2386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2386 raw2386Labels permutation152 permutation4
    _ = mixedMoment B node3683 node3683Labels := by rfl

theorem canonical2387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2387 raw2387Labels = mixedMoment B node3746 node3746Labels := by
  calc
    mixedMoment B raw2387 raw2387Labels = mixedMoment B raw2387step0 raw2387step0Labels := by
      have ha : raw2387step0 = (fun i j => raw2387 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2387step0 raw2387; decide +kernel
      have hl : raw2387step0Labels = raw2387Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2387 raw2387Labels permutation153 permutation6
    mixedMoment B raw2387step0 raw2387step0Labels = mixedMoment B raw2387step1 raw2387step1Labels := by
      have ha : raw2387step1 = -raw2387step0 := by apply Matrix.ext; change ∀ i j, raw2387step1 i j = -(raw2387step0 i j); unfold raw2387step1 raw2387step0; decide +kernel
      have hl : raw2387step1Labels = raw2387step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2387step1 raw2387step1Labels = mixedMoment B raw2387step2 raw2387step2Labels := by
      have ha : raw2387step2 = raw2387step1 := by apply Matrix.ext; unfold raw2387step2 raw2387step1; decide +kernel
      have hl : raw2387step1Labels = labelEmbedding1 ∘ raw2387step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2387step1 raw2387step1Labels raw2387step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3746 node3746Labels := by rfl

theorem canonical2415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2415 raw2415Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw2415 raw2415Labels = mixedMoment B raw2415step0 raw2415step0Labels := by
      have ha : raw2415step0 = (fun i j => raw2415 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2415step0 raw2415; decide +kernel
      have hl : raw2415step0Labels = raw2415Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2415 raw2415Labels permutation32 permutation4
    mixedMoment B raw2415step0 raw2415step0Labels = mixedMoment B raw2415step1 raw2415step1Labels := by
      have ha : raw2415step1 = raw2415step0 := by apply Matrix.ext; unfold raw2415step1 raw2415step0; decide +kernel
      have hl : raw2415step0Labels = labelEmbedding7 ∘ raw2415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2415step0 raw2415step0Labels raw2415step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical2416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2416 raw2416Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw2416 raw2416Labels = mixedMoment B raw2416step0 raw2416step0Labels := by
      have ha : raw2416step0 = (fun i j => raw2416 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2416step0 raw2416; decide +kernel
      have hl : raw2416step0Labels = raw2416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2416 raw2416Labels permutation32 permutation4
    _ = mixedMoment B node3705 node3705Labels := by rfl

theorem canonical2417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2417 raw2417Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw2417 raw2417Labels = mixedMoment B raw2417step0 raw2417step0Labels := by
      have ha : raw2417step0 = (fun i j => raw2417 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2417step0 raw2417; decide +kernel
      have hl : raw2417step0Labels = raw2417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2417 raw2417Labels permutation33 permutation6
    mixedMoment B raw2417step0 raw2417step0Labels = mixedMoment B raw2417step1 raw2417step1Labels := by
      have ha : raw2417step1 = -raw2417step0 := by apply Matrix.ext; change ∀ i j, raw2417step1 i j = -(raw2417step0 i j); unfold raw2417step1 raw2417step0; decide +kernel
      have hl : raw2417step1Labels = raw2417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2417step1 raw2417step1Labels = mixedMoment B raw2417step2 raw2417step2Labels := by
      have ha : raw2417step2 = raw2417step1 := by apply Matrix.ext; unfold raw2417step2 raw2417step1; decide +kernel
      have hl : raw2417step1Labels = labelEmbedding1 ∘ raw2417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2417step1 raw2417step1Labels raw2417step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

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

theorem canonical2580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2580 raw2580Labels = mixedMoment B node5467 node5467Labels := by
  calc
    mixedMoment B raw2580 raw2580Labels = mixedMoment B raw2580step0 raw2580step0Labels := by
      have ha : raw2580step0 = (fun i j => raw2580 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2580step0 raw2580; decide +kernel
      have hl : raw2580step0Labels = raw2580Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2580 raw2580Labels permutation152 permutation4
    mixedMoment B raw2580step0 raw2580step0Labels = mixedMoment B raw2580step1 raw2580step1Labels := by
      have ha : raw2580step1 = raw2580step0 := by apply Matrix.ext; unfold raw2580step1 raw2580step0; decide +kernel
      have hl : raw2580step0Labels = labelEmbedding7 ∘ raw2580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2580step0 raw2580step0Labels raw2580step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5467 node5467Labels := by rfl

theorem canonical2581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2581 raw2581Labels = mixedMoment B node3942 node3942Labels := by
  calc
    mixedMoment B raw2581 raw2581Labels = mixedMoment B raw2581step0 raw2581step0Labels := by
      have ha : raw2581step0 = (fun i j => raw2581 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2581step0 raw2581; decide +kernel
      have hl : raw2581step0Labels = raw2581Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2581 raw2581Labels permutation152 permutation4
    _ = mixedMoment B node3942 node3942Labels := by rfl

theorem canonical2582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2582 raw2582Labels = mixedMoment B node3942 node3942Labels := by
  calc
    mixedMoment B raw2582 raw2582Labels = mixedMoment B raw2582step0 raw2582step0Labels := by
      have ha : raw2582step0 = (fun i j => raw2582 (permutation588 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2582step0 raw2582; decide +kernel
      have hl : raw2582step0Labels = raw2582Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2582 raw2582Labels permutation588 permutation6
    mixedMoment B raw2582step0 raw2582step0Labels = mixedMoment B raw2582step1 raw2582step1Labels := by
      have ha : raw2582step1 = raw2582step0 := by apply Matrix.ext; unfold raw2582step1 raw2582step0; decide +kernel
      have hl : raw2582step0Labels = labelEmbedding1 ∘ raw2582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2582step0 raw2582step0Labels raw2582step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3942 node3942Labels := by rfl

theorem canonical2583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2583 raw2583Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw2583 raw2583Labels = mixedMoment B raw2583step0 raw2583step0Labels := by
      have ha : raw2583step0 = (fun i j => raw2583 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2583step0 raw2583; decide +kernel
      have hl : raw2583step0Labels = raw2583Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2583 raw2583Labels permutation152 permutation4
    mixedMoment B raw2583step0 raw2583step0Labels = mixedMoment B raw2583step1 raw2583step1Labels := by
      have ha : raw2583step1 = raw2583step0 := by apply Matrix.ext; unfold raw2583step1 raw2583step0; decide +kernel
      have hl : raw2583step0Labels = labelEmbedding7 ∘ raw2583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2583step0 raw2583step0Labels raw2583step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2584 raw2584Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw2584 raw2584Labels = mixedMoment B raw2584step0 raw2584step0Labels := by
      have ha : raw2584step0 = (fun i j => raw2584 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2584step0 raw2584; decide +kernel
      have hl : raw2584step0Labels = raw2584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2584 raw2584Labels permutation152 permutation4
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2585 raw2585Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw2585 raw2585Labels = mixedMoment B raw2585step0 raw2585step0Labels := by
      have ha : raw2585step0 = (fun i j => raw2585 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2585step0 raw2585; decide +kernel
      have hl : raw2585step0Labels = raw2585Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2585 raw2585Labels permutation265 permutation6
    mixedMoment B raw2585step0 raw2585step0Labels = mixedMoment B raw2585step1 raw2585step1Labels := by
      have ha : raw2585step1 = -raw2585step0 := by apply Matrix.ext; change ∀ i j, raw2585step1 i j = -(raw2585step0 i j); unfold raw2585step1 raw2585step0; decide +kernel
      have hl : raw2585step1Labels = raw2585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2585step1 raw2585step1Labels = mixedMoment B raw2585step2 raw2585step2Labels := by
      have ha : raw2585step2 = raw2585step1 := by apply Matrix.ext; unfold raw2585step2 raw2585step1; decide +kernel
      have hl : raw2585step1Labels = labelEmbedding1 ∘ raw2585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2585step1 raw2585step1Labels raw2585step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

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

theorem canonical2592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2592 raw2592Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw2592 raw2592Labels = mixedMoment B raw2592step0 raw2592step0Labels := by
      have ha : raw2592step0 = (fun i j => raw2592 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2592step0 raw2592; decide +kernel
      have hl : raw2592step0Labels = raw2592Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2592 raw2592Labels permutation8 permutation4
    mixedMoment B raw2592step0 raw2592step0Labels = mixedMoment B raw2592step1 raw2592step1Labels := by
      have ha : raw2592step1 = raw2592step0 := by apply Matrix.ext; unfold raw2592step1 raw2592step0; decide +kernel
      have hl : raw2592step0Labels = labelEmbedding7 ∘ raw2592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2592step0 raw2592step0Labels raw2592step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

theorem canonical2593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2593 raw2593Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2593 raw2593Labels = mixedMoment B raw2593step0 raw2593step0Labels := by
      have ha : raw2593step0 = (fun i j => raw2593 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2593step0 raw2593; decide +kernel
      have hl : raw2593step0Labels = raw2593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2593 raw2593Labels permutation8 permutation4
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical2594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2594 raw2594Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2594 raw2594Labels = mixedMoment B raw2594step0 raw2594step0Labels := by
      have ha : raw2594step0 = (fun i j => raw2594 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2594step0 raw2594; decide +kernel
      have hl : raw2594step0Labels = raw2594Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2594 raw2594Labels permutation24 permutation6
    mixedMoment B raw2594step0 raw2594step0Labels = mixedMoment B raw2594step1 raw2594step1Labels := by
      have ha : raw2594step1 = raw2594step0 := by apply Matrix.ext; unfold raw2594step1 raw2594step0; decide +kernel
      have hl : raw2594step0Labels = labelEmbedding1 ∘ raw2594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2594step0 raw2594step0Labels raw2594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

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

theorem canonical2616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2616 raw2616Labels = mixedMoment B node5491 node5491Labels := by
  calc
    _ = mixedMoment B node5491 node5491Labels := by rfl

theorem canonical2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2617 raw2617Labels = mixedMoment B node4014 node4014Labels := by
  calc
    _ = mixedMoment B node4014 node4014Labels := by rfl

theorem canonical2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2618 raw2618Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw2618 raw2618Labels = mixedMoment B raw2618step0 raw2618step0Labels := by
      have ha : raw2618step0 = (fun i j => raw2618 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2618step0 raw2618; decide +kernel
      have hl : raw2618step0Labels = raw2618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2618 raw2618Labels permutation10 permutation3
    mixedMoment B raw2618step0 raw2618step0Labels = mixedMoment B raw2618step1 raw2618step1Labels := by
      have ha : raw2618step1 = raw2618step0 := by apply Matrix.ext; unfold raw2618step1 raw2618step0; decide +kernel
      have hl : raw2618step0Labels = labelEmbedding1 ∘ raw2618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2618step0 raw2618step0Labels raw2618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

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

theorem canonical626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw626 raw626Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw626 raw626Labels = mixedMoment B raw626step0 raw626step0Labels := by
      have ha : raw626step0 = (fun i j => raw626 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw626step0 raw626; decide +kernel
      have hl : raw626step0Labels = raw626Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw626 raw626Labels permutation8 permutation5
    mixedMoment B raw626step0 raw626step0Labels = mixedMoment B raw626step1 raw626step1Labels := by
      have ha : raw626step1 = raw626step0 := by apply Matrix.ext; unfold raw626step1 raw626step0; decide +kernel
      have hl : raw626step0Labels = labelEmbedding1 ∘ raw626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw626step0 raw626step0Labels raw626step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

theorem canonical627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw627 raw627Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw627 raw627Labels = mixedMoment B raw627step0 raw627step0Labels := by
      have ha : raw627step0 = (fun i j => raw627 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw627step0 raw627; decide +kernel
      have hl : raw627step0Labels = raw627Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw627 raw627Labels permutation10 permutation4
    _ = mixedMoment B node527 node527Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10451 raw10451Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw10451 raw10451Labels = mixedMoment B raw10451step0 raw10451step0Labels := by
      have hz : ∀ j, raw10451 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10451step0 = (fun i j => raw10451 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10451step0 raw10451; decide +kernel
      have hl : raw10451step0Labels = raw10451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10451 raw10451Labels permutation265 hz
    mixedMoment B raw10451step0 raw10451step0Labels = mixedMoment B raw10451step1 raw10451step1Labels := by
      have ha : raw10451step1 = (fun i j => raw10451step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10451step1 raw10451step0; decide +kernel
      have hl : raw10451step1Labels = raw10451step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10451step0 raw10451step0Labels permutation151 permutation3
    mixedMoment B raw10451step1 raw10451step1Labels = mixedMoment B raw10451step2 raw10451step2Labels := by
      have ha : raw10451step2 = -raw10451step1 := by apply Matrix.ext; change ∀ i j, raw10451step2 i j = -(raw10451step1 i j); unfold raw10451step2 raw10451step1; decide +kernel
      have hl : raw10451step2Labels = raw10451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10451step2 raw10451step2Labels = mixedMoment B raw10451step3 raw10451step3Labels := by
      have ha : raw10451step3 = raw10451step2 := by apply Matrix.ext; unfold raw10451step3 raw10451step2; decide +kernel
      have hl : raw10451step2Labels = labelEmbedding6 ∘ raw10451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10451step2 raw10451step2Labels raw10451step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical10452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10452 raw10452Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw10452 raw10452Labels = mixedMoment B raw10452step0 raw10452step0Labels := by
      have hz : ∀ j, raw10452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10452step0 = (fun i j => raw10452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10452step0 raw10452; decide +kernel
      have hl : raw10452step0Labels = raw10452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10452 raw10452Labels permutation346 hz
    mixedMoment B raw10452step0 raw10452step0Labels = mixedMoment B raw10452step1 raw10452step1Labels := by
      have hz : ∀ j, raw10452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10452step1 = (fun i j => raw10452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10452step1 raw10452step0; decide +kernel
      have hl : raw10452step1Labels = raw10452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10452step0 raw10452step0Labels permutation56 hz
    mixedMoment B raw10452step1 raw10452step1Labels = mixedMoment B raw10452step2 raw10452step2Labels := by
      have ha : raw10452step2 = (fun i j => raw10452step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10452step2 raw10452step1; decide +kernel
      have hl : raw10452step2Labels = raw10452step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10452step1 raw10452step1Labels permutation8 permutation3
    mixedMoment B raw10452step2 raw10452step2Labels = mixedMoment B raw10452step3 raw10452step3Labels := by
      have ha : raw10452step3 = raw10452step2 := by apply Matrix.ext; unfold raw10452step3 raw10452step2; decide +kernel
      have hl : raw10452step2Labels = labelEmbedding6 ∘ raw10452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10452step2 raw10452step2Labels raw10452step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

theorem canonical10453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10453 raw10453Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw10453 raw10453Labels = mixedMoment B raw10453step0 raw10453step0Labels := by
      have hz : ∀ j, raw10453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10453step0 = (fun i j => raw10453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10453step0 raw10453; decide +kernel
      have hl : raw10453step0Labels = raw10453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10453 raw10453Labels permutation346 hz
    mixedMoment B raw10453step0 raw10453step0Labels = mixedMoment B raw10453step1 raw10453step1Labels := by
      have hz : ∀ j, raw10453step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10453step1 = (fun i j => raw10453step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10453step1 raw10453step0; decide +kernel
      have hl : raw10453step1Labels = raw10453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10453step0 raw10453step0Labels permutation56 hz
    mixedMoment B raw10453step1 raw10453step1Labels = mixedMoment B raw10453step2 raw10453step2Labels := by
      have ha : raw10453step2 = (fun i j => raw10453step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10453step2 raw10453step1; decide +kernel
      have hl : raw10453step2Labels = raw10453step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10453step1 raw10453step1Labels permutation10 permutation2
    _ = mixedMoment B node5491 node5491Labels := by rfl

theorem canonical10454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10454 raw10454Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw10454 raw10454Labels = mixedMoment B raw10454step0 raw10454step0Labels := by
      have hz : ∀ j, raw10454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10454step0 = (fun i j => raw10454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10454step0 raw10454; decide +kernel
      have hl : raw10454step0Labels = raw10454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10454 raw10454Labels permutation346 hz
    mixedMoment B raw10454step0 raw10454step0Labels = mixedMoment B raw10454step1 raw10454step1Labels := by
      have hz : ∀ j, raw10454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10454step1 = (fun i j => raw10454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10454step1 raw10454step0; decide +kernel
      have hl : raw10454step1Labels = raw10454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10454step0 raw10454step0Labels permutation56 hz
    mixedMoment B raw10454step1 raw10454step1Labels = mixedMoment B raw10454step2 raw10454step2Labels := by
      have ha : raw10454step2 = (fun i j => raw10454step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10454step2 raw10454step1; decide +kernel
      have hl : raw10454step2Labels = raw10454step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10454step1 raw10454step1Labels permutation9 permutation3
    mixedMoment B raw10454step2 raw10454step2Labels = mixedMoment B raw10454step3 raw10454step3Labels := by
      have ha : raw10454step3 = raw10454step2 := by apply Matrix.ext; unfold raw10454step3 raw10454step2; decide +kernel
      have hl : raw10454step2Labels = labelEmbedding6 ∘ raw10454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10454step2 raw10454step2Labels raw10454step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical10461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10461 raw10461Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw10461 raw10461Labels = mixedMoment B raw10461step0 raw10461step0Labels := by
      have ha : raw10461step0 = (fun i j => raw10461 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10461step0 raw10461; decide +kernel
      have hl : raw10461step0Labels = raw10461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10461 raw10461Labels permutation158 permutation3
    mixedMoment B raw10461step0 raw10461step0Labels = mixedMoment B raw10461step1 raw10461step1Labels := by
      have ha : raw10461step1 = raw10461step0 := by apply Matrix.ext; unfold raw10461step1 raw10461step0; decide +kernel
      have hl : raw10461step0Labels = labelEmbedding6 ∘ raw10461step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10461step0 raw10461step0Labels raw10461step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

theorem canonical10466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10466 raw10466Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw10466 raw10466Labels = mixedMoment B raw10466step0 raw10466step0Labels := by
      have hz : ∀ j, raw10466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10466step0 = (fun i j => raw10466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10466step0 raw10466; decide +kernel
      have hl : raw10466step0Labels = raw10466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10466 raw10466Labels permutation346 hz
    mixedMoment B raw10466step0 raw10466step0Labels = mixedMoment B raw10466step1 raw10466step1Labels := by
      have ha : raw10466step1 = (fun i j => raw10466step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10466step1 raw10466step0; decide +kernel
      have hl : raw10466step1Labels = raw10466step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10466step0 raw10466step0Labels permutation32 permutation3
    mixedMoment B raw10466step1 raw10466step1Labels = mixedMoment B raw10466step2 raw10466step2Labels := by
      have ha : raw10466step2 = raw10466step1 := by apply Matrix.ext; unfold raw10466step2 raw10466step1; decide +kernel
      have hl : raw10466step1Labels = labelEmbedding6 ∘ raw10466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10466step1 raw10466step1Labels raw10466step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical10471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10471 raw10471Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw10471 raw10471Labels = mixedMoment B raw10471step0 raw10471step0Labels := by
      have hz : ∀ j, raw10471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10471step0 = (fun i j => raw10471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10471step0 raw10471; decide +kernel
      have hl : raw10471step0Labels = raw10471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10471 raw10471Labels permutation346 hz
    mixedMoment B raw10471step0 raw10471step0Labels = mixedMoment B raw10471step1 raw10471step1Labels := by
      have ha : raw10471step1 = (fun i j => raw10471step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10471step1 raw10471step0; decide +kernel
      have hl : raw10471step1Labels = raw10471step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10471step0 raw10471step0Labels permutation127 permutation5
    mixedMoment B raw10471step1 raw10471step1Labels = mixedMoment B raw10471step2 raw10471step2Labels := by
      have ha : raw10471step2 = raw10471step1 := by apply Matrix.ext; unfold raw10471step2 raw10471step1; decide +kernel
      have hl : raw10471step1Labels = labelEmbedding8 ∘ raw10471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10471step1 raw10471step1Labels raw10471step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

theorem canonical10476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10476 raw10476Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw10476 raw10476Labels = mixedMoment B raw10476step0 raw10476step0Labels := by
      have hz : ∀ j, raw10476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10476step0 = (fun i j => raw10476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10476step0 raw10476; decide +kernel
      have hl : raw10476step0Labels = raw10476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10476 raw10476Labels permutation346 hz
    mixedMoment B raw10476step0 raw10476step0Labels = mixedMoment B raw10476step1 raw10476step1Labels := by
      have ha : raw10476step1 = (fun i j => raw10476step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10476step1 raw10476step0; decide +kernel
      have hl : raw10476step1Labels = raw10476step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10476step0 raw10476step0Labels permutation151 permutation3
    mixedMoment B raw10476step1 raw10476step1Labels = mixedMoment B raw10476step2 raw10476step2Labels := by
      have ha : raw10476step2 = -raw10476step1 := by apply Matrix.ext; change ∀ i j, raw10476step2 i j = -(raw10476step1 i j); unfold raw10476step2 raw10476step1; decide +kernel
      have hl : raw10476step2Labels = raw10476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10476step2 raw10476step2Labels = mixedMoment B raw10476step3 raw10476step3Labels := by
      have ha : raw10476step3 = raw10476step2 := by apply Matrix.ext; unfold raw10476step3 raw10476step2; decide +kernel
      have hl : raw10476step2Labels = labelEmbedding6 ∘ raw10476step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10476step2 raw10476step2Labels raw10476step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4943 = injectiveMoment H node227 := by
  rfl

theorem canonical4950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4950 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw4950 = injectiveMoment H raw4950step0 := by
      have heq : raw4950step0 = raw4950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4950).symm
    injectiveMoment H raw4950step0 = injectiveMoment H raw4950step1 := by
      have hz : ∀ i, raw4950step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4950step1 = (fun i j => raw4950step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4950step0 permutation5 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
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

theorem canonical7731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7731 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7731 = injectiveMoment H raw7731step0 := by
      have heq : raw7731step0 = (fun i j => raw7731 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7731 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node227 = Sparse.eval value227 (momentVector H) := by
  have heq : pivotMatrix227 = (fun u v => node227 (pivotPermutation227 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node227 = injectiveMoment H pivotMatrix227 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix227 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix227 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (1 : Fin 3) = raw4950 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4950 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (2 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node227 + (injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value227, value11, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node527 node527Labels = Sparse.eval singlePairValue527 (familyPairVector B) := by
  have hp := single_label_three B hB node527
  have hl : node527Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node527 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node527 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node527 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 3) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node527 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value227 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 4) = PairSemantics.raw4943 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node527 PairSemantics.raw4943; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4943 hH).trans (PairSemantics.sound227 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue527, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value227, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4014 node4014Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node527 node527Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw626 singletonSmall4014
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4014) = raw626Labels := by decide +kernel
  rw [hl, canonical626 B hB] at h
  have hc0 : mixedMoment B raw626 (Fin.cases (0 : Fin 1) singletonSmall4014) =
      mixedMoment B node527 node527Labels := by
    have ha : raw626 = raw627 := by apply Matrix.ext; unfold raw626 raw627; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4014 = raw627Labels := by decide +kernel
    rw [ha, hj, canonical627 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4998 node4998Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2383 node2383Labels + mixedMoment B node3352 node3352Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2010 singletonSmall4998
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4998) = raw2010Labels := by decide +kernel
  rw [hl, canonical2010 B hB] at h
  have hc0 : mixedMoment B raw2010 (Fin.cases (0 : Fin 2) singletonSmall4998) =
      mixedMoment B node2383 node2383Labels := by
    have ha : raw2010 = raw2011 := by apply Matrix.ext; unfold raw2010 raw2011; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4998 = raw2011Labels := by decide +kernel
    rw [ha, hj, canonical2011 B hB]
  have hc1 : mixedMoment B raw2010 (Fin.cases (1 : Fin 2) singletonSmall4998) =
      mixedMoment B node3352 node3352Labels := by
    have ha : raw2010 = raw2012 := by apply Matrix.ext; unfold raw2010 raw2012; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4998 = raw2012Labels := by decide +kernel
    rw [ha, hj, canonical2012 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5000 node5000Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2385 node2385Labels + mixedMoment B node3353 node3353Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2013 singletonSmall5000
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5000) = raw2013Labels := by decide +kernel
  rw [hl, canonical2013 B hB] at h
  have hc0 : mixedMoment B raw2013 (Fin.cases (0 : Fin 2) singletonSmall5000) =
      mixedMoment B node2385 node2385Labels := by
    have ha : raw2013 = raw2014 := by apply Matrix.ext; unfold raw2013 raw2014; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5000 = raw2014Labels := by decide +kernel
    rw [ha, hj, canonical2014 B hB]
  have hc1 : mixedMoment B raw2013 (Fin.cases (1 : Fin 2) singletonSmall5000) =
      mixedMoment B node3353 node3353Labels := by
    have ha : raw2013 = raw2015 := by apply Matrix.ext; unfold raw2013 raw2015; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5000 = raw2015Labels := by decide +kernel
    rw [ha, hj, canonical2015 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5003 node5003Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2388 node2388Labels + mixedMoment B node3354 node3354Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2016 singletonSmall5003
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5003) = raw2016Labels := by decide +kernel
  rw [hl, canonical2016 B hB] at h
  have hc0 : mixedMoment B raw2016 (Fin.cases (0 : Fin 2) singletonSmall5003) =
      mixedMoment B node2388 node2388Labels := by
    have ha : raw2016 = raw2017 := by apply Matrix.ext; unfold raw2016 raw2017; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5003 = raw2017Labels := by decide +kernel
    rw [ha, hj, canonical2017 B hB]
  have hc1 : mixedMoment B raw2016 (Fin.cases (1 : Fin 2) singletonSmall5003) =
      mixedMoment B node3354 node3354Labels := by
    have ha : raw2016 = raw2018 := by apply Matrix.ext; unfold raw2016 raw2018; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5003 = raw2018Labels := by decide +kernel
    rw [ha, hj, canonical2018 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5013 node5013Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2398 node2398Labels + mixedMoment B node3341 node3341Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2019 singletonSmall5013
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5013) = raw2019Labels := by decide +kernel
  rw [hl, canonical2019 B hB] at h
  have hc0 : mixedMoment B raw2019 (Fin.cases (0 : Fin 2) singletonSmall5013) =
      mixedMoment B node2398 node2398Labels := by
    have ha : raw2019 = raw2020 := by apply Matrix.ext; unfold raw2019 raw2020; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5013 = raw2020Labels := by decide +kernel
    rw [ha, hj, canonical2020 B hB]
  have hc1 : mixedMoment B raw2019 (Fin.cases (1 : Fin 2) singletonSmall5013) =
      mixedMoment B node3341 node3341Labels := by
    have ha : raw2019 = raw2021 := by apply Matrix.ext; unfold raw2019 raw2021; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5013 = raw2021Labels := by decide +kernel
    rw [ha, hj, canonical2021 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5014 node5014Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2399 node2399Labels + mixedMoment B node2467 node2467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2022 singletonSmall5014
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5014) = raw2022Labels := by decide +kernel
  rw [hl, canonical2022 B hB] at h
  have hc0 : mixedMoment B raw2022 (Fin.cases (0 : Fin 2) singletonSmall5014) =
      mixedMoment B node2399 node2399Labels := by
    have ha : raw2022 = raw2023 := by apply Matrix.ext; unfold raw2022 raw2023; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5014 = raw2023Labels := by decide +kernel
    rw [ha, hj, canonical2023 B hB]
  have hc1 : mixedMoment B raw2022 (Fin.cases (1 : Fin 2) singletonSmall5014) =
      mixedMoment B node2467 node2467Labels := by
    have ha : raw2022 = raw2024 := by apply Matrix.ext; unfold raw2022 raw2024; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5014 = raw2024Labels := by decide +kernel
    rw [ha, hj, canonical2024 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5015 node5015Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2400 node2400Labels + mixedMoment B node3344 node3344Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2025 singletonSmall5015
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5015) = raw2025Labels := by decide +kernel
  rw [hl, canonical2025 B hB] at h
  have hc0 : mixedMoment B raw2025 (Fin.cases (0 : Fin 2) singletonSmall5015) =
      mixedMoment B node2400 node2400Labels := by
    have ha : raw2025 = raw2026 := by apply Matrix.ext; unfold raw2025 raw2026; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5015 = raw2026Labels := by decide +kernel
    rw [ha, hj, canonical2026 B hB]
  have hc1 : mixedMoment B raw2025 (Fin.cases (1 : Fin 2) singletonSmall5015) =
      mixedMoment B node3344 node3344Labels := by
    have ha : raw2025 = raw2027 := by apply Matrix.ext; unfold raw2025 raw2027; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5015 = raw2027Labels := by decide +kernel
    rw [ha, hj, canonical2027 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5018 node5018Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2404 node2404Labels + mixedMoment B node3357 node3357Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2028 singletonSmall5018
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5018) = raw2028Labels := by decide +kernel
  rw [hl, canonical2028 B hB] at h
  have hc0 : mixedMoment B raw2028 (Fin.cases (0 : Fin 2) singletonSmall5018) =
      mixedMoment B node2404 node2404Labels := by
    have ha : raw2028 = raw2029 := by apply Matrix.ext; unfold raw2028 raw2029; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5018 = raw2029Labels := by decide +kernel
    rw [ha, hj, canonical2029 B hB]
  have hc1 : mixedMoment B raw2028 (Fin.cases (1 : Fin 2) singletonSmall5018) =
      mixedMoment B node3357 node3357Labels := by
    have ha : raw2028 = raw2030 := by apply Matrix.ext; unfold raw2028 raw2030; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5018 = raw2030Labels := by decide +kernel
    rw [ha, hj, canonical2030 B hB]
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

theorem singleton5059 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5059 node5059Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2462 node2462Labels + mixedMoment B node3436 node3436Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2085 singletonSmall5059
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5059) = raw2085Labels := by decide +kernel
  rw [hl, canonical2085 B hB] at h
  have hc0 : mixedMoment B raw2085 (Fin.cases (0 : Fin 2) singletonSmall5059) =
      mixedMoment B node2462 node2462Labels := by
    have ha : raw2085 = raw2086 := by apply Matrix.ext; unfold raw2085 raw2086; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5059 = raw2086Labels := by decide +kernel
    rw [ha, hj, canonical2086 B hB]
  have hc1 : mixedMoment B raw2085 (Fin.cases (1 : Fin 2) singletonSmall5059) =
      mixedMoment B node3436 node3436Labels := by
    have ha : raw2085 = raw2087 := by apply Matrix.ext; unfold raw2085 raw2087; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5059 = raw2087Labels := by decide +kernel
    rw [ha, hj, canonical2087 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5102 node5102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2512 node2512Labels + mixedMoment B node3471 node3471Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2127 singletonSmall5102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5102) = raw2127Labels := by decide +kernel
  rw [hl, canonical2127 B hB] at h
  have hc0 : mixedMoment B raw2127 (Fin.cases (0 : Fin 2) singletonSmall5102) =
      mixedMoment B node2512 node2512Labels := by
    have ha : raw2127 = raw2128 := by apply Matrix.ext; unfold raw2127 raw2128; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5102 = raw2128Labels := by decide +kernel
    rw [ha, hj, canonical2128 B hB]
  have hc1 : mixedMoment B raw2127 (Fin.cases (1 : Fin 2) singletonSmall5102) =
      mixedMoment B node3471 node3471Labels := by
    have ha : raw2127 = raw2129 := by apply Matrix.ext; unfold raw2127 raw2129; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5102 = raw2129Labels := by decide +kernel
    rw [ha, hj, canonical2129 B hB]
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

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5275 node5275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2743 node2743Labels + mixedMoment B node3548 node3548Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2286 singletonSmall5275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5275) = raw2286Labels := by decide +kernel
  rw [hl, canonical2286 B hB] at h
  have hc0 : mixedMoment B raw2286 (Fin.cases (0 : Fin 2) singletonSmall5275) =
      mixedMoment B node2743 node2743Labels := by
    have ha : raw2286 = raw2287 := by apply Matrix.ext; unfold raw2286 raw2287; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5275 = raw2287Labels := by decide +kernel
    rw [ha, hj, canonical2287 B hB]
  have hc1 : mixedMoment B raw2286 (Fin.cases (1 : Fin 2) singletonSmall5275) =
      mixedMoment B node3548 node3548Labels := by
    have ha : raw2286 = raw2288 := by apply Matrix.ext; unfold raw2286 raw2288; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5275 = raw2288Labels := by decide +kernel
    rw [ha, hj, canonical2288 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton5346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5346 node5346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3683 node3683Labels + mixedMoment B node3746 node3746Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2385 singletonSmall5346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5346) = raw2385Labels := by decide +kernel
  rw [hl, canonical2385 B hB] at h
  have hc0 : mixedMoment B raw2385 (Fin.cases (0 : Fin 2) singletonSmall5346) =
      mixedMoment B node3683 node3683Labels := by
    have ha : raw2385 = raw2386 := by apply Matrix.ext; unfold raw2385 raw2386; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5346 = raw2386Labels := by decide +kernel
    rw [ha, hj, canonical2386 B hB]
  have hc1 : mixedMoment B raw2385 (Fin.cases (1 : Fin 2) singletonSmall5346) =
      mixedMoment B node3746 node3746Labels := by
    have ha : raw2385 = raw2387 := by apply Matrix.ext; unfold raw2385 raw2387; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5346 = raw2387Labels := by decide +kernel
    rw [ha, hj, canonical2387 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5368 node5368Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3705 node3705Labels + mixedMoment B node3767 node3767Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2415 singletonSmall5368
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5368) = raw2415Labels := by decide +kernel
  rw [hl, canonical2415 B hB] at h
  have hc0 : mixedMoment B raw2415 (Fin.cases (0 : Fin 2) singletonSmall5368) =
      mixedMoment B node3705 node3705Labels := by
    have ha : raw2415 = raw2416 := by apply Matrix.ext; unfold raw2415 raw2416; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5368 = raw2416Labels := by decide +kernel
    rw [ha, hj, canonical2416 B hB]
  have hc1 : mixedMoment B raw2415 (Fin.cases (1 : Fin 2) singletonSmall5368) =
      mixedMoment B node3767 node3767Labels := by
    have ha : raw2415 = raw2417 := by apply Matrix.ext; unfold raw2415 raw2417; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5368 = raw2417Labels := by decide +kernel
    rw [ha, hj, canonical2417 B hB]
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

theorem singleton5467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5467 node5467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3942 node3942Labels + mixedMoment B node3942 node3942Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2580 singletonSmall5467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5467) = raw2580Labels := by decide +kernel
  rw [hl, canonical2580 B hB] at h
  have hc0 : mixedMoment B raw2580 (Fin.cases (0 : Fin 2) singletonSmall5467) =
      mixedMoment B node3942 node3942Labels := by
    have ha : raw2580 = raw2581 := by apply Matrix.ext; unfold raw2580 raw2581; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5467 = raw2581Labels := by decide +kernel
    rw [ha, hj, canonical2581 B hB]
  have hc1 : mixedMoment B raw2580 (Fin.cases (1 : Fin 2) singletonSmall5467) =
      mixedMoment B node3942 node3942Labels := by
    have ha : raw2580 = raw2582 := by apply Matrix.ext; unfold raw2580 raw2582; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5467 = raw2582Labels := by decide +kernel
    rw [ha, hj, canonical2582 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5469 node5469Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3945 node3945Labels + mixedMoment B node3952 node3952Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2583 singletonSmall5469
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5469) = raw2583Labels := by decide +kernel
  rw [hl, canonical2583 B hB] at h
  have hc0 : mixedMoment B raw2583 (Fin.cases (0 : Fin 2) singletonSmall5469) =
      mixedMoment B node3945 node3945Labels := by
    have ha : raw2583 = raw2584 := by apply Matrix.ext; unfold raw2583 raw2584; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5469 = raw2584Labels := by decide +kernel
    rw [ha, hj, canonical2584 B hB]
  have hc1 : mixedMoment B raw2583 (Fin.cases (1 : Fin 2) singletonSmall5469) =
      mixedMoment B node3952 node3952Labels := by
    have ha : raw2583 = raw2585 := by apply Matrix.ext; unfold raw2583 raw2585; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5469 = raw2585Labels := by decide +kernel
    rw [ha, hj, canonical2585 B hB]
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

theorem singleton5475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5475 node5475Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3963 node3963Labels + mixedMoment B node3963 node3963Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2592 singletonSmall5475
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5475) = raw2592Labels := by decide +kernel
  rw [hl, canonical2592 B hB] at h
  have hc0 : mixedMoment B raw2592 (Fin.cases (0 : Fin 2) singletonSmall5475) =
      mixedMoment B node3963 node3963Labels := by
    have ha : raw2592 = raw2593 := by apply Matrix.ext; unfold raw2592 raw2593; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5475 = raw2593Labels := by decide +kernel
    rw [ha, hj, canonical2593 B hB]
  have hc1 : mixedMoment B raw2592 (Fin.cases (1 : Fin 2) singletonSmall5475) =
      mixedMoment B node3963 node3963Labels := by
    have ha : raw2592 = raw2594 := by apply Matrix.ext; unfold raw2592 raw2594; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5475 = raw2594Labels := by decide +kernel
    rw [ha, hj, canonical2594 B hB]
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

theorem singleton5491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5491 node5491Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4014 node4014Labels + mixedMoment B node4014 node4014Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2616 singletonSmall5491
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5491) = raw2616Labels := by decide +kernel
  rw [hl, canonical2616 B hB] at h
  have hc0 : mixedMoment B raw2616 (Fin.cases (0 : Fin 2) singletonSmall5491) =
      mixedMoment B node4014 node4014Labels := by
    have ha : raw2616 = raw2617 := by apply Matrix.ext; unfold raw2616 raw2617; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5491 = raw2617Labels := by decide +kernel
    rw [ha, hj, canonical2617 B hB]
  have hc1 : mixedMoment B raw2616 (Fin.cases (1 : Fin 2) singletonSmall5491) =
      mixedMoment B node4014 node4014Labels := by
    have ha : raw2616 = raw2618 := by apply Matrix.ext; unfold raw2616 raw2618; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5491 = raw2618Labels := by decide +kernel
    rw [ha, hj, canonical2618 B hB]
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

theorem zero5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = 0 := by
  exact mixedMoment_alpha B hF node5477 node5477Labels 2 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2383 node2383Labels = Sparse.eval nodeValue2383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2383) = mixedMoment B node2383 node2383Labels := rfl
  simpa [nodeValue2383, Sparse.eval] using hc.symm

theorem sound2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2385 node2385Labels = Sparse.eval nodeValue2385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2385) = mixedMoment B node2385 node2385Labels := rfl
  simpa [nodeValue2385, Sparse.eval] using hc.symm

theorem sound2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2388 node2388Labels = Sparse.eval nodeValue2388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2388) = mixedMoment B node2388 node2388Labels := rfl
  simpa [nodeValue2388, Sparse.eval] using hc.symm

theorem sound2398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2398 node2398Labels = Sparse.eval nodeValue2398 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2398) = mixedMoment B node2398 node2398Labels := rfl
  simpa [nodeValue2398, Sparse.eval] using hc.symm

theorem sound2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2399 node2399Labels = Sparse.eval nodeValue2399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2399) = mixedMoment B node2399 node2399Labels := rfl
  simpa [nodeValue2399, Sparse.eval] using hc.symm

theorem sound2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2400 node2400Labels = Sparse.eval nodeValue2400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2400) = mixedMoment B node2400 node2400Labels := rfl
  simpa [nodeValue2400, Sparse.eval] using hc.symm

theorem sound2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2404 node2404Labels = Sparse.eval nodeValue2404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2404) = mixedMoment B node2404 node2404Labels := rfl
  simpa [nodeValue2404, Sparse.eval] using hc.symm

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

theorem sound2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2462 node2462Labels = Sparse.eval nodeValue2462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2462) = mixedMoment B node2462 node2462Labels := rfl
  simpa [nodeValue2462, Sparse.eval] using hc.symm

theorem sound2467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2467 node2467Labels = Sparse.eval nodeValue2467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2467) = mixedMoment B node2467 node2467Labels := rfl
  simpa [nodeValue2467, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

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

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3341 node3341Labels = Sparse.eval nodeValue3341 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3341) = mixedMoment B node3341 node3341Labels := rfl
  simpa [nodeValue3341, Sparse.eval] using hc.symm

theorem sound3344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3344 node3344Labels = Sparse.eval nodeValue3344 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3344) = mixedMoment B node3344 node3344Labels := rfl
  simpa [nodeValue3344, Sparse.eval] using hc.symm

theorem sound3352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3352 node3352Labels = Sparse.eval nodeValue3352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3352) = mixedMoment B node3352 node3352Labels := rfl
  simpa [nodeValue3352, Sparse.eval] using hc.symm

theorem sound3353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3353 node3353Labels = Sparse.eval nodeValue3353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3353) = mixedMoment B node3353 node3353Labels := rfl
  simpa [nodeValue3353, Sparse.eval] using hc.symm

theorem sound3354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3354 node3354Labels = Sparse.eval nodeValue3354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3354) = mixedMoment B node3354 node3354Labels := rfl
  simpa [nodeValue3354, Sparse.eval] using hc.symm

theorem sound3357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3357 node3357Labels = Sparse.eval nodeValue3357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3357) = mixedMoment B node3357 node3357Labels := rfl
  simpa [nodeValue3357, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3436 node3436Labels = Sparse.eval nodeValue3436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3436) = mixedMoment B node3436 node3436Labels := rfl
  simpa [nodeValue3436, Sparse.eval] using hc.symm

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

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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

theorem sound3683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3683 node3683Labels = Sparse.eval nodeValue3683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3683) = mixedMoment B node3683 node3683Labels := rfl
  simpa [nodeValue3683, Sparse.eval] using hc.symm

theorem sound3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3705 node3705Labels = Sparse.eval nodeValue3705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3705) = mixedMoment B node3705 node3705Labels := rfl
  simpa [nodeValue3705, Sparse.eval] using hc.symm

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

theorem sound3746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3746 node3746Labels = Sparse.eval nodeValue3746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3746) = mixedMoment B node3746 node3746Labels := rfl
  simpa [nodeValue3746, Sparse.eval] using hc.symm

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

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

theorem sound527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node527 node527Labels = Sparse.eval nodeValue527 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue527 (familyPairVector B) := singlePair527 B _hB
    _ = _ := by norm_num [singlePairValue527, nodeValue527, Sparse.eval, mixedVector]

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

theorem sound3942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3942 node3942Labels = Sparse.eval nodeValue3942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3942) = mixedMoment B node3942 node3942Labels := rfl
  simpa [nodeValue3942, Sparse.eval] using hc.symm

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

theorem sound3952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3952 node3952Labels = Sparse.eval nodeValue3952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3952) = mixedMoment B node3952 node3952Labels := rfl
  simpa [nodeValue3952, Sparse.eval] using hc.symm

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

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

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

theorem sound4014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4014 node4014Labels = Sparse.eval nodeValue4014 (mixedVector B) := by
  have h := singleton4014 B _hB
  rw [sound527 B _hB _hF] at h
  norm_num [nodeValue4014, nodeValue527, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4998 node4998Labels = Sparse.eval nodeValue4998 (mixedVector B) := by
  have h := singleton4998 B _hB
  rw [sound2383 B _hB _hF, sound3352 B _hB _hF] at h
  norm_num [nodeValue4998, nodeValue2383, nodeValue3352, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5000 node5000Labels = Sparse.eval nodeValue5000 (mixedVector B) := by
  have h := singleton5000 B _hB
  rw [sound2385 B _hB _hF, sound3353 B _hB _hF] at h
  norm_num [nodeValue5000, nodeValue2385, nodeValue3353, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5003 node5003Labels = Sparse.eval nodeValue5003 (mixedVector B) := by
  have h := singleton5003 B _hB
  rw [sound2388 B _hB _hF, sound3354 B _hB _hF] at h
  norm_num [nodeValue5003, nodeValue2388, nodeValue3354, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5013 node5013Labels = Sparse.eval nodeValue5013 (mixedVector B) := by
  have h := singleton5013 B _hB
  rw [sound2398 B _hB _hF, sound3341 B _hB _hF] at h
  norm_num [nodeValue5013, nodeValue2398, nodeValue3341, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5014 node5014Labels = Sparse.eval nodeValue5014 (mixedVector B) := by
  have h := singleton5014 B _hB
  rw [sound2399 B _hB _hF, sound2467 B _hB _hF] at h
  norm_num [nodeValue5014, nodeValue2399, nodeValue2467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5015 node5015Labels = Sparse.eval nodeValue5015 (mixedVector B) := by
  have h := singleton5015 B _hB
  rw [sound2400 B _hB _hF, sound3344 B _hB _hF] at h
  norm_num [nodeValue5015, nodeValue2400, nodeValue3344, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5018 node5018Labels = Sparse.eval nodeValue5018 (mixedVector B) := by
  have h := singleton5018 B _hB
  rw [sound2404 B _hB _hF, sound3357 B _hB _hF] at h
  norm_num [nodeValue5018, nodeValue2404, nodeValue3357, Sparse.eval] at h ⊢
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

theorem sound5059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5059 node5059Labels = Sparse.eval nodeValue5059 (mixedVector B) := by
  have h := singleton5059 B _hB
  rw [sound2462 B _hB _hF, sound3436 B _hB _hF] at h
  norm_num [nodeValue5059, nodeValue2462, nodeValue3436, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5102 node5102Labels = Sparse.eval nodeValue5102 (mixedVector B) := by
  have h := singleton5102 B _hB
  rw [sound2512 B _hB _hF, sound3471 B _hB _hF] at h
  norm_num [nodeValue5102, nodeValue2512, nodeValue3471, Sparse.eval] at h ⊢
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

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5275 node5275Labels = Sparse.eval nodeValue5275 (mixedVector B) := by
  have h := singleton5275 B _hB
  rw [sound2743 B _hB _hF, sound3548 B _hB _hF] at h
  norm_num [nodeValue5275, nodeValue2743, nodeValue3548, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5346 node5346Labels = Sparse.eval nodeValue5346 (mixedVector B) := by
  have h := singleton5346 B _hB
  rw [sound3683 B _hB _hF, sound3746 B _hB _hF] at h
  norm_num [nodeValue5346, nodeValue3683, nodeValue3746, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5368 node5368Labels = Sparse.eval nodeValue5368 (mixedVector B) := by
  have h := singleton5368 B _hB
  rw [sound3705 B _hB _hF, sound3767 B _hB _hF] at h
  norm_num [nodeValue5368, nodeValue3705, nodeValue3767, Sparse.eval] at h ⊢
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

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
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

theorem sound5467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5467 node5467Labels = Sparse.eval nodeValue5467 (mixedVector B) := by
  have h := singleton5467 B _hB
  rw [sound3942 B _hB _hF] at h
  norm_num [nodeValue5467, nodeValue3942, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5469 node5469Labels = Sparse.eval nodeValue5469 (mixedVector B) := by
  have h := singleton5469 B _hB
  rw [sound3945 B _hB _hF, sound3952 B _hB _hF] at h
  norm_num [nodeValue5469, nodeValue3945, nodeValue3952, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5472 node5472Labels = Sparse.eval nodeValue5472 (mixedVector B) := by
  have h := singleton5472 B _hB
  rw [sound3957 B _hB _hF] at h
  norm_num [nodeValue5472, nodeValue3957, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5475 node5475Labels = Sparse.eval nodeValue5475 (mixedVector B) := by
  have h := singleton5475 B _hB
  rw [sound3963 B _hB _hF] at h
  norm_num [nodeValue5475, nodeValue3963, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5491 node5491Labels = Sparse.eval nodeValue5491 (mixedVector B) := by
  have h := singleton5491 B _hB
  rw [sound4014 B _hB _hF] at h
  norm_num [nodeValue5491, nodeValue4014, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources33
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1073 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 1) (sourceB1073 + difference 1 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 1) (sourceB1073 + difference 1 0) sourceC1073) = raw17763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17763; decide +kernel
    rw [ha]
    exact (canonical17763 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 2) (sourceB1073 + difference 2 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 2) (sourceB1073 + difference 2 0) sourceC1073) = raw17764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17764; decide +kernel
    rw [ha]
    exact (canonical17764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 3) (sourceB1073 + difference 3 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 3) (sourceB1073 + difference 3 0) sourceC1073) = raw17765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17765; decide +kernel
    rw [ha]
    exact (canonical17765 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 4) (sourceB1073 + difference 4 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 4) (sourceB1073 + difference 4 0) sourceC1073) = raw17766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17766; decide +kernel
    rw [ha]
    exact (canonical17766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1073 + difference 0 5) (sourceB1073 + difference 5 0) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1073 + difference 0 5) (sourceB1073 + difference 5 0) sourceC1073) = raw17767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17767; decide +kernel
    rw [ha]
    exact (canonical17767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 0) (sourceB1073 + difference 0 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 0) (sourceB1073 + difference 0 1) sourceC1073) = raw17768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17768; decide +kernel
    rw [ha]
    exact (canonical17768 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 2) (sourceB1073 + difference 2 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 2) (sourceB1073 + difference 2 1) sourceC1073) = raw10451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10451; decide +kernel
    rw [ha]
    exact (canonical10451 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 3) (sourceB1073 + difference 3 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 3) (sourceB1073 + difference 3 1) sourceC1073) = raw10452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10452; decide +kernel
    rw [ha]
    exact (canonical10452 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 4) (sourceB1073 + difference 4 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 4) (sourceB1073 + difference 4 1) sourceC1073) = raw10453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10453; decide +kernel
    rw [ha]
    exact (canonical10453 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1073 + difference 1 5) (sourceB1073 + difference 5 1) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1073 + difference 1 5) (sourceB1073 + difference 5 1) sourceC1073) = raw10454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10454; decide +kernel
    rw [ha]
    exact (canonical10454 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 0) (sourceB1073 + difference 0 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 0) (sourceB1073 + difference 0 2) sourceC1073) = raw10461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10461; decide +kernel
    rw [ha]
    exact (canonical10461 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 1) (sourceB1073 + difference 1 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 1) (sourceB1073 + difference 1 2) sourceC1073) = raw17769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17769; decide +kernel
    rw [ha]
    exact (canonical17769 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 3) (sourceB1073 + difference 3 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5467) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 3) (sourceB1073 + difference 3 2) sourceC1073) = raw17770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17770; decide +kernel
    rw [ha]
    exact (canonical17770 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 4) (sourceB1073 + difference 4 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 4) (sourceB1073 + difference 4 2) sourceC1073) = raw17771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17771; decide +kernel
    rw [ha]
    exact (canonical17771 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1073 + difference 2 5) (sourceB1073 + difference 5 2) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1073 + difference 2 5) (sourceB1073 + difference 5 2) sourceC1073) = raw17772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17772; decide +kernel
    rw [ha]
    exact (canonical17772 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 0) (sourceB1073 + difference 0 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 0) (sourceB1073 + difference 0 3) sourceC1073) = raw10466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10466; decide +kernel
    rw [ha]
    exact (canonical10466 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 1) (sourceB1073 + difference 1 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 1) (sourceB1073 + difference 1 3) sourceC1073) = raw17773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17773; decide +kernel
    rw [ha]
    exact (canonical17773 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 2) (sourceB1073 + difference 2 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 2) (sourceB1073 + difference 2 3) sourceC1073) = raw17774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17774; decide +kernel
    rw [ha]
    exact (canonical17774 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 4) (sourceB1073 + difference 4 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 4) (sourceB1073 + difference 4 3) sourceC1073) = raw17775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17775; decide +kernel
    rw [ha]
    exact (canonical17775 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1073 + difference 3 5) (sourceB1073 + difference 5 3) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1073 + difference 3 5) (sourceB1073 + difference 5 3) sourceC1073) = raw17776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17776; decide +kernel
    rw [ha]
    exact (canonical17776 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 0) (sourceB1073 + difference 0 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 0) (sourceB1073 + difference 0 4) sourceC1073) = raw10471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10471; decide +kernel
    rw [ha]
    exact (canonical10471 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 1) (sourceB1073 + difference 1 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 1) (sourceB1073 + difference 1 4) sourceC1073) = raw17777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17777; decide +kernel
    rw [ha]
    exact (canonical17777 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 2) (sourceB1073 + difference 2 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 2) (sourceB1073 + difference 2 4) sourceC1073) = raw17778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17778; decide +kernel
    rw [ha]
    exact (canonical17778 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 3) (sourceB1073 + difference 3 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 3) (sourceB1073 + difference 3 4) sourceC1073) = raw17779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17779; decide +kernel
    rw [ha]
    exact (canonical17779 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1073 + difference 4 5) (sourceB1073 + difference 5 4) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1073 + difference 4 5) (sourceB1073 + difference 5 4) sourceC1073) = raw17780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17780; decide +kernel
    rw [ha]
    exact (canonical17780 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 0) (sourceB1073 + difference 0 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 0) (sourceB1073 + difference 0 5) sourceC1073) = raw10476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw10476; decide +kernel
    rw [ha]
    exact (canonical10476 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 1) (sourceB1073 + difference 1 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 1) (sourceB1073 + difference 1 5) sourceC1073) = raw17781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17781; decide +kernel
    rw [ha]
    exact (canonical17781 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 2) (sourceB1073 + difference 2 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 2) (sourceB1073 + difference 2 5) sourceC1073) = raw17782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17782; decide +kernel
    rw [ha]
    exact (canonical17782 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 3) (sourceB1073 + difference 3 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 3) (sourceB1073 + difference 3 5) sourceC1073) = raw17783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17783; decide +kernel
    rw [ha]
    exact (canonical17783 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1073 + difference 5 4) (sourceB1073 + difference 4 5) sourceC1073) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1073 + difference 5 4) (sourceB1073 + difference 4 5) sourceC1073) = raw17784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1073 sourceB1073 sourceC1073 difference raw17784; decide +kernel
    rw [ha]
    exact (canonical17784 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1073 sourceB1073 sourceC1073
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1073, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck926 : Integer.Sparse.reindex keyMap MixedData.row926 = numericRow926 := by decide +kernel

theorem numericCheck926 (x : Master → ℝ) : Integer.Sparse.eval numericRow926 x =
    (17280 : ℝ) * reducedSource926 x := by
  norm_num [numericRow926, reducedSource926, Integer.Sparse.eval, Sparse.eval, nodeValue4998, nodeValue5000, nodeValue5003, nodeValue5013, nodeValue5014, nodeValue5015, nodeValue5018, nodeValue5059, nodeValue5102, nodeValue5259, nodeValue5271, nodeValue5275, nodeValue5346, nodeValue5368, nodeValue5428, nodeValue5467, nodeValue5469, nodeValue5472, nodeValue5473, nodeValue5475, nodeValue5477, nodeValue5478, nodeValue5483, nodeValue5485, nodeValue5490, nodeValue5491, nodeValue5492]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero926 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource926 (mixedVector B) = 0 := by
  have h4998 : mixedVector B (Sum.inr 4998) = Sparse.eval nodeValue4998 (mixedVector B) := by
    change mixedMoment B node4998 node4998Labels = _
    exact sound4998 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5003 : mixedVector B (Sum.inr 5003) = Sparse.eval nodeValue5003 (mixedVector B) := by
    change mixedMoment B node5003 node5003Labels = _
    exact sound5003 B hB hF
  have h5013 : mixedVector B (Sum.inr 5013) = Sparse.eval nodeValue5013 (mixedVector B) := by
    change mixedMoment B node5013 node5013Labels = _
    exact sound5013 B hB hF
  have h5014 : mixedVector B (Sum.inr 5014) = Sparse.eval nodeValue5014 (mixedVector B) := by
    change mixedMoment B node5014 node5014Labels = _
    exact sound5014 B hB hF
  have h5015 : mixedVector B (Sum.inr 5015) = Sparse.eval nodeValue5015 (mixedVector B) := by
    change mixedMoment B node5015 node5015Labels = _
    exact sound5015 B hB hF
  have h5018 : mixedVector B (Sum.inr 5018) = Sparse.eval nodeValue5018 (mixedVector B) := by
    change mixedMoment B node5018 node5018Labels = _
    exact sound5018 B hB hF
  have h5059 : mixedVector B (Sum.inr 5059) = Sparse.eval nodeValue5059 (mixedVector B) := by
    change mixedMoment B node5059 node5059Labels = _
    exact sound5059 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5346 : mixedVector B (Sum.inr 5346) = Sparse.eval nodeValue5346 (mixedVector B) := by
    change mixedMoment B node5346 node5346Labels = _
    exact sound5346 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5467 : mixedVector B (Sum.inr 5467) = Sparse.eval nodeValue5467 (mixedVector B) := by
    change mixedMoment B node5467 node5467Labels = _
    exact sound5467 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5475 : mixedVector B (Sum.inr 5475) = Sparse.eval nodeValue5475 (mixedVector B) := by
    change mixedMoment B node5475 node5475Labels = _
    exact sound5475 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  have h5491 : mixedVector B (Sum.inr 5491) = Sparse.eval nodeValue5491 (mixedVector B) := by
    change mixedMoment B node5491 node5491Labels = _
    exact sound5491 B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492_e B hB hF
  simpa only [sourceForm1073, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4998, h5000, h5003, h5013, h5014, h5015, h5018, h5059, h5102, h5259, h5271, h5275, h5346, h5368, h5428, h5467, h5469, h5472, h5473, h5475, h5477, h5478, h5483, h5485, h5490, h5491, h5492, reducedSource926] using sourceEq1073 B hB

theorem rowSound926_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row926 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck926, numericCheck926, reducedZero926 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e_oai
