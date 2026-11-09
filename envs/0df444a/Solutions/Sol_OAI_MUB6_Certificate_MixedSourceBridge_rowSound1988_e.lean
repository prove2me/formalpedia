-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:45:08.671209+00:00
-- url     : https://prove2.me/submissions/37f44e03-7bdb-4aaf-8133-a6403faa72df

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5416_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1473 raw1473Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw1473 raw1473Labels = mixedMoment B raw1473step0 raw1473step0Labels := by
      have ha : raw1473step0 = (fun i j => raw1473 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1473step0 raw1473; decide +kernel
      have hl : raw1473step0Labels = raw1473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1473 raw1473Labels permutation152 permutation4
    mixedMoment B raw1473step0 raw1473step0Labels = mixedMoment B raw1473step1 raw1473step1Labels := by
      have ha : raw1473step1 = raw1473step0 := by apply Matrix.ext; unfold raw1473step1 raw1473step0; decide +kernel
      have hl : raw1473step0Labels = labelEmbedding7 ∘ raw1473step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1473step0 raw1473step0Labels raw1473step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

theorem canonical1474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1474 raw1474Labels = mixedMoment B node1760 node1760Labels := by
  calc
    mixedMoment B raw1474 raw1474Labels = mixedMoment B raw1474step0 raw1474step0Labels := by
      have ha : raw1474step0 = (fun i j => raw1474 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1474step0 raw1474; decide +kernel
      have hl : raw1474step0Labels = raw1474Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1474 raw1474Labels permutation152 permutation4
    _ = mixedMoment B node1760 node1760Labels := by rfl

theorem canonical1475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1475 raw1475Labels = mixedMoment B node1836 node1836Labels := by
  calc
    mixedMoment B raw1475 raw1475Labels = mixedMoment B raw1475step0 raw1475step0Labels := by
      have ha : raw1475step0 = (fun i j => raw1475 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1475step0 raw1475; decide +kernel
      have hl : raw1475step0Labels = raw1475Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1475 raw1475Labels permutation158 permutation6
    mixedMoment B raw1475step0 raw1475step0Labels = mixedMoment B raw1475step1 raw1475step1Labels := by
      have ha : raw1475step1 = -raw1475step0 := by apply Matrix.ext; change ∀ i j, raw1475step1 i j = -(raw1475step0 i j); unfold raw1475step1 raw1475step0; decide +kernel
      have hl : raw1475step1Labels = raw1475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1475step1 raw1475step1Labels = mixedMoment B raw1475step2 raw1475step2Labels := by
      have ha : raw1475step2 = raw1475step1 := by apply Matrix.ext; unfold raw1475step2 raw1475step1; decide +kernel
      have hl : raw1475step1Labels = labelEmbedding1 ∘ raw1475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1475step1 raw1475step1Labels raw1475step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1836 node1836Labels := by rfl

theorem canonical1476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1476 raw1476Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw1476 raw1476Labels = mixedMoment B raw1476step0 raw1476step0Labels := by
      have ha : raw1476step0 = (fun i j => raw1476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1476step0 raw1476; decide +kernel
      have hl : raw1476step0Labels = raw1476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1476 raw1476Labels permutation152 permutation4
    mixedMoment B raw1476step0 raw1476step0Labels = mixedMoment B raw1476step1 raw1476step1Labels := by
      have ha : raw1476step1 = raw1476step0 := by apply Matrix.ext; unfold raw1476step1 raw1476step0; decide +kernel
      have hl : raw1476step0Labels = labelEmbedding7 ∘ raw1476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1476step0 raw1476step0Labels raw1476step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

theorem canonical1477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1477 raw1477Labels = mixedMoment B node1761 node1761Labels := by
  calc
    mixedMoment B raw1477 raw1477Labels = mixedMoment B raw1477step0 raw1477step0Labels := by
      have ha : raw1477step0 = (fun i j => raw1477 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1477step0 raw1477; decide +kernel
      have hl : raw1477step0Labels = raw1477Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1477 raw1477Labels permutation152 permutation4
    _ = mixedMoment B node1761 node1761Labels := by rfl

theorem canonical1478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1478 raw1478Labels = mixedMoment B node1837 node1837Labels := by
  calc
    mixedMoment B raw1478 raw1478Labels = mixedMoment B raw1478step0 raw1478step0Labels := by
      have ha : raw1478step0 = (fun i j => raw1478 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1478step0 raw1478; decide +kernel
      have hl : raw1478step0Labels = raw1478Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1478 raw1478Labels permutation158 permutation6
    mixedMoment B raw1478step0 raw1478step0Labels = mixedMoment B raw1478step1 raw1478step1Labels := by
      have ha : raw1478step1 = -raw1478step0 := by apply Matrix.ext; change ∀ i j, raw1478step1 i j = -(raw1478step0 i j); unfold raw1478step1 raw1478step0; decide +kernel
      have hl : raw1478step1Labels = raw1478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1478step1 raw1478step1Labels = mixedMoment B raw1478step2 raw1478step2Labels := by
      have ha : raw1478step2 = raw1478step1 := by apply Matrix.ext; unfold raw1478step2 raw1478step1; decide +kernel
      have hl : raw1478step1Labels = labelEmbedding1 ∘ raw1478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1478step1 raw1478step1Labels raw1478step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1837 node1837Labels := by rfl

theorem canonical1485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1485 raw1485Labels = mixedMoment B node4635 node4635Labels := by
  calc
    mixedMoment B raw1485 raw1485Labels = mixedMoment B raw1485step0 raw1485step0Labels := by
      have ha : raw1485step0 = (fun i j => raw1485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1485step0 raw1485; decide +kernel
      have hl : raw1485step0Labels = raw1485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1485 raw1485Labels permutation152 permutation4
    mixedMoment B raw1485step0 raw1485step0Labels = mixedMoment B raw1485step1 raw1485step1Labels := by
      have ha : raw1485step1 = raw1485step0 := by apply Matrix.ext; unfold raw1485step1 raw1485step0; decide +kernel
      have hl : raw1485step0Labels = labelEmbedding7 ∘ raw1485step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1485step0 raw1485step0Labels raw1485step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4635 node4635Labels := by rfl

theorem canonical1486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1486 raw1486Labels = mixedMoment B node1764 node1764Labels := by
  calc
    mixedMoment B raw1486 raw1486Labels = mixedMoment B raw1486step0 raw1486step0Labels := by
      have ha : raw1486step0 = (fun i j => raw1486 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1486step0 raw1486; decide +kernel
      have hl : raw1486step0Labels = raw1486Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1486 raw1486Labels permutation152 permutation4
    _ = mixedMoment B node1764 node1764Labels := by rfl

theorem canonical1487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1487 raw1487Labels = mixedMoment B node1848 node1848Labels := by
  calc
    mixedMoment B raw1487 raw1487Labels = mixedMoment B raw1487step0 raw1487step0Labels := by
      have ha : raw1487step0 = (fun i j => raw1487 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1487step0 raw1487; decide +kernel
      have hl : raw1487step0Labels = raw1487Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1487 raw1487Labels permutation152 permutation6
    mixedMoment B raw1487step0 raw1487step0Labels = mixedMoment B raw1487step1 raw1487step1Labels := by
      have ha : raw1487step1 = -raw1487step0 := by apply Matrix.ext; change ∀ i j, raw1487step1 i j = -(raw1487step0 i j); unfold raw1487step1 raw1487step0; decide +kernel
      have hl : raw1487step1Labels = raw1487step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1487step1 raw1487step1Labels = mixedMoment B raw1487step2 raw1487step2Labels := by
      have ha : raw1487step2 = raw1487step1 := by apply Matrix.ext; unfold raw1487step2 raw1487step1; decide +kernel
      have hl : raw1487step1Labels = labelEmbedding1 ∘ raw1487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1487step1 raw1487step1Labels raw1487step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1848 node1848Labels := by rfl

theorem canonical1503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1503 raw1503Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw1503 raw1503Labels = mixedMoment B raw1503step0 raw1503step0Labels := by
      have ha : raw1503step0 = (fun i j => raw1503 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1503step0 raw1503; decide +kernel
      have hl : raw1503step0Labels = raw1503Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1503 raw1503Labels permutation152 permutation4
    mixedMoment B raw1503step0 raw1503step0Labels = mixedMoment B raw1503step1 raw1503step1Labels := by
      have ha : raw1503step1 = raw1503step0 := by apply Matrix.ext; unfold raw1503step1 raw1503step0; decide +kernel
      have hl : raw1503step0Labels = labelEmbedding7 ∘ raw1503step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1503step0 raw1503step0Labels raw1503step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

theorem canonical1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1504 raw1504Labels = mixedMoment B node1771 node1771Labels := by
  calc
    mixedMoment B raw1504 raw1504Labels = mixedMoment B raw1504step0 raw1504step0Labels := by
      have ha : raw1504step0 = (fun i j => raw1504 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1504step0 raw1504; decide +kernel
      have hl : raw1504step0Labels = raw1504Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1504 raw1504Labels permutation152 permutation4
    _ = mixedMoment B node1771 node1771Labels := by rfl

theorem canonical1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1505 raw1505Labels = mixedMoment B node1838 node1838Labels := by
  calc
    mixedMoment B raw1505 raw1505Labels = mixedMoment B raw1505step0 raw1505step0Labels := by
      have ha : raw1505step0 = (fun i j => raw1505 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1505step0 raw1505; decide +kernel
      have hl : raw1505step0Labels = raw1505Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1505 raw1505Labels permutation153 permutation6
    mixedMoment B raw1505step0 raw1505step0Labels = mixedMoment B raw1505step1 raw1505step1Labels := by
      have ha : raw1505step1 = -raw1505step0 := by apply Matrix.ext; change ∀ i j, raw1505step1 i j = -(raw1505step0 i j); unfold raw1505step1 raw1505step0; decide +kernel
      have hl : raw1505step1Labels = raw1505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1505step1 raw1505step1Labels = mixedMoment B raw1505step2 raw1505step2Labels := by
      have ha : raw1505step2 = raw1505step1 := by apply Matrix.ext; unfold raw1505step2 raw1505step1; decide +kernel
      have hl : raw1505step1Labels = labelEmbedding1 ∘ raw1505step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1505step1 raw1505step1Labels raw1505step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1838 node1838Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14308 raw14308Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14308 raw14308Labels = mixedMoment B raw14308step0 raw14308step0Labels := by
      have ha : raw14308step0 = (fun i j => raw14308 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14308step0 raw14308; decide +kernel
      have hl : raw14308step0Labels = raw14308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14308 raw14308Labels permutation155 permutation3
    mixedMoment B raw14308step0 raw14308step0Labels = mixedMoment B raw14308step1 raw14308step1Labels := by
      have ha : raw14308step1 = raw14308step0 := by apply Matrix.ext; unfold raw14308step1 raw14308step0; decide +kernel
      have hl : raw14308step0Labels = labelEmbedding6 ∘ raw14308step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14308step0 raw14308step0Labels raw14308step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical14317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14317 raw14317Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw14317 raw14317Labels = mixedMoment B raw14317step0 raw14317step0Labels := by
      have ha : raw14317step0 = (fun i j => raw14317 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14317step0 raw14317; decide +kernel
      have hl : raw14317step0Labels = raw14317Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14317 raw14317Labels permutation169 permutation3
    mixedMoment B raw14317step0 raw14317step0Labels = mixedMoment B raw14317step1 raw14317step1Labels := by
      have ha : raw14317step1 = raw14317step0 := by apply Matrix.ext; unfold raw14317step1 raw14317step0; decide +kernel
      have hl : raw14317step0Labels = labelEmbedding6 ∘ raw14317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14317step0 raw14317step0Labels raw14317step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical14321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14321 raw14321Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14321 raw14321Labels = mixedMoment B raw14321step0 raw14321step0Labels := by
      have ha : raw14321step0 = (fun i j => raw14321 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14321step0 raw14321; decide +kernel
      have hl : raw14321step0Labels = raw14321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14321 raw14321Labels permutation155 permutation3
    mixedMoment B raw14321step0 raw14321step0Labels = mixedMoment B raw14321step1 raw14321step1Labels := by
      have ha : raw14321step1 = raw14321step0 := by apply Matrix.ext; unfold raw14321step1 raw14321step0; decide +kernel
      have hl : raw14321step0Labels = labelEmbedding6 ∘ raw14321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14321step0 raw14321step0Labels raw14321step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical14326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14326 raw14326Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14326 raw14326Labels = mixedMoment B raw14326step0 raw14326step0Labels := by
      have ha : raw14326step0 = (fun i j => raw14326 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14326step0 raw14326; decide +kernel
      have hl : raw14326step0Labels = raw14326Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14326 raw14326Labels permutation156 permutation3
    mixedMoment B raw14326step0 raw14326step0Labels = mixedMoment B raw14326step1 raw14326step1Labels := by
      have ha : raw14326step1 = raw14326step0 := by apply Matrix.ext; unfold raw14326step1 raw14326step0; decide +kernel
      have hl : raw14326step0Labels = labelEmbedding6 ∘ raw14326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14326step0 raw14326step0Labels raw14326step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical14329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14329 raw14329Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14329 raw14329Labels = mixedMoment B raw14329step0 raw14329step0Labels := by
      have hz : ∀ j, raw14329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14329step0 = (fun i j => raw14329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14329step0 raw14329; decide +kernel
      have hl : raw14329step0Labels = raw14329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14329 raw14329Labels permutation434 hz
    mixedMoment B raw14329step0 raw14329step0Labels = mixedMoment B raw14329step1 raw14329step1Labels := by
      have ha : raw14329step1 = (fun i j => raw14329step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14329step1 raw14329step0; decide +kernel
      have hl : raw14329step1Labels = raw14329step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14329step0 raw14329step0Labels permutation32 permutation3
    mixedMoment B raw14329step1 raw14329step1Labels = mixedMoment B raw14329step2 raw14329step2Labels := by
      have ha : raw14329step2 = raw14329step1 := by apply Matrix.ext; unfold raw14329step2 raw14329step1; decide +kernel
      have hl : raw14329step1Labels = labelEmbedding6 ∘ raw14329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14329step1 raw14329step1Labels raw14329step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

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

theorem canonical1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1689 raw1689Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw1689 raw1689Labels = mixedMoment B raw1689step0 raw1689step0Labels := by
      have ha : raw1689step0 = (fun i j => raw1689 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1689step0 raw1689; decide +kernel
      have hl : raw1689step0Labels = raw1689Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1689 raw1689Labels permutation152 permutation4
    mixedMoment B raw1689step0 raw1689step0Labels = mixedMoment B raw1689step1 raw1689step1Labels := by
      have ha : raw1689step1 = raw1689step0 := by apply Matrix.ext; unfold raw1689step1 raw1689step0; decide +kernel
      have hl : raw1689step0Labels = labelEmbedding7 ∘ raw1689step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1689step0 raw1689step0Labels raw1689step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1690 raw1690Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw1690 raw1690Labels = mixedMoment B raw1690step0 raw1690step0Labels := by
      have ha : raw1690step0 = (fun i j => raw1690 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1690step0 raw1690; decide +kernel
      have hl : raw1690step0Labels = raw1690Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1690 raw1690Labels permutation152 permutation4
    _ = mixedMoment B node1960 node1960Labels := by rfl

theorem canonical1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1691 raw1691Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw1691 raw1691Labels = mixedMoment B raw1691step0 raw1691step0Labels := by
      have ha : raw1691step0 = (fun i j => raw1691 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1691step0 raw1691; decide +kernel
      have hl : raw1691step0Labels = raw1691Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1691 raw1691Labels permutation152 permutation6
    mixedMoment B raw1691step0 raw1691step0Labels = mixedMoment B raw1691step1 raw1691step1Labels := by
      have ha : raw1691step1 = -raw1691step0 := by apply Matrix.ext; change ∀ i j, raw1691step1 i j = -(raw1691step0 i j); unfold raw1691step1 raw1691step0; decide +kernel
      have hl : raw1691step1Labels = raw1691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1691step1 raw1691step1Labels = mixedMoment B raw1691step2 raw1691step2Labels := by
      have ha : raw1691step2 = raw1691step1 := by apply Matrix.ext; unfold raw1691step2 raw1691step1; decide +kernel
      have hl : raw1691step1Labels = labelEmbedding1 ∘ raw1691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1691step1 raw1691step1Labels raw1691step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

theorem canonical1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1692 raw1692Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw1692 raw1692Labels = mixedMoment B raw1692step0 raw1692step0Labels := by
      have ha : raw1692step0 = (fun i j => raw1692 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1692step0 raw1692; decide +kernel
      have hl : raw1692step0Labels = raw1692Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1692 raw1692Labels permutation152 permutation4
    mixedMoment B raw1692step0 raw1692step0Labels = mixedMoment B raw1692step1 raw1692step1Labels := by
      have ha : raw1692step1 = raw1692step0 := by apply Matrix.ext; unfold raw1692step1 raw1692step0; decide +kernel
      have hl : raw1692step0Labels = labelEmbedding7 ∘ raw1692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1692step0 raw1692step0Labels raw1692step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1693 raw1693Labels = mixedMoment B node1963 node1963Labels := by
  calc
    mixedMoment B raw1693 raw1693Labels = mixedMoment B raw1693step0 raw1693step0Labels := by
      have ha : raw1693step0 = (fun i j => raw1693 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1693step0 raw1693; decide +kernel
      have hl : raw1693step0Labels = raw1693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1693 raw1693Labels permutation152 permutation4
    _ = mixedMoment B node1963 node1963Labels := by rfl

theorem canonical1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1694 raw1694Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw1694 raw1694Labels = mixedMoment B raw1694step0 raw1694step0Labels := by
      have ha : raw1694step0 = (fun i j => raw1694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1694step0 raw1694; decide +kernel
      have hl : raw1694step0Labels = raw1694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1694 raw1694Labels permutation152 permutation6
    mixedMoment B raw1694step0 raw1694step0Labels = mixedMoment B raw1694step1 raw1694step1Labels := by
      have ha : raw1694step1 = -raw1694step0 := by apply Matrix.ext; change ∀ i j, raw1694step1 i j = -(raw1694step0 i j); unfold raw1694step1 raw1694step0; decide +kernel
      have hl : raw1694step1Labels = raw1694step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1694step1 raw1694step1Labels = mixedMoment B raw1694step2 raw1694step2Labels := by
      have ha : raw1694step2 = raw1694step1 := by apply Matrix.ext; unfold raw1694step2 raw1694step1; decide +kernel
      have hl : raw1694step1Labels = labelEmbedding1 ∘ raw1694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1694step1 raw1694step1Labels raw1694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

theorem canonical1701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1701 raw1701Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw1701 raw1701Labels = mixedMoment B raw1701step0 raw1701step0Labels := by
      have ha : raw1701step0 = (fun i j => raw1701 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1701step0 raw1701; decide +kernel
      have hl : raw1701step0Labels = raw1701Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1701 raw1701Labels permutation152 permutation4
    mixedMoment B raw1701step0 raw1701step0Labels = mixedMoment B raw1701step1 raw1701step1Labels := by
      have ha : raw1701step1 = raw1701step0 := by apply Matrix.ext; unfold raw1701step1 raw1701step0; decide +kernel
      have hl : raw1701step0Labels = labelEmbedding7 ∘ raw1701step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1701step0 raw1701step0Labels raw1701step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

theorem canonical1702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1702 raw1702Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw1702 raw1702Labels = mixedMoment B raw1702step0 raw1702step0Labels := by
      have ha : raw1702step0 = (fun i j => raw1702 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1702step0 raw1702; decide +kernel
      have hl : raw1702step0Labels = raw1702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1702 raw1702Labels permutation152 permutation4
    _ = mixedMoment B node1967 node1967Labels := by rfl

theorem canonical1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1703 raw1703Labels = mixedMoment B node2183 node2183Labels := by
  calc
    mixedMoment B raw1703 raw1703Labels = mixedMoment B raw1703step0 raw1703step0Labels := by
      have ha : raw1703step0 = (fun i j => raw1703 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1703step0 raw1703; decide +kernel
      have hl : raw1703step0Labels = raw1703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1703 raw1703Labels permutation152 permutation6
    mixedMoment B raw1703step0 raw1703step0Labels = mixedMoment B raw1703step1 raw1703step1Labels := by
      have ha : raw1703step1 = -raw1703step0 := by apply Matrix.ext; change ∀ i j, raw1703step1 i j = -(raw1703step0 i j); unfold raw1703step1 raw1703step0; decide +kernel
      have hl : raw1703step1Labels = raw1703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1703step1 raw1703step1Labels = mixedMoment B raw1703step2 raw1703step2Labels := by
      have ha : raw1703step2 = raw1703step1 := by apply Matrix.ext; unfold raw1703step2 raw1703step1; decide +kernel
      have hl : raw1703step1Labels = labelEmbedding1 ∘ raw1703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1703step1 raw1703step1Labels raw1703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2183 node2183Labels := by rfl

theorem canonical1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1713 raw1713Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw1713 raw1713Labels = mixedMoment B raw1713step0 raw1713step0Labels := by
      have ha : raw1713step0 = (fun i j => raw1713 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1713step0 raw1713; decide +kernel
      have hl : raw1713step0Labels = raw1713Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1713 raw1713Labels permutation152 permutation4
    mixedMoment B raw1713step0 raw1713step0Labels = mixedMoment B raw1713step1 raw1713step1Labels := by
      have ha : raw1713step1 = raw1713step0 := by apply Matrix.ext; unfold raw1713step1 raw1713step0; decide +kernel
      have hl : raw1713step0Labels = labelEmbedding7 ∘ raw1713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1713step0 raw1713step0Labels raw1713step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

theorem canonical1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1714 raw1714Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw1714 raw1714Labels = mixedMoment B raw1714step0 raw1714step0Labels := by
      have ha : raw1714step0 = (fun i j => raw1714 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1714step0 raw1714; decide +kernel
      have hl : raw1714step0Labels = raw1714Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1714 raw1714Labels permutation152 permutation4
    _ = mixedMoment B node1987 node1987Labels := by rfl

theorem canonical1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1715 raw1715Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw1715 raw1715Labels = mixedMoment B raw1715step0 raw1715step0Labels := by
      have ha : raw1715step0 = (fun i j => raw1715 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1715step0 raw1715; decide +kernel
      have hl : raw1715step0Labels = raw1715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1715 raw1715Labels permutation176 permutation6
    mixedMoment B raw1715step0 raw1715step0Labels = mixedMoment B raw1715step1 raw1715step1Labels := by
      have ha : raw1715step1 = -raw1715step0 := by apply Matrix.ext; change ∀ i j, raw1715step1 i j = -(raw1715step0 i j); unfold raw1715step1 raw1715step0; decide +kernel
      have hl : raw1715step1Labels = raw1715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1715step1 raw1715step1Labels = mixedMoment B raw1715step2 raw1715step2Labels := by
      have ha : raw1715step2 = raw1715step1 := by apply Matrix.ext; unfold raw1715step2 raw1715step1; decide +kernel
      have hl : raw1715step1Labels = labelEmbedding1 ∘ raw1715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1715step1 raw1715step1Labels raw1715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1996 node1996Labels := by rfl

theorem canonical1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1716 raw1716Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw1716 raw1716Labels = mixedMoment B raw1716step0 raw1716step0Labels := by
      have ha : raw1716step0 = (fun i j => raw1716 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1716step0 raw1716; decide +kernel
      have hl : raw1716step0Labels = raw1716Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1716 raw1716Labels permutation152 permutation4
    mixedMoment B raw1716step0 raw1716step0Labels = mixedMoment B raw1716step1 raw1716step1Labels := by
      have ha : raw1716step1 = raw1716step0 := by apply Matrix.ext; unfold raw1716step1 raw1716step0; decide +kernel
      have hl : raw1716step0Labels = labelEmbedding7 ∘ raw1716step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1716step0 raw1716step0Labels raw1716step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical1717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1717 raw1717Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw1717 raw1717Labels = mixedMoment B raw1717step0 raw1717step0Labels := by
      have ha : raw1717step0 = (fun i j => raw1717 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1717step0 raw1717; decide +kernel
      have hl : raw1717step0Labels = raw1717Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1717 raw1717Labels permutation152 permutation4
    _ = mixedMoment B node1990 node1990Labels := by rfl

theorem canonical1718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1718 raw1718Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw1718 raw1718Labels = mixedMoment B raw1718step0 raw1718step0Labels := by
      have ha : raw1718step0 = (fun i j => raw1718 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1718step0 raw1718; decide +kernel
      have hl : raw1718step0Labels = raw1718Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1718 raw1718Labels permutation176 permutation6
    mixedMoment B raw1718step0 raw1718step0Labels = mixedMoment B raw1718step1 raw1718step1Labels := by
      have ha : raw1718step1 = -raw1718step0 := by apply Matrix.ext; change ∀ i j, raw1718step1 i j = -(raw1718step0 i j); unfold raw1718step1 raw1718step0; decide +kernel
      have hl : raw1718step1Labels = raw1718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1718step1 raw1718step1Labels = mixedMoment B raw1718step2 raw1718step2Labels := by
      have ha : raw1718step2 = raw1718step1 := by apply Matrix.ext; unfold raw1718step2 raw1718step1; decide +kernel
      have hl : raw1718step1Labels = labelEmbedding1 ∘ raw1718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1718step1 raw1718step1Labels raw1718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1997 node1997Labels := by rfl

theorem canonical1719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1719 raw1719Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw1719 raw1719Labels = mixedMoment B raw1719step0 raw1719step0Labels := by
      have ha : raw1719step0 = (fun i j => raw1719 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1719step0 raw1719; decide +kernel
      have hl : raw1719step0Labels = raw1719Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1719 raw1719Labels permutation152 permutation4
    mixedMoment B raw1719step0 raw1719step0Labels = mixedMoment B raw1719step1 raw1719step1Labels := by
      have ha : raw1719step1 = raw1719step0 := by apply Matrix.ext; unfold raw1719step1 raw1719step0; decide +kernel
      have hl : raw1719step0Labels = labelEmbedding7 ∘ raw1719step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1719step0 raw1719step0Labels raw1719step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1720 raw1720Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1720 raw1720Labels = mixedMoment B raw1720step0 raw1720step0Labels := by
      have ha : raw1720step0 = (fun i j => raw1720 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1720step0 raw1720; decide +kernel
      have hl : raw1720step0Labels = raw1720Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1720 raw1720Labels permutation152 permutation4
    _ = mixedMoment B node2000 node2000Labels := by rfl

theorem canonical1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1721 raw1721Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1721 raw1721Labels = mixedMoment B raw1721step0 raw1721step0Labels := by
      have ha : raw1721step0 = (fun i j => raw1721 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1721step0 raw1721; decide +kernel
      have hl : raw1721step0Labels = raw1721Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1721 raw1721Labels permutation177 permutation6
    mixedMoment B raw1721step0 raw1721step0Labels = mixedMoment B raw1721step1 raw1721step1Labels := by
      have ha : raw1721step1 = -raw1721step0 := by apply Matrix.ext; change ∀ i j, raw1721step1 i j = -(raw1721step0 i j); unfold raw1721step1 raw1721step0; decide +kernel
      have hl : raw1721step1Labels = raw1721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1721step1 raw1721step1Labels = mixedMoment B raw1721step2 raw1721step2Labels := by
      have ha : raw1721step2 = raw1721step1 := by apply Matrix.ext; unfold raw1721step2 raw1721step1; decide +kernel
      have hl : raw1721step1Labels = labelEmbedding1 ∘ raw1721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1721step1 raw1721step1Labels raw1721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2000 node2000Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2394 raw2394Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw2394 raw2394Labels = mixedMoment B raw2394step0 raw2394step0Labels := by
      have ha : raw2394step0 = (fun i j => raw2394 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2394step0 raw2394; decide +kernel
      have hl : raw2394step0Labels = raw2394Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2394 raw2394Labels permutation152 permutation4
    mixedMoment B raw2394step0 raw2394step0Labels = mixedMoment B raw2394step1 raw2394step1Labels := by
      have ha : raw2394step1 = raw2394step0 := by apply Matrix.ext; unfold raw2394step1 raw2394step0; decide +kernel
      have hl : raw2394step0Labels = labelEmbedding7 ∘ raw2394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2394step0 raw2394step0Labels raw2394step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical2395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2395 raw2395Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw2395 raw2395Labels = mixedMoment B raw2395step0 raw2395step0Labels := by
      have ha : raw2395step0 = (fun i j => raw2395 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2395step0 raw2395; decide +kernel
      have hl : raw2395step0Labels = raw2395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2395 raw2395Labels permutation152 permutation4
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical2396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2396 raw2396Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw2396 raw2396Labels = mixedMoment B raw2396step0 raw2396step0Labels := by
      have ha : raw2396step0 = (fun i j => raw2396 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2396step0 raw2396; decide +kernel
      have hl : raw2396step0Labels = raw2396Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2396 raw2396Labels permutation158 permutation6
    mixedMoment B raw2396step0 raw2396step0Labels = mixedMoment B raw2396step1 raw2396step1Labels := by
      have ha : raw2396step1 = -raw2396step0 := by apply Matrix.ext; change ∀ i j, raw2396step1 i j = -(raw2396step0 i j); unfold raw2396step1 raw2396step0; decide +kernel
      have hl : raw2396step1Labels = raw2396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2396step1 raw2396step1Labels = mixedMoment B raw2396step2 raw2396step2Labels := by
      have ha : raw2396step2 = raw2396step1 := by apply Matrix.ext; unfold raw2396step2 raw2396step1; decide +kernel
      have hl : raw2396step1Labels = labelEmbedding1 ∘ raw2396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2396step1 raw2396step1Labels raw2396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31570 raw31570Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw31570 raw31570Labels = mixedMoment B raw31570step0 raw31570step0Labels := by
      have ha : raw31570step0 = (fun i j => raw31570 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31570step0 raw31570; decide +kernel
      have hl : raw31570step0Labels = raw31570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31570 raw31570Labels permutation152 permutation3
    mixedMoment B raw31570step0 raw31570step0Labels = mixedMoment B raw31570step1 raw31570step1Labels := by
      have ha : raw31570step1 = raw31570step0 := by apply Matrix.ext; unfold raw31570step1 raw31570step0; decide +kernel
      have hl : raw31570step0Labels = labelEmbedding6 ∘ raw31570step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31570step0 raw31570step0Labels raw31570step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4201 node4201Labels := by rfl

theorem canonical31571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31571 raw31571Labels = mixedMoment B node4635 node4635Labels := by
  calc
    mixedMoment B raw31571 raw31571Labels = mixedMoment B raw31571step0 raw31571step0Labels := by
      have ha : raw31571step0 = (fun i j => raw31571 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31571step0 raw31571; decide +kernel
      have hl : raw31571step0Labels = raw31571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31571 raw31571Labels permutation152 permutation3
    mixedMoment B raw31571step0 raw31571step0Labels = mixedMoment B raw31571step1 raw31571step1Labels := by
      have ha : raw31571step1 = raw31571step0 := by apply Matrix.ext; unfold raw31571step1 raw31571step0; decide +kernel
      have hl : raw31571step0Labels = labelEmbedding6 ∘ raw31571step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31571step0 raw31571step0Labels raw31571step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4635 node4635Labels := by rfl

theorem canonical31572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31572 raw31572Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw31572 raw31572Labels = mixedMoment B raw31572step0 raw31572step0Labels := by
      have ha : raw31572step0 = (fun i j => raw31572 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31572step0 raw31572; decide +kernel
      have hl : raw31572step0Labels = raw31572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31572 raw31572Labels permutation152 permutation3
    mixedMoment B raw31572step0 raw31572step0Labels = mixedMoment B raw31572step1 raw31572step1Labels := by
      have ha : raw31572step1 = raw31572step0 := by apply Matrix.ext; unfold raw31572step1 raw31572step0; decide +kernel
      have hl : raw31572step0Labels = labelEmbedding6 ∘ raw31572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31572step0 raw31572step0Labels raw31572step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical265
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33970 raw33970Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw33970 raw33970Labels = mixedMoment B raw33970step0 raw33970step0Labels := by
      have ha : raw33970step0 = (fun i j => raw33970 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33970step0 raw33970; decide +kernel
      have hl : raw33970step0Labels = raw33970Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33970 raw33970Labels permutation154 permutation3
    mixedMoment B raw33970step0 raw33970step0Labels = mixedMoment B raw33970step1 raw33970step1Labels := by
      have ha : raw33970step1 = raw33970step0 := by apply Matrix.ext; unfold raw33970step1 raw33970step0; decide +kernel
      have hl : raw33970step0Labels = labelEmbedding6 ∘ raw33970step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33970step0 raw33970step0Labels raw33970step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical33971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33971 raw33971Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw33971 raw33971Labels = mixedMoment B raw33971step0 raw33971step0Labels := by
      have ha : raw33971step0 = (fun i j => raw33971 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33971step0 raw33971; decide +kernel
      have hl : raw33971step0Labels = raw33971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33971 raw33971Labels permutation154 permutation3
    mixedMoment B raw33971step0 raw33971step0Labels = mixedMoment B raw33971step1 raw33971step1Labels := by
      have ha : raw33971step1 = raw33971step0 := by apply Matrix.ext; unfold raw33971step1 raw33971step0; decide +kernel
      have hl : raw33971step0Labels = labelEmbedding6 ∘ raw33971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33971step0 raw33971step0Labels raw33971step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical33972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33972 raw33972Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw33972 raw33972Labels = mixedMoment B raw33972step0 raw33972step0Labels := by
      have ha : raw33972step0 = (fun i j => raw33972 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33972step0 raw33972; decide +kernel
      have hl : raw33972step0Labels = raw33972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33972 raw33972Labels permutation164 permutation3
    mixedMoment B raw33972step0 raw33972step0Labels = mixedMoment B raw33972step1 raw33972step1Labels := by
      have ha : raw33972step1 = raw33972step0 := by apply Matrix.ext; unfold raw33972step1 raw33972step0; decide +kernel
      have hl : raw33972step0Labels = labelEmbedding6 ∘ raw33972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33972step0 raw33972step0Labels raw33972step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical33973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33973 raw33973Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw33973 raw33973Labels = mixedMoment B raw33973step0 raw33973step0Labels := by
      have ha : raw33973step0 = (fun i j => raw33973 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33973step0 raw33973; decide +kernel
      have hl : raw33973step0Labels = raw33973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33973 raw33973Labels permutation166 permutation3
    mixedMoment B raw33973step0 raw33973step0Labels = mixedMoment B raw33973step1 raw33973step1Labels := by
      have ha : raw33973step1 = raw33973step0 := by apply Matrix.ext; unfold raw33973step1 raw33973step0; decide +kernel
      have hl : raw33973step0Labels = labelEmbedding6 ∘ raw33973step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33973step0 raw33973step0Labels raw33973step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

theorem canonical33974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33974 raw33974Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw33974 raw33974Labels = mixedMoment B raw33974step0 raw33974step0Labels := by
      have ha : raw33974step0 = (fun i j => raw33974 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33974step0 raw33974; decide +kernel
      have hl : raw33974step0Labels = raw33974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33974 raw33974Labels permutation166 permutation3
    mixedMoment B raw33974step0 raw33974step0Labels = mixedMoment B raw33974step1 raw33974step1Labels := by
      have ha : raw33974step1 = raw33974step0 := by apply Matrix.ext; unfold raw33974step1 raw33974step0; decide +kernel
      have hl : raw33974step0Labels = labelEmbedding6 ∘ raw33974step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33974step0 raw33974step0Labels raw33974step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

theorem canonical33975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33975 raw33975Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw33975 raw33975Labels = mixedMoment B raw33975step0 raw33975step0Labels := by
      have ha : raw33975step0 = (fun i j => raw33975 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33975step0 raw33975; decide +kernel
      have hl : raw33975step0Labels = raw33975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33975 raw33975Labels permutation166 permutation3
    mixedMoment B raw33975step0 raw33975step0Labels = mixedMoment B raw33975step1 raw33975step1Labels := by
      have ha : raw33975step1 = raw33975step0 := by apply Matrix.ext; unfold raw33975step1 raw33975step0; decide +kernel
      have hl : raw33975step0Labels = labelEmbedding6 ∘ raw33975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33975step0 raw33975step0Labels raw33975step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical33976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33976 raw33976Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw33976 raw33976Labels = mixedMoment B raw33976step0 raw33976step0Labels := by
      have ha : raw33976step0 = (fun i j => raw33976 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33976step0 raw33976; decide +kernel
      have hl : raw33976step0Labels = raw33976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33976 raw33976Labels permutation155 permutation3
    mixedMoment B raw33976step0 raw33976step0Labels = mixedMoment B raw33976step1 raw33976step1Labels := by
      have ha : raw33976step1 = raw33976step0 := by apply Matrix.ext; unfold raw33976step1 raw33976step0; decide +kernel
      have hl : raw33976step0Labels = labelEmbedding6 ∘ raw33976step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33976step0 raw33976step0Labels raw33976step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4197 node4197Labels := by rfl

theorem canonical33977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33977 raw33977Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw33977 raw33977Labels = mixedMoment B raw33977step0 raw33977step0Labels := by
      have ha : raw33977step0 = (fun i j => raw33977 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33977step0 raw33977; decide +kernel
      have hl : raw33977step0Labels = raw33977Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33977 raw33977Labels permutation155 permutation3
    mixedMoment B raw33977step0 raw33977step0Labels = mixedMoment B raw33977step1 raw33977step1Labels := by
      have ha : raw33977step1 = raw33977step0 := by apply Matrix.ext; unfold raw33977step1 raw33977step0; decide +kernel
      have hl : raw33977step0Labels = labelEmbedding6 ∘ raw33977step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33977step0 raw33977step0Labels raw33977step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

theorem canonical33978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33978 raw33978Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw33978 raw33978Labels = mixedMoment B raw33978step0 raw33978step0Labels := by
      have ha : raw33978step0 = (fun i j => raw33978 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33978step0 raw33978; decide +kernel
      have hl : raw33978step0Labels = raw33978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33978 raw33978Labels permutation155 permutation3
    mixedMoment B raw33978step0 raw33978step0Labels = mixedMoment B raw33978step1 raw33978step1Labels := by
      have ha : raw33978step1 = raw33978step0 := by apply Matrix.ext; unfold raw33978step1 raw33978step0; decide +kernel
      have hl : raw33978step0Labels = labelEmbedding6 ∘ raw33978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33978step0 raw33978step0Labels raw33978step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical33979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33979 raw33979Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw33979 raw33979Labels = mixedMoment B raw33979step0 raw33979step0Labels := by
      have ha : raw33979step0 = (fun i j => raw33979 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33979step0 raw33979; decide +kernel
      have hl : raw33979step0Labels = raw33979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33979 raw33979Labels permutation165 permutation3
    mixedMoment B raw33979step0 raw33979step0Labels = mixedMoment B raw33979step1 raw33979step1Labels := by
      have ha : raw33979step1 = raw33979step0 := by apply Matrix.ext; unfold raw33979step1 raw33979step0; decide +kernel
      have hl : raw33979step0Labels = labelEmbedding6 ∘ raw33979step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33979step0 raw33979step0Labels raw33979step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical33980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33980 raw33980Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw33980 raw33980Labels = mixedMoment B raw33980step0 raw33980step0Labels := by
      have ha : raw33980step0 = (fun i j => raw33980 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33980step0 raw33980; decide +kernel
      have hl : raw33980step0Labels = raw33980Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33980 raw33980Labels permutation154 permutation3
    mixedMoment B raw33980step0 raw33980step0Labels = mixedMoment B raw33980step1 raw33980step1Labels := by
      have ha : raw33980step1 = raw33980step0 := by apply Matrix.ext; unfold raw33980step1 raw33980step0; decide +kernel
      have hl : raw33980step0Labels = labelEmbedding6 ∘ raw33980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33980step0 raw33980step0Labels raw33980step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4196 node4196Labels := by rfl

theorem canonical33981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33981 raw33981Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw33981 raw33981Labels = mixedMoment B raw33981step0 raw33981step0Labels := by
      have ha : raw33981step0 = (fun i j => raw33981 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33981step0 raw33981; decide +kernel
      have hl : raw33981step0Labels = raw33981Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33981 raw33981Labels permutation154 permutation3
    mixedMoment B raw33981step0 raw33981step0Labels = mixedMoment B raw33981step1 raw33981step1Labels := by
      have ha : raw33981step1 = raw33981step0 := by apply Matrix.ext; unfold raw33981step1 raw33981step0; decide +kernel
      have hl : raw33981step0Labels = labelEmbedding6 ∘ raw33981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33981step0 raw33981step0Labels raw33981step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

theorem canonical33982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33982 raw33982Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw33982 raw33982Labels = mixedMoment B raw33982step0 raw33982step0Labels := by
      have ha : raw33982step0 = (fun i j => raw33982 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33982step0 raw33982; decide +kernel
      have hl : raw33982step0Labels = raw33982Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33982 raw33982Labels permutation154 permutation3
    mixedMoment B raw33982step0 raw33982step0Labels = mixedMoment B raw33982step1 raw33982step1Labels := by
      have ha : raw33982step1 = raw33982step0 := by apply Matrix.ext; unfold raw33982step1 raw33982step0; decide +kernel
      have hl : raw33982step0Labels = labelEmbedding6 ∘ raw33982step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33982step0 raw33982step0Labels raw33982step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical33983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33983 raw33983Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw33983 raw33983Labels = mixedMoment B raw33983step0 raw33983step0Labels := by
      have ha : raw33983step0 = (fun i j => raw33983 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33983step0 raw33983; decide +kernel
      have hl : raw33983step0Labels = raw33983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33983 raw33983Labels permutation164 permutation3
    mixedMoment B raw33983step0 raw33983step0Labels = mixedMoment B raw33983step1 raw33983step1Labels := by
      have ha : raw33983step1 = raw33983step0 := by apply Matrix.ext; unfold raw33983step1 raw33983step0; decide +kernel
      have hl : raw33983step0Labels = labelEmbedding6 ∘ raw33983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33983step0 raw33983step0Labels raw33983step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

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

theorem canonical852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw852 raw852Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw852 raw852Labels = mixedMoment B raw852step0 raw852step0Labels := by
      have ha : raw852step0 = (fun i j => raw852 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw852step0 raw852; decide +kernel
      have hl : raw852step0Labels = raw852Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw852 raw852Labels permutation152 permutation4
    mixedMoment B raw852step0 raw852step0Labels = mixedMoment B raw852step1 raw852step1Labels := by
      have ha : raw852step1 = raw852step0 := by apply Matrix.ext; unfold raw852step1 raw852step0; decide +kernel
      have hl : raw852step0Labels = labelEmbedding7 ∘ raw852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw852step0 raw852step0Labels raw852step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4196 node4196Labels := by rfl

theorem canonical853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw853 raw853Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw853 raw853Labels = mixedMoment B raw853step0 raw853step0Labels := by
      have ha : raw853step0 = (fun i j => raw853 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw853step0 raw853; decide +kernel
      have hl : raw853step0Labels = raw853Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw853 raw853Labels permutation152 permutation4
    _ = mixedMoment B node699 node699Labels := by rfl

theorem canonical854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw854 raw854Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw854 raw854Labels = mixedMoment B raw854step0 raw854step0Labels := by
      have ha : raw854step0 = (fun i j => raw854 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw854step0 raw854; decide +kernel
      have hl : raw854step0Labels = raw854Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw854 raw854Labels permutation158 permutation6
    mixedMoment B raw854step0 raw854step0Labels = mixedMoment B raw854step1 raw854step1Labels := by
      have ha : raw854step1 = -raw854step0 := by apply Matrix.ext; change ∀ i j, raw854step1 i j = -(raw854step0 i j); unfold raw854step1 raw854step0; decide +kernel
      have hl : raw854step1Labels = raw854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw854step1 raw854step1Labels = mixedMoment B raw854step2 raw854step2Labels := by
      have ha : raw854step2 = raw854step1 := by apply Matrix.ext; unfold raw854step2 raw854step1; decide +kernel
      have hl : raw854step1Labels = labelEmbedding1 ∘ raw854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw854step1 raw854step1Labels raw854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node748 node748Labels := by rfl

theorem canonical855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw855 raw855Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw855 raw855Labels = mixedMoment B raw855step0 raw855step0Labels := by
      have ha : raw855step0 = (fun i j => raw855 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw855step0 raw855; decide +kernel
      have hl : raw855step0Labels = raw855Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw855 raw855Labels permutation152 permutation4
    mixedMoment B raw855step0 raw855step0Labels = mixedMoment B raw855step1 raw855step1Labels := by
      have ha : raw855step1 = raw855step0 := by apply Matrix.ext; unfold raw855step1 raw855step0; decide +kernel
      have hl : raw855step0Labels = labelEmbedding7 ∘ raw855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw855step0 raw855step0Labels raw855step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4197 node4197Labels := by rfl

theorem canonical856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw856 raw856Labels = mixedMoment B node700 node700Labels := by
  calc
    mixedMoment B raw856 raw856Labels = mixedMoment B raw856step0 raw856step0Labels := by
      have ha : raw856step0 = (fun i j => raw856 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw856step0 raw856; decide +kernel
      have hl : raw856step0Labels = raw856Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw856 raw856Labels permutation152 permutation4
    _ = mixedMoment B node700 node700Labels := by rfl

theorem canonical857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw857 raw857Labels = mixedMoment B node749 node749Labels := by
  calc
    mixedMoment B raw857 raw857Labels = mixedMoment B raw857step0 raw857step0Labels := by
      have ha : raw857step0 = (fun i j => raw857 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw857step0 raw857; decide +kernel
      have hl : raw857step0Labels = raw857Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw857 raw857Labels permutation158 permutation6
    mixedMoment B raw857step0 raw857step0Labels = mixedMoment B raw857step1 raw857step1Labels := by
      have ha : raw857step1 = -raw857step0 := by apply Matrix.ext; change ∀ i j, raw857step1 i j = -(raw857step0 i j); unfold raw857step1 raw857step0; decide +kernel
      have hl : raw857step1Labels = raw857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw857step1 raw857step1Labels = mixedMoment B raw857step2 raw857step2Labels := by
      have ha : raw857step2 = raw857step1 := by apply Matrix.ext; unfold raw857step2 raw857step1; decide +kernel
      have hl : raw857step1Labels = labelEmbedding1 ∘ raw857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw857step1 raw857step1Labels raw857step2Labels labelEmbedding1 hl
    _ = mixedMoment B node749 node749Labels := by rfl

theorem canonical867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw867 raw867Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw867 raw867Labels = mixedMoment B raw867step0 raw867step0Labels := by
      have ha : raw867step0 = (fun i j => raw867 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw867step0 raw867; decide +kernel
      have hl : raw867step0Labels = raw867Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw867 raw867Labels permutation152 permutation4
    mixedMoment B raw867step0 raw867step0Labels = mixedMoment B raw867step1 raw867step1Labels := by
      have ha : raw867step1 = raw867step0 := by apply Matrix.ext; unfold raw867step1 raw867step0; decide +kernel
      have hl : raw867step0Labels = labelEmbedding7 ∘ raw867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw867step0 raw867step0Labels raw867step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4201 node4201Labels := by rfl

theorem canonical868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw868 raw868Labels = mixedMoment B node704 node704Labels := by
  calc
    mixedMoment B raw868 raw868Labels = mixedMoment B raw868step0 raw868step0Labels := by
      have ha : raw868step0 = (fun i j => raw868 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw868step0 raw868; decide +kernel
      have hl : raw868step0Labels = raw868Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw868 raw868Labels permutation152 permutation4
    _ = mixedMoment B node704 node704Labels := by rfl

theorem canonical869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw869 raw869Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw869 raw869Labels = mixedMoment B raw869step0 raw869step0Labels := by
      have ha : raw869step0 = (fun i j => raw869 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw869step0 raw869; decide +kernel
      have hl : raw869step0Labels = raw869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw869 raw869Labels permutation152 permutation6
    mixedMoment B raw869step0 raw869step0Labels = mixedMoment B raw869step1 raw869step1Labels := by
      have ha : raw869step1 = -raw869step0 := by apply Matrix.ext; change ∀ i j, raw869step1 i j = -(raw869step0 i j); unfold raw869step1 raw869step0; decide +kernel
      have hl : raw869step1Labels = raw869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw869step1 raw869step1Labels = mixedMoment B raw869step2 raw869step2Labels := by
      have ha : raw869step2 = raw869step1 := by apply Matrix.ext; unfold raw869step2 raw869step1; decide +kernel
      have hl : raw869step1Labels = labelEmbedding1 ∘ raw869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw869step1 raw869step1Labels raw869step2Labels labelEmbedding1 hl
    _ = mixedMoment B node761 node761Labels := by rfl

theorem canonical891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw891 raw891Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw891 raw891Labels = mixedMoment B raw891step0 raw891step0Labels := by
      have ha : raw891step0 = (fun i j => raw891 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw891step0 raw891; decide +kernel
      have hl : raw891step0Labels = raw891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw891 raw891Labels permutation152 permutation4
    mixedMoment B raw891step0 raw891step0Labels = mixedMoment B raw891step1 raw891step1Labels := by
      have ha : raw891step1 = raw891step0 := by apply Matrix.ext; unfold raw891step1 raw891step0; decide +kernel
      have hl : raw891step0Labels = labelEmbedding7 ∘ raw891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw891step0 raw891step0Labels raw891step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

theorem canonical892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw892 raw892Labels = mixedMoment B node713 node713Labels := by
  calc
    mixedMoment B raw892 raw892Labels = mixedMoment B raw892step0 raw892step0Labels := by
      have ha : raw892step0 = (fun i j => raw892 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw892step0 raw892; decide +kernel
      have hl : raw892step0Labels = raw892Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw892 raw892Labels permutation152 permutation4
    _ = mixedMoment B node713 node713Labels := by rfl

theorem canonical893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw893 raw893Labels = mixedMoment B node751 node751Labels := by
  calc
    mixedMoment B raw893 raw893Labels = mixedMoment B raw893step0 raw893step0Labels := by
      have ha : raw893step0 = (fun i j => raw893 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw893step0 raw893; decide +kernel
      have hl : raw893step0Labels = raw893Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw893 raw893Labels permutation153 permutation6
    mixedMoment B raw893step0 raw893step0Labels = mixedMoment B raw893step1 raw893step1Labels := by
      have ha : raw893step1 = -raw893step0 := by apply Matrix.ext; change ∀ i j, raw893step1 i j = -(raw893step0 i j); unfold raw893step1 raw893step0; decide +kernel
      have hl : raw893step1Labels = raw893step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw893step1 raw893step1Labels = mixedMoment B raw893step2 raw893step2Labels := by
      have ha : raw893step2 = raw893step1 := by apply Matrix.ext; unfold raw893step2 raw893step1; decide +kernel
      have hl : raw893step1Labels = labelEmbedding1 ∘ raw893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw893step1 raw893step1Labels raw893step2Labels labelEmbedding1 hl
    _ = mixedMoment B node751 node751Labels := by rfl

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

theorem singleton4196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4196 node4196Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node699 node699Labels + mixedMoment B node748 node748Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw852 singletonSmall4196
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4196) = raw852Labels := by decide +kernel
  rw [hl, canonical852 B hB] at h
  have hc0 : mixedMoment B raw852 (Fin.cases (0 : Fin 2) singletonSmall4196) =
      mixedMoment B node699 node699Labels := by
    have ha : raw852 = raw853 := by apply Matrix.ext; unfold raw852 raw853; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4196 = raw853Labels := by decide +kernel
    rw [ha, hj, canonical853 B hB]
  have hc1 : mixedMoment B raw852 (Fin.cases (1 : Fin 2) singletonSmall4196) =
      mixedMoment B node748 node748Labels := by
    have ha : raw852 = raw854 := by apply Matrix.ext; unfold raw852 raw854; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4196 = raw854Labels := by decide +kernel
    rw [ha, hj, canonical854 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4197 node4197Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node700 node700Labels + mixedMoment B node749 node749Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw855 singletonSmall4197
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4197) = raw855Labels := by decide +kernel
  rw [hl, canonical855 B hB] at h
  have hc0 : mixedMoment B raw855 (Fin.cases (0 : Fin 2) singletonSmall4197) =
      mixedMoment B node700 node700Labels := by
    have ha : raw855 = raw856 := by apply Matrix.ext; unfold raw855 raw856; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4197 = raw856Labels := by decide +kernel
    rw [ha, hj, canonical856 B hB]
  have hc1 : mixedMoment B raw855 (Fin.cases (1 : Fin 2) singletonSmall4197) =
      mixedMoment B node749 node749Labels := by
    have ha : raw855 = raw857 := by apply Matrix.ext; unfold raw855 raw857; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4197 = raw857Labels := by decide +kernel
    rw [ha, hj, canonical857 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4201 node4201Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node704 node704Labels + mixedMoment B node761 node761Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw867 singletonSmall4201
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4201) = raw867Labels := by decide +kernel
  rw [hl, canonical867 B hB] at h
  have hc0 : mixedMoment B raw867 (Fin.cases (0 : Fin 2) singletonSmall4201) =
      mixedMoment B node704 node704Labels := by
    have ha : raw867 = raw868 := by apply Matrix.ext; unfold raw867 raw868; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4201 = raw868Labels := by decide +kernel
    rw [ha, hj, canonical868 B hB]
  have hc1 : mixedMoment B raw867 (Fin.cases (1 : Fin 2) singletonSmall4201) =
      mixedMoment B node761 node761Labels := by
    have ha : raw867 = raw869 := by apply Matrix.ext; unfold raw867 raw869; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4201 = raw869Labels := by decide +kernel
    rw [ha, hj, canonical869 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4210 node4210Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node713 node713Labels + mixedMoment B node751 node751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw891 singletonSmall4210
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4210) = raw891Labels := by decide +kernel
  rw [hl, canonical891 B hB] at h
  have hc0 : mixedMoment B raw891 (Fin.cases (0 : Fin 2) singletonSmall4210) =
      mixedMoment B node713 node713Labels := by
    have ha : raw891 = raw892 := by apply Matrix.ext; unfold raw891 raw892; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4210 = raw892Labels := by decide +kernel
    rw [ha, hj, canonical892 B hB]
  have hc1 : mixedMoment B raw891 (Fin.cases (1 : Fin 2) singletonSmall4210) =
      mixedMoment B node751 node751Labels := by
    have ha : raw891 = raw893 := by apply Matrix.ext; unfold raw891 raw893; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4210 = raw893Labels := by decide +kernel
    rw [ha, hj, canonical893 B hB]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4631 node4631Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1760 node1760Labels + mixedMoment B node1836 node1836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1473 singletonSmall4631
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4631) = raw1473Labels := by decide +kernel
  rw [hl, canonical1473 B hB] at h
  have hc0 : mixedMoment B raw1473 (Fin.cases (0 : Fin 2) singletonSmall4631) =
      mixedMoment B node1760 node1760Labels := by
    have ha : raw1473 = raw1474 := by apply Matrix.ext; unfold raw1473 raw1474; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4631 = raw1474Labels := by decide +kernel
    rw [ha, hj, canonical1474 B hB]
  have hc1 : mixedMoment B raw1473 (Fin.cases (1 : Fin 2) singletonSmall4631) =
      mixedMoment B node1836 node1836Labels := by
    have ha : raw1473 = raw1475 := by apply Matrix.ext; unfold raw1473 raw1475; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4631 = raw1475Labels := by decide +kernel
    rw [ha, hj, canonical1475 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4632 node4632Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1761 node1761Labels + mixedMoment B node1837 node1837Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1476 singletonSmall4632
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4632) = raw1476Labels := by decide +kernel
  rw [hl, canonical1476 B hB] at h
  have hc0 : mixedMoment B raw1476 (Fin.cases (0 : Fin 2) singletonSmall4632) =
      mixedMoment B node1761 node1761Labels := by
    have ha : raw1476 = raw1477 := by apply Matrix.ext; unfold raw1476 raw1477; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4632 = raw1477Labels := by decide +kernel
    rw [ha, hj, canonical1477 B hB]
  have hc1 : mixedMoment B raw1476 (Fin.cases (1 : Fin 2) singletonSmall4632) =
      mixedMoment B node1837 node1837Labels := by
    have ha : raw1476 = raw1478 := by apply Matrix.ext; unfold raw1476 raw1478; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4632 = raw1478Labels := by decide +kernel
    rw [ha, hj, canonical1478 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4635 node4635Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1764 node1764Labels + mixedMoment B node1848 node1848Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1485 singletonSmall4635
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4635) = raw1485Labels := by decide +kernel
  rw [hl, canonical1485 B hB] at h
  have hc0 : mixedMoment B raw1485 (Fin.cases (0 : Fin 2) singletonSmall4635) =
      mixedMoment B node1764 node1764Labels := by
    have ha : raw1485 = raw1486 := by apply Matrix.ext; unfold raw1485 raw1486; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4635 = raw1486Labels := by decide +kernel
    rw [ha, hj, canonical1486 B hB]
  have hc1 : mixedMoment B raw1485 (Fin.cases (1 : Fin 2) singletonSmall4635) =
      mixedMoment B node1848 node1848Labels := by
    have ha : raw1485 = raw1487 := by apply Matrix.ext; unfold raw1485 raw1487; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4635 = raw1487Labels := by decide +kernel
    rw [ha, hj, canonical1487 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4642 node4642Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1771 node1771Labels + mixedMoment B node1838 node1838Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1503 singletonSmall4642
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4642) = raw1503Labels := by decide +kernel
  rw [hl, canonical1503 B hB] at h
  have hc0 : mixedMoment B raw1503 (Fin.cases (0 : Fin 2) singletonSmall4642) =
      mixedMoment B node1771 node1771Labels := by
    have ha : raw1503 = raw1504 := by apply Matrix.ext; unfold raw1503 raw1504; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4642 = raw1504Labels := by decide +kernel
    rw [ha, hj, canonical1504 B hB]
  have hc1 : mixedMoment B raw1503 (Fin.cases (1 : Fin 2) singletonSmall4642) =
      mixedMoment B node1838 node1838Labels := by
    have ha : raw1503 = raw1505 := by apply Matrix.ext; unfold raw1503 raw1505; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4642 = raw1505Labels := by decide +kernel
    rw [ha, hj, canonical1505 B hB]
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

theorem singleton4760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4760 node4760Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1960 node1960Labels + mixedMoment B node2173 node2173Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1689 singletonSmall4760
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4760) = raw1689Labels := by decide +kernel
  rw [hl, canonical1689 B hB] at h
  have hc0 : mixedMoment B raw1689 (Fin.cases (0 : Fin 2) singletonSmall4760) =
      mixedMoment B node1960 node1960Labels := by
    have ha : raw1689 = raw1690 := by apply Matrix.ext; unfold raw1689 raw1690; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4760 = raw1690Labels := by decide +kernel
    rw [ha, hj, canonical1690 B hB]
  have hc1 : mixedMoment B raw1689 (Fin.cases (1 : Fin 2) singletonSmall4760) =
      mixedMoment B node2173 node2173Labels := by
    have ha : raw1689 = raw1691 := by apply Matrix.ext; unfold raw1689 raw1691; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4760 = raw1691Labels := by decide +kernel
    rw [ha, hj, canonical1691 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4763 node4763Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1963 node1963Labels + mixedMoment B node2174 node2174Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1692 singletonSmall4763
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4763) = raw1692Labels := by decide +kernel
  rw [hl, canonical1692 B hB] at h
  have hc0 : mixedMoment B raw1692 (Fin.cases (0 : Fin 2) singletonSmall4763) =
      mixedMoment B node1963 node1963Labels := by
    have ha : raw1692 = raw1693 := by apply Matrix.ext; unfold raw1692 raw1693; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4763 = raw1693Labels := by decide +kernel
    rw [ha, hj, canonical1693 B hB]
  have hc1 : mixedMoment B raw1692 (Fin.cases (1 : Fin 2) singletonSmall4763) =
      mixedMoment B node2174 node2174Labels := by
    have ha : raw1692 = raw1694 := by apply Matrix.ext; unfold raw1692 raw1694; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4763 = raw1694Labels := by decide +kernel
    rw [ha, hj, canonical1694 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4767 node4767Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1967 node1967Labels + mixedMoment B node2183 node2183Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1701 singletonSmall4767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4767) = raw1701Labels := by decide +kernel
  rw [hl, canonical1701 B hB] at h
  have hc0 : mixedMoment B raw1701 (Fin.cases (0 : Fin 2) singletonSmall4767) =
      mixedMoment B node1967 node1967Labels := by
    have ha : raw1701 = raw1702 := by apply Matrix.ext; unfold raw1701 raw1702; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4767 = raw1702Labels := by decide +kernel
    rw [ha, hj, canonical1702 B hB]
  have hc1 : mixedMoment B raw1701 (Fin.cases (1 : Fin 2) singletonSmall4767) =
      mixedMoment B node2183 node2183Labels := by
    have ha : raw1701 = raw1703 := by apply Matrix.ext; unfold raw1701 raw1703; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4767 = raw1703Labels := by decide +kernel
    rw [ha, hj, canonical1703 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4779 node4779Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1987 node1987Labels + mixedMoment B node1996 node1996Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1713 singletonSmall4779
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4779) = raw1713Labels := by decide +kernel
  rw [hl, canonical1713 B hB] at h
  have hc0 : mixedMoment B raw1713 (Fin.cases (0 : Fin 2) singletonSmall4779) =
      mixedMoment B node1987 node1987Labels := by
    have ha : raw1713 = raw1714 := by apply Matrix.ext; unfold raw1713 raw1714; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4779 = raw1714Labels := by decide +kernel
    rw [ha, hj, canonical1714 B hB]
  have hc1 : mixedMoment B raw1713 (Fin.cases (1 : Fin 2) singletonSmall4779) =
      mixedMoment B node1996 node1996Labels := by
    have ha : raw1713 = raw1715 := by apply Matrix.ext; unfold raw1713 raw1715; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4779 = raw1715Labels := by decide +kernel
    rw [ha, hj, canonical1715 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4782 node4782Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1990 node1990Labels + mixedMoment B node1997 node1997Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1716 singletonSmall4782
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4782) = raw1716Labels := by decide +kernel
  rw [hl, canonical1716 B hB] at h
  have hc0 : mixedMoment B raw1716 (Fin.cases (0 : Fin 2) singletonSmall4782) =
      mixedMoment B node1990 node1990Labels := by
    have ha : raw1716 = raw1717 := by apply Matrix.ext; unfold raw1716 raw1717; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4782 = raw1717Labels := by decide +kernel
    rw [ha, hj, canonical1717 B hB]
  have hc1 : mixedMoment B raw1716 (Fin.cases (1 : Fin 2) singletonSmall4782) =
      mixedMoment B node1997 node1997Labels := by
    have ha : raw1716 = raw1718 := by apply Matrix.ext; unfold raw1716 raw1718; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4782 = raw1718Labels := by decide +kernel
    rw [ha, hj, canonical1718 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4787 node4787Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2000 node2000Labels + mixedMoment B node2000 node2000Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1719 singletonSmall4787
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4787) = raw1719Labels := by decide +kernel
  rw [hl, canonical1719 B hB] at h
  have hc0 : mixedMoment B raw1719 (Fin.cases (0 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1720 := by apply Matrix.ext; unfold raw1719 raw1720; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4787 = raw1720Labels := by decide +kernel
    rw [ha, hj, canonical1720 B hB]
  have hc1 : mixedMoment B raw1719 (Fin.cases (1 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1721 := by apply Matrix.ext; unfold raw1719 raw1721; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4787 = raw1721Labels := by decide +kernel
    rw [ha, hj, canonical1721 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5352 node5352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3690 node3690Labels + mixedMoment B node3764 node3764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2394 singletonSmall5352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5352) = raw2394Labels := by decide +kernel
  rw [hl, canonical2394 B hB] at h
  have hc0 : mixedMoment B raw2394 (Fin.cases (0 : Fin 2) singletonSmall5352) =
      mixedMoment B node3690 node3690Labels := by
    have ha : raw2394 = raw2395 := by apply Matrix.ext; unfold raw2394 raw2395; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5352 = raw2395Labels := by decide +kernel
    rw [ha, hj, canonical2395 B hB]
  have hc1 : mixedMoment B raw2394 (Fin.cases (1 : Fin 2) singletonSmall5352) =
      mixedMoment B node3764 node3764Labels := by
    have ha : raw2394 = raw2396 := by apply Matrix.ext; unfold raw2394 raw2396; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5352 = raw2396Labels := by decide +kernel
    rw [ha, hj, canonical2396 B hB]
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

theorem sound704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node704 node704Labels = Sparse.eval nodeValue704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 704) = mixedMoment B node704 node704Labels := rfl
  simpa [nodeValue704, Sparse.eval] using hc.symm

theorem sound713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node713 node713Labels = Sparse.eval nodeValue713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 713) = mixedMoment B node713 node713Labels := rfl
  simpa [nodeValue713, Sparse.eval] using hc.symm

theorem sound748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node748 node748Labels = Sparse.eval nodeValue748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 748) = mixedMoment B node748 node748Labels := rfl
  simpa [nodeValue748, Sparse.eval] using hc.symm

theorem sound749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node749 node749Labels = Sparse.eval nodeValue749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 749) = mixedMoment B node749 node749Labels := rfl
  simpa [nodeValue749, Sparse.eval] using hc.symm

theorem sound751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node751 node751Labels = Sparse.eval nodeValue751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 751) = mixedMoment B node751 node751Labels := rfl
  simpa [nodeValue751, Sparse.eval] using hc.symm

theorem sound761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node761 node761Labels = Sparse.eval nodeValue761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 761) = mixedMoment B node761 node761Labels := rfl
  simpa [nodeValue761, Sparse.eval] using hc.symm

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

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

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

theorem sound1760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1760 node1760Labels = Sparse.eval nodeValue1760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1760) = mixedMoment B node1760 node1760Labels := rfl
  simpa [nodeValue1760, Sparse.eval] using hc.symm

theorem sound1761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1761 node1761Labels = Sparse.eval nodeValue1761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1761) = mixedMoment B node1761 node1761Labels := rfl
  simpa [nodeValue1761, Sparse.eval] using hc.symm

theorem sound1764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1764 node1764Labels = Sparse.eval nodeValue1764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1764) = mixedMoment B node1764 node1764Labels := rfl
  simpa [nodeValue1764, Sparse.eval] using hc.symm

theorem sound1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1771 node1771Labels = Sparse.eval nodeValue1771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1771) = mixedMoment B node1771 node1771Labels := rfl
  simpa [nodeValue1771, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1836 node1836Labels = Sparse.eval nodeValue1836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1836) = mixedMoment B node1836 node1836Labels := rfl
  simpa [nodeValue1836, Sparse.eval] using hc.symm

theorem sound1837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1837 node1837Labels = Sparse.eval nodeValue1837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1837) = mixedMoment B node1837 node1837Labels := rfl
  simpa [nodeValue1837, Sparse.eval] using hc.symm

theorem sound1838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1838 node1838Labels = Sparse.eval nodeValue1838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1838) = mixedMoment B node1838 node1838Labels := rfl
  simpa [nodeValue1838, Sparse.eval] using hc.symm

theorem sound1848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1848 node1848Labels = Sparse.eval nodeValue1848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1848) = mixedMoment B node1848 node1848Labels := rfl
  simpa [nodeValue1848, Sparse.eval] using hc.symm

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

theorem sound1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1960 node1960Labels = Sparse.eval nodeValue1960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1960) = mixedMoment B node1960 node1960Labels := rfl
  simpa [nodeValue1960, Sparse.eval] using hc.symm

theorem sound1963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1963 node1963Labels = Sparse.eval nodeValue1963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1963) = mixedMoment B node1963 node1963Labels := rfl
  simpa [nodeValue1963, Sparse.eval] using hc.symm

theorem sound1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1967 node1967Labels = Sparse.eval nodeValue1967 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1967) = mixedMoment B node1967 node1967Labels := rfl
  simpa [nodeValue1967, Sparse.eval] using hc.symm

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

theorem sound1987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1987 node1987Labels = Sparse.eval nodeValue1987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1987) = mixedMoment B node1987 node1987Labels := rfl
  simpa [nodeValue1987, Sparse.eval] using hc.symm

theorem sound1990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1990 node1990Labels = Sparse.eval nodeValue1990 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1990) = mixedMoment B node1990 node1990Labels := rfl
  simpa [nodeValue1990, Sparse.eval] using hc.symm

theorem sound1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1996 node1996Labels = Sparse.eval nodeValue1996 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1996) = mixedMoment B node1996 node1996Labels := rfl
  simpa [nodeValue1996, Sparse.eval] using hc.symm

theorem sound1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1997 node1997Labels = Sparse.eval nodeValue1997 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1997) = mixedMoment B node1997 node1997Labels := rfl
  simpa [nodeValue1997, Sparse.eval] using hc.symm

theorem sound2000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2000 node2000Labels = Sparse.eval nodeValue2000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2000) = mixedMoment B node2000 node2000Labels := rfl
  simpa [nodeValue2000, Sparse.eval] using hc.symm

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

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

theorem sound2173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2173 node2173Labels = Sparse.eval nodeValue2173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2173) = mixedMoment B node2173 node2173Labels := rfl
  simpa [nodeValue2173, Sparse.eval] using hc.symm

theorem sound2174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2174 node2174Labels = Sparse.eval nodeValue2174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2174) = mixedMoment B node2174 node2174Labels := rfl
  simpa [nodeValue2174, Sparse.eval] using hc.symm

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

theorem sound2183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2183 node2183Labels = Sparse.eval nodeValue2183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2183) = mixedMoment B node2183 node2183Labels := rfl
  simpa [nodeValue2183, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

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

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

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

theorem sound4196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4196 node4196Labels = Sparse.eval nodeValue4196 (mixedVector B) := by
  have h := singleton4196 B _hB
  rw [sound699 B _hB _hF, sound748 B _hB _hF] at h
  norm_num [nodeValue4196, nodeValue699, nodeValue748, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4197 node4197Labels = Sparse.eval nodeValue4197 (mixedVector B) := by
  have h := singleton4197 B _hB
  rw [sound700 B _hB _hF, sound749 B _hB _hF] at h
  norm_num [nodeValue4197, nodeValue700, nodeValue749, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4201 node4201Labels = Sparse.eval nodeValue4201 (mixedVector B) := by
  have h := singleton4201 B _hB
  rw [sound704 B _hB _hF, sound761 B _hB _hF] at h
  norm_num [nodeValue4201, nodeValue704, nodeValue761, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4210 node4210Labels = Sparse.eval nodeValue4210 (mixedVector B) := by
  have h := singleton4210 B _hB
  rw [sound713 B _hB _hF, sound751 B _hB _hF] at h
  norm_num [nodeValue4210, nodeValue713, nodeValue751, Sparse.eval] at h ⊢
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

theorem sound4249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4249 node4249Labels = Sparse.eval nodeValue4249 (mixedVector B) := by
  have h := singleton4249 B _hB
  rw [sound783 B _hB _hF, sound803 B _hB _hF] at h
  norm_num [nodeValue4249, nodeValue783, nodeValue803, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4631 node4631Labels = Sparse.eval nodeValue4631 (mixedVector B) := by
  have h := singleton4631 B _hB
  rw [sound1760 B _hB _hF, sound1836 B _hB _hF] at h
  norm_num [nodeValue4631, nodeValue1760, nodeValue1836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4632 node4632Labels = Sparse.eval nodeValue4632 (mixedVector B) := by
  have h := singleton4632 B _hB
  rw [sound1761 B _hB _hF, sound1837 B _hB _hF] at h
  norm_num [nodeValue4632, nodeValue1761, nodeValue1837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4635 node4635Labels = Sparse.eval nodeValue4635 (mixedVector B) := by
  have h := singleton4635 B _hB
  rw [sound1764 B _hB _hF, sound1848 B _hB _hF] at h
  norm_num [nodeValue4635, nodeValue1764, nodeValue1848, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4642 node4642Labels = Sparse.eval nodeValue4642 (mixedVector B) := by
  have h := singleton4642 B _hB
  rw [sound1771 B _hB _hF, sound1838 B _hB _hF] at h
  norm_num [nodeValue4642, nodeValue1771, nodeValue1838, Sparse.eval] at h ⊢
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

theorem sound4760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4760 node4760Labels = Sparse.eval nodeValue4760 (mixedVector B) := by
  have h := singleton4760 B _hB
  rw [sound1960 B _hB _hF, sound2173 B _hB _hF] at h
  norm_num [nodeValue4760, nodeValue1960, nodeValue2173, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4763 node4763Labels = Sparse.eval nodeValue4763 (mixedVector B) := by
  have h := singleton4763 B _hB
  rw [sound1963 B _hB _hF, sound2174 B _hB _hF] at h
  norm_num [nodeValue4763, nodeValue1963, nodeValue2174, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4767 node4767Labels = Sparse.eval nodeValue4767 (mixedVector B) := by
  have h := singleton4767 B _hB
  rw [sound1967 B _hB _hF, sound2183 B _hB _hF] at h
  norm_num [nodeValue4767, nodeValue1967, nodeValue2183, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4779 node4779Labels = Sparse.eval nodeValue4779 (mixedVector B) := by
  have h := singleton4779 B _hB
  rw [sound1987 B _hB _hF, sound1996 B _hB _hF] at h
  norm_num [nodeValue4779, nodeValue1987, nodeValue1996, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4782 node4782Labels = Sparse.eval nodeValue4782 (mixedVector B) := by
  have h := singleton4782 B _hB
  rw [sound1990 B _hB _hF, sound1997 B _hB _hF] at h
  norm_num [nodeValue4782, nodeValue1990, nodeValue1997, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4787 node4787Labels = Sparse.eval nodeValue4787 (mixedVector B) := by
  have h := singleton4787 B _hB
  rw [sound2000 B _hB _hF] at h
  norm_num [nodeValue4787, nodeValue2000, Sparse.eval] at h ⊢
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

theorem sound4801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4801 node4801Labels = Sparse.eval nodeValue4801 (mixedVector B) := by
  have h := singleton4801 B _hB
  rw [sound2019 B _hB _hF, sound2190 B _hB _hF] at h
  norm_num [nodeValue4801, nodeValue2019, nodeValue2190, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5352 node5352Labels = Sparse.eval nodeValue5352 (mixedVector B) := by
  have h := singleton5352 B _hB
  rw [sound3690 B _hB _hF, sound3764 B _hB _hF] at h
  norm_num [nodeValue5352, nodeValue3690, nodeValue3764, Sparse.eval] at h ⊢
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

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2470 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 1) (sourceB2470 + difference 1 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 1) (sourceB2470 + difference 1 0) sourceC2470) = raw33970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33970; decide +kernel
    rw [ha]
    exact (canonical33970 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 2) (sourceB2470 + difference 2 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 2) (sourceB2470 + difference 2 0) sourceC2470) = raw33971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33971; decide +kernel
    rw [ha]
    exact (canonical33971 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 3) (sourceB2470 + difference 3 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 3) (sourceB2470 + difference 3 0) sourceC2470) = raw11315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11315; decide +kernel
    rw [ha]
    exact (canonical11315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 4) (sourceB2470 + difference 4 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 4) (sourceB2470 + difference 4 0) sourceC2470) = raw33972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33972; decide +kernel
    rw [ha]
    exact (canonical33972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 5) (sourceB2470 + difference 5 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 5) (sourceB2470 + difference 5 0) sourceC2470) = raw14308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14308; decide +kernel
    rw [ha]
    exact (canonical14308 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 0) (sourceB2470 + difference 0 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 0) (sourceB2470 + difference 0 1) sourceC2470) = raw11330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11330; decide +kernel
    rw [ha]
    exact (canonical11330 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 2) (sourceB2470 + difference 2 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 2) (sourceB2470 + difference 2 1) sourceC2470) = raw11332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11332; decide +kernel
    rw [ha]
    exact (canonical11332 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 3) (sourceB2470 + difference 3 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 3) (sourceB2470 + difference 3 1) sourceC2470) = raw14329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14329; decide +kernel
    rw [ha]
    exact (canonical14329 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 4) (sourceB2470 + difference 4 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 4) (sourceB2470 + difference 4 1) sourceC2470) = raw11333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11333; decide +kernel
    rw [ha]
    exact (canonical11333 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 5) (sourceB2470 + difference 5 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 5) (sourceB2470 + difference 5 1) sourceC2470) = raw11334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11334; decide +kernel
    rw [ha]
    exact (canonical11334 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 0) (sourceB2470 + difference 0 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 0) (sourceB2470 + difference 0 2) sourceC2470) = raw33973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33973; decide +kernel
    rw [ha]
    exact (canonical33973 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 1) (sourceB2470 + difference 1 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 1) (sourceB2470 + difference 1 2) sourceC2470) = raw33974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33974; decide +kernel
    rw [ha]
    exact (canonical33974 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 3) (sourceB2470 + difference 3 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 3) (sourceB2470 + difference 3 2) sourceC2470) = raw11326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11326; decide +kernel
    rw [ha]
    exact (canonical11326 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 4) (sourceB2470 + difference 4 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 4) (sourceB2470 + difference 4 2) sourceC2470) = raw33975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33975; decide +kernel
    rw [ha]
    exact (canonical33975 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 5) (sourceB2470 + difference 5 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 5) (sourceB2470 + difference 5 2) sourceC2470) = raw14317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14317; decide +kernel
    rw [ha]
    exact (canonical14317 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 0) (sourceB2470 + difference 0 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 0) (sourceB2470 + difference 0 3) sourceC2470) = raw33976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33976; decide +kernel
    rw [ha]
    exact (canonical33976 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 1) (sourceB2470 + difference 1 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 1) (sourceB2470 + difference 1 3) sourceC2470) = raw33977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33977; decide +kernel
    rw [ha]
    exact (canonical33977 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 2) (sourceB2470 + difference 2 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 2) (sourceB2470 + difference 2 3) sourceC2470) = raw33978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33978; decide +kernel
    rw [ha]
    exact (canonical33978 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 4) (sourceB2470 + difference 4 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 4) (sourceB2470 + difference 4 3) sourceC2470) = raw33979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33979; decide +kernel
    rw [ha]
    exact (canonical33979 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 5) (sourceB2470 + difference 5 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 5) (sourceB2470 + difference 5 3) sourceC2470) = raw14321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14321; decide +kernel
    rw [ha]
    exact (canonical14321 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 0) (sourceB2470 + difference 0 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4201) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 0) (sourceB2470 + difference 0 4) sourceC2470) = raw31570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw31570; decide +kernel
    rw [ha]
    exact (canonical31570 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 1) (sourceB2470 + difference 1 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4635) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 1) (sourceB2470 + difference 1 4) sourceC2470) = raw31571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw31571; decide +kernel
    rw [ha]
    exact (canonical31571 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 2) (sourceB2470 + difference 2 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 2) (sourceB2470 + difference 2 4) sourceC2470) = raw31572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw31572; decide +kernel
    rw [ha]
    exact (canonical31572 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 3) (sourceB2470 + difference 3 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 3) (sourceB2470 + difference 3 4) sourceC2470) = raw11336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11336; decide +kernel
    rw [ha]
    exact (canonical11336 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 5) (sourceB2470 + difference 5 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 5) (sourceB2470 + difference 5 4) sourceC2470) = raw14326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14326; decide +kernel
    rw [ha]
    exact (canonical14326 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 0) (sourceB2470 + difference 0 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 0) (sourceB2470 + difference 0 5) sourceC2470) = raw33980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33980; decide +kernel
    rw [ha]
    exact (canonical33980 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 1) (sourceB2470 + difference 1 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 1) (sourceB2470 + difference 1 5) sourceC2470) = raw33981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33981; decide +kernel
    rw [ha]
    exact (canonical33981 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 2) (sourceB2470 + difference 2 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 2) (sourceB2470 + difference 2 5) sourceC2470) = raw33982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33982; decide +kernel
    rw [ha]
    exact (canonical33982 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 3) (sourceB2470 + difference 3 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 3) (sourceB2470 + difference 3 5) sourceC2470) = raw11341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11341; decide +kernel
    rw [ha]
    exact (canonical11341 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 4) (sourceB2470 + difference 4 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 4) (sourceB2470 + difference 4 5) sourceC2470) = raw33983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33983; decide +kernel
    rw [ha]
    exact (canonical33983 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2470 sourceB2470 sourceC2470
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2470, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1988 : Integer.Sparse.reindex keyMap MixedData.row1988 = numericRow1988 := by decide +kernel

theorem numericCheck1988 (x : Master → ℝ) : Integer.Sparse.eval numericRow1988 x =
    (51840 : ℝ) * reducedSource1988 x := by
  norm_num [numericRow1988, reducedSource1988, Integer.Sparse.eval, Sparse.eval, nodeValue4196, nodeValue4197, nodeValue4201, nodeValue4210, nodeValue4249, nodeValue4631, nodeValue4632, nodeValue4635, nodeValue4642, nodeValue4760, nodeValue4763, nodeValue4767, nodeValue4779, nodeValue4782, nodeValue4787, nodeValue4801, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4831, nodeValue4835, nodeValue4887, nodeValue4888, nodeValue5352, nodeValue5416, nodeValue5424, nodeValue5433, nodeValue5434]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1988 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1988 (mixedVector B) = 0 := by
  have h4196 : mixedVector B (Sum.inr 4196) = Sparse.eval nodeValue4196 (mixedVector B) := by
    change mixedMoment B node4196 node4196Labels = _
    exact sound4196 B hB hF
  have h4197 : mixedVector B (Sum.inr 4197) = Sparse.eval nodeValue4197 (mixedVector B) := by
    change mixedMoment B node4197 node4197Labels = _
    exact sound4197 B hB hF
  have h4201 : mixedVector B (Sum.inr 4201) = Sparse.eval nodeValue4201 (mixedVector B) := by
    change mixedMoment B node4201 node4201Labels = _
    exact sound4201 B hB hF
  have h4210 : mixedVector B (Sum.inr 4210) = Sparse.eval nodeValue4210 (mixedVector B) := by
    change mixedMoment B node4210 node4210Labels = _
    exact sound4210 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4631 : mixedVector B (Sum.inr 4631) = Sparse.eval nodeValue4631 (mixedVector B) := by
    change mixedMoment B node4631 node4631Labels = _
    exact sound4631 B hB hF
  have h4632 : mixedVector B (Sum.inr 4632) = Sparse.eval nodeValue4632 (mixedVector B) := by
    change mixedMoment B node4632 node4632Labels = _
    exact sound4632 B hB hF
  have h4635 : mixedVector B (Sum.inr 4635) = Sparse.eval nodeValue4635 (mixedVector B) := by
    change mixedMoment B node4635 node4635Labels = _
    exact sound4635 B hB hF
  have h4642 : mixedVector B (Sum.inr 4642) = Sparse.eval nodeValue4642 (mixedVector B) := by
    change mixedMoment B node4642 node4642Labels = _
    exact sound4642 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
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
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416_e B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  simpa only [sourceForm2470, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4196, h4197, h4201, h4210, h4249, h4631, h4632, h4635, h4642, h4760, h4763, h4767, h4779, h4782, h4787, h4801, h4802, h4804, h4811, h4831, h4835, h4887, h4888, h5352, h5416, h5424, h5433, h5434, reducedSource1988] using sourceEq2470 B hB

theorem rowSound1988_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1988 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1988, numericCheck1988, reducedZero1988 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e_oai
