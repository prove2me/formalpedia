-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:22:46.082498+00:00
-- url     : https://prove2.me/submissions/468fc35a-d07d-4470-95df-493ca4eb1e54

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15113 raw15113Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw15113 raw15113Labels = mixedMoment B raw15113step0 raw15113step0Labels := by
      have hz : ∀ j, raw15113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15113step0 = (fun i j => raw15113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15113step0 raw15113; decide +kernel
      have hl : raw15113step0Labels = raw15113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15113 raw15113Labels permutation346 hz
    mixedMoment B raw15113step0 raw15113step0Labels = mixedMoment B raw15113step1 raw15113step1Labels := by
      have ha : raw15113step1 = (fun i j => raw15113step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15113step1 raw15113step0; decide +kernel
      have hl : raw15113step1Labels = raw15113step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15113step0 raw15113step0Labels permutation32 permutation6
    mixedMoment B raw15113step1 raw15113step1Labels = mixedMoment B raw15113step2 raw15113step2Labels := by
      have ha : raw15113step2 = raw15113step1 := by apply Matrix.ext; unfold raw15113step2 raw15113step1; decide +kernel
      have hl : raw15113step1Labels = labelEmbedding9 ∘ raw15113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15113step1 raw15113step1Labels raw15113step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical15117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15117 raw15117Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15117 raw15117Labels = mixedMoment B raw15117step0 raw15117step0Labels := by
      have hz : ∀ j, raw15117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15117step0 = (fun i j => raw15117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15117step0 raw15117; decide +kernel
      have hl : raw15117step0Labels = raw15117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15117 raw15117Labels permutation346 hz
    mixedMoment B raw15117step0 raw15117step0Labels = mixedMoment B raw15117step1 raw15117step1Labels := by
      have ha : raw15117step1 = (fun i j => raw15117step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15117step1 raw15117step0; decide +kernel
      have hl : raw15117step1Labels = raw15117step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15117step0 raw15117step0Labels permutation151 permutation7
    mixedMoment B raw15117step1 raw15117step1Labels = mixedMoment B raw15117step2 raw15117step2Labels := by
      have ha : raw15117step2 = -raw15117step1 := by apply Matrix.ext; change ∀ i j, raw15117step2 i j = -(raw15117step1 i j); unfold raw15117step2 raw15117step1; decide +kernel
      have hl : raw15117step2Labels = raw15117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15117step2 raw15117step2Labels = mixedMoment B raw15117step3 raw15117step3Labels := by
      have ha : raw15117step3 = raw15117step2 := by apply Matrix.ext; unfold raw15117step3 raw15117step2; decide +kernel
      have hl : raw15117step2Labels = labelEmbedding10 ∘ raw15117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15117step2 raw15117step2Labels raw15117step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical15124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15124 raw15124Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw15124 raw15124Labels = mixedMoment B raw15124step0 raw15124step0Labels := by
      have ha : raw15124step0 = (fun i j => raw15124 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15124step0 raw15124; decide +kernel
      have hl : raw15124step0Labels = raw15124Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15124 raw15124Labels permutation152 permutation6
    mixedMoment B raw15124step0 raw15124step0Labels = mixedMoment B raw15124step1 raw15124step1Labels := by
      have ha : raw15124step1 = raw15124step0 := by apply Matrix.ext; unfold raw15124step1 raw15124step0; decide +kernel
      have hl : raw15124step0Labels = labelEmbedding9 ∘ raw15124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15124step0 raw15124step0Labels raw15124step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical15127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15127 raw15127Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15127 raw15127Labels = mixedMoment B raw15127step0 raw15127step0Labels := by
      have ha : raw15127step0 = (fun i j => raw15127 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15127step0 raw15127; decide +kernel
      have hl : raw15127step0Labels = raw15127Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15127 raw15127Labels permutation682 permutation7
    mixedMoment B raw15127step0 raw15127step0Labels = mixedMoment B raw15127step1 raw15127step1Labels := by
      have ha : raw15127step1 = -raw15127step0 := by apply Matrix.ext; change ∀ i j, raw15127step1 i j = -(raw15127step0 i j); unfold raw15127step1 raw15127step0; decide +kernel
      have hl : raw15127step1Labels = raw15127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15127step1 raw15127step1Labels = mixedMoment B raw15127step2 raw15127step2Labels := by
      have ha : raw15127step2 = raw15127step1 := by apply Matrix.ext; unfold raw15127step2 raw15127step1; decide +kernel
      have hl : raw15127step1Labels = labelEmbedding10 ∘ raw15127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15127step1 raw15127step1Labels raw15127step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical15200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15200 raw15200Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15200 raw15200Labels = mixedMoment B raw15200step0 raw15200step0Labels := by
      have hz : ∀ j, raw15200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15200step0 = (fun i j => raw15200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15200step0 raw15200; decide +kernel
      have hl : raw15200step0Labels = raw15200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15200 raw15200Labels permutation346 hz
    mixedMoment B raw15200step0 raw15200step0Labels = mixedMoment B raw15200step1 raw15200step1Labels := by
      have ha : raw15200step1 = (fun i j => raw15200step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15200step1 raw15200step0; decide +kernel
      have hl : raw15200step1Labels = raw15200step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15200step0 raw15200step0Labels permutation151 permutation7
    mixedMoment B raw15200step1 raw15200step1Labels = mixedMoment B raw15200step2 raw15200step2Labels := by
      have ha : raw15200step2 = -raw15200step1 := by apply Matrix.ext; change ∀ i j, raw15200step2 i j = -(raw15200step1 i j); unfold raw15200step2 raw15200step1; decide +kernel
      have hl : raw15200step2Labels = raw15200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15200step2 raw15200step2Labels = mixedMoment B raw15200step3 raw15200step3Labels := by
      have ha : raw15200step3 = raw15200step2 := by apply Matrix.ext; unfold raw15200step3 raw15200step2; decide +kernel
      have hl : raw15200step2Labels = labelEmbedding10 ∘ raw15200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15200step2 raw15200step2Labels raw15200step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical15205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15205 raw15205Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15205 raw15205Labels = mixedMoment B raw15205step0 raw15205step0Labels := by
      have ha : raw15205step0 = (fun i j => raw15205 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15205step0 raw15205; decide +kernel
      have hl : raw15205step0Labels = raw15205Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15205 raw15205Labels permutation152 permutation6
    mixedMoment B raw15205step0 raw15205step0Labels = mixedMoment B raw15205step1 raw15205step1Labels := by
      have ha : raw15205step1 = raw15205step0 := by apply Matrix.ext; unfold raw15205step1 raw15205step0; decide +kernel
      have hl : raw15205step0Labels = labelEmbedding9 ∘ raw15205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15205step0 raw15205step0Labels raw15205step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

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

theorem canonical15664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15664 raw15664Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw15664 raw15664Labels = mixedMoment B raw15664step0 raw15664step0Labels := by
      have ha : raw15664step0 = (fun i j => raw15664 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15664step0 raw15664; decide +kernel
      have hl : raw15664step0Labels = raw15664Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15664 raw15664Labels permutation682 permutation7
    mixedMoment B raw15664step0 raw15664step0Labels = mixedMoment B raw15664step1 raw15664step1Labels := by
      have ha : raw15664step1 = -raw15664step0 := by apply Matrix.ext; change ∀ i j, raw15664step1 i j = -(raw15664step0 i j); unfold raw15664step1 raw15664step0; decide +kernel
      have hl : raw15664step1Labels = raw15664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15664step1 raw15664step1Labels = mixedMoment B raw15664step2 raw15664step2Labels := by
      have ha : raw15664step2 = raw15664step1 := by apply Matrix.ext; unfold raw15664step2 raw15664step1; decide +kernel
      have hl : raw15664step1Labels = labelEmbedding10 ∘ raw15664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15664step1 raw15664step1Labels raw15664step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

theorem canonical15667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15667 raw15667Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw15667 raw15667Labels = mixedMoment B raw15667step0 raw15667step0Labels := by
      have ha : raw15667step0 = (fun i j => raw15667 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15667step0 raw15667; decide +kernel
      have hl : raw15667step0Labels = raw15667Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15667 raw15667Labels permutation682 permutation2
    _ = mixedMoment B node5365 node5365Labels := by rfl

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

theorem canonical15859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15859 raw15859Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15859 raw15859Labels = mixedMoment B raw15859step0 raw15859step0Labels := by
      have hz : ∀ j, raw15859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15859step0 = (fun i j => raw15859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15859step0 raw15859; decide +kernel
      have hl : raw15859step0Labels = raw15859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15859 raw15859Labels permutation434 hz
    mixedMoment B raw15859step0 raw15859step0Labels = mixedMoment B raw15859step1 raw15859step1Labels := by
      have ha : raw15859step1 = (fun i j => raw15859step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15859step1 raw15859step0; decide +kernel
      have hl : raw15859step1Labels = raw15859step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15859step0 raw15859step0Labels permutation151 permutation7
    mixedMoment B raw15859step1 raw15859step1Labels = mixedMoment B raw15859step2 raw15859step2Labels := by
      have ha : raw15859step2 = -raw15859step1 := by apply Matrix.ext; change ∀ i j, raw15859step2 i j = -(raw15859step1 i j); unfold raw15859step2 raw15859step1; decide +kernel
      have hl : raw15859step2Labels = raw15859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15859step2 raw15859step2Labels = mixedMoment B raw15859step3 raw15859step3Labels := by
      have ha : raw15859step3 = raw15859step2 := by apply Matrix.ext; unfold raw15859step3 raw15859step2; decide +kernel
      have hl : raw15859step2Labels = labelEmbedding10 ∘ raw15859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15859step2 raw15859step2Labels raw15859step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical15860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15860 raw15860Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw15860 raw15860Labels = mixedMoment B raw15860step0 raw15860step0Labels := by
      have ha : raw15860step0 = (fun i j => raw15860 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15860step0 raw15860; decide +kernel
      have hl : raw15860step0Labels = raw15860Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15860 raw15860Labels permutation682 permutation2
    _ = mixedMoment B node5098 node5098Labels := by rfl

theorem canonical15865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15865 raw15865Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw15865 raw15865Labels = mixedMoment B raw15865step0 raw15865step0Labels := by
      have ha : raw15865step0 = (fun i j => raw15865 (permutation672 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15865step0 raw15865; decide +kernel
      have hl : raw15865step0Labels = raw15865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15865 raw15865Labels permutation672 permutation2
    _ = mixedMoment B node5407 node5407Labels := by rfl

theorem canonical15869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15869 raw15869Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw15869 raw15869Labels = mixedMoment B raw15869step0 raw15869step0Labels := by
      have ha : raw15869step0 = (fun i j => raw15869 (permutation671 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15869step0 raw15869; decide +kernel
      have hl : raw15869step0Labels = raw15869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15869 raw15869Labels permutation671 permutation2
    _ = mixedMoment B node5407 node5407Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16842 raw16842Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw16842 raw16842Labels = mixedMoment B raw16842step0 raw16842step0Labels := by
      have ha : raw16842step0 = (fun i j => raw16842 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16842step0 raw16842; decide +kernel
      have hl : raw16842step0Labels = raw16842Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16842 raw16842Labels permutation674 permutation2
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical16843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16843 raw16843Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw16843 raw16843Labels = mixedMoment B raw16843step0 raw16843step0Labels := by
      have hz : ∀ j, raw16843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16843step0 = (fun i j => raw16843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16843step0 raw16843; decide +kernel
      have hl : raw16843step0Labels = raw16843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16843 raw16843Labels permutation434 hz
    mixedMoment B raw16843step0 raw16843step0Labels = mixedMoment B raw16843step1 raw16843step1Labels := by
      have ha : raw16843step1 = (fun i j => raw16843step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16843step1 raw16843step0; decide +kernel
      have hl : raw16843step1Labels = raw16843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16843step0 raw16843step0Labels permutation32 permutation6
    mixedMoment B raw16843step1 raw16843step1Labels = mixedMoment B raw16843step2 raw16843step2Labels := by
      have ha : raw16843step2 = raw16843step1 := by apply Matrix.ext; unfold raw16843step2 raw16843step1; decide +kernel
      have hl : raw16843step1Labels = labelEmbedding9 ∘ raw16843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16843step1 raw16843step1Labels raw16843step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical16848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16848 raw16848Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw16848 raw16848Labels = mixedMoment B raw16848step0 raw16848step0Labels := by
      have ha : raw16848step0 = (fun i j => raw16848 (permutation675 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16848step0 raw16848; decide +kernel
      have hl : raw16848step0Labels = raw16848Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16848 raw16848Labels permutation675 permutation2
    _ = mixedMoment B node5402 node5402Labels := by rfl

theorem canonical16853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16853 raw16853Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw16853 raw16853Labels = mixedMoment B raw16853step0 raw16853step0Labels := by
      have ha : raw16853step0 = (fun i j => raw16853 (permutation673 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16853step0 raw16853; decide +kernel
      have hl : raw16853step0Labels = raw16853Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16853 raw16853Labels permutation673 permutation2
    _ = mixedMoment B node5402 node5402Labels := by rfl

theorem canonical16858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16858 raw16858Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw16858 raw16858Labels = mixedMoment B raw16858step0 raw16858step0Labels := by
      have ha : raw16858step0 = (fun i j => raw16858 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16858step0 raw16858; decide +kernel
      have hl : raw16858step0Labels = raw16858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16858 raw16858Labels permutation682 permutation7
    mixedMoment B raw16858step0 raw16858step0Labels = mixedMoment B raw16858step1 raw16858step1Labels := by
      have ha : raw16858step1 = -raw16858step0 := by apply Matrix.ext; change ∀ i j, raw16858step1 i j = -(raw16858step0 i j); unfold raw16858step1 raw16858step0; decide +kernel
      have hl : raw16858step1Labels = raw16858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16858step1 raw16858step1Labels = mixedMoment B raw16858step2 raw16858step2Labels := by
      have ha : raw16858step2 = raw16858step1 := by apply Matrix.ext; unfold raw16858step2 raw16858step1; decide +kernel
      have hl : raw16858step1Labels = labelEmbedding10 ∘ raw16858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16858step1 raw16858step1Labels raw16858step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17038 raw17038Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw17038 raw17038Labels = mixedMoment B raw17038step0 raw17038step0Labels := by
      have hz : ∀ j, raw17038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17038step0 = (fun i j => raw17038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17038step0 raw17038; decide +kernel
      have hl : raw17038step0Labels = raw17038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17038 raw17038Labels permutation346 hz
    mixedMoment B raw17038step0 raw17038step0Labels = mixedMoment B raw17038step1 raw17038step1Labels := by
      have ha : raw17038step1 = (fun i j => raw17038step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17038step1 raw17038step0; decide +kernel
      have hl : raw17038step1Labels = raw17038step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17038step0 raw17038step0Labels permutation148 permutation2
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical17122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17122 raw17122Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw17122 raw17122Labels = mixedMoment B raw17122step0 raw17122step0Labels := by
      have hz : ∀ j, raw17122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17122step0 = (fun i j => raw17122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17122step0 raw17122; decide +kernel
      have hl : raw17122step0Labels = raw17122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17122 raw17122Labels permutation346 hz
    mixedMoment B raw17122step0 raw17122step0Labels = mixedMoment B raw17122step1 raw17122step1Labels := by
      have ha : raw17122step1 = (fun i j => raw17122step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17122step1 raw17122step0; decide +kernel
      have hl : raw17122step1Labels = raw17122step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17122step0 raw17122step0Labels permutation149 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical17123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17123 raw17123Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw17123 raw17123Labels = mixedMoment B raw17123step0 raw17123step0Labels := by
      have ha : raw17123step0 = (fun i j => raw17123 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17123step0 raw17123; decide +kernel
      have hl : raw17123step0Labels = raw17123Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17123 raw17123Labels permutation152 permutation6
    mixedMoment B raw17123step0 raw17123step0Labels = mixedMoment B raw17123step1 raw17123step1Labels := by
      have ha : raw17123step1 = raw17123step0 := by apply Matrix.ext; unfold raw17123step1 raw17123step0; decide +kernel
      have hl : raw17123step0Labels = labelEmbedding9 ∘ raw17123step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17123step0 raw17123step0Labels raw17123step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17223 raw17223Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw17223 raw17223Labels = mixedMoment B raw17223step0 raw17223step0Labels := by
      have hz : ∀ j, raw17223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17223step0 = (fun i j => raw17223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17223step0 raw17223; decide +kernel
      have hl : raw17223step0Labels = raw17223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17223 raw17223Labels permutation434 hz
    mixedMoment B raw17223step0 raw17223step0Labels = mixedMoment B raw17223step1 raw17223step1Labels := by
      have ha : raw17223step1 = (fun i j => raw17223step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17223step1 raw17223step0; decide +kernel
      have hl : raw17223step1Labels = raw17223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17223step0 raw17223step0Labels permutation149 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

theorem canonical17224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17224 raw17224Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw17224 raw17224Labels = mixedMoment B raw17224step0 raw17224step0Labels := by
      have ha : raw17224step0 = (fun i j => raw17224 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17224step0 raw17224; decide +kernel
      have hl : raw17224step0Labels = raw17224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17224 raw17224Labels permutation674 permutation2
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical17225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17225 raw17225Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw17225 raw17225Labels = mixedMoment B raw17225step0 raw17225step0Labels := by
      have ha : raw17225step0 = (fun i j => raw17225 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17225step0 raw17225; decide +kernel
      have hl : raw17225step0Labels = raw17225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17225 raw17225Labels permutation674 permutation2
    _ = mixedMoment B node5072 node5072Labels := by rfl

theorem canonical17226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17226 raw17226Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw17226 raw17226Labels = mixedMoment B raw17226step0 raw17226step0Labels := by
      have hz : ∀ j, raw17226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17226step0 = (fun i j => raw17226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17226step0 raw17226; decide +kernel
      have hl : raw17226step0Labels = raw17226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17226 raw17226Labels permutation434 hz
    mixedMoment B raw17226step0 raw17226step0Labels = mixedMoment B raw17226step1 raw17226step1Labels := by
      have ha : raw17226step1 = (fun i j => raw17226step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17226step1 raw17226step0; decide +kernel
      have hl : raw17226step1Labels = raw17226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17226step0 raw17226step0Labels permutation148 permutation2
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical17227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17227 raw17227Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw17227 raw17227Labels = mixedMoment B raw17227step0 raw17227step0Labels := by
      have ha : raw17227step0 = (fun i j => raw17227 (permutation675 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17227step0 raw17227; decide +kernel
      have hl : raw17227step0Labels = raw17227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17227 raw17227Labels permutation675 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical17228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17228 raw17228Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw17228 raw17228Labels = mixedMoment B raw17228step0 raw17228step0Labels := by
      have ha : raw17228step0 = (fun i j => raw17228 (permutation675 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17228step0 raw17228; decide +kernel
      have hl : raw17228step0Labels = raw17228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17228 raw17228Labels permutation675 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical17229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17229 raw17229Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw17229 raw17229Labels = mixedMoment B raw17229step0 raw17229step0Labels := by
      have ha : raw17229step0 = (fun i j => raw17229 (permutation673 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17229step0 raw17229; decide +kernel
      have hl : raw17229step0Labels = raw17229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17229 raw17229Labels permutation673 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical17230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17230 raw17230Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw17230 raw17230Labels = mixedMoment B raw17230step0 raw17230step0Labels := by
      have ha : raw17230step0 = (fun i j => raw17230 (permutation673 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17230step0 raw17230; decide +kernel
      have hl : raw17230step0Labels = raw17230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17230 raw17230Labels permutation673 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical17231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17231 raw17231Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17231 raw17231Labels = mixedMoment B raw17231step0 raw17231step0Labels := by
      have hz : ∀ j, raw17231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17231step0 = (fun i j => raw17231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17231step0 raw17231; decide +kernel
      have hl : raw17231step0Labels = raw17231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17231 raw17231Labels permutation434 hz
    mixedMoment B raw17231step0 raw17231step0Labels = mixedMoment B raw17231step1 raw17231step1Labels := by
      have ha : raw17231step1 = (fun i j => raw17231step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17231step1 raw17231step0; decide +kernel
      have hl : raw17231step1Labels = raw17231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17231step0 raw17231step0Labels permutation151 permutation7
    mixedMoment B raw17231step1 raw17231step1Labels = mixedMoment B raw17231step2 raw17231step2Labels := by
      have ha : raw17231step2 = -raw17231step1 := by apply Matrix.ext; change ∀ i j, raw17231step2 i j = -(raw17231step1 i j); unfold raw17231step2 raw17231step1; decide +kernel
      have hl : raw17231step2Labels = raw17231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17231step2 raw17231step2Labels = mixedMoment B raw17231step3 raw17231step3Labels := by
      have ha : raw17231step3 = raw17231step2 := by apply Matrix.ext; unfold raw17231step3 raw17231step2; decide +kernel
      have hl : raw17231step2Labels = labelEmbedding10 ∘ raw17231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17231step2 raw17231step2Labels raw17231step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical17232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17232 raw17232Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw17232 raw17232Labels = mixedMoment B raw17232step0 raw17232step0Labels := by
      have ha : raw17232step0 = (fun i j => raw17232 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17232step0 raw17232; decide +kernel
      have hl : raw17232step0Labels = raw17232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17232 raw17232Labels permutation674 permutation2
    _ = mixedMoment B node5256 node5256Labels := by rfl

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

theorem canonical2121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2121 raw2121Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw2121 raw2121Labels = mixedMoment B raw2121step0 raw2121step0Labels := by
      have ha : raw2121step0 = (fun i j => raw2121 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2121step0 raw2121; decide +kernel
      have hl : raw2121step0Labels = raw2121Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2121 raw2121Labels permutation152 permutation4
    mixedMoment B raw2121step0 raw2121step0Labels = mixedMoment B raw2121step1 raw2121step1Labels := by
      have ha : raw2121step1 = raw2121step0 := by apply Matrix.ext; unfold raw2121step1 raw2121step0; decide +kernel
      have hl : raw2121step0Labels = labelEmbedding7 ∘ raw2121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2121step0 raw2121step0Labels raw2121step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

theorem canonical2122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2122 raw2122Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw2122 raw2122Labels = mixedMoment B raw2122step0 raw2122step0Labels := by
      have ha : raw2122step0 = (fun i j => raw2122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2122step0 raw2122; decide +kernel
      have hl : raw2122step0Labels = raw2122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2122 raw2122Labels permutation152 permutation4
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical2123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2123 raw2123Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw2123 raw2123Labels = mixedMoment B raw2123step0 raw2123step0Labels := by
      have ha : raw2123step0 = (fun i j => raw2123 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2123step0 raw2123; decide +kernel
      have hl : raw2123step0Labels = raw2123Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2123 raw2123Labels permutation152 permutation6
    mixedMoment B raw2123step0 raw2123step0Labels = mixedMoment B raw2123step1 raw2123step1Labels := by
      have ha : raw2123step1 = -raw2123step0 := by apply Matrix.ext; change ∀ i j, raw2123step1 i j = -(raw2123step0 i j); unfold raw2123step1 raw2123step0; decide +kernel
      have hl : raw2123step1Labels = raw2123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2123step1 raw2123step1Labels = mixedMoment B raw2123step2 raw2123step2Labels := by
      have ha : raw2123step2 = raw2123step1 := by apply Matrix.ext; unfold raw2123step2 raw2123step1; decide +kernel
      have hl : raw2123step1Labels = labelEmbedding1 ∘ raw2123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2123step1 raw2123step1Labels raw2123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

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

theorem canonical2391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2391 raw2391Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw2391 raw2391Labels = mixedMoment B raw2391step0 raw2391step0Labels := by
      have ha : raw2391step0 = (fun i j => raw2391 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2391step0 raw2391; decide +kernel
      have hl : raw2391step0Labels = raw2391Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2391 raw2391Labels permutation152 permutation4
    mixedMoment B raw2391step0 raw2391step0Labels = mixedMoment B raw2391step1 raw2391step1Labels := by
      have ha : raw2391step1 = raw2391step0 := by apply Matrix.ext; unfold raw2391step1 raw2391step0; decide +kernel
      have hl : raw2391step0Labels = labelEmbedding7 ∘ raw2391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2391step0 raw2391step0Labels raw2391step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical2392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2392 raw2392Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw2392 raw2392Labels = mixedMoment B raw2392step0 raw2392step0Labels := by
      have ha : raw2392step0 = (fun i j => raw2392 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2392step0 raw2392; decide +kernel
      have hl : raw2392step0Labels = raw2392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2392 raw2392Labels permutation152 permutation4
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical2393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2393 raw2393Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw2393 raw2393Labels = mixedMoment B raw2393step0 raw2393step0Labels := by
      have ha : raw2393step0 = (fun i j => raw2393 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2393step0 raw2393; decide +kernel
      have hl : raw2393step0Labels = raw2393Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2393 raw2393Labels permutation160 permutation6
    mixedMoment B raw2393step0 raw2393step0Labels = mixedMoment B raw2393step1 raw2393step1Labels := by
      have ha : raw2393step1 = -raw2393step0 := by apply Matrix.ext; change ∀ i j, raw2393step1 i j = -(raw2393step0 i j); unfold raw2393step1 raw2393step0; decide +kernel
      have hl : raw2393step1Labels = raw2393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2393step1 raw2393step1Labels = mixedMoment B raw2393step2 raw2393step2Labels := by
      have ha : raw2393step2 = raw2393step1 := by apply Matrix.ext; unfold raw2393step2 raw2393step1; decide +kernel
      have hl : raw2393step1Labels = labelEmbedding1 ∘ raw2393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2393step1 raw2393step1Labels raw2393step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical2412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2412 raw2412Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw2412 raw2412Labels = mixedMoment B raw2412step0 raw2412step0Labels := by
      have ha : raw2412step0 = (fun i j => raw2412 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2412step0 raw2412; decide +kernel
      have hl : raw2412step0Labels = raw2412Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2412 raw2412Labels permutation152 permutation4
    mixedMoment B raw2412step0 raw2412step0Labels = mixedMoment B raw2412step1 raw2412step1Labels := by
      have ha : raw2412step1 = raw2412step0 := by apply Matrix.ext; unfold raw2412step1 raw2412step0; decide +kernel
      have hl : raw2412step0Labels = labelEmbedding7 ∘ raw2412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2412step0 raw2412step0Labels raw2412step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

theorem canonical2413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2413 raw2413Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw2413 raw2413Labels = mixedMoment B raw2413step0 raw2413step0Labels := by
      have ha : raw2413step0 = (fun i j => raw2413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2413step0 raw2413; decide +kernel
      have hl : raw2413step0Labels = raw2413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2413 raw2413Labels permutation152 permutation4
    _ = mixedMoment B node3703 node3703Labels := by rfl

theorem canonical2414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2414 raw2414Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw2414 raw2414Labels = mixedMoment B raw2414step0 raw2414step0Labels := by
      have ha : raw2414step0 = (fun i j => raw2414 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2414step0 raw2414; decide +kernel
      have hl : raw2414step0Labels = raw2414Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2414 raw2414Labels permutation152 permutation6
    mixedMoment B raw2414step0 raw2414step0Labels = mixedMoment B raw2414step1 raw2414step1Labels := by
      have ha : raw2414step1 = -raw2414step0 := by apply Matrix.ext; change ∀ i j, raw2414step1 i j = -(raw2414step0 i j); unfold raw2414step1 raw2414step0; decide +kernel
      have hl : raw2414step1Labels = raw2414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2414step1 raw2414step1Labels = mixedMoment B raw2414step2 raw2414step2Labels := by
      have ha : raw2414step2 = raw2414step1 := by apply Matrix.ext; unfold raw2414step2 raw2414step1; decide +kernel
      have hl : raw2414step1Labels = labelEmbedding1 ∘ raw2414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2414step1 raw2414step1Labels raw2414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

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

theorem canonical2472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2472 raw2472Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw2472 raw2472Labels = mixedMoment B raw2472step0 raw2472step0Labels := by
      have ha : raw2472step0 = (fun i j => raw2472 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2472step0 raw2472; decide +kernel
      have hl : raw2472step0Labels = raw2472Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2472 raw2472Labels permutation152 permutation4
    mixedMoment B raw2472step0 raw2472step0Labels = mixedMoment B raw2472step1 raw2472step1Labels := by
      have ha : raw2472step1 = raw2472step0 := by apply Matrix.ext; unfold raw2472step1 raw2472step0; decide +kernel
      have hl : raw2472step0Labels = labelEmbedding7 ∘ raw2472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2472step0 raw2472step0Labels raw2472step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2473 raw2473Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw2473 raw2473Labels = mixedMoment B raw2473step0 raw2473step0Labels := by
      have ha : raw2473step0 = (fun i j => raw2473 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2473step0 raw2473; decide +kernel
      have hl : raw2473step0Labels = raw2473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2473 raw2473Labels permutation152 permutation4
    _ = mixedMoment B node3786 node3786Labels := by rfl

theorem canonical2474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2474 raw2474Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw2474 raw2474Labels = mixedMoment B raw2474step0 raw2474step0Labels := by
      have ha : raw2474step0 = (fun i j => raw2474 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2474step0 raw2474; decide +kernel
      have hl : raw2474step0Labels = raw2474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2474 raw2474Labels permutation160 permutation6
    mixedMoment B raw2474step0 raw2474step0Labels = mixedMoment B raw2474step1 raw2474step1Labels := by
      have ha : raw2474step1 = -raw2474step0 := by apply Matrix.ext; change ∀ i j, raw2474step1 i j = -(raw2474step0 i j); unfold raw2474step1 raw2474step0; decide +kernel
      have hl : raw2474step1Labels = raw2474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2474step1 raw2474step1Labels = mixedMoment B raw2474step2 raw2474step2Labels := by
      have ha : raw2474step2 = raw2474step1 := by apply Matrix.ext; unfold raw2474step2 raw2474step1; decide +kernel
      have hl : raw2474step1Labels = labelEmbedding1 ∘ raw2474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2474step1 raw2474step1Labels raw2474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

theorem canonical2484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2484 raw2484Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw2484 raw2484Labels = mixedMoment B raw2484step0 raw2484step0Labels := by
      have ha : raw2484step0 = (fun i j => raw2484 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2484step0 raw2484; decide +kernel
      have hl : raw2484step0Labels = raw2484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2484 raw2484Labels permutation152 permutation4
    mixedMoment B raw2484step0 raw2484step0Labels = mixedMoment B raw2484step1 raw2484step1Labels := by
      have ha : raw2484step1 = raw2484step0 := by apply Matrix.ext; unfold raw2484step1 raw2484step0; decide +kernel
      have hl : raw2484step0Labels = labelEmbedding7 ∘ raw2484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2484step0 raw2484step0Labels raw2484step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2485 raw2485Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw2485 raw2485Labels = mixedMoment B raw2485step0 raw2485step0Labels := by
      have ha : raw2485step0 = (fun i j => raw2485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2485step0 raw2485; decide +kernel
      have hl : raw2485step0Labels = raw2485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2485 raw2485Labels permutation152 permutation4
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2486 raw2486Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw2486 raw2486Labels = mixedMoment B raw2486step0 raw2486step0Labels := by
      have ha : raw2486step0 = (fun i j => raw2486 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2486step0 raw2486; decide +kernel
      have hl : raw2486step0Labels = raw2486Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2486 raw2486Labels permutation164 permutation6
    mixedMoment B raw2486step0 raw2486step0Labels = mixedMoment B raw2486step1 raw2486step1Labels := by
      have ha : raw2486step1 = -raw2486step0 := by apply Matrix.ext; change ∀ i j, raw2486step1 i j = -(raw2486step0 i j); unfold raw2486step1 raw2486step0; decide +kernel
      have hl : raw2486step1Labels = raw2486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2486step1 raw2486step1Labels = mixedMoment B raw2486step2 raw2486step2Labels := by
      have ha : raw2486step2 = raw2486step1 := by apply Matrix.ext; unfold raw2486step2 raw2486step1; decide +kernel
      have hl : raw2486step1Labels = labelEmbedding1 ∘ raw2486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2486step1 raw2486step1Labels raw2486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

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

theorem singleton5098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5098 node5098Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2508 node2508Labels + mixedMoment B node3460 node3460Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2121 singletonSmall5098
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5098) = raw2121Labels := by decide +kernel
  rw [hl, canonical2121 B hB] at h
  have hc0 : mixedMoment B raw2121 (Fin.cases (0 : Fin 2) singletonSmall5098) =
      mixedMoment B node2508 node2508Labels := by
    have ha : raw2121 = raw2122 := by apply Matrix.ext; unfold raw2121 raw2122; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5098 = raw2122Labels := by decide +kernel
    rw [ha, hj, canonical2122 B hB]
  have hc1 : mixedMoment B raw2121 (Fin.cases (1 : Fin 2) singletonSmall5098) =
      mixedMoment B node3460 node3460Labels := by
    have ha : raw2121 = raw2123 := by apply Matrix.ext; unfold raw2121 raw2123; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5098 = raw2123Labels := by decide +kernel
    rw [ha, hj, canonical2123 B hB]
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

theorem singleton5351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5351 node5351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3689 node3689Labels + mixedMoment B node3757 node3757Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2391 singletonSmall5351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5351) = raw2391Labels := by decide +kernel
  rw [hl, canonical2391 B hB] at h
  have hc0 : mixedMoment B raw2391 (Fin.cases (0 : Fin 2) singletonSmall5351) =
      mixedMoment B node3689 node3689Labels := by
    have ha : raw2391 = raw2392 := by apply Matrix.ext; unfold raw2391 raw2392; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5351 = raw2392Labels := by decide +kernel
    rw [ha, hj, canonical2392 B hB]
  have hc1 : mixedMoment B raw2391 (Fin.cases (1 : Fin 2) singletonSmall5351) =
      mixedMoment B node3757 node3757Labels := by
    have ha : raw2391 = raw2393 := by apply Matrix.ext; unfold raw2391 raw2393; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5351 = raw2393Labels := by decide +kernel
    rw [ha, hj, canonical2393 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5365 node5365Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3703 node3703Labels + mixedMoment B node3758 node3758Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2412 singletonSmall5365
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5365) = raw2412Labels := by decide +kernel
  rw [hl, canonical2412 B hB] at h
  have hc0 : mixedMoment B raw2412 (Fin.cases (0 : Fin 2) singletonSmall5365) =
      mixedMoment B node3703 node3703Labels := by
    have ha : raw2412 = raw2413 := by apply Matrix.ext; unfold raw2412 raw2413; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5365 = raw2413Labels := by decide +kernel
    rw [ha, hj, canonical2413 B hB]
  have hc1 : mixedMoment B raw2412 (Fin.cases (1 : Fin 2) singletonSmall5365) =
      mixedMoment B node3758 node3758Labels := by
    have ha : raw2412 = raw2414 := by apply Matrix.ext; unfold raw2412 raw2414; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5365 = raw2414Labels := by decide +kernel
    rw [ha, hj, canonical2414 B hB]
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

theorem singleton5400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5400 node5400Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3786 node3786Labels + mixedMoment B node3799 node3799Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2472 singletonSmall5400
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5400) = raw2472Labels := by decide +kernel
  rw [hl, canonical2472 B hB] at h
  have hc0 : mixedMoment B raw2472 (Fin.cases (0 : Fin 2) singletonSmall5400) =
      mixedMoment B node3786 node3786Labels := by
    have ha : raw2472 = raw2473 := by apply Matrix.ext; unfold raw2472 raw2473; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5400 = raw2473Labels := by decide +kernel
    rw [ha, hj, canonical2473 B hB]
  have hc1 : mixedMoment B raw2472 (Fin.cases (1 : Fin 2) singletonSmall5400) =
      mixedMoment B node3799 node3799Labels := by
    have ha : raw2472 = raw2474 := by apply Matrix.ext; unfold raw2472 raw2474; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5400 = raw2474Labels := by decide +kernel
    rw [ha, hj, canonical2474 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5405 node5405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3800 node3800Labels + mixedMoment B node3805 node3805Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2484 singletonSmall5405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5405) = raw2484Labels := by decide +kernel
  rw [hl, canonical2484 B hB] at h
  have hc0 : mixedMoment B raw2484 (Fin.cases (0 : Fin 2) singletonSmall5405) =
      mixedMoment B node3800 node3800Labels := by
    have ha : raw2484 = raw2485 := by apply Matrix.ext; unfold raw2484 raw2485; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5405 = raw2485Labels := by decide +kernel
    rw [ha, hj, canonical2485 B hB]
  have hc1 : mixedMoment B raw2484 (Fin.cases (1 : Fin 2) singletonSmall5405) =
      mixedMoment B node3805 node3805Labels := by
    have ha : raw2484 = raw2486 := by apply Matrix.ext; unfold raw2484 raw2486; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5405 = raw2486Labels := by decide +kernel
    rw [ha, hj, canonical2486 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2508 node2508Labels = Sparse.eval nodeValue2508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2508) = mixedMoment B node2508 node2508Labels := rfl
  simpa [nodeValue2508, Sparse.eval] using hc.symm

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

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

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

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

theorem sound3703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3703 node3703Labels = Sparse.eval nodeValue3703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3703) = mixedMoment B node3703 node3703Labels := rfl
  simpa [nodeValue3703, Sparse.eval] using hc.symm

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

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3758 node3758Labels = Sparse.eval nodeValue3758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3758) = mixedMoment B node3758 node3758Labels := rfl
  simpa [nodeValue3758, Sparse.eval] using hc.symm

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

theorem sound3786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3786 node3786Labels = Sparse.eval nodeValue3786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3786) = mixedMoment B node3786 node3786Labels := rfl
  simpa [nodeValue3786, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

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

theorem sound5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5074 node5074Labels = Sparse.eval nodeValue5074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5074) = mixedMoment B node5074 node5074Labels := rfl
  simpa [nodeValue5074, Sparse.eval] using hc.symm

theorem sound5098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5098 node5098Labels = Sparse.eval nodeValue5098 (mixedVector B) := by
  have h := singleton5098 B _hB
  rw [sound2508 B _hB _hF, sound3460 B _hB _hF] at h
  norm_num [nodeValue5098, nodeValue2508, nodeValue3460, Sparse.eval] at h ⊢
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

theorem zero5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = 0 := by
  exact mixedMoment_alpha B hF node5256 node5256Labels 1 permutation203
    (by decide +kernel)

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

theorem sound5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = Sparse.eval nodeValue5256 (mixedVector B) := by
  simpa only [nodeValue5256, Sparse.eval_nil] using zero5256 B _hB _hF

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

theorem sound5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5351 node5351Labels = Sparse.eval nodeValue5351 (mixedVector B) := by
  have h := singleton5351 B _hB
  rw [sound3689 B _hB _hF, sound3757 B _hB _hF] at h
  norm_num [nodeValue5351, nodeValue3689, nodeValue3757, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5353 node5353Labels = Sparse.eval nodeValue5353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5353) = mixedMoment B node5353 node5353Labels := rfl
  simpa [nodeValue5353, Sparse.eval] using hc.symm

theorem sound5365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5365 node5365Labels = Sparse.eval nodeValue5365 (mixedVector B) := by
  have h := singleton5365 B _hB
  rw [sound3703 B _hB _hF, sound3758 B _hB _hF] at h
  norm_num [nodeValue5365, nodeValue3703, nodeValue3758, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = 0 := by
  exact mixedMoment_order_one B hB node5409 node5409Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = 0 := by
  exact mixedMoment_order_one B hB node5410 node5410Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5400 node5400Labels = Sparse.eval nodeValue5400 (mixedVector B) := by
  have h := singleton5400 B _hB
  rw [sound3786 B _hB _hF, sound3799 B _hB _hF] at h
  norm_num [nodeValue5400, nodeValue3786, nodeValue3799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5402 node5402Labels = Sparse.eval nodeValue5402 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5402) = mixedMoment B node5402 node5402Labels := rfl
  simpa [nodeValue5402, Sparse.eval] using hc.symm

theorem sound5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5405 node5405Labels = Sparse.eval nodeValue5405 (mixedVector B) := by
  have h := singleton5405 B _hB
  rw [sound3800 B _hB _hF, sound3805 B _hB _hF] at h
  norm_num [nodeValue5405, nodeValue3800, nodeValue3805, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5407 node5407Labels = Sparse.eval nodeValue5407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5407) = mixedMoment B node5407 node5407Labels := rfl
  simpa [nodeValue5407, Sparse.eval] using hc.symm

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

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

theorem sound5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = Sparse.eval nodeValue5471 (mixedVector B) := by
  simpa only [nodeValue5471, Sparse.eval_nil] using zero5471 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources32
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1050 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 1) (sourceB1050 + difference 1 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 1) (sourceB1050 + difference 1 0) sourceC1050) = raw16842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16842; decide +kernel
    rw [ha]
    exact (canonical16842 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 2) (sourceB1050 + difference 2 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 2) (sourceB1050 + difference 2 0) sourceC1050) = raw17122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17122; decide +kernel
    rw [ha]
    exact (canonical17122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 3) (sourceB1050 + difference 3 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 3) (sourceB1050 + difference 3 0) sourceC1050) = raw17223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17223; decide +kernel
    rw [ha]
    exact (canonical17223 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 4) (sourceB1050 + difference 4 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 4) (sourceB1050 + difference 4 0) sourceC1050) = raw17224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17224; decide +kernel
    rw [ha]
    exact (canonical17224 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1050 + difference 0 5) (sourceB1050 + difference 5 0) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA1050 + difference 0 5) (sourceB1050 + difference 5 0) sourceC1050) = raw17225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17225; decide +kernel
    rw [ha]
    exact (canonical17225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 0) (sourceB1050 + difference 0 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 0) (sourceB1050 + difference 0 1) sourceC1050) = raw15127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15127; decide +kernel
    rw [ha]
    exact (canonical15127 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 2) (sourceB1050 + difference 2 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 2) (sourceB1050 + difference 2 1) sourceC1050) = raw15117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15117; decide +kernel
    rw [ha]
    exact (canonical15117 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 3) (sourceB1050 + difference 3 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 3) (sourceB1050 + difference 3 1) sourceC1050) = raw15859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15859; decide +kernel
    rw [ha]
    exact (canonical15859 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 4) (sourceB1050 + difference 4 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 4) (sourceB1050 + difference 4 1) sourceC1050) = raw15667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15667; decide +kernel
    rw [ha]
    exact (canonical15667 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1050 + difference 1 5) (sourceB1050 + difference 5 1) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1050 + difference 1 5) (sourceB1050 + difference 5 1) sourceC1050) = raw15860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15860; decide +kernel
    rw [ha]
    exact (canonical15860 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 0) (sourceB1050 + difference 0 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 0) (sourceB1050 + difference 0 2) sourceC1050) = raw15865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15865; decide +kernel
    rw [ha]
    exact (canonical15865 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 1) (sourceB1050 + difference 1 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 1) (sourceB1050 + difference 1 2) sourceC1050) = raw16848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16848; decide +kernel
    rw [ha]
    exact (canonical16848 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 3) (sourceB1050 + difference 3 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 3) (sourceB1050 + difference 3 2) sourceC1050) = raw17226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17226; decide +kernel
    rw [ha]
    exact (canonical17226 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 4) (sourceB1050 + difference 4 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 4) (sourceB1050 + difference 4 2) sourceC1050) = raw17227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17227; decide +kernel
    rw [ha]
    exact (canonical17227 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1050 + difference 2 5) (sourceB1050 + difference 5 2) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1050 + difference 2 5) (sourceB1050 + difference 5 2) sourceC1050) = raw17228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17228; decide +kernel
    rw [ha]
    exact (canonical17228 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 0) (sourceB1050 + difference 0 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 0) (sourceB1050 + difference 0 3) sourceC1050) = raw15869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15869; decide +kernel
    rw [ha]
    exact (canonical15869 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 1) (sourceB1050 + difference 1 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 1) (sourceB1050 + difference 1 3) sourceC1050) = raw16853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16853; decide +kernel
    rw [ha]
    exact (canonical16853 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 2) (sourceB1050 + difference 2 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 2) (sourceB1050 + difference 2 3) sourceC1050) = raw17038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17038; decide +kernel
    rw [ha]
    exact (canonical17038 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 4) (sourceB1050 + difference 4 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 4) (sourceB1050 + difference 4 3) sourceC1050) = raw17229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17229; decide +kernel
    rw [ha]
    exact (canonical17229 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1050 + difference 3 5) (sourceB1050 + difference 5 3) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1050 + difference 3 5) (sourceB1050 + difference 5 3) sourceC1050) = raw17230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17230; decide +kernel
    rw [ha]
    exact (canonical17230 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 0) (sourceB1050 + difference 0 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 0) (sourceB1050 + difference 0 4) sourceC1050) = raw15205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15205; decide +kernel
    rw [ha]
    exact (canonical15205 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 1) (sourceB1050 + difference 1 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 1) (sourceB1050 + difference 1 4) sourceC1050) = raw16858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16858; decide +kernel
    rw [ha]
    exact (canonical16858 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 2) (sourceB1050 + difference 2 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 2) (sourceB1050 + difference 2 4) sourceC1050) = raw15200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15200; decide +kernel
    rw [ha]
    exact (canonical15200 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 3) (sourceB1050 + difference 3 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 3) (sourceB1050 + difference 3 4) sourceC1050) = raw17231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17231; decide +kernel
    rw [ha]
    exact (canonical17231 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1050 + difference 4 5) (sourceB1050 + difference 5 4) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA1050 + difference 4 5) (sourceB1050 + difference 5 4) sourceC1050) = raw17232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17232; decide +kernel
    rw [ha]
    exact (canonical17232 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 0) (sourceB1050 + difference 0 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 0) (sourceB1050 + difference 0 5) sourceC1050) = raw15124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15124; decide +kernel
    rw [ha]
    exact (canonical15124 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 1) (sourceB1050 + difference 1 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 1) (sourceB1050 + difference 1 5) sourceC1050) = raw17123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw17123; decide +kernel
    rw [ha]
    exact (canonical17123 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 2) (sourceB1050 + difference 2 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 2) (sourceB1050 + difference 2 5) sourceC1050) = raw15113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15113; decide +kernel
    rw [ha]
    exact (canonical15113 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 3) (sourceB1050 + difference 3 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 3) (sourceB1050 + difference 3 5) sourceC1050) = raw16843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw16843; decide +kernel
    rw [ha]
    exact (canonical16843 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1050 + difference 5 4) (sourceB1050 + difference 4 5) sourceC1050) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1050 + difference 5 4) (sourceB1050 + difference 4 5) sourceC1050) = raw15664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1050 sourceB1050 sourceC1050 difference raw15664; decide +kernel
    rw [ha]
    exact (canonical15664 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1050 sourceB1050 sourceC1050
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1050, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck903 : Integer.Sparse.reindex keyMap MixedData.row903 = numericRow903 := by decide +kernel

theorem numericCheck903 (x : Master → ℝ) : Integer.Sparse.eval numericRow903 x =
    (8640 : ℝ) * reducedSource903 x := by
  norm_num [numericRow903, reducedSource903, Integer.Sparse.eval, Sparse.eval, nodeValue5072, nodeValue5074, nodeValue5098, nodeValue5256, nodeValue5351, nodeValue5353, nodeValue5365, nodeValue5400, nodeValue5402, nodeValue5405, nodeValue5406, nodeValue5407, nodeValue5409, nodeValue5410, nodeValue5411, nodeValue5429, nodeValue5434, nodeValue5471, nodeValue5483]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero903 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource903 (mixedVector B) = 0 := by
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5074 : mixedVector B (Sum.inr 5074) = Sparse.eval nodeValue5074 (mixedVector B) := by
    change mixedMoment B node5074 node5074Labels = _
    exact sound5074 B hB hF
  have h5098 : mixedVector B (Sum.inr 5098) = Sparse.eval nodeValue5098 (mixedVector B) := by
    change mixedMoment B node5098 node5098Labels = _
    exact sound5098 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5365 : mixedVector B (Sum.inr 5365) = Sparse.eval nodeValue5365 (mixedVector B) := by
    change mixedMoment B node5365 node5365Labels = _
    exact sound5365 B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5402 : mixedVector B (Sum.inr 5402) = Sparse.eval nodeValue5402 (mixedVector B) := by
    change mixedMoment B node5402 node5402Labels = _
    exact sound5402 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5407 : mixedVector B (Sum.inr 5407) = Sparse.eval nodeValue5407 (mixedVector B) := by
    change mixedMoment B node5407 node5407Labels = _
    exact sound5407 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5471 : mixedVector B (Sum.inr 5471) = Sparse.eval nodeValue5471 (mixedVector B) := by
    change mixedMoment B node5471 node5471Labels = _
    exact sound5471 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  simpa only [sourceForm1050, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5072, h5074, h5098, h5256, h5351, h5353, h5365, h5400, h5402, h5405, h5406, h5407, h5409, h5410, h5411, h5429, h5434, h5471, h5483, reducedSource903] using sourceEq1050 B hB

theorem rowSound903_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row903 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck903, numericCheck903, reducedZero903 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound903_e_oai
