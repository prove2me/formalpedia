-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:24:10.999283+00:00
-- url     : https://prove2.me/submissions/3e1771fd-e90f-426b-8a65-10fbe218093d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5167_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5169_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13775 raw13775Labels = mixedMoment B node5482 node5482Labels := by
  calc
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical13786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13786 raw13786Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw13786 raw13786Labels = mixedMoment B raw13786step0 raw13786step0Labels := by
      have ha : raw13786step0 = (fun i j => raw13786 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13786step0 raw13786; decide +kernel
      have hl : raw13786step0Labels = raw13786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13786 raw13786Labels permutation156 permutation3
    mixedMoment B raw13786step0 raw13786step0Labels = mixedMoment B raw13786step1 raw13786step1Labels := by
      have ha : raw13786step1 = raw13786step0 := by apply Matrix.ext; unfold raw13786step1 raw13786step0; decide +kernel
      have hl : raw13786step0Labels = labelEmbedding6 ∘ raw13786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13786step0 raw13786step0Labels raw13786step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

theorem canonical13791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13791 raw13791Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw13791 raw13791Labels = mixedMoment B raw13791step0 raw13791step0Labels := by
      have ha : raw13791step0 = (fun i j => raw13791 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13791step0 raw13791; decide +kernel
      have hl : raw13791step0Labels = raw13791Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13791 raw13791Labels permutation157 permutation3
    mixedMoment B raw13791step0 raw13791step0Labels = mixedMoment B raw13791step1 raw13791step1Labels := by
      have ha : raw13791step1 = raw13791step0 := by apply Matrix.ext; unfold raw13791step1 raw13791step0; decide +kernel
      have hl : raw13791step0Labels = labelEmbedding6 ∘ raw13791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13791step0 raw13791step0Labels raw13791step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical13796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13796 raw13796Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw13796 raw13796Labels = mixedMoment B raw13796step0 raw13796step0Labels := by
      have ha : raw13796step0 = (fun i j => raw13796 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13796step0 raw13796; decide +kernel
      have hl : raw13796step0Labels = raw13796Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13796 raw13796Labels permutation156 permutation3
    mixedMoment B raw13796step0 raw13796step0Labels = mixedMoment B raw13796step1 raw13796step1Labels := by
      have ha : raw13796step1 = raw13796step0 := by apply Matrix.ext; unfold raw13796step1 raw13796step0; decide +kernel
      have hl : raw13796step0Labels = labelEmbedding6 ∘ raw13796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13796step0 raw13796step0Labels raw13796step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical13800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13800 raw13800Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw13800 raw13800Labels = mixedMoment B raw13800step0 raw13800step0Labels := by
      have ha : raw13800step0 = (fun i j => raw13800 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13800step0 raw13800; decide +kernel
      have hl : raw13800step0Labels = raw13800Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13800 raw13800Labels permutation176 permutation3
    mixedMoment B raw13800step0 raw13800step0Labels = mixedMoment B raw13800step1 raw13800step1Labels := by
      have ha : raw13800step1 = raw13800step0 := by apply Matrix.ext; unfold raw13800step1 raw13800step0; decide +kernel
      have hl : raw13800step0Labels = labelEmbedding6 ∘ raw13800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13800step0 raw13800step0Labels raw13800step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical13802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13802 raw13802Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw13802 raw13802Labels = mixedMoment B raw13802step0 raw13802step0Labels := by
      have ha : raw13802step0 = (fun i j => raw13802 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13802step0 raw13802; decide +kernel
      have hl : raw13802step0Labels = raw13802Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13802 raw13802Labels permutation176 permutation3
    mixedMoment B raw13802step0 raw13802step0Labels = mixedMoment B raw13802step1 raw13802step1Labels := by
      have ha : raw13802step1 = raw13802step0 := by apply Matrix.ext; unfold raw13802step1 raw13802step0; decide +kernel
      have hl : raw13802step0Labels = labelEmbedding6 ∘ raw13802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13802step0 raw13802step0Labels raw13802step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

theorem canonical13803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13803 raw13803Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13803 raw13803Labels = mixedMoment B raw13803step0 raw13803step0Labels := by
      have hz : ∀ j, raw13803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13803step0 = (fun i j => raw13803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13803step0 raw13803; decide +kernel
      have hl : raw13803step0Labels = raw13803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13803 raw13803Labels permutation434 hz
    mixedMoment B raw13803step0 raw13803step0Labels = mixedMoment B raw13803step1 raw13803step1Labels := by
      have ha : raw13803step1 = (fun i j => raw13803step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13803step1 raw13803step0; decide +kernel
      have hl : raw13803step1Labels = raw13803step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13803step0 raw13803step0Labels permutation38 permutation3
    mixedMoment B raw13803step1 raw13803step1Labels = mixedMoment B raw13803step2 raw13803step2Labels := by
      have ha : raw13803step2 = raw13803step1 := by apply Matrix.ext; unfold raw13803step2 raw13803step1; decide +kernel
      have hl : raw13803step1Labels = labelEmbedding6 ∘ raw13803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13803step1 raw13803step1Labels raw13803step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical13804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13804 raw13804Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13804 raw13804Labels = mixedMoment B raw13804step0 raw13804step0Labels := by
      have hz : ∀ j, raw13804 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13804step0 = (fun i j => raw13804 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13804step0 raw13804; decide +kernel
      have hl : raw13804step0Labels = raw13804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13804 raw13804Labels permutation520 hz
    mixedMoment B raw13804step0 raw13804step0Labels = mixedMoment B raw13804step1 raw13804step1Labels := by
      have ha : raw13804step1 = (fun i j => raw13804step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13804step1 raw13804step0; decide +kernel
      have hl : raw13804step1Labels = raw13804step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13804step0 raw13804step0Labels permutation38 permutation3
    mixedMoment B raw13804step1 raw13804step1Labels = mixedMoment B raw13804step2 raw13804step2Labels := by
      have ha : raw13804step2 = raw13804step1 := by apply Matrix.ext; unfold raw13804step2 raw13804step1; decide +kernel
      have hl : raw13804step1Labels = labelEmbedding6 ∘ raw13804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13804step1 raw13804step1Labels raw13804step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

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

theorem canonical1890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1890 raw1890Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw1890 raw1890Labels = mixedMoment B raw1890step0 raw1890step0Labels := by
      have ha : raw1890step0 = (fun i j => raw1890 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1890step0 raw1890; decide +kernel
      have hl : raw1890step0Labels = raw1890Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1890 raw1890Labels permutation152 permutation4
    mixedMoment B raw1890step0 raw1890step0Labels = mixedMoment B raw1890step1 raw1890step1Labels := by
      have ha : raw1890step1 = raw1890step0 := by apply Matrix.ext; unfold raw1890step1 raw1890step0; decide +kernel
      have hl : raw1890step0Labels = labelEmbedding7 ∘ raw1890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1890step0 raw1890step0Labels raw1890step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

theorem canonical1891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1891 raw1891Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw1891 raw1891Labels = mixedMoment B raw1891step0 raw1891step0Labels := by
      have ha : raw1891step0 = (fun i j => raw1891 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1891step0 raw1891; decide +kernel
      have hl : raw1891step0Labels = raw1891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1891 raw1891Labels permutation152 permutation4
    _ = mixedMoment B node2317 node2317Labels := by rfl

theorem canonical1892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1892 raw1892Labels = mixedMoment B node3399 node3399Labels := by
  calc
    mixedMoment B raw1892 raw1892Labels = mixedMoment B raw1892step0 raw1892step0Labels := by
      have ha : raw1892step0 = (fun i j => raw1892 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1892step0 raw1892; decide +kernel
      have hl : raw1892step0Labels = raw1892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1892 raw1892Labels permutation152 permutation6
    mixedMoment B raw1892step0 raw1892step0Labels = mixedMoment B raw1892step1 raw1892step1Labels := by
      have ha : raw1892step1 = -raw1892step0 := by apply Matrix.ext; change ∀ i j, raw1892step1 i j = -(raw1892step0 i j); unfold raw1892step1 raw1892step0; decide +kernel
      have hl : raw1892step1Labels = raw1892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1892step1 raw1892step1Labels = mixedMoment B raw1892step2 raw1892step2Labels := by
      have ha : raw1892step2 = raw1892step1 := by apply Matrix.ext; unfold raw1892step2 raw1892step1; decide +kernel
      have hl : raw1892step1Labels = labelEmbedding1 ∘ raw1892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1892step1 raw1892step1Labels raw1892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3399 node3399Labels := by rfl

theorem canonical1893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1893 raw1893Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw1893 raw1893Labels = mixedMoment B raw1893step0 raw1893step0Labels := by
      have ha : raw1893step0 = (fun i j => raw1893 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1893step0 raw1893; decide +kernel
      have hl : raw1893step0Labels = raw1893Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1893 raw1893Labels permutation152 permutation4
    mixedMoment B raw1893step0 raw1893step0Labels = mixedMoment B raw1893step1 raw1893step1Labels := by
      have ha : raw1893step1 = raw1893step0 := by apply Matrix.ext; unfold raw1893step1 raw1893step0; decide +kernel
      have hl : raw1893step0Labels = labelEmbedding7 ∘ raw1893step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1893step0 raw1893step0Labels raw1893step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical1894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1894 raw1894Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw1894 raw1894Labels = mixedMoment B raw1894step0 raw1894step0Labels := by
      have ha : raw1894step0 = (fun i j => raw1894 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1894step0 raw1894; decide +kernel
      have hl : raw1894step0Labels = raw1894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1894 raw1894Labels permutation152 permutation4
    _ = mixedMoment B node2318 node2318Labels := by rfl

theorem canonical1895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1895 raw1895Labels = mixedMoment B node3400 node3400Labels := by
  calc
    mixedMoment B raw1895 raw1895Labels = mixedMoment B raw1895step0 raw1895step0Labels := by
      have ha : raw1895step0 = (fun i j => raw1895 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1895step0 raw1895; decide +kernel
      have hl : raw1895step0Labels = raw1895Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1895 raw1895Labels permutation152 permutation6
    mixedMoment B raw1895step0 raw1895step0Labels = mixedMoment B raw1895step1 raw1895step1Labels := by
      have ha : raw1895step1 = -raw1895step0 := by apply Matrix.ext; change ∀ i j, raw1895step1 i j = -(raw1895step0 i j); unfold raw1895step1 raw1895step0; decide +kernel
      have hl : raw1895step1Labels = raw1895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1895step1 raw1895step1Labels = mixedMoment B raw1895step2 raw1895step2Labels := by
      have ha : raw1895step2 = raw1895step1 := by apply Matrix.ext; unfold raw1895step2 raw1895step1; decide +kernel
      have hl : raw1895step1Labels = labelEmbedding1 ∘ raw1895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1895step1 raw1895step1Labels raw1895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3400 node3400Labels := by rfl

theorem canonical1905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1905 raw1905Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw1905 raw1905Labels = mixedMoment B raw1905step0 raw1905step0Labels := by
      have ha : raw1905step0 = (fun i j => raw1905 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1905step0 raw1905; decide +kernel
      have hl : raw1905step0Labels = raw1905Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1905 raw1905Labels permutation152 permutation4
    mixedMoment B raw1905step0 raw1905step0Labels = mixedMoment B raw1905step1 raw1905step1Labels := by
      have ha : raw1905step1 = raw1905step0 := by apply Matrix.ext; unfold raw1905step1 raw1905step0; decide +kernel
      have hl : raw1905step0Labels = labelEmbedding7 ∘ raw1905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1905step0 raw1905step0Labels raw1905step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

theorem canonical1906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1906 raw1906Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw1906 raw1906Labels = mixedMoment B raw1906step0 raw1906step0Labels := by
      have ha : raw1906step0 = (fun i j => raw1906 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1906step0 raw1906; decide +kernel
      have hl : raw1906step0Labels = raw1906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1906 raw1906Labels permutation152 permutation4
    _ = mixedMoment B node2332 node2332Labels := by rfl

theorem canonical1907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1907 raw1907Labels = mixedMoment B node3410 node3410Labels := by
  calc
    mixedMoment B raw1907 raw1907Labels = mixedMoment B raw1907step0 raw1907step0Labels := by
      have ha : raw1907step0 = (fun i j => raw1907 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1907step0 raw1907; decide +kernel
      have hl : raw1907step0Labels = raw1907Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1907 raw1907Labels permutation152 permutation6
    mixedMoment B raw1907step0 raw1907step0Labels = mixedMoment B raw1907step1 raw1907step1Labels := by
      have ha : raw1907step1 = -raw1907step0 := by apply Matrix.ext; change ∀ i j, raw1907step1 i j = -(raw1907step0 i j); unfold raw1907step1 raw1907step0; decide +kernel
      have hl : raw1907step1Labels = raw1907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1907step1 raw1907step1Labels = mixedMoment B raw1907step2 raw1907step2Labels := by
      have ha : raw1907step2 = raw1907step1 := by apply Matrix.ext; unfold raw1907step2 raw1907step1; decide +kernel
      have hl : raw1907step1Labels = labelEmbedding1 ∘ raw1907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1907step1 raw1907step1Labels raw1907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3410 node3410Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18770 raw18770Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw18770 raw18770Labels = mixedMoment B raw18770step0 raw18770step0Labels := by
      have ha : raw18770step0 = (fun i j => raw18770 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18770step0 raw18770; decide +kernel
      have hl : raw18770step0Labels = raw18770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18770 raw18770Labels permutation180 permutation3
    mixedMoment B raw18770step0 raw18770step0Labels = mixedMoment B raw18770step1 raw18770step1Labels := by
      have ha : raw18770step1 = raw18770step0 := by apply Matrix.ext; unfold raw18770step1 raw18770step0; decide +kernel
      have hl : raw18770step0Labels = labelEmbedding6 ∘ raw18770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18770step0 raw18770step0Labels raw18770step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical18783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18783 raw18783Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw18783 raw18783Labels = mixedMoment B raw18783step0 raw18783step0Labels := by
      have ha : raw18783step0 = (fun i j => raw18783 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18783step0 raw18783; decide +kernel
      have hl : raw18783step0Labels = raw18783Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18783 raw18783Labels permutation152 permutation3
    mixedMoment B raw18783step0 raw18783step0Labels = mixedMoment B raw18783step1 raw18783step1Labels := by
      have ha : raw18783step1 = raw18783step0 := by apply Matrix.ext; unfold raw18783step1 raw18783step0; decide +kernel
      have hl : raw18783step0Labels = labelEmbedding6 ∘ raw18783step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18783step0 raw18783step0Labels raw18783step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

theorem canonical18784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18784 raw18784Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18784 raw18784Labels = mixedMoment B raw18784step0 raw18784step0Labels := by
      have ha : raw18784step0 = (fun i j => raw18784 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18784step0 raw18784; decide +kernel
      have hl : raw18784step0Labels = raw18784Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18784 raw18784Labels permutation176 permutation3
    mixedMoment B raw18784step0 raw18784step0Labels = mixedMoment B raw18784step1 raw18784step1Labels := by
      have ha : raw18784step1 = raw18784step0 := by apply Matrix.ext; unfold raw18784step1 raw18784step0; decide +kernel
      have hl : raw18784step0Labels = labelEmbedding6 ∘ raw18784step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18784step0 raw18784step0Labels raw18784step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical18785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18785 raw18785Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18785 raw18785Labels = mixedMoment B raw18785step0 raw18785step0Labels := by
      have hz : ∀ j, raw18785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18785step0 = (fun i j => raw18785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18785step0 raw18785; decide +kernel
      have hl : raw18785step0Labels = raw18785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18785 raw18785Labels permutation434 hz
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical18786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18786 raw18786Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18786 raw18786Labels = mixedMoment B raw18786step0 raw18786step0Labels := by
      have hz : ∀ j, raw18786 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18786step0 = (fun i j => raw18786 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18786step0 raw18786; decide +kernel
      have hl : raw18786step0Labels = raw18786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18786 raw18786Labels permutation520 hz
    _ = mixedMoment B node5483 node5483Labels := by rfl

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

theorem canonical1992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1992 raw1992Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw1992 raw1992Labels = mixedMoment B raw1992step0 raw1992step0Labels := by
      have ha : raw1992step0 = (fun i j => raw1992 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1992step0 raw1992; decide +kernel
      have hl : raw1992step0Labels = raw1992Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1992 raw1992Labels permutation152 permutation4
    mixedMoment B raw1992step0 raw1992step0Labels = mixedMoment B raw1992step1 raw1992step1Labels := by
      have ha : raw1992step1 = raw1992step0 := by apply Matrix.ext; unfold raw1992step1 raw1992step0; decide +kernel
      have hl : raw1992step0Labels = labelEmbedding7 ∘ raw1992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1992step0 raw1992step0Labels raw1992step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

theorem canonical1993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1993 raw1993Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw1993 raw1993Labels = mixedMoment B raw1993step0 raw1993step0Labels := by
      have ha : raw1993step0 = (fun i j => raw1993 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1993step0 raw1993; decide +kernel
      have hl : raw1993step0Labels = raw1993Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1993 raw1993Labels permutation152 permutation4
    _ = mixedMoment B node2371 node2371Labels := by rfl

theorem canonical1994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1994 raw1994Labels = mixedMoment B node3335 node3335Labels := by
  calc
    mixedMoment B raw1994 raw1994Labels = mixedMoment B raw1994step0 raw1994step0Labels := by
      have ha : raw1994step0 = (fun i j => raw1994 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1994step0 raw1994; decide +kernel
      have hl : raw1994step0Labels = raw1994Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1994 raw1994Labels permutation152 permutation6
    mixedMoment B raw1994step0 raw1994step0Labels = mixedMoment B raw1994step1 raw1994step1Labels := by
      have ha : raw1994step1 = -raw1994step0 := by apply Matrix.ext; change ∀ i j, raw1994step1 i j = -(raw1994step0 i j); unfold raw1994step1 raw1994step0; decide +kernel
      have hl : raw1994step1Labels = raw1994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1994step1 raw1994step1Labels = mixedMoment B raw1994step2 raw1994step2Labels := by
      have ha : raw1994step2 = raw1994step1 := by apply Matrix.ext; unfold raw1994step2 raw1994step1; decide +kernel
      have hl : raw1994step1Labels = labelEmbedding1 ∘ raw1994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1994step1 raw1994step1Labels raw1994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3335 node3335Labels := by rfl

theorem canonical1995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1995 raw1995Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw1995 raw1995Labels = mixedMoment B raw1995step0 raw1995step0Labels := by
      have ha : raw1995step0 = (fun i j => raw1995 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1995step0 raw1995; decide +kernel
      have hl : raw1995step0Labels = raw1995Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1995 raw1995Labels permutation152 permutation4
    mixedMoment B raw1995step0 raw1995step0Labels = mixedMoment B raw1995step1 raw1995step1Labels := by
      have ha : raw1995step1 = raw1995step0 := by apply Matrix.ext; unfold raw1995step1 raw1995step0; decide +kernel
      have hl : raw1995step0Labels = labelEmbedding7 ∘ raw1995step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1995step0 raw1995step0Labels raw1995step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1996 raw1996Labels = mixedMoment B node2372 node2372Labels := by
  calc
    mixedMoment B raw1996 raw1996Labels = mixedMoment B raw1996step0 raw1996step0Labels := by
      have ha : raw1996step0 = (fun i j => raw1996 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1996step0 raw1996; decide +kernel
      have hl : raw1996step0Labels = raw1996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1996 raw1996Labels permutation152 permutation4
    _ = mixedMoment B node2372 node2372Labels := by rfl

theorem canonical1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1997 raw1997Labels = mixedMoment B node3336 node3336Labels := by
  calc
    mixedMoment B raw1997 raw1997Labels = mixedMoment B raw1997step0 raw1997step0Labels := by
      have ha : raw1997step0 = (fun i j => raw1997 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1997step0 raw1997; decide +kernel
      have hl : raw1997step0Labels = raw1997Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1997 raw1997Labels permutation152 permutation6
    mixedMoment B raw1997step0 raw1997step0Labels = mixedMoment B raw1997step1 raw1997step1Labels := by
      have ha : raw1997step1 = -raw1997step0 := by apply Matrix.ext; change ∀ i j, raw1997step1 i j = -(raw1997step0 i j); unfold raw1997step1 raw1997step0; decide +kernel
      have hl : raw1997step1Labels = raw1997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1997step1 raw1997step1Labels = mixedMoment B raw1997step2 raw1997step2Labels := by
      have ha : raw1997step2 = raw1997step1 := by apply Matrix.ext; unfold raw1997step2 raw1997step1; decide +kernel
      have hl : raw1997step1Labels = labelEmbedding1 ∘ raw1997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1997step1 raw1997step1Labels raw1997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3336 node3336Labels := by rfl

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

theorem canonical2097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2097 raw2097Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw2097 raw2097Labels = mixedMoment B raw2097step0 raw2097step0Labels := by
      have ha : raw2097step0 = (fun i j => raw2097 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2097step0 raw2097; decide +kernel
      have hl : raw2097step0Labels = raw2097Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2097 raw2097Labels permutation32 permutation4
    mixedMoment B raw2097step0 raw2097step0Labels = mixedMoment B raw2097step1 raw2097step1Labels := by
      have ha : raw2097step1 = raw2097step0 := by apply Matrix.ext; unfold raw2097step1 raw2097step0; decide +kernel
      have hl : raw2097step0Labels = labelEmbedding7 ∘ raw2097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2097step0 raw2097step0Labels raw2097step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical2098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2098 raw2098Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw2098 raw2098Labels = mixedMoment B raw2098step0 raw2098step0Labels := by
      have ha : raw2098step0 = (fun i j => raw2098 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2098step0 raw2098; decide +kernel
      have hl : raw2098step0Labels = raw2098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2098 raw2098Labels permutation32 permutation4
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical2099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2099 raw2099Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw2099 raw2099Labels = mixedMoment B raw2099step0 raw2099step0Labels := by
      have ha : raw2099step0 = (fun i j => raw2099 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2099step0 raw2099; decide +kernel
      have hl : raw2099step0Labels = raw2099Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2099 raw2099Labels permutation34 permutation6
    mixedMoment B raw2099step0 raw2099step0Labels = mixedMoment B raw2099step1 raw2099step1Labels := by
      have ha : raw2099step1 = -raw2099step0 := by apply Matrix.ext; change ∀ i j, raw2099step1 i j = -(raw2099step0 i j); unfold raw2099step1 raw2099step0; decide +kernel
      have hl : raw2099step1Labels = raw2099step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2099step1 raw2099step1Labels = mixedMoment B raw2099step2 raw2099step2Labels := by
      have ha : raw2099step2 = raw2099step1 := by apply Matrix.ext; unfold raw2099step2 raw2099step1; decide +kernel
      have hl : raw2099step1Labels = labelEmbedding1 ∘ raw2099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2099step1 raw2099step1Labels raw2099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2163 raw2163Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw2163 raw2163Labels = mixedMoment B raw2163step0 raw2163step0Labels := by
      have ha : raw2163step0 = (fun i j => raw2163 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2163step0 raw2163; decide +kernel
      have hl : raw2163step0Labels = raw2163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2163 raw2163Labels permutation152 permutation4
    mixedMoment B raw2163step0 raw2163step0Labels = mixedMoment B raw2163step1 raw2163step1Labels := by
      have ha : raw2163step1 = raw2163step0 := by apply Matrix.ext; unfold raw2163step1 raw2163step0; decide +kernel
      have hl : raw2163step0Labels = labelEmbedding7 ∘ raw2163step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2163step0 raw2163step0Labels raw2163step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2164 raw2164Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw2164 raw2164Labels = mixedMoment B raw2164step0 raw2164step0Labels := by
      have ha : raw2164step0 = (fun i j => raw2164 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2164step0 raw2164; decide +kernel
      have hl : raw2164step0Labels = raw2164Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2164 raw2164Labels permutation152 permutation4
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2165 raw2165Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw2165 raw2165Labels = mixedMoment B raw2165step0 raw2165step0Labels := by
      have ha : raw2165step0 = (fun i j => raw2165 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2165step0 raw2165; decide +kernel
      have hl : raw2165step0Labels = raw2165Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2165 raw2165Labels permutation176 permutation6
    mixedMoment B raw2165step0 raw2165step0Labels = mixedMoment B raw2165step1 raw2165step1Labels := by
      have ha : raw2165step1 = -raw2165step0 := by apply Matrix.ext; change ∀ i j, raw2165step1 i j = -(raw2165step0 i j); unfold raw2165step1 raw2165step0; decide +kernel
      have hl : raw2165step1Labels = raw2165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2165step1 raw2165step1Labels = mixedMoment B raw2165step2 raw2165step2Labels := by
      have ha : raw2165step2 = raw2165step1 := by apply Matrix.ext; unfold raw2165step2 raw2165step1; decide +kernel
      have hl : raw2165step1Labels = labelEmbedding1 ∘ raw2165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2165step1 raw2165step1Labels raw2165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

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

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32881 raw32881Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw32881 raw32881Labels = mixedMoment B raw32881step0 raw32881step0Labels := by
      have ha : raw32881step0 = (fun i j => raw32881 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32881step0 raw32881; decide +kernel
      have hl : raw32881step0Labels = raw32881Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32881 raw32881Labels permutation152 permutation3
    mixedMoment B raw32881step0 raw32881step0Labels = mixedMoment B raw32881step1 raw32881step1Labels := by
      have ha : raw32881step1 = raw32881step0 := by apply Matrix.ext; unfold raw32881step1 raw32881step0; decide +kernel
      have hl : raw32881step0Labels = labelEmbedding6 ∘ raw32881step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32881step0 raw32881step0Labels raw32881step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical32882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32882 raw32882Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw32882 raw32882Labels = mixedMoment B raw32882step0 raw32882step0Labels := by
      have ha : raw32882step0 = (fun i j => raw32882 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32882step0 raw32882; decide +kernel
      have hl : raw32882step0Labels = raw32882Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32882 raw32882Labels permutation152 permutation3
    mixedMoment B raw32882step0 raw32882step0Labels = mixedMoment B raw32882step1 raw32882step1Labels := by
      have ha : raw32882step1 = raw32882step0 := by apply Matrix.ext; unfold raw32882step1 raw32882step0; decide +kernel
      have hl : raw32882step0Labels = labelEmbedding6 ∘ raw32882step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32882step0 raw32882step0Labels raw32882step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

theorem canonical32883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32883 raw32883Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32883 raw32883Labels = mixedMoment B raw32883step0 raw32883step0Labels := by
      have hz : ∀ j, raw32883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32883step0 = (fun i j => raw32883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32883step0 raw32883; decide +kernel
      have hl : raw32883step0Labels = raw32883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32883 raw32883Labels permutation434 hz
    mixedMoment B raw32883step0 raw32883step0Labels = mixedMoment B raw32883step1 raw32883step1Labels := by
      have ha : raw32883step1 = (fun i j => raw32883step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32883step1 raw32883step0; decide +kernel
      have hl : raw32883step1Labels = raw32883step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32883step0 raw32883step0Labels permutation32 permutation3
    mixedMoment B raw32883step1 raw32883step1Labels = mixedMoment B raw32883step2 raw32883step2Labels := by
      have ha : raw32883step2 = raw32883step1 := by apply Matrix.ext; unfold raw32883step2 raw32883step1; decide +kernel
      have hl : raw32883step1Labels = labelEmbedding6 ∘ raw32883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32883step1 raw32883step1Labels raw32883step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

theorem canonical32884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32884 raw32884Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32884 raw32884Labels = mixedMoment B raw32884step0 raw32884step0Labels := by
      have hz : ∀ j, raw32884 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32884step0 = (fun i j => raw32884 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32884step0 raw32884; decide +kernel
      have hl : raw32884step0Labels = raw32884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32884 raw32884Labels permutation520 hz
    mixedMoment B raw32884step0 raw32884step0Labels = mixedMoment B raw32884step1 raw32884step1Labels := by
      have ha : raw32884step1 = (fun i j => raw32884step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32884step1 raw32884step0; decide +kernel
      have hl : raw32884step1Labels = raw32884step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32884step0 raw32884step0Labels permutation32 permutation3
    mixedMoment B raw32884step1 raw32884step1Labels = mixedMoment B raw32884step2 raw32884step2Labels := by
      have ha : raw32884step2 = raw32884step1 := by apply Matrix.ext; unfold raw32884step2 raw32884step1; decide +kernel
      have hl : raw32884step1Labels = labelEmbedding6 ∘ raw32884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32884step1 raw32884step1Labels raw32884step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

theorem canonical32885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32885 raw32885Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw32885 raw32885Labels = mixedMoment B raw32885step0 raw32885step0Labels := by
      have ha : raw32885step0 = (fun i j => raw32885 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32885step0 raw32885; decide +kernel
      have hl : raw32885step0Labels = raw32885Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32885 raw32885Labels permutation155 permutation3
    mixedMoment B raw32885step0 raw32885step0Labels = mixedMoment B raw32885step1 raw32885step1Labels := by
      have ha : raw32885step1 = raw32885step0 := by apply Matrix.ext; unfold raw32885step1 raw32885step0; decide +kernel
      have hl : raw32885step0Labels = labelEmbedding6 ∘ raw32885step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32885step0 raw32885step0Labels raw32885step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical32886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32886 raw32886Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw32886 raw32886Labels = mixedMoment B raw32886step0 raw32886step0Labels := by
      have ha : raw32886step0 = (fun i j => raw32886 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32886step0 raw32886; decide +kernel
      have hl : raw32886step0Labels = raw32886Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32886 raw32886Labels permutation155 permutation3
    mixedMoment B raw32886step0 raw32886step0Labels = mixedMoment B raw32886step1 raw32886step1Labels := by
      have ha : raw32886step1 = raw32886step0 := by apply Matrix.ext; unfold raw32886step1 raw32886step0; decide +kernel
      have hl : raw32886step0Labels = labelEmbedding6 ∘ raw32886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32886step0 raw32886step0Labels raw32886step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical32887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32887 raw32887Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw32887 raw32887Labels = mixedMoment B raw32887step0 raw32887step0Labels := by
      have ha : raw32887step0 = (fun i j => raw32887 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32887step0 raw32887; decide +kernel
      have hl : raw32887step0Labels = raw32887Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32887 raw32887Labels permutation179 permutation3
    mixedMoment B raw32887step0 raw32887step0Labels = mixedMoment B raw32887step1 raw32887step1Labels := by
      have ha : raw32887step1 = raw32887step0 := by apply Matrix.ext; unfold raw32887step1 raw32887step0; decide +kernel
      have hl : raw32887step0Labels = labelEmbedding6 ∘ raw32887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32887step0 raw32887step0Labels raw32887step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical32888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32888 raw32888Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32888 raw32888Labels = mixedMoment B raw32888step0 raw32888step0Labels := by
      have hz : ∀ j, raw32888 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32888step0 = (fun i j => raw32888 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32888step0 raw32888; decide +kernel
      have hl : raw32888step0Labels = raw32888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32888 raw32888Labels permutation520 hz
    mixedMoment B raw32888step0 raw32888step0Labels = mixedMoment B raw32888step1 raw32888step1Labels := by
      have ha : raw32888step1 = (fun i j => raw32888step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32888step1 raw32888step0; decide +kernel
      have hl : raw32888step1Labels = raw32888step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32888step0 raw32888step0Labels permutation33 permutation3
    mixedMoment B raw32888step1 raw32888step1Labels = mixedMoment B raw32888step2 raw32888step2Labels := by
      have ha : raw32888step2 = raw32888step1 := by apply Matrix.ext; unfold raw32888step2 raw32888step1; decide +kernel
      have hl : raw32888step1Labels = labelEmbedding6 ∘ raw32888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32888step1 raw32888step1Labels raw32888step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical32889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32889 raw32889Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw32889 raw32889Labels = mixedMoment B raw32889step0 raw32889step0Labels := by
      have ha : raw32889step0 = (fun i j => raw32889 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32889step0 raw32889; decide +kernel
      have hl : raw32889step0Labels = raw32889Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32889 raw32889Labels permutation153 permutation3
    mixedMoment B raw32889step0 raw32889step0Labels = mixedMoment B raw32889step1 raw32889step1Labels := by
      have ha : raw32889step1 = raw32889step0 := by apply Matrix.ext; unfold raw32889step1 raw32889step0; decide +kernel
      have hl : raw32889step0Labels = labelEmbedding6 ∘ raw32889step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32889step0 raw32889step0Labels raw32889step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical32890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32890 raw32890Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw32890 raw32890Labels = mixedMoment B raw32890step0 raw32890step0Labels := by
      have ha : raw32890step0 = (fun i j => raw32890 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32890step0 raw32890; decide +kernel
      have hl : raw32890step0Labels = raw32890Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32890 raw32890Labels permutation153 permutation3
    mixedMoment B raw32890step0 raw32890step0Labels = mixedMoment B raw32890step1 raw32890step1Labels := by
      have ha : raw32890step1 = raw32890step0 := by apply Matrix.ext; unfold raw32890step1 raw32890step0; decide +kernel
      have hl : raw32890step0Labels = labelEmbedding6 ∘ raw32890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32890step0 raw32890step0Labels raw32890step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical32891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32891 raw32891Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw32891 raw32891Labels = mixedMoment B raw32891step0 raw32891step0Labels := by
      have ha : raw32891step0 = (fun i j => raw32891 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32891step0 raw32891; decide +kernel
      have hl : raw32891step0Labels = raw32891Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32891 raw32891Labels permutation177 permutation3
    mixedMoment B raw32891step0 raw32891step0Labels = mixedMoment B raw32891step1 raw32891step1Labels := by
      have ha : raw32891step1 = raw32891step0 := by apply Matrix.ext; unfold raw32891step1 raw32891step0; decide +kernel
      have hl : raw32891step0Labels = labelEmbedding6 ∘ raw32891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32891step0 raw32891step0Labels raw32891step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical32892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32892 raw32892Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32892 raw32892Labels = mixedMoment B raw32892step0 raw32892step0Labels := by
      have hz : ∀ j, raw32892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32892step0 = (fun i j => raw32892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32892step0 raw32892; decide +kernel
      have hl : raw32892step0Labels = raw32892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32892 raw32892Labels permutation434 hz
    mixedMoment B raw32892step0 raw32892step0Labels = mixedMoment B raw32892step1 raw32892step1Labels := by
      have ha : raw32892step1 = (fun i j => raw32892step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32892step1 raw32892step0; decide +kernel
      have hl : raw32892step1Labels = raw32892step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32892step0 raw32892step0Labels permutation33 permutation3
    mixedMoment B raw32892step1 raw32892step1Labels = mixedMoment B raw32892step2 raw32892step2Labels := by
      have ha : raw32892step2 = raw32892step1 := by apply Matrix.ext; unfold raw32892step2 raw32892step1; decide +kernel
      have hl : raw32892step1Labels = labelEmbedding6 ∘ raw32892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32892step1 raw32892step1Labels raw32892step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical32893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32893 raw32893Labels = mixedMoment B node4322 node4322Labels := by
  calc
    mixedMoment B raw32893 raw32893Labels = mixedMoment B raw32893step0 raw32893step0Labels := by
      have ha : raw32893step0 = (fun i j => raw32893 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32893step0 raw32893; decide +kernel
      have hl : raw32893step0Labels = raw32893Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32893 raw32893Labels permutation152 permutation3
    mixedMoment B raw32893step0 raw32893step0Labels = mixedMoment B raw32893step1 raw32893step1Labels := by
      have ha : raw32893step1 = raw32893step0 := by apply Matrix.ext; unfold raw32893step1 raw32893step0; decide +kernel
      have hl : raw32893step0Labels = labelEmbedding6 ∘ raw32893step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32893step0 raw32893step0Labels raw32893step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4322 node4322Labels := by rfl

theorem canonical32894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32894 raw32894Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw32894 raw32894Labels = mixedMoment B raw32894step0 raw32894step0Labels := by
      have ha : raw32894step0 = (fun i j => raw32894 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32894step0 raw32894; decide +kernel
      have hl : raw32894step0Labels = raw32894Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32894 raw32894Labels permutation152 permutation3
    mixedMoment B raw32894step0 raw32894step0Labels = mixedMoment B raw32894step1 raw32894step1Labels := by
      have ha : raw32894step1 = raw32894step0 := by apply Matrix.ext; unfold raw32894step1 raw32894step0; decide +kernel
      have hl : raw32894step0Labels = labelEmbedding6 ∘ raw32894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32894step0 raw32894step0Labels raw32894step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

theorem canonical32895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32895 raw32895Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw32895 raw32895Labels = mixedMoment B raw32895step0 raw32895step0Labels := by
      have ha : raw32895step0 = (fun i j => raw32895 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32895step0 raw32895; decide +kernel
      have hl : raw32895step0Labels = raw32895Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32895 raw32895Labels permutation176 permutation3
    mixedMoment B raw32895step0 raw32895step0Labels = mixedMoment B raw32895step1 raw32895step1Labels := by
      have ha : raw32895step1 = raw32895step0 := by apply Matrix.ext; unfold raw32895step1 raw32895step0; decide +kernel
      have hl : raw32895step0Labels = labelEmbedding6 ∘ raw32895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32895step0 raw32895step0Labels raw32895step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical257
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32896 raw32896Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw32896 raw32896Labels = mixedMoment B raw32896step0 raw32896step0Labels := by
      have hz : ∀ j, raw32896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32896step0 = (fun i j => raw32896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32896step0 raw32896; decide +kernel
      have hl : raw32896step0Labels = raw32896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32896 raw32896Labels permutation434 hz
    mixedMoment B raw32896step0 raw32896step0Labels = mixedMoment B raw32896step1 raw32896step1Labels := by
      have ha : raw32896step1 = (fun i j => raw32896step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32896step1 raw32896step0; decide +kernel
      have hl : raw32896step1Labels = raw32896step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32896step0 raw32896step0Labels permutation151 permutation3
    mixedMoment B raw32896step1 raw32896step1Labels = mixedMoment B raw32896step2 raw32896step2Labels := by
      have ha : raw32896step2 = -raw32896step1 := by apply Matrix.ext; change ∀ i j, raw32896step2 i j = -(raw32896step1 i j); unfold raw32896step2 raw32896step1; decide +kernel
      have hl : raw32896step2Labels = raw32896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32896step2 raw32896step2Labels = mixedMoment B raw32896step3 raw32896step3Labels := by
      have ha : raw32896step3 = raw32896step2 := by apply Matrix.ext; unfold raw32896step3 raw32896step2; decide +kernel
      have hl : raw32896step2Labels = labelEmbedding6 ∘ raw32896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32896step2 raw32896step2Labels raw32896step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical32897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32897 raw32897Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw32897 raw32897Labels = mixedMoment B raw32897step0 raw32897step0Labels := by
      have hz : ∀ j, raw32897 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32897step0 = (fun i j => raw32897 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32897step0 raw32897; decide +kernel
      have hl : raw32897step0Labels = raw32897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32897 raw32897Labels permutation520 hz
    mixedMoment B raw32897step0 raw32897step0Labels = mixedMoment B raw32897step1 raw32897step1Labels := by
      have ha : raw32897step1 = (fun i j => raw32897step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32897step1 raw32897step0; decide +kernel
      have hl : raw32897step1Labels = raw32897step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32897step0 raw32897step0Labels permutation151 permutation3
    mixedMoment B raw32897step1 raw32897step1Labels = mixedMoment B raw32897step2 raw32897step2Labels := by
      have ha : raw32897step2 = -raw32897step1 := by apply Matrix.ext; change ∀ i j, raw32897step2 i j = -(raw32897step1 i j); unfold raw32897step2 raw32897step1; decide +kernel
      have hl : raw32897step2Labels = raw32897step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32897step2 raw32897step2Labels = mixedMoment B raw32897step3 raw32897step3Labels := by
      have ha : raw32897step3 = raw32897step2 := by apply Matrix.ext; unfold raw32897step3 raw32897step2; decide +kernel
      have hl : raw32897step2Labels = labelEmbedding6 ∘ raw32897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32897step2 raw32897step2Labels raw32897step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

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

theorem canonical1101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1101 raw1101Labels = mixedMoment B node4322 node4322Labels := by
  calc
    mixedMoment B raw1101 raw1101Labels = mixedMoment B raw1101step0 raw1101step0Labels := by
      have ha : raw1101step0 = (fun i j => raw1101 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1101step0 raw1101; decide +kernel
      have hl : raw1101step0Labels = raw1101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1101 raw1101Labels permutation152 permutation4
    mixedMoment B raw1101step0 raw1101step0Labels = mixedMoment B raw1101step1 raw1101step1Labels := by
      have ha : raw1101step1 = raw1101step0 := by apply Matrix.ext; unfold raw1101step1 raw1101step0; decide +kernel
      have hl : raw1101step0Labels = labelEmbedding7 ∘ raw1101step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1101step0 raw1101step0Labels raw1101step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4322 node4322Labels := by rfl

theorem canonical1102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1102 raw1102Labels = mixedMoment B node900 node900Labels := by
  calc
    mixedMoment B raw1102 raw1102Labels = mixedMoment B raw1102step0 raw1102step0Labels := by
      have ha : raw1102step0 = (fun i j => raw1102 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1102step0 raw1102; decide +kernel
      have hl : raw1102step0Labels = raw1102Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1102 raw1102Labels permutation152 permutation4
    _ = mixedMoment B node900 node900Labels := by rfl

theorem canonical1103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1103 raw1103Labels = mixedMoment B node1588 node1588Labels := by
  calc
    mixedMoment B raw1103 raw1103Labels = mixedMoment B raw1103step0 raw1103step0Labels := by
      have ha : raw1103step0 = (fun i j => raw1103 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1103step0 raw1103; decide +kernel
      have hl : raw1103step0Labels = raw1103Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1103 raw1103Labels permutation176 permutation6
    mixedMoment B raw1103step0 raw1103step0Labels = mixedMoment B raw1103step1 raw1103step1Labels := by
      have ha : raw1103step1 = -raw1103step0 := by apply Matrix.ext; change ∀ i j, raw1103step1 i j = -(raw1103step0 i j); unfold raw1103step1 raw1103step0; decide +kernel
      have hl : raw1103step1Labels = raw1103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1103step1 raw1103step1Labels = mixedMoment B raw1103step2 raw1103step2Labels := by
      have ha : raw1103step2 = raw1103step1 := by apply Matrix.ext; unfold raw1103step2 raw1103step1; decide +kernel
      have hl : raw1103step1Labels = labelEmbedding1 ∘ raw1103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1103step1 raw1103step1Labels raw1103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1588 node1588Labels := by rfl

theorem canonical1104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1104 raw1104Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw1104 raw1104Labels = mixedMoment B raw1104step0 raw1104step0Labels := by
      have ha : raw1104step0 = (fun i j => raw1104 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1104step0 raw1104; decide +kernel
      have hl : raw1104step0Labels = raw1104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1104 raw1104Labels permutation152 permutation4
    mixedMoment B raw1104step0 raw1104step0Labels = mixedMoment B raw1104step1 raw1104step1Labels := by
      have ha : raw1104step1 = raw1104step0 := by apply Matrix.ext; unfold raw1104step1 raw1104step0; decide +kernel
      have hl : raw1104step0Labels = labelEmbedding7 ∘ raw1104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1104step0 raw1104step0Labels raw1104step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical1105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1105 raw1105Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw1105 raw1105Labels = mixedMoment B raw1105step0 raw1105step0Labels := by
      have ha : raw1105step0 = (fun i j => raw1105 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1105step0 raw1105; decide +kernel
      have hl : raw1105step0Labels = raw1105Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1105 raw1105Labels permutation152 permutation4
    _ = mixedMoment B node901 node901Labels := by rfl

theorem canonical1106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1106 raw1106Labels = mixedMoment B node1589 node1589Labels := by
  calc
    mixedMoment B raw1106 raw1106Labels = mixedMoment B raw1106step0 raw1106step0Labels := by
      have ha : raw1106step0 = (fun i j => raw1106 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1106step0 raw1106; decide +kernel
      have hl : raw1106step0Labels = raw1106Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1106 raw1106Labels permutation176 permutation6
    mixedMoment B raw1106step0 raw1106step0Labels = mixedMoment B raw1106step1 raw1106step1Labels := by
      have ha : raw1106step1 = -raw1106step0 := by apply Matrix.ext; change ∀ i j, raw1106step1 i j = -(raw1106step0 i j); unfold raw1106step1 raw1106step0; decide +kernel
      have hl : raw1106step1Labels = raw1106step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1106step1 raw1106step1Labels = mixedMoment B raw1106step2 raw1106step2Labels := by
      have ha : raw1106step2 = raw1106step1 := by apply Matrix.ext; unfold raw1106step2 raw1106step1; decide +kernel
      have hl : raw1106step1Labels = labelEmbedding1 ∘ raw1106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1106step1 raw1106step1Labels raw1106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1589 node1589Labels := by rfl

theorem canonical1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1128 raw1128Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw1128 raw1128Labels = mixedMoment B raw1128step0 raw1128step0Labels := by
      have ha : raw1128step0 = (fun i j => raw1128 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1128step0 raw1128; decide +kernel
      have hl : raw1128step0Labels = raw1128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1128 raw1128Labels permutation152 permutation4
    mixedMoment B raw1128step0 raw1128step0Labels = mixedMoment B raw1128step1 raw1128step1Labels := by
      have ha : raw1128step1 = raw1128step0 := by apply Matrix.ext; unfold raw1128step1 raw1128step0; decide +kernel
      have hl : raw1128step0Labels = labelEmbedding7 ∘ raw1128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1128step0 raw1128step0Labels raw1128step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1129 raw1129Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw1129 raw1129Labels = mixedMoment B raw1129step0 raw1129step0Labels := by
      have ha : raw1129step0 = (fun i j => raw1129 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1129step0 raw1129; decide +kernel
      have hl : raw1129step0Labels = raw1129Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1129 raw1129Labels permutation152 permutation4
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1130 raw1130Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw1130 raw1130Labels = mixedMoment B raw1130step0 raw1130step0Labels := by
      have ha : raw1130step0 = (fun i j => raw1130 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1130step0 raw1130; decide +kernel
      have hl : raw1130step0Labels = raw1130Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1130 raw1130Labels permutation152 permutation6
    mixedMoment B raw1130step0 raw1130step0Labels = mixedMoment B raw1130step1 raw1130step1Labels := by
      have ha : raw1130step1 = -raw1130step0 := by apply Matrix.ext; change ∀ i j, raw1130step1 i j = -(raw1130step0 i j); unfold raw1130step1 raw1130step0; decide +kernel
      have hl : raw1130step1Labels = raw1130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1130step1 raw1130step1Labels = mixedMoment B raw1130step2 raw1130step2Labels := by
      have ha : raw1130step2 = raw1130step1 := by apply Matrix.ext; unfold raw1130step2 raw1130step1; decide +kernel
      have hl : raw1130step1Labels = labelEmbedding1 ∘ raw1130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1130step1 raw1130step1Labels raw1130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

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

theorem canonical1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1212 raw1212Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw1212 raw1212Labels = mixedMoment B raw1212step0 raw1212step0Labels := by
      have ha : raw1212step0 = (fun i j => raw1212 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1212step0 raw1212; decide +kernel
      have hl : raw1212step0Labels = raw1212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1212 raw1212Labels permutation152 permutation4
    mixedMoment B raw1212step0 raw1212step0Labels = mixedMoment B raw1212step1 raw1212step1Labels := by
      have ha : raw1212step1 = raw1212step0 := by apply Matrix.ext; unfold raw1212step1 raw1212step0; decide +kernel
      have hl : raw1212step0Labels = labelEmbedding7 ∘ raw1212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1212step0 raw1212step0Labels raw1212step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1213 raw1213Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw1213 raw1213Labels = mixedMoment B raw1213step0 raw1213step0Labels := by
      have ha : raw1213step0 = (fun i j => raw1213 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1213step0 raw1213; decide +kernel
      have hl : raw1213step0Labels = raw1213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1213 raw1213Labels permutation152 permutation4
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical1214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1214 raw1214Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw1214 raw1214Labels = mixedMoment B raw1214step0 raw1214step0Labels := by
      have ha : raw1214step0 = (fun i j => raw1214 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1214step0 raw1214; decide +kernel
      have hl : raw1214step0Labels = raw1214Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1214 raw1214Labels permutation152 permutation6
    mixedMoment B raw1214step0 raw1214step0Labels = mixedMoment B raw1214step1 raw1214step1Labels := by
      have ha : raw1214step1 = -raw1214step0 := by apply Matrix.ext; change ∀ i j, raw1214step1 i j = -(raw1214step0 i j); unfold raw1214step1 raw1214step0; decide +kernel
      have hl : raw1214step1Labels = raw1214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1214step1 raw1214step1Labels = mixedMoment B raw1214step2 raw1214step2Labels := by
      have ha : raw1214step2 = raw1214step1 := by apply Matrix.ext; unfold raw1214step2 raw1214step1; decide +kernel
      have hl : raw1214step1Labels = labelEmbedding1 ∘ raw1214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1214step1 raw1214step1Labels raw1214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1616 node1616Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4322 node4322Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node900 node900Labels + mixedMoment B node1588 node1588Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1101 singletonSmall4322
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4322) = raw1101Labels := by decide +kernel
  rw [hl, canonical1101 B hB] at h
  have hc0 : mixedMoment B raw1101 (Fin.cases (0 : Fin 2) singletonSmall4322) =
      mixedMoment B node900 node900Labels := by
    have ha : raw1101 = raw1102 := by apply Matrix.ext; unfold raw1101 raw1102; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4322 = raw1102Labels := by decide +kernel
    rw [ha, hj, canonical1102 B hB]
  have hc1 : mixedMoment B raw1101 (Fin.cases (1 : Fin 2) singletonSmall4322) =
      mixedMoment B node1588 node1588Labels := by
    have ha : raw1101 = raw1103 := by apply Matrix.ext; unfold raw1101 raw1103; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4322 = raw1103Labels := by decide +kernel
    rw [ha, hj, canonical1103 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4323 node4323Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node901 node901Labels + mixedMoment B node1589 node1589Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1104 singletonSmall4323
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4323) = raw1104Labels := by decide +kernel
  rw [hl, canonical1104 B hB] at h
  have hc0 : mixedMoment B raw1104 (Fin.cases (0 : Fin 2) singletonSmall4323) =
      mixedMoment B node901 node901Labels := by
    have ha : raw1104 = raw1105 := by apply Matrix.ext; unfold raw1104 raw1105; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4323 = raw1105Labels := by decide +kernel
    rw [ha, hj, canonical1105 B hB]
  have hc1 : mixedMoment B raw1104 (Fin.cases (1 : Fin 2) singletonSmall4323) =
      mixedMoment B node1589 node1589Labels := by
    have ha : raw1104 = raw1106 := by apply Matrix.ext; unfold raw1104 raw1106; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4323 = raw1106Labels := by decide +kernel
    rw [ha, hj, canonical1106 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4344 node4344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node922 node922Labels + mixedMoment B node1673 node1673Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1128 singletonSmall4344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4344) = raw1128Labels := by decide +kernel
  rw [hl, canonical1128 B hB] at h
  have hc0 : mixedMoment B raw1128 (Fin.cases (0 : Fin 2) singletonSmall4344) =
      mixedMoment B node922 node922Labels := by
    have ha : raw1128 = raw1129 := by apply Matrix.ext; unfold raw1128 raw1129; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4344 = raw1129Labels := by decide +kernel
    rw [ha, hj, canonical1129 B hB]
  have hc1 : mixedMoment B raw1128 (Fin.cases (1 : Fin 2) singletonSmall4344) =
      mixedMoment B node1673 node1673Labels := by
    have ha : raw1128 = raw1130 := by apply Matrix.ext; unfold raw1128 raw1130; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4344 = raw1130Labels := by decide +kernel
    rw [ha, hj, canonical1130 B hB]
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

theorem singleton4399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4399 node4399Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node980 node980Labels + mixedMoment B node1616 node1616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1212 singletonSmall4399
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4399) = raw1212Labels := by decide +kernel
  rw [hl, canonical1212 B hB] at h
  have hc0 : mixedMoment B raw1212 (Fin.cases (0 : Fin 2) singletonSmall4399) =
      mixedMoment B node980 node980Labels := by
    have ha : raw1212 = raw1213 := by apply Matrix.ext; unfold raw1212 raw1213; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4399 = raw1213Labels := by decide +kernel
    rw [ha, hj, canonical1213 B hB]
  have hc1 : mixedMoment B raw1212 (Fin.cases (1 : Fin 2) singletonSmall4399) =
      mixedMoment B node1616 node1616Labels := by
    have ha : raw1212 = raw1214 := by apply Matrix.ext; unfold raw1212 raw1214; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4399 = raw1214Labels := by decide +kernel
    rw [ha, hj, canonical1214 B hB]
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

theorem singleton4927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4927 node4927Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2317 node2317Labels + mixedMoment B node3399 node3399Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1890 singletonSmall4927
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4927) = raw1890Labels := by decide +kernel
  rw [hl, canonical1890 B hB] at h
  have hc0 : mixedMoment B raw1890 (Fin.cases (0 : Fin 2) singletonSmall4927) =
      mixedMoment B node2317 node2317Labels := by
    have ha : raw1890 = raw1891 := by apply Matrix.ext; unfold raw1890 raw1891; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4927 = raw1891Labels := by decide +kernel
    rw [ha, hj, canonical1891 B hB]
  have hc1 : mixedMoment B raw1890 (Fin.cases (1 : Fin 2) singletonSmall4927) =
      mixedMoment B node3399 node3399Labels := by
    have ha : raw1890 = raw1892 := by apply Matrix.ext; unfold raw1890 raw1892; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4927 = raw1892Labels := by decide +kernel
    rw [ha, hj, canonical1892 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4928 node4928Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2318 node2318Labels + mixedMoment B node3400 node3400Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1893 singletonSmall4928
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4928) = raw1893Labels := by decide +kernel
  rw [hl, canonical1893 B hB] at h
  have hc0 : mixedMoment B raw1893 (Fin.cases (0 : Fin 2) singletonSmall4928) =
      mixedMoment B node2318 node2318Labels := by
    have ha : raw1893 = raw1894 := by apply Matrix.ext; unfold raw1893 raw1894; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4928 = raw1894Labels := by decide +kernel
    rw [ha, hj, canonical1894 B hB]
  have hc1 : mixedMoment B raw1893 (Fin.cases (1 : Fin 2) singletonSmall4928) =
      mixedMoment B node3400 node3400Labels := by
    have ha : raw1893 = raw1895 := by apply Matrix.ext; unfold raw1893 raw1895; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4928 = raw1895Labels := by decide +kernel
    rw [ha, hj, canonical1895 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4941 node4941Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2332 node2332Labels + mixedMoment B node3410 node3410Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1905 singletonSmall4941
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4941) = raw1905Labels := by decide +kernel
  rw [hl, canonical1905 B hB] at h
  have hc0 : mixedMoment B raw1905 (Fin.cases (0 : Fin 2) singletonSmall4941) =
      mixedMoment B node2332 node2332Labels := by
    have ha : raw1905 = raw1906 := by apply Matrix.ext; unfold raw1905 raw1906; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4941 = raw1906Labels := by decide +kernel
    rw [ha, hj, canonical1906 B hB]
  have hc1 : mixedMoment B raw1905 (Fin.cases (1 : Fin 2) singletonSmall4941) =
      mixedMoment B node3410 node3410Labels := by
    have ha : raw1905 = raw1907 := by apply Matrix.ext; unfold raw1905 raw1907; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4941 = raw1907Labels := by decide +kernel
    rw [ha, hj, canonical1907 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4986 node4986Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2371 node2371Labels + mixedMoment B node3335 node3335Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1992 singletonSmall4986
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4986) = raw1992Labels := by decide +kernel
  rw [hl, canonical1992 B hB] at h
  have hc0 : mixedMoment B raw1992 (Fin.cases (0 : Fin 2) singletonSmall4986) =
      mixedMoment B node2371 node2371Labels := by
    have ha : raw1992 = raw1993 := by apply Matrix.ext; unfold raw1992 raw1993; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4986 = raw1993Labels := by decide +kernel
    rw [ha, hj, canonical1993 B hB]
  have hc1 : mixedMoment B raw1992 (Fin.cases (1 : Fin 2) singletonSmall4986) =
      mixedMoment B node3335 node3335Labels := by
    have ha : raw1992 = raw1994 := by apply Matrix.ext; unfold raw1992 raw1994; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4986 = raw1994Labels := by decide +kernel
    rw [ha, hj, canonical1994 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4987 node4987Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2372 node2372Labels + mixedMoment B node3336 node3336Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1995 singletonSmall4987
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4987) = raw1995Labels := by decide +kernel
  rw [hl, canonical1995 B hB] at h
  have hc0 : mixedMoment B raw1995 (Fin.cases (0 : Fin 2) singletonSmall4987) =
      mixedMoment B node2372 node2372Labels := by
    have ha : raw1995 = raw1996 := by apply Matrix.ext; unfold raw1995 raw1996; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4987 = raw1996Labels := by decide +kernel
    rw [ha, hj, canonical1996 B hB]
  have hc1 : mixedMoment B raw1995 (Fin.cases (1 : Fin 2) singletonSmall4987) =
      mixedMoment B node3336 node3336Labels := by
    have ha : raw1995 = raw1997 := by apply Matrix.ext; unfold raw1995 raw1997; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4987 = raw1997Labels := by decide +kernel
    rw [ha, hj, canonical1997 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem singleton5075 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5075 node5075Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2482 node2482Labels + mixedMoment B node3468 node3468Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2097 singletonSmall5075
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5075) = raw2097Labels := by decide +kernel
  rw [hl, canonical2097 B hB] at h
  have hc0 : mixedMoment B raw2097 (Fin.cases (0 : Fin 2) singletonSmall5075) =
      mixedMoment B node2482 node2482Labels := by
    have ha : raw2097 = raw2098 := by apply Matrix.ext; unfold raw2097 raw2098; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5075 = raw2098Labels := by decide +kernel
    rw [ha, hj, canonical2098 B hB]
  have hc1 : mixedMoment B raw2097 (Fin.cases (1 : Fin 2) singletonSmall5075) =
      mixedMoment B node3468 node3468Labels := by
    have ha : raw2097 = raw2099 := by apply Matrix.ext; unfold raw2097 raw2099; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5075 = raw2099Labels := by decide +kernel
    rw [ha, hj, canonical2099 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5134 node5134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2553 node2553Labels + mixedMoment B node3514 node3514Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2163 singletonSmall5134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5134) = raw2163Labels := by decide +kernel
  rw [hl, canonical2163 B hB] at h
  have hc0 : mixedMoment B raw2163 (Fin.cases (0 : Fin 2) singletonSmall5134) =
      mixedMoment B node2553 node2553Labels := by
    have ha : raw2163 = raw2164 := by apply Matrix.ext; unfold raw2163 raw2164; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5134 = raw2164Labels := by decide +kernel
    rw [ha, hj, canonical2164 B hB]
  have hc1 : mixedMoment B raw2163 (Fin.cases (1 : Fin 2) singletonSmall5134) =
      mixedMoment B node3514 node3514Labels := by
    have ha : raw2163 = raw2165 := by apply Matrix.ext; unfold raw2163 raw2165; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5134 = raw2165Labels := by decide +kernel
    rw [ha, hj, canonical2165 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
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

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem zero5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5460 node5460Labels = 0 := by
  exact mixedMoment_alpha B hF node5460 node5460Labels 2 permutation152
    (by decide +kernel)

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

theorem sound900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node900 node900Labels = Sparse.eval nodeValue900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 900) = mixedMoment B node900 node900Labels := rfl
  simpa [nodeValue900, Sparse.eval] using hc.symm

theorem sound901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node901 node901Labels = Sparse.eval nodeValue901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 901) = mixedMoment B node901 node901Labels := rfl
  simpa [nodeValue901, Sparse.eval] using hc.symm

theorem sound922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node922 node922Labels = Sparse.eval nodeValue922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 922) = mixedMoment B node922 node922Labels := rfl
  simpa [nodeValue922, Sparse.eval] using hc.symm

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

theorem sound980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node980 node980Labels = Sparse.eval nodeValue980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 980) = mixedMoment B node980 node980Labels := rfl
  simpa [nodeValue980, Sparse.eval] using hc.symm

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

theorem sound1588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1588 node1588Labels = Sparse.eval nodeValue1588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1588) = mixedMoment B node1588 node1588Labels := rfl
  simpa [nodeValue1588, Sparse.eval] using hc.symm

theorem sound1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1589 node1589Labels = Sparse.eval nodeValue1589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1589) = mixedMoment B node1589 node1589Labels := rfl
  simpa [nodeValue1589, Sparse.eval] using hc.symm

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

theorem sound1616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1616 node1616Labels = Sparse.eval nodeValue1616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1616) = mixedMoment B node1616 node1616Labels := rfl
  simpa [nodeValue1616, Sparse.eval] using hc.symm

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

theorem sound1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1673 node1673Labels = Sparse.eval nodeValue1673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1673) = mixedMoment B node1673 node1673Labels := rfl
  simpa [nodeValue1673, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2317 node2317Labels = Sparse.eval nodeValue2317 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2317) = mixedMoment B node2317 node2317Labels := rfl
  simpa [nodeValue2317, Sparse.eval] using hc.symm

theorem sound2318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2318 node2318Labels = Sparse.eval nodeValue2318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2318) = mixedMoment B node2318 node2318Labels := rfl
  simpa [nodeValue2318, Sparse.eval] using hc.symm

theorem sound2332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2332 node2332Labels = Sparse.eval nodeValue2332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2332) = mixedMoment B node2332 node2332Labels := rfl
  simpa [nodeValue2332, Sparse.eval] using hc.symm

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

theorem sound2371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2371 node2371Labels = Sparse.eval nodeValue2371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2371) = mixedMoment B node2371 node2371Labels := rfl
  simpa [nodeValue2371, Sparse.eval] using hc.symm

theorem sound2372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2372 node2372Labels = Sparse.eval nodeValue2372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2372) = mixedMoment B node2372 node2372Labels := rfl
  simpa [nodeValue2372, Sparse.eval] using hc.symm

theorem sound2383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2383 node2383Labels = Sparse.eval nodeValue2383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2383) = mixedMoment B node2383 node2383Labels := rfl
  simpa [nodeValue2383, Sparse.eval] using hc.symm

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

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

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

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

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

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

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

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

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

theorem sound3335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3335 node3335Labels = Sparse.eval nodeValue3335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3335) = mixedMoment B node3335 node3335Labels := rfl
  simpa [nodeValue3335, Sparse.eval] using hc.symm

theorem sound3336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3336 node3336Labels = Sparse.eval nodeValue3336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3336) = mixedMoment B node3336 node3336Labels := rfl
  simpa [nodeValue3336, Sparse.eval] using hc.symm

theorem sound3352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3352 node3352Labels = Sparse.eval nodeValue3352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3352) = mixedMoment B node3352 node3352Labels := rfl
  simpa [nodeValue3352, Sparse.eval] using hc.symm

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

theorem sound3399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3399 node3399Labels = Sparse.eval nodeValue3399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3399) = mixedMoment B node3399 node3399Labels := rfl
  simpa [nodeValue3399, Sparse.eval] using hc.symm

theorem sound3400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3400 node3400Labels = Sparse.eval nodeValue3400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3400) = mixedMoment B node3400 node3400Labels := rfl
  simpa [nodeValue3400, Sparse.eval] using hc.symm

theorem sound3410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3410 node3410Labels = Sparse.eval nodeValue3410 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3410) = mixedMoment B node3410 node3410Labels := rfl
  simpa [nodeValue3410, Sparse.eval] using hc.symm

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

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound4322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4322 node4322Labels = Sparse.eval nodeValue4322 (mixedVector B) := by
  have h := singleton4322 B _hB
  rw [sound900 B _hB _hF, sound1588 B _hB _hF] at h
  norm_num [nodeValue4322, nodeValue900, nodeValue1588, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4323 node4323Labels = Sparse.eval nodeValue4323 (mixedVector B) := by
  have h := singleton4323 B _hB
  rw [sound901 B _hB _hF, sound1589 B _hB _hF] at h
  norm_num [nodeValue4323, nodeValue901, nodeValue1589, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4344 node4344Labels = Sparse.eval nodeValue4344 (mixedVector B) := by
  have h := singleton4344 B _hB
  rw [sound922 B _hB _hF, sound1673 B _hB _hF] at h
  norm_num [nodeValue4344, nodeValue922, nodeValue1673, Sparse.eval] at h ⊢
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

theorem sound4399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4399 node4399Labels = Sparse.eval nodeValue4399 (mixedVector B) := by
  have h := singleton4399 B _hB
  rw [sound980 B _hB _hF, sound1616 B _hB _hF] at h
  norm_num [nodeValue4399, nodeValue980, nodeValue1616, Sparse.eval] at h ⊢
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

theorem sound4927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4927 node4927Labels = Sparse.eval nodeValue4927 (mixedVector B) := by
  have h := singleton4927 B _hB
  rw [sound2317 B _hB _hF, sound3399 B _hB _hF] at h
  norm_num [nodeValue4927, nodeValue2317, nodeValue3399, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4928 node4928Labels = Sparse.eval nodeValue4928 (mixedVector B) := by
  have h := singleton4928 B _hB
  rw [sound2318 B _hB _hF, sound3400 B _hB _hF] at h
  norm_num [nodeValue4928, nodeValue2318, nodeValue3400, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4941 node4941Labels = Sparse.eval nodeValue4941 (mixedVector B) := by
  have h := singleton4941 B _hB
  rw [sound2332 B _hB _hF, sound3410 B _hB _hF] at h
  norm_num [nodeValue4941, nodeValue2332, nodeValue3410, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4986 node4986Labels = Sparse.eval nodeValue4986 (mixedVector B) := by
  have h := singleton4986 B _hB
  rw [sound2371 B _hB _hF, sound3335 B _hB _hF] at h
  norm_num [nodeValue4986, nodeValue2371, nodeValue3335, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4987 node4987Labels = Sparse.eval nodeValue4987 (mixedVector B) := by
  have h := singleton4987 B _hB
  rw [sound2372 B _hB _hF, sound3336 B _hB _hF] at h
  norm_num [nodeValue4987, nodeValue2372, nodeValue3336, Sparse.eval] at h ⊢
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

theorem sound5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5075 node5075Labels = Sparse.eval nodeValue5075 (mixedVector B) := by
  have h := singleton5075 B _hB
  rw [sound2482 B _hB _hF, sound3468 B _hB _hF] at h
  norm_num [nodeValue5075, nodeValue2482, nodeValue3468, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
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

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
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

theorem sound5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5460 node5460Labels = Sparse.eval nodeValue5460 (mixedVector B) := by
  simpa only [nodeValue5460, Sparse.eval_nil] using zero5460 B _hB _hF

theorem sound5469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5469 node5469Labels = Sparse.eval nodeValue5469 (mixedVector B) := by
  have h := singleton5469 B _hB
  rw [sound3945 B _hB _hF, sound3952 B _hB _hF] at h
  norm_num [nodeValue5469, nodeValue3945, nodeValue3952, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources75
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2400 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 1) (sourceB2400 + difference 1 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 1) (sourceB2400 + difference 1 0) sourceC2400) = raw18783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18783; decide +kernel
    rw [ha]
    exact (canonical18783 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 2) (sourceB2400 + difference 2 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 2) (sourceB2400 + difference 2 0) sourceC2400) = raw18784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18784; decide +kernel
    rw [ha]
    exact (canonical18784 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 3) (sourceB2400 + difference 3 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 3) (sourceB2400 + difference 3 0) sourceC2400) = raw18785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18785; decide +kernel
    rw [ha]
    exact (canonical18785 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 4) (sourceB2400 + difference 4 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 4) (sourceB2400 + difference 4 0) sourceC2400) = raw18786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18786; decide +kernel
    rw [ha]
    exact (canonical18786 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2400 + difference 0 5) (sourceB2400 + difference 5 0) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2400 + difference 0 5) (sourceB2400 + difference 5 0) sourceC2400) = raw13775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13775; decide +kernel
    rw [ha]
    exact (canonical13775 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 0) (sourceB2400 + difference 0 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 0) (sourceB2400 + difference 0 1) sourceC2400) = raw13800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13800; decide +kernel
    rw [ha]
    exact (canonical13800 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 2) (sourceB2400 + difference 2 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 2) (sourceB2400 + difference 2 1) sourceC2400) = raw13802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13802; decide +kernel
    rw [ha]
    exact (canonical13802 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 3) (sourceB2400 + difference 3 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 3) (sourceB2400 + difference 3 1) sourceC2400) = raw13803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13803; decide +kernel
    rw [ha]
    exact (canonical13803 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 4) (sourceB2400 + difference 4 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 4) (sourceB2400 + difference 4 1) sourceC2400) = raw13804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13804; decide +kernel
    rw [ha]
    exact (canonical13804 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2400 + difference 1 5) (sourceB2400 + difference 5 1) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2400 + difference 1 5) (sourceB2400 + difference 5 1) sourceC2400) = raw18770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw18770; decide +kernel
    rw [ha]
    exact (canonical18770 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 0) (sourceB2400 + difference 0 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 0) (sourceB2400 + difference 0 2) sourceC2400) = raw32881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32881; decide +kernel
    rw [ha]
    exact (canonical32881 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 1) (sourceB2400 + difference 1 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 1) (sourceB2400 + difference 1 2) sourceC2400) = raw32882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32882; decide +kernel
    rw [ha]
    exact (canonical32882 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 3) (sourceB2400 + difference 3 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 3) (sourceB2400 + difference 3 2) sourceC2400) = raw32883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32883; decide +kernel
    rw [ha]
    exact (canonical32883 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 4) (sourceB2400 + difference 4 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 4) (sourceB2400 + difference 4 2) sourceC2400) = raw32884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32884; decide +kernel
    rw [ha]
    exact (canonical32884 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2400 + difference 2 5) (sourceB2400 + difference 5 2) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2400 + difference 2 5) (sourceB2400 + difference 5 2) sourceC2400) = raw13786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13786; decide +kernel
    rw [ha]
    exact (canonical13786 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 0) (sourceB2400 + difference 0 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 0) (sourceB2400 + difference 0 3) sourceC2400) = raw32885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32885; decide +kernel
    rw [ha]
    exact (canonical32885 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 1) (sourceB2400 + difference 1 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 1) (sourceB2400 + difference 1 3) sourceC2400) = raw32886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32886; decide +kernel
    rw [ha]
    exact (canonical32886 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 2) (sourceB2400 + difference 2 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 2) (sourceB2400 + difference 2 3) sourceC2400) = raw32887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32887; decide +kernel
    rw [ha]
    exact (canonical32887 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 4) (sourceB2400 + difference 4 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 4) (sourceB2400 + difference 4 3) sourceC2400) = raw32888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32888; decide +kernel
    rw [ha]
    exact (canonical32888 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2400 + difference 3 5) (sourceB2400 + difference 5 3) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2400 + difference 3 5) (sourceB2400 + difference 5 3) sourceC2400) = raw13791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13791; decide +kernel
    rw [ha]
    exact (canonical13791 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 0) (sourceB2400 + difference 0 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 0) (sourceB2400 + difference 0 4) sourceC2400) = raw32889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32889; decide +kernel
    rw [ha]
    exact (canonical32889 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 1) (sourceB2400 + difference 1 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 1) (sourceB2400 + difference 1 4) sourceC2400) = raw32890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32890; decide +kernel
    rw [ha]
    exact (canonical32890 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 2) (sourceB2400 + difference 2 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 2) (sourceB2400 + difference 2 4) sourceC2400) = raw32891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32891; decide +kernel
    rw [ha]
    exact (canonical32891 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 3) (sourceB2400 + difference 3 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 3) (sourceB2400 + difference 3 4) sourceC2400) = raw32892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32892; decide +kernel
    rw [ha]
    exact (canonical32892 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2400 + difference 4 5) (sourceB2400 + difference 5 4) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2400 + difference 4 5) (sourceB2400 + difference 5 4) sourceC2400) = raw13796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw13796; decide +kernel
    rw [ha]
    exact (canonical13796 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 0) (sourceB2400 + difference 0 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4322) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 0) (sourceB2400 + difference 0 5) sourceC2400) = raw32893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32893; decide +kernel
    rw [ha]
    exact (canonical32893 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 1) (sourceB2400 + difference 1 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 1) (sourceB2400 + difference 1 5) sourceC2400) = raw32894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32894; decide +kernel
    rw [ha]
    exact (canonical32894 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 2) (sourceB2400 + difference 2 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4986) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 2) (sourceB2400 + difference 2 5) sourceC2400) = raw32895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32895; decide +kernel
    rw [ha]
    exact (canonical32895 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 3) (sourceB2400 + difference 3 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 3) (sourceB2400 + difference 3 5) sourceC2400) = raw32896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32896; decide +kernel
    rw [ha]
    exact (canonical32896 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2400 + difference 5 4) (sourceB2400 + difference 4 5) sourceC2400) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2400 + difference 5 4) (sourceB2400 + difference 4 5) sourceC2400) = raw32897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2400 sourceB2400 sourceC2400 difference raw32897; decide +kernel
    rw [ha]
    exact (canonical32897 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2400 sourceB2400 sourceC2400
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2400, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1948 : Integer.Sparse.reindex keyMap MixedData.row1948 = numericRow1948 := by decide +kernel

theorem numericCheck1948 (x : Master → ℝ) : Integer.Sparse.eval numericRow1948 x =
    (17280 : ℝ) * reducedSource1948 x := by
  norm_num [numericRow1948, reducedSource1948, Integer.Sparse.eval, Sparse.eval, nodeValue4322, nodeValue4323, nodeValue4344, nodeValue4399, nodeValue4927, nodeValue4928, nodeValue4941, nodeValue4986, nodeValue4987, nodeValue4998, nodeValue5075, nodeValue5134, nodeValue5141, nodeValue5167, nodeValue5169, nodeValue5257, nodeValue5259, nodeValue5460, nodeValue5469, nodeValue5482, nodeValue5483]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1948 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1948 (mixedVector B) = 0 := by
  have h4322 : mixedVector B (Sum.inr 4322) = Sparse.eval nodeValue4322 (mixedVector B) := by
    change mixedMoment B node4322 node4322Labels = _
    exact sound4322 B hB hF
  have h4323 : mixedVector B (Sum.inr 4323) = Sparse.eval nodeValue4323 (mixedVector B) := by
    change mixedMoment B node4323 node4323Labels = _
    exact sound4323 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4927 : mixedVector B (Sum.inr 4927) = Sparse.eval nodeValue4927 (mixedVector B) := by
    change mixedMoment B node4927 node4927Labels = _
    exact sound4927 B hB hF
  have h4928 : mixedVector B (Sum.inr 4928) = Sparse.eval nodeValue4928 (mixedVector B) := by
    change mixedMoment B node4928 node4928Labels = _
    exact sound4928 B hB hF
  have h4941 : mixedVector B (Sum.inr 4941) = Sparse.eval nodeValue4941 (mixedVector B) := by
    change mixedMoment B node4941 node4941Labels = _
    exact sound4941 B hB hF
  have h4986 : mixedVector B (Sum.inr 4986) = Sparse.eval nodeValue4986 (mixedVector B) := by
    change mixedMoment B node4986 node4986Labels = _
    exact sound4986 B hB hF
  have h4987 : mixedVector B (Sum.inr 4987) = Sparse.eval nodeValue4987 (mixedVector B) := by
    change mixedMoment B node4987 node4987Labels = _
    exact sound4987 B hB hF
  have h4998 : mixedVector B (Sum.inr 4998) = Sparse.eval nodeValue4998 (mixedVector B) := by
    change mixedMoment B node4998 node4998Labels = _
    exact sound4998 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167_e B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169_e B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5460 : mixedVector B (Sum.inr 5460) = Sparse.eval nodeValue5460 (mixedVector B) := by
    change mixedMoment B node5460 node5460Labels = _
    exact sound5460 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  simpa only [sourceForm2400, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4322, h4323, h4344, h4399, h4927, h4928, h4941, h4986, h4987, h4998, h5075, h5134, h5141, h5167, h5169, h5257, h5259, h5460, h5469, h5482, h5483, reducedSource1948] using sourceEq2400 B hB

theorem rowSound1948_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1948 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1948, numericCheck1948, reducedZero1948 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e_oai
