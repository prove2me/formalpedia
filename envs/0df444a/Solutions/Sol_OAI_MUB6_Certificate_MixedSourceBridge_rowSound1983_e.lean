-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:32:37.04673+00:00
-- url     : https://prove2.me/submissions/e1caa210-dc99-4af4-bbda-84d2921411b2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5417_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e

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

theorem canonical1479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1479 raw1479Labels = mixedMoment B node4633 node4633Labels := by
  calc
    mixedMoment B raw1479 raw1479Labels = mixedMoment B raw1479step0 raw1479step0Labels := by
      have ha : raw1479step0 = (fun i j => raw1479 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1479step0 raw1479; decide +kernel
      have hl : raw1479step0Labels = raw1479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1479 raw1479Labels permutation152 permutation4
    mixedMoment B raw1479step0 raw1479step0Labels = mixedMoment B raw1479step1 raw1479step1Labels := by
      have ha : raw1479step1 = raw1479step0 := by apply Matrix.ext; unfold raw1479step1 raw1479step0; decide +kernel
      have hl : raw1479step0Labels = labelEmbedding7 ∘ raw1479step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1479step0 raw1479step0Labels raw1479step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4633 node4633Labels := by rfl

theorem canonical1480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1480 raw1480Labels = mixedMoment B node1762 node1762Labels := by
  calc
    mixedMoment B raw1480 raw1480Labels = mixedMoment B raw1480step0 raw1480step0Labels := by
      have ha : raw1480step0 = (fun i j => raw1480 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1480step0 raw1480; decide +kernel
      have hl : raw1480step0Labels = raw1480Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1480 raw1480Labels permutation152 permutation4
    _ = mixedMoment B node1762 node1762Labels := by rfl

theorem canonical1481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1481 raw1481Labels = mixedMoment B node1847 node1847Labels := by
  calc
    mixedMoment B raw1481 raw1481Labels = mixedMoment B raw1481step0 raw1481step0Labels := by
      have ha : raw1481step0 = (fun i j => raw1481 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1481step0 raw1481; decide +kernel
      have hl : raw1481step0Labels = raw1481Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1481 raw1481Labels permutation152 permutation6
    mixedMoment B raw1481step0 raw1481step0Labels = mixedMoment B raw1481step1 raw1481step1Labels := by
      have ha : raw1481step1 = -raw1481step0 := by apply Matrix.ext; change ∀ i j, raw1481step1 i j = -(raw1481step0 i j); unfold raw1481step1 raw1481step0; decide +kernel
      have hl : raw1481step1Labels = raw1481step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1481step1 raw1481step1Labels = mixedMoment B raw1481step2 raw1481step2Labels := by
      have ha : raw1481step2 = raw1481step1 := by apply Matrix.ext; unfold raw1481step2 raw1481step1; decide +kernel
      have hl : raw1481step1Labels = labelEmbedding1 ∘ raw1481step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1481step1 raw1481step1Labels raw1481step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1847 node1847Labels := by rfl

theorem canonical1482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1482 raw1482Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw1482 raw1482Labels = mixedMoment B raw1482step0 raw1482step0Labels := by
      have ha : raw1482step0 = (fun i j => raw1482 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1482step0 raw1482; decide +kernel
      have hl : raw1482step0Labels = raw1482Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1482 raw1482Labels permutation152 permutation4
    mixedMoment B raw1482step0 raw1482step0Labels = mixedMoment B raw1482step1 raw1482step1Labels := by
      have ha : raw1482step1 = raw1482step0 := by apply Matrix.ext; unfold raw1482step1 raw1482step0; decide +kernel
      have hl : raw1482step0Labels = labelEmbedding7 ∘ raw1482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1482step0 raw1482step0Labels raw1482step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

theorem canonical1483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1483 raw1483Labels = mixedMoment B node1763 node1763Labels := by
  calc
    mixedMoment B raw1483 raw1483Labels = mixedMoment B raw1483step0 raw1483step0Labels := by
      have ha : raw1483step0 = (fun i j => raw1483 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1483step0 raw1483; decide +kernel
      have hl : raw1483step0Labels = raw1483Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1483 raw1483Labels permutation152 permutation4
    _ = mixedMoment B node1763 node1763Labels := by rfl

theorem canonical1484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1484 raw1484Labels = mixedMoment B node1842 node1842Labels := by
  calc
    mixedMoment B raw1484 raw1484Labels = mixedMoment B raw1484step0 raw1484step0Labels := by
      have ha : raw1484step0 = (fun i j => raw1484 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1484step0 raw1484; decide +kernel
      have hl : raw1484step0Labels = raw1484Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1484 raw1484Labels permutation164 permutation6
    mixedMoment B raw1484step0 raw1484step0Labels = mixedMoment B raw1484step1 raw1484step1Labels := by
      have ha : raw1484step1 = -raw1484step0 := by apply Matrix.ext; change ∀ i j, raw1484step1 i j = -(raw1484step0 i j); unfold raw1484step1 raw1484step0; decide +kernel
      have hl : raw1484step1Labels = raw1484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1484step1 raw1484step1Labels = mixedMoment B raw1484step2 raw1484step2Labels := by
      have ha : raw1484step2 = raw1484step1 := by apply Matrix.ext; unfold raw1484step2 raw1484step1; decide +kernel
      have hl : raw1484step1Labels = labelEmbedding1 ∘ raw1484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1484step1 raw1484step1Labels raw1484step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1842 node1842Labels := by rfl

theorem canonical1512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1512 raw1512Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw1512 raw1512Labels = mixedMoment B raw1512step0 raw1512step0Labels := by
      have ha : raw1512step0 = (fun i j => raw1512 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1512step0 raw1512; decide +kernel
      have hl : raw1512step0Labels = raw1512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1512 raw1512Labels permutation152 permutation4
    mixedMoment B raw1512step0 raw1512step0Labels = mixedMoment B raw1512step1 raw1512step1Labels := by
      have ha : raw1512step1 = raw1512step0 := by apply Matrix.ext; unfold raw1512step1 raw1512step0; decide +kernel
      have hl : raw1512step0Labels = labelEmbedding7 ∘ raw1512step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1512step0 raw1512step0Labels raw1512step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

theorem canonical1513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1513 raw1513Labels = mixedMoment B node1776 node1776Labels := by
  calc
    mixedMoment B raw1513 raw1513Labels = mixedMoment B raw1513step0 raw1513step0Labels := by
      have ha : raw1513step0 = (fun i j => raw1513 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1513step0 raw1513; decide +kernel
      have hl : raw1513step0Labels = raw1513Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1513 raw1513Labels permutation152 permutation4
    _ = mixedMoment B node1776 node1776Labels := by rfl

theorem canonical1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1514 raw1514Labels = mixedMoment B node1844 node1844Labels := by
  calc
    mixedMoment B raw1514 raw1514Labels = mixedMoment B raw1514step0 raw1514step0Labels := by
      have ha : raw1514step0 = (fun i j => raw1514 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1514step0 raw1514; decide +kernel
      have hl : raw1514step0Labels = raw1514Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1514 raw1514Labels permutation170 permutation6
    mixedMoment B raw1514step0 raw1514step0Labels = mixedMoment B raw1514step1 raw1514step1Labels := by
      have ha : raw1514step1 = -raw1514step0 := by apply Matrix.ext; change ∀ i j, raw1514step1 i j = -(raw1514step0 i j); unfold raw1514step1 raw1514step0; decide +kernel
      have hl : raw1514step1Labels = raw1514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1514step1 raw1514step1Labels = mixedMoment B raw1514step2 raw1514step2Labels := by
      have ha : raw1514step2 = raw1514step1 := by apply Matrix.ext; unfold raw1514step2 raw1514step1; decide +kernel
      have hl : raw1514step1Labels = labelEmbedding1 ∘ raw1514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1514step1 raw1514step1Labels raw1514step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1844 node1844Labels := by rfl

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

theorem canonical1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1695 raw1695Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw1695 raw1695Labels = mixedMoment B raw1695step0 raw1695step0Labels := by
      have ha : raw1695step0 = (fun i j => raw1695 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1695step0 raw1695; decide +kernel
      have hl : raw1695step0Labels = raw1695Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1695 raw1695Labels permutation152 permutation4
    mixedMoment B raw1695step0 raw1695step0Labels = mixedMoment B raw1695step1 raw1695step1Labels := by
      have ha : raw1695step1 = raw1695step0 := by apply Matrix.ext; unfold raw1695step1 raw1695step0; decide +kernel
      have hl : raw1695step0Labels = labelEmbedding7 ∘ raw1695step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1695step0 raw1695step0Labels raw1695step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4764 node4764Labels := by rfl

theorem canonical1696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1696 raw1696Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw1696 raw1696Labels = mixedMoment B raw1696step0 raw1696step0Labels := by
      have ha : raw1696step0 = (fun i j => raw1696 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1696step0 raw1696; decide +kernel
      have hl : raw1696step0Labels = raw1696Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1696 raw1696Labels permutation152 permutation4
    _ = mixedMoment B node1964 node1964Labels := by rfl

theorem canonical1697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1697 raw1697Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw1697 raw1697Labels = mixedMoment B raw1697step0 raw1697step0Labels := by
      have ha : raw1697step0 = (fun i j => raw1697 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1697step0 raw1697; decide +kernel
      have hl : raw1697step0Labels = raw1697Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1697 raw1697Labels permutation152 permutation6
    mixedMoment B raw1697step0 raw1697step0Labels = mixedMoment B raw1697step1 raw1697step1Labels := by
      have ha : raw1697step1 = -raw1697step0 := by apply Matrix.ext; change ∀ i j, raw1697step1 i j = -(raw1697step0 i j); unfold raw1697step1 raw1697step0; decide +kernel
      have hl : raw1697step1Labels = raw1697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1697step1 raw1697step1Labels = mixedMoment B raw1697step2 raw1697step2Labels := by
      have ha : raw1697step2 = raw1697step1 := by apply Matrix.ext; unfold raw1697step2 raw1697step1; decide +kernel
      have hl : raw1697step1Labels = labelEmbedding1 ∘ raw1697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1697step1 raw1697step1Labels raw1697step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2182 node2182Labels := by rfl

theorem canonical1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1698 raw1698Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw1698 raw1698Labels = mixedMoment B raw1698step0 raw1698step0Labels := by
      have ha : raw1698step0 = (fun i j => raw1698 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1698step0 raw1698; decide +kernel
      have hl : raw1698step0Labels = raw1698Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1698 raw1698Labels permutation152 permutation4
    mixedMoment B raw1698step0 raw1698step0Labels = mixedMoment B raw1698step1 raw1698step1Labels := by
      have ha : raw1698step1 = raw1698step0 := by apply Matrix.ext; unfold raw1698step1 raw1698step0; decide +kernel
      have hl : raw1698step0Labels = labelEmbedding7 ∘ raw1698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1698step0 raw1698step0Labels raw1698step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

theorem canonical1699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1699 raw1699Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw1699 raw1699Labels = mixedMoment B raw1699step0 raw1699step0Labels := by
      have ha : raw1699step0 = (fun i j => raw1699 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1699step0 raw1699; decide +kernel
      have hl : raw1699step0Labels = raw1699Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1699 raw1699Labels permutation152 permutation4
    _ = mixedMoment B node1966 node1966Labels := by rfl

theorem canonical1700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1700 raw1700Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw1700 raw1700Labels = mixedMoment B raw1700step0 raw1700step0Labels := by
      have ha : raw1700step0 = (fun i j => raw1700 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1700step0 raw1700; decide +kernel
      have hl : raw1700step0Labels = raw1700Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1700 raw1700Labels permutation154 permutation6
    mixedMoment B raw1700step0 raw1700step0Labels = mixedMoment B raw1700step1 raw1700step1Labels := by
      have ha : raw1700step1 = -raw1700step0 := by apply Matrix.ext; change ∀ i j, raw1700step1 i j = -(raw1700step0 i j); unfold raw1700step1 raw1700step0; decide +kernel
      have hl : raw1700step1Labels = raw1700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1700step1 raw1700step1Labels = mixedMoment B raw1700step2 raw1700step2Labels := by
      have ha : raw1700step2 = raw1700step1 := by apply Matrix.ext; unfold raw1700step2 raw1700step1; decide +kernel
      have hl : raw1700step1Labels = labelEmbedding1 ∘ raw1700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1700step1 raw1700step1Labels raw1700step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

theorem canonical1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1725 raw1725Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw1725 raw1725Labels = mixedMoment B raw1725step0 raw1725step0Labels := by
      have ha : raw1725step0 = (fun i j => raw1725 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1725step0 raw1725; decide +kernel
      have hl : raw1725step0Labels = raw1725Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1725 raw1725Labels permutation152 permutation4
    mixedMoment B raw1725step0 raw1725step0Labels = mixedMoment B raw1725step1 raw1725step1Labels := by
      have ha : raw1725step1 = raw1725step0 := by apply Matrix.ext; unfold raw1725step1 raw1725step0; decide +kernel
      have hl : raw1725step0Labels = labelEmbedding7 ∘ raw1725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1725step0 raw1725step0Labels raw1725step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1726 raw1726Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw1726 raw1726Labels = mixedMoment B raw1726step0 raw1726step0Labels := by
      have ha : raw1726step0 = (fun i j => raw1726 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1726step0 raw1726; decide +kernel
      have hl : raw1726step0Labels = raw1726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1726 raw1726Labels permutation152 permutation4
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1727 raw1727Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw1727 raw1727Labels = mixedMoment B raw1727step0 raw1727step0Labels := by
      have ha : raw1727step0 = (fun i j => raw1727 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1727step0 raw1727; decide +kernel
      have hl : raw1727step0Labels = raw1727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1727 raw1727Labels permutation200 permutation6
    mixedMoment B raw1727step0 raw1727step0Labels = mixedMoment B raw1727step1 raw1727step1Labels := by
      have ha : raw1727step1 = -raw1727step0 := by apply Matrix.ext; change ∀ i j, raw1727step1 i j = -(raw1727step0 i j); unfold raw1727step1 raw1727step0; decide +kernel
      have hl : raw1727step1Labels = raw1727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1727step1 raw1727step1Labels = mixedMoment B raw1727step2 raw1727step2Labels := by
      have ha : raw1727step2 = raw1727step1 := by apply Matrix.ext; unfold raw1727step2 raw1727step1; decide +kernel
      have hl : raw1727step1Labels = labelEmbedding1 ∘ raw1727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1727step1 raw1727step1Labels raw1727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2075 node2075Labels := by rfl

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

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1746 raw1746Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw1746 raw1746Labels = mixedMoment B raw1746step0 raw1746step0Labels := by
      have ha : raw1746step0 = (fun i j => raw1746 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1746step0 raw1746; decide +kernel
      have hl : raw1746step0Labels = raw1746Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1746 raw1746Labels permutation32 permutation4
    mixedMoment B raw1746step0 raw1746step0Labels = mixedMoment B raw1746step1 raw1746step1Labels := by
      have ha : raw1746step1 = raw1746step0 := by apply Matrix.ext; unfold raw1746step1 raw1746step0; decide +kernel
      have hl : raw1746step0Labels = labelEmbedding7 ∘ raw1746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1746step0 raw1746step0Labels raw1746step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1747 raw1747Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw1747 raw1747Labels = mixedMoment B raw1747step0 raw1747step0Labels := by
      have ha : raw1747step0 = (fun i j => raw1747 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1747step0 raw1747; decide +kernel
      have hl : raw1747step0Labels = raw1747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1747 raw1747Labels permutation32 permutation4
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1748 raw1748Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw1748 raw1748Labels = mixedMoment B raw1748step0 raw1748step0Labels := by
      have ha : raw1748step0 = (fun i j => raw1748 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1748step0 raw1748; decide +kernel
      have hl : raw1748step0Labels = raw1748Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1748 raw1748Labels permutation34 permutation6
    mixedMoment B raw1748step0 raw1748step0Labels = mixedMoment B raw1748step1 raw1748step1Labels := by
      have ha : raw1748step1 = -raw1748step0 := by apply Matrix.ext; change ∀ i j, raw1748step1 i j = -(raw1748step0 i j); unfold raw1748step1 raw1748step0; decide +kernel
      have hl : raw1748step1Labels = raw1748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1748step1 raw1748step1Labels = mixedMoment B raw1748step2 raw1748step2Labels := by
      have ha : raw1748step2 = raw1748step1 := by apply Matrix.ext; unfold raw1748step2 raw1748step1; decide +kernel
      have hl : raw1748step1Labels = labelEmbedding1 ∘ raw1748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1748step1 raw1748step1Labels raw1748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1752 raw1752Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw1752 raw1752Labels = mixedMoment B raw1752step0 raw1752step0Labels := by
      have ha : raw1752step0 = (fun i j => raw1752 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1752step0 raw1752; decide +kernel
      have hl : raw1752step0Labels = raw1752Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1752 raw1752Labels permutation152 permutation4
    mixedMoment B raw1752step0 raw1752step0Labels = mixedMoment B raw1752step1 raw1752step1Labels := by
      have ha : raw1752step1 = raw1752step0 := by apply Matrix.ext; unfold raw1752step1 raw1752step0; decide +kernel
      have hl : raw1752step0Labels = labelEmbedding7 ∘ raw1752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1752step0 raw1752step0Labels raw1752step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1753 raw1753Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw1753 raw1753Labels = mixedMoment B raw1753step0 raw1753step0Labels := by
      have ha : raw1753step0 = (fun i j => raw1753 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1753step0 raw1753; decide +kernel
      have hl : raw1753step0Labels = raw1753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1753 raw1753Labels permutation152 permutation4
    _ = mixedMoment B node2046 node2046Labels := by rfl

theorem canonical1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1754 raw1754Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw1754 raw1754Labels = mixedMoment B raw1754step0 raw1754step0Labels := by
      have ha : raw1754step0 = (fun i j => raw1754 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1754step0 raw1754; decide +kernel
      have hl : raw1754step0Labels = raw1754Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1754 raw1754Labels permutation176 permutation6
    mixedMoment B raw1754step0 raw1754step0Labels = mixedMoment B raw1754step1 raw1754step1Labels := by
      have ha : raw1754step1 = -raw1754step0 := by apply Matrix.ext; change ∀ i j, raw1754step1 i j = -(raw1754step0 i j); unfold raw1754step1 raw1754step0; decide +kernel
      have hl : raw1754step1Labels = raw1754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1754step1 raw1754step1Labels = mixedMoment B raw1754step2 raw1754step2Labels := by
      have ha : raw1754step2 = raw1754step1 := by apply Matrix.ext; unfold raw1754step2 raw1754step1; decide +kernel
      have hl : raw1754step1Labels = labelEmbedding1 ∘ raw1754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1754step1 raw1754step1Labels raw1754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2077 node2077Labels := by rfl

theorem canonical1770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1770 raw1770Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw1770 raw1770Labels = mixedMoment B raw1770step0 raw1770step0Labels := by
      have ha : raw1770step0 = (fun i j => raw1770 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1770step0 raw1770; decide +kernel
      have hl : raw1770step0Labels = raw1770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1770 raw1770Labels permutation32 permutation4
    mixedMoment B raw1770step0 raw1770step0Labels = mixedMoment B raw1770step1 raw1770step1Labels := by
      have ha : raw1770step1 = raw1770step0 := by apply Matrix.ext; unfold raw1770step1 raw1770step0; decide +kernel
      have hl : raw1770step0Labels = labelEmbedding7 ∘ raw1770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1770step0 raw1770step0Labels raw1770step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1771 raw1771Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw1771 raw1771Labels = mixedMoment B raw1771step0 raw1771step0Labels := by
      have ha : raw1771step0 = (fun i j => raw1771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1771step0 raw1771; decide +kernel
      have hl : raw1771step0Labels = raw1771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1771 raw1771Labels permutation32 permutation4
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical1772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1772 raw1772Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw1772 raw1772Labels = mixedMoment B raw1772step0 raw1772step0Labels := by
      have ha : raw1772step0 = (fun i j => raw1772 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1772step0 raw1772; decide +kernel
      have hl : raw1772step0Labels = raw1772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1772 raw1772Labels permutation36 permutation6
    mixedMoment B raw1772step0 raw1772step0Labels = mixedMoment B raw1772step1 raw1772step1Labels := by
      have ha : raw1772step1 = -raw1772step0 := by apply Matrix.ext; change ∀ i j, raw1772step1 i j = -(raw1772step0 i j); unfold raw1772step1 raw1772step0; decide +kernel
      have hl : raw1772step1Labels = raw1772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1772step1 raw1772step1Labels = mixedMoment B raw1772step2 raw1772step2Labels := by
      have ha : raw1772step2 = raw1772step1 := by apply Matrix.ext; unfold raw1772step2 raw1772step1; decide +kernel
      have hl : raw1772step1Labels = labelEmbedding1 ∘ raw1772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1772step1 raw1772step1Labels raw1772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical1788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1788 raw1788Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw1788 raw1788Labels = mixedMoment B raw1788step0 raw1788step0Labels := by
      have ha : raw1788step0 = (fun i j => raw1788 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1788step0 raw1788; decide +kernel
      have hl : raw1788step0Labels = raw1788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1788 raw1788Labels permutation152 permutation4
    mixedMoment B raw1788step0 raw1788step0Labels = mixedMoment B raw1788step1 raw1788step1Labels := by
      have ha : raw1788step1 = raw1788step0 := by apply Matrix.ext; unfold raw1788step1 raw1788step0; decide +kernel
      have hl : raw1788step0Labels = labelEmbedding7 ∘ raw1788step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1788step0 raw1788step0Labels raw1788step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical1789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1789 raw1789Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw1789 raw1789Labels = mixedMoment B raw1789step0 raw1789step0Labels := by
      have ha : raw1789step0 = (fun i j => raw1789 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1789step0 raw1789; decide +kernel
      have hl : raw1789step0Labels = raw1789Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1789 raw1789Labels permutation152 permutation4
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical1790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1790 raw1790Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw1790 raw1790Labels = mixedMoment B raw1790step0 raw1790step0Labels := by
      have ha : raw1790step0 = (fun i j => raw1790 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1790step0 raw1790; decide +kernel
      have hl : raw1790step0Labels = raw1790Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1790 raw1790Labels permutation182 permutation6
    mixedMoment B raw1790step0 raw1790step0Labels = mixedMoment B raw1790step1 raw1790step1Labels := by
      have ha : raw1790step1 = -raw1790step0 := by apply Matrix.ext; change ∀ i j, raw1790step1 i j = -(raw1790step0 i j); unfold raw1790step1 raw1790step0; decide +kernel
      have hl : raw1790step1Labels = raw1790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1790step1 raw1790step1Labels = mixedMoment B raw1790step2 raw1790step2Labels := by
      have ha : raw1790step2 = raw1790step1 := by apply Matrix.ext; unfold raw1790step2 raw1790step1; decide +kernel
      have hl : raw1790step1Labels = labelEmbedding1 ∘ raw1790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1790step1 raw1790step1Labels raw1790step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

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

theorem canonical2397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2397 raw2397Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw2397 raw2397Labels = mixedMoment B raw2397step0 raw2397step0Labels := by
      have ha : raw2397step0 = (fun i j => raw2397 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2397step0 raw2397; decide +kernel
      have hl : raw2397step0Labels = raw2397Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2397 raw2397Labels permutation152 permutation4
    mixedMoment B raw2397step0 raw2397step0Labels = mixedMoment B raw2397step1 raw2397step1Labels := by
      have ha : raw2397step1 = raw2397step0 := by apply Matrix.ext; unfold raw2397step1 raw2397step0; decide +kernel
      have hl : raw2397step0Labels = labelEmbedding7 ∘ raw2397step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2397step0 raw2397step0Labels raw2397step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical2398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2398 raw2398Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw2398 raw2398Labels = mixedMoment B raw2398step0 raw2398step0Labels := by
      have ha : raw2398step0 = (fun i j => raw2398 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2398step0 raw2398; decide +kernel
      have hl : raw2398step0Labels = raw2398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2398 raw2398Labels permutation152 permutation4
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2399 raw2399Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw2399 raw2399Labels = mixedMoment B raw2399step0 raw2399step0Labels := by
      have ha : raw2399step0 = (fun i j => raw2399 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2399step0 raw2399; decide +kernel
      have hl : raw2399step0Labels = raw2399Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2399 raw2399Labels permutation170 permutation6
    mixedMoment B raw2399step0 raw2399step0Labels = mixedMoment B raw2399step1 raw2399step1Labels := by
      have ha : raw2399step1 = -raw2399step0 := by apply Matrix.ext; change ∀ i j, raw2399step1 i j = -(raw2399step0 i j); unfold raw2399step1 raw2399step0; decide +kernel
      have hl : raw2399step1Labels = raw2399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2399step1 raw2399step1Labels = mixedMoment B raw2399step2 raw2399step2Labels := by
      have ha : raw2399step2 = raw2399step1 := by apply Matrix.ext; unfold raw2399step2 raw2399step1; decide +kernel
      have hl : raw2399step1Labels = labelEmbedding1 ∘ raw2399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2399step1 raw2399step1Labels raw2399step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

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

theorem canonical2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2520 raw2520Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw2520 raw2520Labels = mixedMoment B raw2520step0 raw2520step0Labels := by
      have ha : raw2520step0 = (fun i j => raw2520 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2520step0 raw2520; decide +kernel
      have hl : raw2520step0Labels = raw2520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2520 raw2520Labels permutation152 permutation4
    mixedMoment B raw2520step0 raw2520step0Labels = mixedMoment B raw2520step1 raw2520step1Labels := by
      have ha : raw2520step1 = raw2520step0 := by apply Matrix.ext; unfold raw2520step1 raw2520step0; decide +kernel
      have hl : raw2520step0Labels = labelEmbedding7 ∘ raw2520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2520step0 raw2520step0Labels raw2520step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2521 raw2521Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw2521 raw2521Labels = mixedMoment B raw2521step0 raw2521step0Labels := by
      have ha : raw2521step0 = (fun i j => raw2521 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2521step0 raw2521; decide +kernel
      have hl : raw2521step0Labels = raw2521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2521 raw2521Labels permutation152 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2522 raw2522Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw2522 raw2522Labels = mixedMoment B raw2522step0 raw2522step0Labels := by
      have ha : raw2522step0 = (fun i j => raw2522 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2522step0 raw2522; decide +kernel
      have hl : raw2522step0Labels = raw2522Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2522 raw2522Labels permutation200 permutation6
    mixedMoment B raw2522step0 raw2522step0Labels = mixedMoment B raw2522step1 raw2522step1Labels := by
      have ha : raw2522step1 = -raw2522step0 := by apply Matrix.ext; change ∀ i j, raw2522step1 i j = -(raw2522step0 i j); unfold raw2522step1 raw2522step0; decide +kernel
      have hl : raw2522step1Labels = raw2522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2522step1 raw2522step1Labels = mixedMoment B raw2522step2 raw2522step2Labels := by
      have ha : raw2522step2 = raw2522step1 := by apply Matrix.ext; unfold raw2522step2 raw2522step1; decide +kernel
      have hl : raw2522step1Labels = labelEmbedding1 ∘ raw2522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2522step1 raw2522step1Labels raw2522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31384 raw31384Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw31384 raw31384Labels = mixedMoment B raw31384step0 raw31384step0Labels := by
      have hz : ∀ j, raw31384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31384step0 = (fun i j => raw31384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31384step0 raw31384; decide +kernel
      have hl : raw31384step0Labels = raw31384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31384 raw31384Labels permutation434 hz
    mixedMoment B raw31384step0 raw31384step0Labels = mixedMoment B raw31384step1 raw31384step1Labels := by
      have ha : raw31384step1 = (fun i j => raw31384step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31384step1 raw31384step0; decide +kernel
      have hl : raw31384step1Labels = raw31384step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31384step0 raw31384step0Labels permutation32 permutation3
    mixedMoment B raw31384step1 raw31384step1Labels = mixedMoment B raw31384step2 raw31384step2Labels := by
      have ha : raw31384step2 = raw31384step1 := by apply Matrix.ext; unfold raw31384step2 raw31384step1; decide +kernel
      have hl : raw31384step1Labels = labelEmbedding6 ∘ raw31384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31384step1 raw31384step1Labels raw31384step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical31389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31389 raw31389Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw31389 raw31389Labels = mixedMoment B raw31389step0 raw31389step0Labels := by
      have ha : raw31389step0 = (fun i j => raw31389 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31389step0 raw31389; decide +kernel
      have hl : raw31389step0Labels = raw31389Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31389 raw31389Labels permutation153 permutation3
    mixedMoment B raw31389step0 raw31389step0Labels = mixedMoment B raw31389step1 raw31389step1Labels := by
      have ha : raw31389step1 = raw31389step0 := by apply Matrix.ext; unfold raw31389step1 raw31389step0; decide +kernel
      have hl : raw31389step0Labels = labelEmbedding6 ∘ raw31389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31389step0 raw31389step0Labels raw31389step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4200 node4200Labels := by rfl

theorem canonical31390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31390 raw31390Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw31390 raw31390Labels = mixedMoment B raw31390step0 raw31390step0Labels := by
      have ha : raw31390step0 = (fun i j => raw31390 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31390step0 raw31390; decide +kernel
      have hl : raw31390step0Labels = raw31390Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31390 raw31390Labels permutation153 permutation3
    mixedMoment B raw31390step0 raw31390step0Labels = mixedMoment B raw31390step1 raw31390step1Labels := by
      have ha : raw31390step1 = raw31390step0 := by apply Matrix.ext; unfold raw31390step1 raw31390step0; decide +kernel
      have hl : raw31390step0Labels = labelEmbedding6 ∘ raw31390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31390step0 raw31390step0Labels raw31390step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

theorem canonical31391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31391 raw31391Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw31391 raw31391Labels = mixedMoment B raw31391step0 raw31391step0Labels := by
      have ha : raw31391step0 = (fun i j => raw31391 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31391step0 raw31391; decide +kernel
      have hl : raw31391step0Labels = raw31391Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31391 raw31391Labels permutation153 permutation3
    mixedMoment B raw31391step0 raw31391step0Labels = mixedMoment B raw31391step1 raw31391step1Labels := by
      have ha : raw31391step1 = raw31391step0 := by apply Matrix.ext; unfold raw31391step1 raw31391step0; decide +kernel
      have hl : raw31391step0Labels = labelEmbedding6 ∘ raw31391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31391step0 raw31391step0Labels raw31391step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

theorem canonical31392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31392 raw31392Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw31392 raw31392Labels = mixedMoment B raw31392step0 raw31392step0Labels := by
      have ha : raw31392step0 = (fun i j => raw31392 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31392step0 raw31392; decide +kernel
      have hl : raw31392step0Labels = raw31392Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31392 raw31392Labels permutation156 permutation3
    mixedMoment B raw31392step0 raw31392step0Labels = mixedMoment B raw31392step1 raw31392step1Labels := by
      have ha : raw31392step1 = raw31392step0 := by apply Matrix.ext; unfold raw31392step1 raw31392step0; decide +kernel
      have hl : raw31392step0Labels = labelEmbedding6 ∘ raw31392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31392step0 raw31392step0Labels raw31392step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical264
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33845 raw33845Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw33845 raw33845Labels = mixedMoment B raw33845step0 raw33845step0Labels := by
      have ha : raw33845step0 = (fun i j => raw33845 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33845step0 raw33845; decide +kernel
      have hl : raw33845step0Labels = raw33845Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33845 raw33845Labels permutation152 permutation3
    mixedMoment B raw33845step0 raw33845step0Labels = mixedMoment B raw33845step1 raw33845step1Labels := by
      have ha : raw33845step1 = raw33845step0 := by apply Matrix.ext; unfold raw33845step1 raw33845step0; decide +kernel
      have hl : raw33845step0Labels = labelEmbedding6 ∘ raw33845step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33845step0 raw33845step0Labels raw33845step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical33846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33846 raw33846Labels = mixedMoment B node5417 node5417Labels := by
  calc
    mixedMoment B raw33846 raw33846Labels = mixedMoment B raw33846step0 raw33846step0Labels := by
      have ha : raw33846step0 = (fun i j => raw33846 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33846step0 raw33846; decide +kernel
      have hl : raw33846step0Labels = raw33846Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33846 raw33846Labels permutation662 permutation2
    mixedMoment B raw33846step0 raw33846step0Labels = mixedMoment B raw33846step1 raw33846step1Labels := by
      have ha : raw33846step1 = -raw33846step0 := by apply Matrix.ext; change ∀ i j, raw33846step1 i j = -(raw33846step0 i j); unfold raw33846step1 raw33846step0; decide +kernel
      have hl : raw33846step1Labels = raw33846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5417 node5417Labels := by rfl

theorem canonical33847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33847 raw33847Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw33847 raw33847Labels = mixedMoment B raw33847step0 raw33847step0Labels := by
      have hz : ∀ j, raw33847 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33847step0 = (fun i j => raw33847 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33847step0 raw33847; decide +kernel
      have hl : raw33847step0Labels = raw33847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33847 raw33847Labels permutation520 hz
    mixedMoment B raw33847step0 raw33847step0Labels = mixedMoment B raw33847step1 raw33847step1Labels := by
      have ha : raw33847step1 = (fun i j => raw33847step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33847step1 raw33847step0; decide +kernel
      have hl : raw33847step1Labels = raw33847step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33847step0 raw33847step0Labels permutation151 permutation2
    mixedMoment B raw33847step1 raw33847step1Labels = mixedMoment B raw33847step2 raw33847step2Labels := by
      have ha : raw33847step2 = -raw33847step1 := by apply Matrix.ext; change ∀ i j, raw33847step2 i j = -(raw33847step1 i j); unfold raw33847step2 raw33847step1; decide +kernel
      have hl : raw33847step2Labels = raw33847step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical33848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33848 raw33848Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw33848 raw33848Labels = mixedMoment B raw33848step0 raw33848step0Labels := by
      have ha : raw33848step0 = (fun i j => raw33848 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33848step0 raw33848; decide +kernel
      have hl : raw33848step0Labels = raw33848Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33848 raw33848Labels permutation156 permutation3
    mixedMoment B raw33848step0 raw33848step0Labels = mixedMoment B raw33848step1 raw33848step1Labels := by
      have ha : raw33848step1 = raw33848step0 := by apply Matrix.ext; unfold raw33848step1 raw33848step0; decide +kernel
      have hl : raw33848step0Labels = labelEmbedding6 ∘ raw33848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33848step0 raw33848step0Labels raw33848step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical33849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33849 raw33849Labels = mixedMoment B node4217 node4217Labels := by
  calc
    mixedMoment B raw33849 raw33849Labels = mixedMoment B raw33849step0 raw33849step0Labels := by
      have ha : raw33849step0 = (fun i j => raw33849 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33849step0 raw33849; decide +kernel
      have hl : raw33849step0Labels = raw33849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33849 raw33849Labels permutation160 permutation3
    mixedMoment B raw33849step0 raw33849step0Labels = mixedMoment B raw33849step1 raw33849step1Labels := by
      have ha : raw33849step1 = raw33849step0 := by apply Matrix.ext; unfold raw33849step1 raw33849step0; decide +kernel
      have hl : raw33849step0Labels = labelEmbedding6 ∘ raw33849step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33849step0 raw33849step0Labels raw33849step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4217 node4217Labels := by rfl

theorem canonical33850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33850 raw33850Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw33850 raw33850Labels = mixedMoment B raw33850step0 raw33850step0Labels := by
      have ha : raw33850step0 = (fun i j => raw33850 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33850step0 raw33850; decide +kernel
      have hl : raw33850step0Labels = raw33850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33850 raw33850Labels permutation160 permutation3
    mixedMoment B raw33850step0 raw33850step0Labels = mixedMoment B raw33850step1 raw33850step1Labels := by
      have ha : raw33850step1 = raw33850step0 := by apply Matrix.ext; unfold raw33850step1 raw33850step0; decide +kernel
      have hl : raw33850step0Labels = labelEmbedding6 ∘ raw33850step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33850step0 raw33850step0Labels raw33850step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

theorem canonical33851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33851 raw33851Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw33851 raw33851Labels = mixedMoment B raw33851step0 raw33851step0Labels := by
      have hz : ∀ j, raw33851 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33851step0 = (fun i j => raw33851 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33851step0 raw33851; decide +kernel
      have hl : raw33851step0Labels = raw33851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33851 raw33851Labels permutation520 hz
    mixedMoment B raw33851step0 raw33851step0Labels = mixedMoment B raw33851step1 raw33851step1Labels := by
      have ha : raw33851step1 = (fun i j => raw33851step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33851step1 raw33851step0; decide +kernel
      have hl : raw33851step1Labels = raw33851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33851step0 raw33851step0Labels permutation34 permutation3
    mixedMoment B raw33851step1 raw33851step1Labels = mixedMoment B raw33851step2 raw33851step2Labels := by
      have ha : raw33851step2 = raw33851step1 := by apply Matrix.ext; unfold raw33851step2 raw33851step1; decide +kernel
      have hl : raw33851step1Labels = labelEmbedding6 ∘ raw33851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33851step1 raw33851step1Labels raw33851step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical33852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33852 raw33852Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw33852 raw33852Labels = mixedMoment B raw33852step0 raw33852step0Labels := by
      have ha : raw33852step0 = (fun i j => raw33852 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33852step0 raw33852; decide +kernel
      have hl : raw33852step0Labels = raw33852Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33852 raw33852Labels permutation173 permutation3
    mixedMoment B raw33852step0 raw33852step0Labels = mixedMoment B raw33852step1 raw33852step1Labels := by
      have ha : raw33852step1 = raw33852step0 := by apply Matrix.ext; unfold raw33852step1 raw33852step0; decide +kernel
      have hl : raw33852step0Labels = labelEmbedding6 ∘ raw33852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33852step0 raw33852step0Labels raw33852step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical33853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33853 raw33853Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw33853 raw33853Labels = mixedMoment B raw33853step0 raw33853step0Labels := by
      have ha : raw33853step0 = (fun i j => raw33853 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33853step0 raw33853; decide +kernel
      have hl : raw33853step0Labels = raw33853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33853 raw33853Labels permutation155 permutation3
    mixedMoment B raw33853step0 raw33853step0Labels = mixedMoment B raw33853step1 raw33853step1Labels := by
      have ha : raw33853step1 = raw33853step0 := by apply Matrix.ext; unfold raw33853step1 raw33853step0; decide +kernel
      have hl : raw33853step0Labels = labelEmbedding6 ∘ raw33853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33853step0 raw33853step0Labels raw33853step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4200 node4200Labels := by rfl

theorem canonical33854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33854 raw33854Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw33854 raw33854Labels = mixedMoment B raw33854step0 raw33854step0Labels := by
      have ha : raw33854step0 = (fun i j => raw33854 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33854step0 raw33854; decide +kernel
      have hl : raw33854step0Labels = raw33854Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33854 raw33854Labels permutation155 permutation3
    mixedMoment B raw33854step0 raw33854step0Labels = mixedMoment B raw33854step1 raw33854step1Labels := by
      have ha : raw33854step1 = raw33854step0 := by apply Matrix.ext; unfold raw33854step1 raw33854step0; decide +kernel
      have hl : raw33854step0Labels = labelEmbedding6 ∘ raw33854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33854step0 raw33854step0Labels raw33854step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

theorem canonical33855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33855 raw33855Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw33855 raw33855Labels = mixedMoment B raw33855step0 raw33855step0Labels := by
      have ha : raw33855step0 = (fun i j => raw33855 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33855step0 raw33855; decide +kernel
      have hl : raw33855step0Labels = raw33855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33855 raw33855Labels permutation155 permutation3
    mixedMoment B raw33855step0 raw33855step0Labels = mixedMoment B raw33855step1 raw33855step1Labels := by
      have ha : raw33855step1 = raw33855step0 := by apply Matrix.ext; unfold raw33855step1 raw33855step0; decide +kernel
      have hl : raw33855step0Labels = labelEmbedding6 ∘ raw33855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33855step0 raw33855step0Labels raw33855step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

theorem canonical33856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33856 raw33856Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw33856 raw33856Labels = mixedMoment B raw33856step0 raw33856step0Labels := by
      have hz : ∀ j, raw33856 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33856step0 = (fun i j => raw33856 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33856step0 raw33856; decide +kernel
      have hl : raw33856step0Labels = raw33856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33856 raw33856Labels permutation520 hz
    mixedMoment B raw33856step0 raw33856step0Labels = mixedMoment B raw33856step1 raw33856step1Labels := by
      have ha : raw33856step1 = (fun i j => raw33856step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33856step1 raw33856step0; decide +kernel
      have hl : raw33856step1Labels = raw33856step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33856step0 raw33856step0Labels permutation33 permutation3
    mixedMoment B raw33856step1 raw33856step1Labels = mixedMoment B raw33856step2 raw33856step2Labels := by
      have ha : raw33856step2 = raw33856step1 := by apply Matrix.ext; unfold raw33856step2 raw33856step1; decide +kernel
      have hl : raw33856step1Labels = labelEmbedding6 ∘ raw33856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33856step1 raw33856step1Labels raw33856step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical33857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33857 raw33857Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw33857 raw33857Labels = mixedMoment B raw33857step0 raw33857step0Labels := by
      have ha : raw33857step0 = (fun i j => raw33857 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33857step0 raw33857; decide +kernel
      have hl : raw33857step0Labels = raw33857Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33857 raw33857Labels permutation157 permutation3
    mixedMoment B raw33857step0 raw33857step0Labels = mixedMoment B raw33857step1 raw33857step1Labels := by
      have ha : raw33857step1 = raw33857step0 := by apply Matrix.ext; unfold raw33857step1 raw33857step0; decide +kernel
      have hl : raw33857step0Labels = labelEmbedding6 ∘ raw33857step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33857step0 raw33857step0Labels raw33857step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical33858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33858 raw33858Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw33858 raw33858Labels = mixedMoment B raw33858step0 raw33858step0Labels := by
      have ha : raw33858step0 = (fun i j => raw33858 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33858step0 raw33858; decide +kernel
      have hl : raw33858step0Labels = raw33858Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33858 raw33858Labels permutation152 permutation3
    mixedMoment B raw33858step0 raw33858step0Labels = mixedMoment B raw33858step1 raw33858step1Labels := by
      have ha : raw33858step1 = raw33858step0 := by apply Matrix.ext; unfold raw33858step1 raw33858step0; decide +kernel
      have hl : raw33858step0Labels = labelEmbedding6 ∘ raw33858step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33858step0 raw33858step0Labels raw33858step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4199 node4199Labels := by rfl

theorem canonical33859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33859 raw33859Labels = mixedMoment B node4633 node4633Labels := by
  calc
    mixedMoment B raw33859 raw33859Labels = mixedMoment B raw33859step0 raw33859step0Labels := by
      have ha : raw33859step0 = (fun i j => raw33859 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33859step0 raw33859; decide +kernel
      have hl : raw33859step0Labels = raw33859Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33859 raw33859Labels permutation152 permutation3
    mixedMoment B raw33859step0 raw33859step0Labels = mixedMoment B raw33859step1 raw33859step1Labels := by
      have ha : raw33859step1 = raw33859step0 := by apply Matrix.ext; unfold raw33859step1 raw33859step0; decide +kernel
      have hl : raw33859step0Labels = labelEmbedding6 ∘ raw33859step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33859step0 raw33859step0Labels raw33859step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4633 node4633Labels := by rfl

theorem canonical33860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33860 raw33860Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw33860 raw33860Labels = mixedMoment B raw33860step0 raw33860step0Labels := by
      have ha : raw33860step0 = (fun i j => raw33860 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33860step0 raw33860; decide +kernel
      have hl : raw33860step0Labels = raw33860Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33860 raw33860Labels permutation152 permutation3
    mixedMoment B raw33860step0 raw33860step0Labels = mixedMoment B raw33860step1 raw33860step1Labels := by
      have ha : raw33860step1 = raw33860step0 := by apply Matrix.ext; unfold raw33860step1 raw33860step0; decide +kernel
      have hl : raw33860step0Labels = labelEmbedding6 ∘ raw33860step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33860step0 raw33860step0Labels raw33860step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4764 node4764Labels := by rfl

theorem canonical33861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33861 raw33861Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw33861 raw33861Labels = mixedMoment B raw33861step0 raw33861step0Labels := by
      have hz : ∀ j, raw33861 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33861step0 = (fun i j => raw33861 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33861step0 raw33861; decide +kernel
      have hl : raw33861step0Labels = raw33861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33861 raw33861Labels permutation520 hz
    mixedMoment B raw33861step0 raw33861step0Labels = mixedMoment B raw33861step1 raw33861step1Labels := by
      have ha : raw33861step1 = (fun i j => raw33861step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33861step1 raw33861step0; decide +kernel
      have hl : raw33861step1Labels = raw33861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33861step0 raw33861step0Labels permutation32 permutation3
    mixedMoment B raw33861step1 raw33861step1Labels = mixedMoment B raw33861step2 raw33861step2Labels := by
      have ha : raw33861step2 = raw33861step1 := by apply Matrix.ext; unfold raw33861step2 raw33861step1; decide +kernel
      have hl : raw33861step1Labels = labelEmbedding6 ∘ raw33861step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33861step1 raw33861step1Labels raw33861step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

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

theorem canonical861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw861 raw861Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw861 raw861Labels = mixedMoment B raw861step0 raw861step0Labels := by
      have ha : raw861step0 = (fun i j => raw861 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw861step0 raw861; decide +kernel
      have hl : raw861step0Labels = raw861Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw861 raw861Labels permutation152 permutation4
    mixedMoment B raw861step0 raw861step0Labels = mixedMoment B raw861step1 raw861step1Labels := by
      have ha : raw861step1 = raw861step0 := by apply Matrix.ext; unfold raw861step1 raw861step0; decide +kernel
      have hl : raw861step0Labels = labelEmbedding7 ∘ raw861step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw861step0 raw861step0Labels raw861step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4199 node4199Labels := by rfl

theorem canonical862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw862 raw862Labels = mixedMoment B node702 node702Labels := by
  calc
    mixedMoment B raw862 raw862Labels = mixedMoment B raw862step0 raw862step0Labels := by
      have ha : raw862step0 = (fun i j => raw862 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw862step0 raw862; decide +kernel
      have hl : raw862step0Labels = raw862Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw862 raw862Labels permutation152 permutation4
    _ = mixedMoment B node702 node702Labels := by rfl

theorem canonical863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw863 raw863Labels = mixedMoment B node760 node760Labels := by
  calc
    mixedMoment B raw863 raw863Labels = mixedMoment B raw863step0 raw863step0Labels := by
      have ha : raw863step0 = (fun i j => raw863 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw863step0 raw863; decide +kernel
      have hl : raw863step0Labels = raw863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw863 raw863Labels permutation152 permutation6
    mixedMoment B raw863step0 raw863step0Labels = mixedMoment B raw863step1 raw863step1Labels := by
      have ha : raw863step1 = -raw863step0 := by apply Matrix.ext; change ∀ i j, raw863step1 i j = -(raw863step0 i j); unfold raw863step1 raw863step0; decide +kernel
      have hl : raw863step1Labels = raw863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw863step1 raw863step1Labels = mixedMoment B raw863step2 raw863step2Labels := by
      have ha : raw863step2 = raw863step1 := by apply Matrix.ext; unfold raw863step2 raw863step1; decide +kernel
      have hl : raw863step1Labels = labelEmbedding1 ∘ raw863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw863step1 raw863step1Labels raw863step2Labels labelEmbedding1 hl
    _ = mixedMoment B node760 node760Labels := by rfl

theorem canonical864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw864 raw864Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw864 raw864Labels = mixedMoment B raw864step0 raw864step0Labels := by
      have ha : raw864step0 = (fun i j => raw864 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw864step0 raw864; decide +kernel
      have hl : raw864step0Labels = raw864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw864 raw864Labels permutation152 permutation4
    mixedMoment B raw864step0 raw864step0Labels = mixedMoment B raw864step1 raw864step1Labels := by
      have ha : raw864step1 = raw864step0 := by apply Matrix.ext; unfold raw864step1 raw864step0; decide +kernel
      have hl : raw864step0Labels = labelEmbedding7 ∘ raw864step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw864step0 raw864step0Labels raw864step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4200 node4200Labels := by rfl

theorem canonical865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw865 raw865Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw865 raw865Labels = mixedMoment B raw865step0 raw865step0Labels := by
      have ha : raw865step0 = (fun i j => raw865 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw865step0 raw865; decide +kernel
      have hl : raw865step0Labels = raw865Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw865 raw865Labels permutation152 permutation4
    _ = mixedMoment B node703 node703Labels := by rfl

theorem canonical866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw866 raw866Labels = mixedMoment B node754 node754Labels := by
  calc
    mixedMoment B raw866 raw866Labels = mixedMoment B raw866step0 raw866step0Labels := by
      have ha : raw866step0 = (fun i j => raw866 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw866step0 raw866; decide +kernel
      have hl : raw866step0Labels = raw866Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw866 raw866Labels permutation164 permutation6
    mixedMoment B raw866step0 raw866step0Labels = mixedMoment B raw866step1 raw866step1Labels := by
      have ha : raw866step1 = -raw866step0 := by apply Matrix.ext; change ∀ i j, raw866step1 i j = -(raw866step0 i j); unfold raw866step1 raw866step0; decide +kernel
      have hl : raw866step1Labels = raw866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw866step1 raw866step1Labels = mixedMoment B raw866step2 raw866step2Labels := by
      have ha : raw866step2 = raw866step1 := by apply Matrix.ext; unfold raw866step2 raw866step1; decide +kernel
      have hl : raw866step1Labels = labelEmbedding1 ∘ raw866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw866step1 raw866step1Labels raw866step2Labels labelEmbedding1 hl
    _ = mixedMoment B node754 node754Labels := by rfl

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

theorem canonical900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw900 raw900Labels = mixedMoment B node4217 node4217Labels := by
  calc
    mixedMoment B raw900 raw900Labels = mixedMoment B raw900step0 raw900step0Labels := by
      have ha : raw900step0 = (fun i j => raw900 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw900step0 raw900; decide +kernel
      have hl : raw900step0Labels = raw900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw900 raw900Labels permutation152 permutation4
    mixedMoment B raw900step0 raw900step0Labels = mixedMoment B raw900step1 raw900step1Labels := by
      have ha : raw900step1 = raw900step0 := by apply Matrix.ext; unfold raw900step1 raw900step0; decide +kernel
      have hl : raw900step0Labels = labelEmbedding7 ∘ raw900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw900step0 raw900step0Labels raw900step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4217 node4217Labels := by rfl

theorem canonical901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw901 raw901Labels = mixedMoment B node719 node719Labels := by
  calc
    mixedMoment B raw901 raw901Labels = mixedMoment B raw901step0 raw901step0Labels := by
      have ha : raw901step0 = (fun i j => raw901 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw901step0 raw901; decide +kernel
      have hl : raw901step0Labels = raw901Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw901 raw901Labels permutation152 permutation4
    _ = mixedMoment B node719 node719Labels := by rfl

theorem canonical902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw902 raw902Labels = mixedMoment B node756 node756Labels := by
  calc
    mixedMoment B raw902 raw902Labels = mixedMoment B raw902step0 raw902step0Labels := by
      have ha : raw902step0 = (fun i j => raw902 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw902step0 raw902; decide +kernel
      have hl : raw902step0Labels = raw902Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw902 raw902Labels permutation170 permutation6
    mixedMoment B raw902step0 raw902step0Labels = mixedMoment B raw902step1 raw902step1Labels := by
      have ha : raw902step1 = -raw902step0 := by apply Matrix.ext; change ∀ i j, raw902step1 i j = -(raw902step0 i j); unfold raw902step1 raw902step0; decide +kernel
      have hl : raw902step1Labels = raw902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw902step1 raw902step1Labels = mixedMoment B raw902step2 raw902step2Labels := by
      have ha : raw902step2 = raw902step1 := by apply Matrix.ext; unfold raw902step2 raw902step1; decide +kernel
      have hl : raw902step1Labels = labelEmbedding1 ∘ raw902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw902step1 raw902step1Labels raw902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node756 node756Labels := by rfl

theorem canonical975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw975 raw975Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw975 raw975Labels = mixedMoment B raw975step0 raw975step0Labels := by
      have ha : raw975step0 = (fun i j => raw975 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw975step0 raw975; decide +kernel
      have hl : raw975step0Labels = raw975Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw975 raw975Labels permutation152 permutation4
    mixedMoment B raw975step0 raw975step0Labels = mixedMoment B raw975step1 raw975step1Labels := by
      have ha : raw975step1 = raw975step0 := by apply Matrix.ext; unfold raw975step1 raw975step0; decide +kernel
      have hl : raw975step0Labels = labelEmbedding7 ∘ raw975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw975step0 raw975step0Labels raw975step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw976 raw976Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw976 raw976Labels = mixedMoment B raw976step0 raw976step0Labels := by
      have ha : raw976step0 = (fun i j => raw976 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw976step0 raw976; decide +kernel
      have hl : raw976step0Labels = raw976Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw976 raw976Labels permutation152 permutation4
    _ = mixedMoment B node786 node786Labels := by rfl

theorem canonical977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw977 raw977Labels = mixedMoment B node822 node822Labels := by
  calc
    mixedMoment B raw977 raw977Labels = mixedMoment B raw977step0 raw977step0Labels := by
      have ha : raw977step0 = (fun i j => raw977 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw977step0 raw977; decide +kernel
      have hl : raw977step0Labels = raw977Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw977 raw977Labels permutation246 permutation6
    mixedMoment B raw977step0 raw977step0Labels = mixedMoment B raw977step1 raw977step1Labels := by
      have ha : raw977step1 = -raw977step0 := by apply Matrix.ext; change ∀ i j, raw977step1 i j = -(raw977step0 i j); unfold raw977step1 raw977step0; decide +kernel
      have hl : raw977step1Labels = raw977step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw977step1 raw977step1Labels = mixedMoment B raw977step2 raw977step2Labels := by
      have ha : raw977step2 = raw977step1 := by apply Matrix.ext; unfold raw977step2 raw977step1; decide +kernel
      have hl : raw977step1Labels = labelEmbedding1 ∘ raw977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw977step1 raw977step1Labels raw977step2Labels labelEmbedding1 hl
    _ = mixedMoment B node822 node822Labels := by rfl

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

theorem canonical11102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11102 raw11102Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw11102 raw11102Labels = mixedMoment B raw11102step0 raw11102step0Labels := by
      have hz : ∀ j, raw11102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11102step0 = (fun i j => raw11102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11102step0 raw11102; decide +kernel
      have hl : raw11102step0Labels = raw11102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11102 raw11102Labels permutation434 hz
    mixedMoment B raw11102step0 raw11102step0Labels = mixedMoment B raw11102step1 raw11102step1Labels := by
      have ha : raw11102step1 = (fun i j => raw11102step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11102step1 raw11102step0; decide +kernel
      have hl : raw11102step1Labels = raw11102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11102step0 raw11102step0Labels permutation151 permutation2
    mixedMoment B raw11102step1 raw11102step1Labels = mixedMoment B raw11102step2 raw11102step2Labels := by
      have ha : raw11102step2 = -raw11102step1 := by apply Matrix.ext; change ∀ i j, raw11102step2 i j = -(raw11102step1 i j); unfold raw11102step2 raw11102step1; decide +kernel
      have hl : raw11102step2Labels = raw11102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical11113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11113 raw11113Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw11113 raw11113Labels = mixedMoment B raw11113step0 raw11113step0Labels := by
      have hz : ∀ j, raw11113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11113step0 = (fun i j => raw11113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11113step0 raw11113; decide +kernel
      have hl : raw11113step0Labels = raw11113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11113 raw11113Labels permutation434 hz
    mixedMoment B raw11113step0 raw11113step0Labels = mixedMoment B raw11113step1 raw11113step1Labels := by
      have ha : raw11113step1 = (fun i j => raw11113step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11113step1 raw11113step0; decide +kernel
      have hl : raw11113step1Labels = raw11113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11113step0 raw11113step0Labels permutation34 permutation3
    mixedMoment B raw11113step1 raw11113step1Labels = mixedMoment B raw11113step2 raw11113step2Labels := by
      have ha : raw11113step2 = raw11113step1 := by apply Matrix.ext; unfold raw11113step2 raw11113step1; decide +kernel
      have hl : raw11113step1Labels = labelEmbedding6 ∘ raw11113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11113step1 raw11113step1Labels raw11113step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical11117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11117 raw11117Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw11117 raw11117Labels = mixedMoment B raw11117step0 raw11117step0Labels := by
      have ha : raw11117step0 = (fun i j => raw11117 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11117step0 raw11117; decide +kernel
      have hl : raw11117step0Labels = raw11117Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11117 raw11117Labels permutation152 permutation3
    mixedMoment B raw11117step0 raw11117step0Labels = mixedMoment B raw11117step1 raw11117step1Labels := by
      have ha : raw11117step1 = raw11117step0 := by apply Matrix.ext; unfold raw11117step1 raw11117step0; decide +kernel
      have hl : raw11117step0Labels = labelEmbedding6 ∘ raw11117step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11117step0 raw11117step0Labels raw11117step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical11119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11119 raw11119Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw11119 raw11119Labels = mixedMoment B raw11119step0 raw11119step0Labels := by
      have ha : raw11119step0 = (fun i j => raw11119 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11119step0 raw11119; decide +kernel
      have hl : raw11119step0Labels = raw11119Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11119 raw11119Labels permutation176 permutation3
    mixedMoment B raw11119step0 raw11119step0Labels = mixedMoment B raw11119step1 raw11119step1Labels := by
      have ha : raw11119step1 = raw11119step0 := by apply Matrix.ext; unfold raw11119step1 raw11119step0; decide +kernel
      have hl : raw11119step0Labels = labelEmbedding6 ∘ raw11119step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11119step0 raw11119step0Labels raw11119step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical11120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11120 raw11120Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw11120 raw11120Labels = mixedMoment B raw11120step0 raw11120step0Labels := by
      have hz : ∀ j, raw11120 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11120step0 = (fun i j => raw11120 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11120step0 raw11120; decide +kernel
      have hl : raw11120step0Labels = raw11120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11120 raw11120Labels permutation520 hz
    mixedMoment B raw11120step0 raw11120step0Labels = mixedMoment B raw11120step1 raw11120step1Labels := by
      have ha : raw11120step1 = (fun i j => raw11120step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11120step1 raw11120step0; decide +kernel
      have hl : raw11120step1Labels = raw11120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11120step0 raw11120step0Labels permutation32 permutation3
    mixedMoment B raw11120step1 raw11120step1Labels = mixedMoment B raw11120step2 raw11120step2Labels := by
      have ha : raw11120step2 = raw11120step1 := by apply Matrix.ext; unfold raw11120step2 raw11120step1; decide +kernel
      have hl : raw11120step1Labels = labelEmbedding6 ∘ raw11120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11120step1 raw11120step1Labels raw11120step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical11121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11121 raw11121Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw11121 raw11121Labels = mixedMoment B raw11121step0 raw11121step0Labels := by
      have ha : raw11121step0 = (fun i j => raw11121 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11121step0 raw11121; decide +kernel
      have hl : raw11121step0Labels = raw11121Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11121 raw11121Labels permutation246 permutation5
    mixedMoment B raw11121step0 raw11121step0Labels = mixedMoment B raw11121step1 raw11121step1Labels := by
      have ha : raw11121step1 = -raw11121step0 := by apply Matrix.ext; change ∀ i j, raw11121step1 i j = -(raw11121step0 i j); unfold raw11121step1 raw11121step0; decide +kernel
      have hl : raw11121step1Labels = raw11121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11121step1 raw11121step1Labels = mixedMoment B raw11121step2 raw11121step2Labels := by
      have ha : raw11121step2 = raw11121step1 := by apply Matrix.ext; unfold raw11121step2 raw11121step1; decide +kernel
      have hl : raw11121step1Labels = labelEmbedding8 ∘ raw11121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11121step1 raw11121step1Labels raw11121step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical11123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11123 raw11123Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw11123 raw11123Labels = mixedMoment B raw11123step0 raw11123step0Labels := by
      have hz : ∀ j, raw11123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11123step0 = (fun i j => raw11123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11123step0 raw11123; decide +kernel
      have hl : raw11123step0Labels = raw11123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11123 raw11123Labels permutation434 hz
    mixedMoment B raw11123step0 raw11123step0Labels = mixedMoment B raw11123step1 raw11123step1Labels := by
      have ha : raw11123step1 = (fun i j => raw11123step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11123step1 raw11123step0; decide +kernel
      have hl : raw11123step1Labels = raw11123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11123step0 raw11123step0Labels permutation33 permutation3
    mixedMoment B raw11123step1 raw11123step1Labels = mixedMoment B raw11123step2 raw11123step2Labels := by
      have ha : raw11123step2 = raw11123step1 := by apply Matrix.ext; unfold raw11123step2 raw11123step1; decide +kernel
      have hl : raw11123step1Labels = labelEmbedding6 ∘ raw11123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11123step1 raw11123step1Labels raw11123step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical11128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11128 raw11128Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw11128 raw11128Labels = mixedMoment B raw11128step0 raw11128step0Labels := by
      have hz : ∀ j, raw11128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11128step0 = (fun i j => raw11128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11128step0 raw11128; decide +kernel
      have hl : raw11128step0Labels = raw11128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11128 raw11128Labels permutation434 hz
    mixedMoment B raw11128step0 raw11128step0Labels = mixedMoment B raw11128step1 raw11128step1Labels := by
      have ha : raw11128step1 = (fun i j => raw11128step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11128step1 raw11128step0; decide +kernel
      have hl : raw11128step1Labels = raw11128step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11128step0 raw11128step0Labels permutation32 permutation3
    mixedMoment B raw11128step1 raw11128step1Labels = mixedMoment B raw11128step2 raw11128step2Labels := by
      have ha : raw11128step2 = raw11128step1 := by apply Matrix.ext; unfold raw11128step2 raw11128step1; decide +kernel
      have hl : raw11128step1Labels = labelEmbedding6 ∘ raw11128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11128step1 raw11128step1Labels raw11128step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

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

theorem singleton4199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4199 node4199Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node702 node702Labels + mixedMoment B node760 node760Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw861 singletonSmall4199
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4199) = raw861Labels := by decide +kernel
  rw [hl, canonical861 B hB] at h
  have hc0 : mixedMoment B raw861 (Fin.cases (0 : Fin 2) singletonSmall4199) =
      mixedMoment B node702 node702Labels := by
    have ha : raw861 = raw862 := by apply Matrix.ext; unfold raw861 raw862; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4199 = raw862Labels := by decide +kernel
    rw [ha, hj, canonical862 B hB]
  have hc1 : mixedMoment B raw861 (Fin.cases (1 : Fin 2) singletonSmall4199) =
      mixedMoment B node760 node760Labels := by
    have ha : raw861 = raw863 := by apply Matrix.ext; unfold raw861 raw863; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4199 = raw863Labels := by decide +kernel
    rw [ha, hj, canonical863 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4200 node4200Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node703 node703Labels + mixedMoment B node754 node754Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw864 singletonSmall4200
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4200) = raw864Labels := by decide +kernel
  rw [hl, canonical864 B hB] at h
  have hc0 : mixedMoment B raw864 (Fin.cases (0 : Fin 2) singletonSmall4200) =
      mixedMoment B node703 node703Labels := by
    have ha : raw864 = raw865 := by apply Matrix.ext; unfold raw864 raw865; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4200 = raw865Labels := by decide +kernel
    rw [ha, hj, canonical865 B hB]
  have hc1 : mixedMoment B raw864 (Fin.cases (1 : Fin 2) singletonSmall4200) =
      mixedMoment B node754 node754Labels := by
    have ha : raw864 = raw866 := by apply Matrix.ext; unfold raw864 raw866; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4200 = raw866Labels := by decide +kernel
    rw [ha, hj, canonical866 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4217 node4217Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node719 node719Labels + mixedMoment B node756 node756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw900 singletonSmall4217
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4217) = raw900Labels := by decide +kernel
  rw [hl, canonical900 B hB] at h
  have hc0 : mixedMoment B raw900 (Fin.cases (0 : Fin 2) singletonSmall4217) =
      mixedMoment B node719 node719Labels := by
    have ha : raw900 = raw901 := by apply Matrix.ext; unfold raw900 raw901; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4217 = raw901Labels := by decide +kernel
    rw [ha, hj, canonical901 B hB]
  have hc1 : mixedMoment B raw900 (Fin.cases (1 : Fin 2) singletonSmall4217) =
      mixedMoment B node756 node756Labels := by
    have ha : raw900 = raw902 := by apply Matrix.ext; unfold raw900 raw902; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4217 = raw902Labels := by decide +kernel
    rw [ha, hj, canonical902 B hB]
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

theorem singleton4252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4252 node4252Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node786 node786Labels + mixedMoment B node822 node822Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw975 singletonSmall4252
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4252) = raw975Labels := by decide +kernel
  rw [hl, canonical975 B hB] at h
  have hc0 : mixedMoment B raw975 (Fin.cases (0 : Fin 2) singletonSmall4252) =
      mixedMoment B node786 node786Labels := by
    have ha : raw975 = raw976 := by apply Matrix.ext; unfold raw975 raw976; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4252 = raw976Labels := by decide +kernel
    rw [ha, hj, canonical976 B hB]
  have hc1 : mixedMoment B raw975 (Fin.cases (1 : Fin 2) singletonSmall4252) =
      mixedMoment B node822 node822Labels := by
    have ha : raw975 = raw977 := by apply Matrix.ext; unfold raw975 raw977; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4252 = raw977Labels := by decide +kernel
    rw [ha, hj, canonical977 B hB]
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

theorem singleton4633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4633 node4633Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1762 node1762Labels + mixedMoment B node1847 node1847Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1479 singletonSmall4633
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4633) = raw1479Labels := by decide +kernel
  rw [hl, canonical1479 B hB] at h
  have hc0 : mixedMoment B raw1479 (Fin.cases (0 : Fin 2) singletonSmall4633) =
      mixedMoment B node1762 node1762Labels := by
    have ha : raw1479 = raw1480 := by apply Matrix.ext; unfold raw1479 raw1480; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4633 = raw1480Labels := by decide +kernel
    rw [ha, hj, canonical1480 B hB]
  have hc1 : mixedMoment B raw1479 (Fin.cases (1 : Fin 2) singletonSmall4633) =
      mixedMoment B node1847 node1847Labels := by
    have ha : raw1479 = raw1481 := by apply Matrix.ext; unfold raw1479 raw1481; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4633 = raw1481Labels := by decide +kernel
    rw [ha, hj, canonical1481 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4634 node4634Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1763 node1763Labels + mixedMoment B node1842 node1842Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1482 singletonSmall4634
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4634) = raw1482Labels := by decide +kernel
  rw [hl, canonical1482 B hB] at h
  have hc0 : mixedMoment B raw1482 (Fin.cases (0 : Fin 2) singletonSmall4634) =
      mixedMoment B node1763 node1763Labels := by
    have ha : raw1482 = raw1483 := by apply Matrix.ext; unfold raw1482 raw1483; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4634 = raw1483Labels := by decide +kernel
    rw [ha, hj, canonical1483 B hB]
  have hc1 : mixedMoment B raw1482 (Fin.cases (1 : Fin 2) singletonSmall4634) =
      mixedMoment B node1842 node1842Labels := by
    have ha : raw1482 = raw1484 := by apply Matrix.ext; unfold raw1482 raw1484; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4634 = raw1484Labels := by decide +kernel
    rw [ha, hj, canonical1484 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4648 node4648Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1776 node1776Labels + mixedMoment B node1844 node1844Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1512 singletonSmall4648
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4648) = raw1512Labels := by decide +kernel
  rw [hl, canonical1512 B hB] at h
  have hc0 : mixedMoment B raw1512 (Fin.cases (0 : Fin 2) singletonSmall4648) =
      mixedMoment B node1776 node1776Labels := by
    have ha : raw1512 = raw1513 := by apply Matrix.ext; unfold raw1512 raw1513; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4648 = raw1513Labels := by decide +kernel
    rw [ha, hj, canonical1513 B hB]
  have hc1 : mixedMoment B raw1512 (Fin.cases (1 : Fin 2) singletonSmall4648) =
      mixedMoment B node1844 node1844Labels := by
    have ha : raw1512 = raw1514 := by apply Matrix.ext; unfold raw1512 raw1514; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4648 = raw1514Labels := by decide +kernel
    rw [ha, hj, canonical1514 B hB]
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

theorem singleton4764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4764 node4764Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1964 node1964Labels + mixedMoment B node2182 node2182Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1695 singletonSmall4764
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4764) = raw1695Labels := by decide +kernel
  rw [hl, canonical1695 B hB] at h
  have hc0 : mixedMoment B raw1695 (Fin.cases (0 : Fin 2) singletonSmall4764) =
      mixedMoment B node1964 node1964Labels := by
    have ha : raw1695 = raw1696 := by apply Matrix.ext; unfold raw1695 raw1696; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4764 = raw1696Labels := by decide +kernel
    rw [ha, hj, canonical1696 B hB]
  have hc1 : mixedMoment B raw1695 (Fin.cases (1 : Fin 2) singletonSmall4764) =
      mixedMoment B node2182 node2182Labels := by
    have ha : raw1695 = raw1697 := by apply Matrix.ext; unfold raw1695 raw1697; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4764 = raw1697Labels := by decide +kernel
    rw [ha, hj, canonical1697 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4766 node4766Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1966 node1966Labels + mixedMoment B node2177 node2177Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1698 singletonSmall4766
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4766) = raw1698Labels := by decide +kernel
  rw [hl, canonical1698 B hB] at h
  have hc0 : mixedMoment B raw1698 (Fin.cases (0 : Fin 2) singletonSmall4766) =
      mixedMoment B node1966 node1966Labels := by
    have ha : raw1698 = raw1699 := by apply Matrix.ext; unfold raw1698 raw1699; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4766 = raw1699Labels := by decide +kernel
    rw [ha, hj, canonical1699 B hB]
  have hc1 : mixedMoment B raw1698 (Fin.cases (1 : Fin 2) singletonSmall4766) =
      mixedMoment B node2177 node2177Labels := by
    have ha : raw1698 = raw1700 := by apply Matrix.ext; unfold raw1698 raw1700; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4766 = raw1700Labels := by decide +kernel
    rw [ha, hj, canonical1700 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4798 node4798Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2016 node2016Labels + mixedMoment B node2075 node2075Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1725 singletonSmall4798
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4798) = raw1725Labels := by decide +kernel
  rw [hl, canonical1725 B hB] at h
  have hc0 : mixedMoment B raw1725 (Fin.cases (0 : Fin 2) singletonSmall4798) =
      mixedMoment B node2016 node2016Labels := by
    have ha : raw1725 = raw1726 := by apply Matrix.ext; unfold raw1725 raw1726; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4798 = raw1726Labels := by decide +kernel
    rw [ha, hj, canonical1726 B hB]
  have hc1 : mixedMoment B raw1725 (Fin.cases (1 : Fin 2) singletonSmall4798) =
      mixedMoment B node2075 node2075Labels := by
    have ha : raw1725 = raw1727 := by apply Matrix.ext; unfold raw1725 raw1727; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4798 = raw1727Labels := by decide +kernel
    rw [ha, hj, canonical1727 B hB]
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

theorem singleton4807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4807 node4807Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2025 node2025Labels + mixedMoment B node2224 node2224Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1743 singletonSmall4807
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4807) = raw1743Labels := by decide +kernel
  rw [hl, canonical1743 B hB] at h
  have hc0 : mixedMoment B raw1743 (Fin.cases (0 : Fin 2) singletonSmall4807) =
      mixedMoment B node2025 node2025Labels := by
    have ha : raw1743 = raw1744 := by apply Matrix.ext; unfold raw1743 raw1744; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4807 = raw1744Labels := by decide +kernel
    rw [ha, hj, canonical1744 B hB]
  have hc1 : mixedMoment B raw1743 (Fin.cases (1 : Fin 2) singletonSmall4807) =
      mixedMoment B node2224 node2224Labels := by
    have ha : raw1743 = raw1745 := by apply Matrix.ext; unfold raw1743 raw1745; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4807 = raw1745Labels := by decide +kernel
    rw [ha, hj, canonical1745 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4810 node4810Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2028 node2028Labels + mixedMoment B node2215 node2215Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1746 singletonSmall4810
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4810) = raw1746Labels := by decide +kernel
  rw [hl, canonical1746 B hB] at h
  have hc0 : mixedMoment B raw1746 (Fin.cases (0 : Fin 2) singletonSmall4810) =
      mixedMoment B node2028 node2028Labels := by
    have ha : raw1746 = raw1747 := by apply Matrix.ext; unfold raw1746 raw1747; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4810 = raw1747Labels := by decide +kernel
    rw [ha, hj, canonical1747 B hB]
  have hc1 : mixedMoment B raw1746 (Fin.cases (1 : Fin 2) singletonSmall4810) =
      mixedMoment B node2215 node2215Labels := by
    have ha : raw1746 = raw1748 := by apply Matrix.ext; unfold raw1746 raw1748; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4810 = raw1748Labels := by decide +kernel
    rw [ha, hj, canonical1748 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4826 node4826Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2046 node2046Labels + mixedMoment B node2077 node2077Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1752 singletonSmall4826
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4826) = raw1752Labels := by decide +kernel
  rw [hl, canonical1752 B hB] at h
  have hc0 : mixedMoment B raw1752 (Fin.cases (0 : Fin 2) singletonSmall4826) =
      mixedMoment B node2046 node2046Labels := by
    have ha : raw1752 = raw1753 := by apply Matrix.ext; unfold raw1752 raw1753; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4826 = raw1753Labels := by decide +kernel
    rw [ha, hj, canonical1753 B hB]
  have hc1 : mixedMoment B raw1752 (Fin.cases (1 : Fin 2) singletonSmall4826) =
      mixedMoment B node2077 node2077Labels := by
    have ha : raw1752 = raw1754 := by apply Matrix.ext; unfold raw1752 raw1754; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4826 = raw1754Labels := by decide +kernel
    rw [ha, hj, canonical1754 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4839 node4839Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2058 node2058Labels + mixedMoment B node2216 node2216Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1770 singletonSmall4839
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4839) = raw1770Labels := by decide +kernel
  rw [hl, canonical1770 B hB] at h
  have hc0 : mixedMoment B raw1770 (Fin.cases (0 : Fin 2) singletonSmall4839) =
      mixedMoment B node2058 node2058Labels := by
    have ha : raw1770 = raw1771 := by apply Matrix.ext; unfold raw1770 raw1771; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4839 = raw1771Labels := by decide +kernel
    rw [ha, hj, canonical1771 B hB]
  have hc1 : mixedMoment B raw1770 (Fin.cases (1 : Fin 2) singletonSmall4839) =
      mixedMoment B node2216 node2216Labels := by
    have ha : raw1770 = raw1772 := by apply Matrix.ext; unfold raw1770 raw1772; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4839 = raw1772Labels := by decide +kernel
    rw [ha, hj, canonical1772 B hB]
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

theorem singleton4864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4864 node4864Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2105 node2105Labels + mixedMoment B node2241 node2241Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1788 singletonSmall4864
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4864) = raw1788Labels := by decide +kernel
  rw [hl, canonical1788 B hB] at h
  have hc0 : mixedMoment B raw1788 (Fin.cases (0 : Fin 2) singletonSmall4864) =
      mixedMoment B node2105 node2105Labels := by
    have ha : raw1788 = raw1789 := by apply Matrix.ext; unfold raw1788 raw1789; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4864 = raw1789Labels := by decide +kernel
    rw [ha, hj, canonical1789 B hB]
  have hc1 : mixedMoment B raw1788 (Fin.cases (1 : Fin 2) singletonSmall4864) =
      mixedMoment B node2241 node2241Labels := by
    have ha : raw1788 = raw1790 := by apply Matrix.ext; unfold raw1788 raw1790; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4864 = raw1790Labels := by decide +kernel
    rw [ha, hj, canonical1790 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5354 node5354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3692 node3692Labels + mixedMoment B node3769 node3769Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2397 singletonSmall5354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5354) = raw2397Labels := by decide +kernel
  rw [hl, canonical2397 B hB] at h
  have hc0 : mixedMoment B raw2397 (Fin.cases (0 : Fin 2) singletonSmall5354) =
      mixedMoment B node3692 node3692Labels := by
    have ha : raw2397 = raw2398 := by apply Matrix.ext; unfold raw2397 raw2398; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5354 = raw2398Labels := by decide +kernel
    rw [ha, hj, canonical2398 B hB]
  have hc1 : mixedMoment B raw2397 (Fin.cases (1 : Fin 2) singletonSmall5354) =
      mixedMoment B node3769 node3769Labels := by
    have ha : raw2397 = raw2399 := by apply Matrix.ext; unfold raw2397 raw2399; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5354 = raw2399Labels := by decide +kernel
    rw [ha, hj, canonical2399 B hB]
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

theorem singleton5431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5431 node5431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3849 node3849Labels + mixedMoment B node3875 node3875Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2520 singletonSmall5431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5431) = raw2520Labels := by decide +kernel
  rw [hl, canonical2520 B hB] at h
  have hc0 : mixedMoment B raw2520 (Fin.cases (0 : Fin 2) singletonSmall5431) =
      mixedMoment B node3849 node3849Labels := by
    have ha : raw2520 = raw2521 := by apply Matrix.ext; unfold raw2520 raw2521; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5431 = raw2521Labels := by decide +kernel
    rw [ha, hj, canonical2521 B hB]
  have hc1 : mixedMoment B raw2520 (Fin.cases (1 : Fin 2) singletonSmall5431) =
      mixedMoment B node3875 node3875Labels := by
    have ha : raw2520 = raw2522 := by apply Matrix.ext; unfold raw2520 raw2522; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5431 = raw2522Labels := by decide +kernel
    rw [ha, hj, canonical2522 B hB]
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

theorem sound702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node702 node702Labels = Sparse.eval nodeValue702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 702) = mixedMoment B node702 node702Labels := rfl
  simpa [nodeValue702, Sparse.eval] using hc.symm

theorem sound703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node703 node703Labels = Sparse.eval nodeValue703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 703) = mixedMoment B node703 node703Labels := rfl
  simpa [nodeValue703, Sparse.eval] using hc.symm

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

theorem sound719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node719 node719Labels = Sparse.eval nodeValue719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 719) = mixedMoment B node719 node719Labels := rfl
  simpa [nodeValue719, Sparse.eval] using hc.symm

theorem sound754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node754 node754Labels = Sparse.eval nodeValue754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 754) = mixedMoment B node754 node754Labels := rfl
  simpa [nodeValue754, Sparse.eval] using hc.symm

theorem sound756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node756 node756Labels = Sparse.eval nodeValue756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 756) = mixedMoment B node756 node756Labels := rfl
  simpa [nodeValue756, Sparse.eval] using hc.symm

theorem sound760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node760 node760Labels = Sparse.eval nodeValue760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 760) = mixedMoment B node760 node760Labels := rfl
  simpa [nodeValue760, Sparse.eval] using hc.symm

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

theorem sound786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node786 node786Labels = Sparse.eval nodeValue786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 786) = mixedMoment B node786 node786Labels := rfl
  simpa [nodeValue786, Sparse.eval] using hc.symm

theorem sound822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node822 node822Labels = Sparse.eval nodeValue822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 822) = mixedMoment B node822 node822Labels := rfl
  simpa [nodeValue822, Sparse.eval] using hc.symm

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

theorem sound1762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1762 node1762Labels = Sparse.eval nodeValue1762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1762) = mixedMoment B node1762 node1762Labels := rfl
  simpa [nodeValue1762, Sparse.eval] using hc.symm

theorem sound1763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1763 node1763Labels = Sparse.eval nodeValue1763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1763) = mixedMoment B node1763 node1763Labels := rfl
  simpa [nodeValue1763, Sparse.eval] using hc.symm

theorem sound1776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1776 node1776Labels = Sparse.eval nodeValue1776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1776) = mixedMoment B node1776 node1776Labels := rfl
  simpa [nodeValue1776, Sparse.eval] using hc.symm

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

theorem sound1842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1842 node1842Labels = Sparse.eval nodeValue1842 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1842) = mixedMoment B node1842 node1842Labels := rfl
  simpa [nodeValue1842, Sparse.eval] using hc.symm

theorem sound1844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1844 node1844Labels = Sparse.eval nodeValue1844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1844) = mixedMoment B node1844 node1844Labels := rfl
  simpa [nodeValue1844, Sparse.eval] using hc.symm

theorem sound1847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1847 node1847Labels = Sparse.eval nodeValue1847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1847) = mixedMoment B node1847 node1847Labels := rfl
  simpa [nodeValue1847, Sparse.eval] using hc.symm

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

theorem sound1964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1964 node1964Labels = Sparse.eval nodeValue1964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1964) = mixedMoment B node1964 node1964Labels := rfl
  simpa [nodeValue1964, Sparse.eval] using hc.symm

theorem sound1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1966 node1966Labels = Sparse.eval nodeValue1966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1966) = mixedMoment B node1966 node1966Labels := rfl
  simpa [nodeValue1966, Sparse.eval] using hc.symm

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

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

theorem sound2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2046 node2046Labels = Sparse.eval nodeValue2046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2046) = mixedMoment B node2046 node2046Labels := rfl
  simpa [nodeValue2046, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

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

theorem sound2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2177 node2177Labels = Sparse.eval nodeValue2177 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2177) = mixedMoment B node2177 node2177Labels := rfl
  simpa [nodeValue2177, Sparse.eval] using hc.symm

theorem sound2182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2182 node2182Labels = Sparse.eval nodeValue2182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2182) = mixedMoment B node2182 node2182Labels := rfl
  simpa [nodeValue2182, Sparse.eval] using hc.symm

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

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

theorem sound2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2241 node2241Labels = Sparse.eval nodeValue2241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2241) = mixedMoment B node2241 node2241Labels := rfl
  simpa [nodeValue2241, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

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

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

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

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

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

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

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

theorem sound4199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4199 node4199Labels = Sparse.eval nodeValue4199 (mixedVector B) := by
  have h := singleton4199 B _hB
  rw [sound702 B _hB _hF, sound760 B _hB _hF] at h
  norm_num [nodeValue4199, nodeValue702, nodeValue760, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4200 node4200Labels = Sparse.eval nodeValue4200 (mixedVector B) := by
  have h := singleton4200 B _hB
  rw [sound703 B _hB _hF, sound754 B _hB _hF] at h
  norm_num [nodeValue4200, nodeValue703, nodeValue754, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4217 node4217Labels = Sparse.eval nodeValue4217 (mixedVector B) := by
  have h := singleton4217 B _hB
  rw [sound719 B _hB _hF, sound756 B _hB _hF] at h
  norm_num [nodeValue4217, nodeValue719, nodeValue756, Sparse.eval] at h ⊢
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

theorem sound4252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4252 node4252Labels = Sparse.eval nodeValue4252 (mixedVector B) := by
  have h := singleton4252 B _hB
  rw [sound786 B _hB _hF, sound822 B _hB _hF] at h
  norm_num [nodeValue4252, nodeValue786, nodeValue822, Sparse.eval] at h ⊢
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

theorem sound4633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4633 node4633Labels = Sparse.eval nodeValue4633 (mixedVector B) := by
  have h := singleton4633 B _hB
  rw [sound1762 B _hB _hF, sound1847 B _hB _hF] at h
  norm_num [nodeValue4633, nodeValue1762, nodeValue1847, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4634 node4634Labels = Sparse.eval nodeValue4634 (mixedVector B) := by
  have h := singleton4634 B _hB
  rw [sound1763 B _hB _hF, sound1842 B _hB _hF] at h
  norm_num [nodeValue4634, nodeValue1763, nodeValue1842, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4648 node4648Labels = Sparse.eval nodeValue4648 (mixedVector B) := by
  have h := singleton4648 B _hB
  rw [sound1776 B _hB _hF, sound1844 B _hB _hF] at h
  norm_num [nodeValue4648, nodeValue1776, nodeValue1844, Sparse.eval] at h ⊢
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

theorem sound4764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4764 node4764Labels = Sparse.eval nodeValue4764 (mixedVector B) := by
  have h := singleton4764 B _hB
  rw [sound1964 B _hB _hF, sound2182 B _hB _hF] at h
  norm_num [nodeValue4764, nodeValue1964, nodeValue2182, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4766 node4766Labels = Sparse.eval nodeValue4766 (mixedVector B) := by
  have h := singleton4766 B _hB
  rw [sound1966 B _hB _hF, sound2177 B _hB _hF] at h
  norm_num [nodeValue4766, nodeValue1966, nodeValue2177, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4798 node4798Labels = Sparse.eval nodeValue4798 (mixedVector B) := by
  have h := singleton4798 B _hB
  rw [sound2016 B _hB _hF, sound2075 B _hB _hF] at h
  norm_num [nodeValue4798, nodeValue2016, nodeValue2075, Sparse.eval] at h ⊢
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

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4826 node4826Labels = Sparse.eval nodeValue4826 (mixedVector B) := by
  have h := singleton4826 B _hB
  rw [sound2046 B _hB _hF, sound2077 B _hB _hF] at h
  norm_num [nodeValue4826, nodeValue2046, nodeValue2077, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
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

theorem sound4864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4864 node4864Labels = Sparse.eval nodeValue4864 (mixedVector B) := by
  have h := singleton4864 B _hB
  rw [sound2105 B _hB _hF, sound2241 B _hB _hF] at h
  norm_num [nodeValue4864, nodeValue2105, nodeValue2241, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
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

theorem sound5354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5354 node5354Labels = Sparse.eval nodeValue5354 (mixedVector B) := by
  have h := singleton5354 B _hB
  rw [sound3692 B _hB _hF, sound3769 B _hB _hF] at h
  norm_num [nodeValue5354, nodeValue3692, nodeValue3769, Sparse.eval] at h ⊢
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

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
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

theorem sourceEq2464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2464 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 1) (sourceB2464 + difference 1 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 1) (sourceB2464 + difference 1 0) sourceC2464) = raw33845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33845; decide +kernel
    rw [ha]
    exact (canonical33845 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 2) (sourceB2464 + difference 2 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 2) (sourceB2464 + difference 2 0) sourceC2464) = raw33846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33846; decide +kernel
    rw [ha]
    exact (canonical33846 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 3) (sourceB2464 + difference 3 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 3) (sourceB2464 + difference 3 0) sourceC2464) = raw11102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11102; decide +kernel
    rw [ha]
    exact (canonical11102 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 4) (sourceB2464 + difference 4 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 4) (sourceB2464 + difference 4 0) sourceC2464) = raw33847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33847; decide +kernel
    rw [ha]
    exact (canonical33847 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 5) (sourceB2464 + difference 5 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 5) (sourceB2464 + difference 5 0) sourceC2464) = raw33848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33848; decide +kernel
    rw [ha]
    exact (canonical33848 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 0) (sourceB2464 + difference 0 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 0) (sourceB2464 + difference 0 1) sourceC2464) = raw11117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11117; decide +kernel
    rw [ha]
    exact (canonical11117 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 2) (sourceB2464 + difference 2 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 2) (sourceB2464 + difference 2 1) sourceC2464) = raw11119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11119; decide +kernel
    rw [ha]
    exact (canonical11119 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 3) (sourceB2464 + difference 3 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 3) (sourceB2464 + difference 3 1) sourceC2464) = raw31384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31384; decide +kernel
    rw [ha]
    exact (canonical31384 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 4) (sourceB2464 + difference 4 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 4) (sourceB2464 + difference 4 1) sourceC2464) = raw11120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11120; decide +kernel
    rw [ha]
    exact (canonical11120 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 5) (sourceB2464 + difference 5 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 5) (sourceB2464 + difference 5 1) sourceC2464) = raw11121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11121; decide +kernel
    rw [ha]
    exact (canonical11121 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 0) (sourceB2464 + difference 0 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4217) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 0) (sourceB2464 + difference 0 2) sourceC2464) = raw33849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33849; decide +kernel
    rw [ha]
    exact (canonical33849 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 1) (sourceB2464 + difference 1 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4648) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 1) (sourceB2464 + difference 1 2) sourceC2464) = raw33850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33850; decide +kernel
    rw [ha]
    exact (canonical33850 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 3) (sourceB2464 + difference 3 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 3) (sourceB2464 + difference 3 2) sourceC2464) = raw11113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11113; decide +kernel
    rw [ha]
    exact (canonical11113 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 4) (sourceB2464 + difference 4 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 4) (sourceB2464 + difference 4 2) sourceC2464) = raw33851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33851; decide +kernel
    rw [ha]
    exact (canonical33851 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 5) (sourceB2464 + difference 5 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 5) (sourceB2464 + difference 5 2) sourceC2464) = raw33852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33852; decide +kernel
    rw [ha]
    exact (canonical33852 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 0) (sourceB2464 + difference 0 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4200) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 0) (sourceB2464 + difference 0 3) sourceC2464) = raw33853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33853; decide +kernel
    rw [ha]
    exact (canonical33853 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 1) (sourceB2464 + difference 1 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 1) (sourceB2464 + difference 1 3) sourceC2464) = raw33854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33854; decide +kernel
    rw [ha]
    exact (canonical33854 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 2) (sourceB2464 + difference 2 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 2) (sourceB2464 + difference 2 3) sourceC2464) = raw33855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33855; decide +kernel
    rw [ha]
    exact (canonical33855 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 4) (sourceB2464 + difference 4 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 4) (sourceB2464 + difference 4 3) sourceC2464) = raw33856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33856; decide +kernel
    rw [ha]
    exact (canonical33856 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 5) (sourceB2464 + difference 5 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 5) (sourceB2464 + difference 5 3) sourceC2464) = raw33857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33857; decide +kernel
    rw [ha]
    exact (canonical33857 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 0) (sourceB2464 + difference 0 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4200) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 0) (sourceB2464 + difference 0 4) sourceC2464) = raw31389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31389; decide +kernel
    rw [ha]
    exact (canonical31389 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 1) (sourceB2464 + difference 1 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 1) (sourceB2464 + difference 1 4) sourceC2464) = raw31390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31390; decide +kernel
    rw [ha]
    exact (canonical31390 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 2) (sourceB2464 + difference 2 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 2) (sourceB2464 + difference 2 4) sourceC2464) = raw31391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31391; decide +kernel
    rw [ha]
    exact (canonical31391 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 3) (sourceB2464 + difference 3 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 3) (sourceB2464 + difference 3 4) sourceC2464) = raw11123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11123; decide +kernel
    rw [ha]
    exact (canonical11123 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 5) (sourceB2464 + difference 5 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 5) (sourceB2464 + difference 5 4) sourceC2464) = raw31392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31392; decide +kernel
    rw [ha]
    exact (canonical31392 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 0) (sourceB2464 + difference 0 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4199) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 0) (sourceB2464 + difference 0 5) sourceC2464) = raw33858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33858; decide +kernel
    rw [ha]
    exact (canonical33858 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 1) (sourceB2464 + difference 1 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4633) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 1) (sourceB2464 + difference 1 5) sourceC2464) = raw33859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33859; decide +kernel
    rw [ha]
    exact (canonical33859 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 2) (sourceB2464 + difference 2 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4764) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 2) (sourceB2464 + difference 2 5) sourceC2464) = raw33860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33860; decide +kernel
    rw [ha]
    exact (canonical33860 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 3) (sourceB2464 + difference 3 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 3) (sourceB2464 + difference 3 5) sourceC2464) = raw11128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11128; decide +kernel
    rw [ha]
    exact (canonical11128 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 4) (sourceB2464 + difference 4 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 4) (sourceB2464 + difference 4 5) sourceC2464) = raw33861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33861; decide +kernel
    rw [ha]
    exact (canonical33861 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2464 sourceB2464 sourceC2464
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2464, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1983 : Integer.Sparse.reindex keyMap MixedData.row1983 = numericRow1983 := by decide +kernel

theorem numericCheck1983 (x : Master → ℝ) : Integer.Sparse.eval numericRow1983 x =
    (51840 : ℝ) * reducedSource1983 x := by
  norm_num [numericRow1983, reducedSource1983, Integer.Sparse.eval, Sparse.eval, nodeValue4199, nodeValue4200, nodeValue4217, nodeValue4252, nodeValue4633, nodeValue4634, nodeValue4648, nodeValue4764, nodeValue4766, nodeValue4798, nodeValue4805, nodeValue4807, nodeValue4810, nodeValue4826, nodeValue4839, nodeValue4864, nodeValue4889, nodeValue5354, nodeValue5417, nodeValue5431, nodeValue5435]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1983 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1983 (mixedVector B) = 0 := by
  have h4199 : mixedVector B (Sum.inr 4199) = Sparse.eval nodeValue4199 (mixedVector B) := by
    change mixedMoment B node4199 node4199Labels = _
    exact sound4199 B hB hF
  have h4200 : mixedVector B (Sum.inr 4200) = Sparse.eval nodeValue4200 (mixedVector B) := by
    change mixedMoment B node4200 node4200Labels = _
    exact sound4200 B hB hF
  have h4217 : mixedVector B (Sum.inr 4217) = Sparse.eval nodeValue4217 (mixedVector B) := by
    change mixedMoment B node4217 node4217Labels = _
    exact sound4217 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4633 : mixedVector B (Sum.inr 4633) = Sparse.eval nodeValue4633 (mixedVector B) := by
    change mixedMoment B node4633 node4633Labels = _
    exact sound4633 B hB hF
  have h4634 : mixedVector B (Sum.inr 4634) = Sparse.eval nodeValue4634 (mixedVector B) := by
    change mixedMoment B node4634 node4634Labels = _
    exact sound4634 B hB hF
  have h4648 : mixedVector B (Sum.inr 4648) = Sparse.eval nodeValue4648 (mixedVector B) := by
    change mixedMoment B node4648 node4648Labels = _
    exact sound4648 B hB hF
  have h4764 : mixedVector B (Sum.inr 4764) = Sparse.eval nodeValue4764 (mixedVector B) := by
    change mixedMoment B node4764 node4764Labels = _
    exact sound4764 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5417 : mixedVector B (Sum.inr 5417) = Sparse.eval nodeValue5417 (mixedVector B) := by
    change mixedMoment B node5417 node5417Labels = _
    exact sound5417_e B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  simpa only [sourceForm2464, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4199, h4200, h4217, h4252, h4633, h4634, h4648, h4764, h4766, h4798, h4805, h4807, h4810, h4826, h4839, h4864, h4889, h5354, h5417, h5431, h5435, reducedSource1983] using sourceEq2464 B hB

theorem rowSound1983_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1983 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1983, numericCheck1983, reducedZero1983 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e_oai
