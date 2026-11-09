-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:15:17.178131+00:00
-- url     : https://prove2.me/submissions/564a510b-4d63-4d36-b35b-ce056ef35aca

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5386_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5417_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19240 raw19240Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19240 raw19240Labels = mixedMoment B raw19240step0 raw19240step0Labels := by
      have ha : raw19240step0 = (fun i j => raw19240 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19240step0 raw19240; decide +kernel
      have hl : raw19240step0Labels = raw19240Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19240 raw19240Labels permutation265 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical19241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19241 raw19241Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw19241 raw19241Labels = mixedMoment B raw19241step0 raw19241step0Labels := by
      have ha : raw19241step0 = (fun i j => raw19241 (permutation361 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19241step0 raw19241; decide +kernel
      have hl : raw19241step0Labels = raw19241Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19241 raw19241Labels permutation361 permutation5
    mixedMoment B raw19241step0 raw19241step0Labels = mixedMoment B raw19241step1 raw19241step1Labels := by
      have ha : raw19241step1 = -raw19241step0 := by apply Matrix.ext; change ∀ i j, raw19241step1 i j = -(raw19241step0 i j); unfold raw19241step1 raw19241step0; decide +kernel
      have hl : raw19241step1Labels = raw19241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19241step1 raw19241step1Labels = mixedMoment B raw19241step2 raw19241step2Labels := by
      have ha : raw19241step2 = raw19241step1 := by apply Matrix.ext; unfold raw19241step2 raw19241step1; decide +kernel
      have hl : raw19241step1Labels = labelEmbedding8 ∘ raw19241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19241step1 raw19241step1Labels raw19241step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical19242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19242 raw19242Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19242 raw19242Labels = mixedMoment B raw19242step0 raw19242step0Labels := by
      have hz : ∀ j, raw19242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19242step0 = (fun i j => raw19242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19242step0 raw19242; decide +kernel
      have hl : raw19242step0Labels = raw19242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19242 raw19242Labels permutation434 hz
    mixedMoment B raw19242step0 raw19242step0Labels = mixedMoment B raw19242step1 raw19242step1Labels := by
      have ha : raw19242step1 = (fun i j => raw19242step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19242step1 raw19242step0; decide +kernel
      have hl : raw19242step1Labels = raw19242step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19242step0 raw19242step0Labels permutation69 permutation6
    mixedMoment B raw19242step1 raw19242step1Labels = mixedMoment B raw19242step2 raw19242step2Labels := by
      have ha : raw19242step2 = -raw19242step1 := by apply Matrix.ext; change ∀ i j, raw19242step2 i j = -(raw19242step1 i j); unfold raw19242step2 raw19242step1; decide +kernel
      have hl : raw19242step2Labels = raw19242step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19242step2 raw19242step2Labels = mixedMoment B raw19242step3 raw19242step3Labels := by
      have ha : raw19242step3 = raw19242step2 := by apply Matrix.ext; unfold raw19242step3 raw19242step2; decide +kernel
      have hl : raw19242step2Labels = labelEmbedding9 ∘ raw19242step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19242step2 raw19242step2Labels raw19242step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical19243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19243 raw19243Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19243 raw19243Labels = mixedMoment B raw19243step0 raw19243step0Labels := by
      have hz : ∀ j, raw19243 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19243step0 = (fun i j => raw19243 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19243step0 raw19243; decide +kernel
      have hl : raw19243step0Labels = raw19243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19243 raw19243Labels permutation520 hz
    mixedMoment B raw19243step0 raw19243step0Labels = mixedMoment B raw19243step1 raw19243step1Labels := by
      have ha : raw19243step1 = (fun i j => raw19243step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19243step1 raw19243step0; decide +kernel
      have hl : raw19243step1Labels = raw19243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19243step0 raw19243step0Labels permutation69 permutation6
    mixedMoment B raw19243step1 raw19243step1Labels = mixedMoment B raw19243step2 raw19243step2Labels := by
      have ha : raw19243step2 = -raw19243step1 := by apply Matrix.ext; change ∀ i j, raw19243step2 i j = -(raw19243step1 i j); unfold raw19243step2 raw19243step1; decide +kernel
      have hl : raw19243step2Labels = raw19243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19243step2 raw19243step2Labels = mixedMoment B raw19243step3 raw19243step3Labels := by
      have ha : raw19243step3 = raw19243step2 := by apply Matrix.ext; unfold raw19243step3 raw19243step2; decide +kernel
      have hl : raw19243step2Labels = labelEmbedding9 ∘ raw19243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19243step2 raw19243step2Labels raw19243step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical19244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19244 raw19244Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw19244 raw19244Labels = mixedMoment B raw19244step0 raw19244step0Labels := by
      have ha : raw19244step0 = (fun i j => raw19244 (permutation313 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19244step0 raw19244; decide +kernel
      have hl : raw19244step0Labels = raw19244Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19244 raw19244Labels permutation313 permutation6
    mixedMoment B raw19244step0 raw19244step0Labels = mixedMoment B raw19244step1 raw19244step1Labels := by
      have ha : raw19244step1 = -raw19244step0 := by apply Matrix.ext; change ∀ i j, raw19244step1 i j = -(raw19244step0 i j); unfold raw19244step1 raw19244step0; decide +kernel
      have hl : raw19244step1Labels = raw19244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19244step1 raw19244step1Labels = mixedMoment B raw19244step2 raw19244step2Labels := by
      have ha : raw19244step2 = raw19244step1 := by apply Matrix.ext; unfold raw19244step2 raw19244step1; decide +kernel
      have hl : raw19244step1Labels = labelEmbedding9 ∘ raw19244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19244step1 raw19244step1Labels raw19244step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical19245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19245 raw19245Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw19245 raw19245Labels = mixedMoment B raw19245step0 raw19245step0Labels := by
      have ha : raw19245step0 = (fun i j => raw19245 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19245step0 raw19245; decide +kernel
      have hl : raw19245step0Labels = raw19245Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19245 raw19245Labels permutation197 permutation5
    mixedMoment B raw19245step0 raw19245step0Labels = mixedMoment B raw19245step1 raw19245step1Labels := by
      have ha : raw19245step1 = -raw19245step0 := by apply Matrix.ext; change ∀ i j, raw19245step1 i j = -(raw19245step0 i j); unfold raw19245step1 raw19245step0; decide +kernel
      have hl : raw19245step1Labels = raw19245step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19245step1 raw19245step1Labels = mixedMoment B raw19245step2 raw19245step2Labels := by
      have ha : raw19245step2 = raw19245step1 := by apply Matrix.ext; unfold raw19245step2 raw19245step1; decide +kernel
      have hl : raw19245step1Labels = labelEmbedding8 ∘ raw19245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19245step1 raw19245step1Labels raw19245step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical19246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19246 raw19246Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw19246 raw19246Labels = mixedMoment B raw19246step0 raw19246step0Labels := by
      have ha : raw19246step0 = (fun i j => raw19246 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19246step0 raw19246; decide +kernel
      have hl : raw19246step0Labels = raw19246Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19246 raw19246Labels permutation197 permutation5
    mixedMoment B raw19246step0 raw19246step0Labels = mixedMoment B raw19246step1 raw19246step1Labels := by
      have ha : raw19246step1 = -raw19246step0 := by apply Matrix.ext; change ∀ i j, raw19246step1 i j = -(raw19246step0 i j); unfold raw19246step1 raw19246step0; decide +kernel
      have hl : raw19246step1Labels = raw19246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19246step1 raw19246step1Labels = mixedMoment B raw19246step2 raw19246step2Labels := by
      have ha : raw19246step2 = raw19246step1 := by apply Matrix.ext; unfold raw19246step2 raw19246step1; decide +kernel
      have hl : raw19246step1Labels = labelEmbedding8 ∘ raw19246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19246step1 raw19246step1Labels raw19246step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical19247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19247 raw19247Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw19247 raw19247Labels = mixedMoment B raw19247step0 raw19247step0Labels := by
      have hz : ∀ j, raw19247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19247step0 = (fun i j => raw19247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19247step0 raw19247; decide +kernel
      have hl : raw19247step0Labels = raw19247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19247 raw19247Labels permutation434 hz
    mixedMoment B raw19247step0 raw19247step0Labels = mixedMoment B raw19247step1 raw19247step1Labels := by
      have ha : raw19247step1 = (fun i j => raw19247step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19247step1 raw19247step0; decide +kernel
      have hl : raw19247step1Labels = raw19247step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19247step0 raw19247step0Labels permutation73 permutation4
    mixedMoment B raw19247step1 raw19247step1Labels = mixedMoment B raw19247step2 raw19247step2Labels := by
      have ha : raw19247step2 = raw19247step1 := by apply Matrix.ext; unfold raw19247step2 raw19247step1; decide +kernel
      have hl : raw19247step1Labels = labelEmbedding7 ∘ raw19247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19247step1 raw19247step1Labels raw19247step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical19248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19248 raw19248Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw19248 raw19248Labels = mixedMoment B raw19248step0 raw19248step0Labels := by
      have hz : ∀ j, raw19248 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19248step0 = (fun i j => raw19248 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19248step0 raw19248; decide +kernel
      have hl : raw19248step0Labels = raw19248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19248 raw19248Labels permutation520 hz
    mixedMoment B raw19248step0 raw19248step0Labels = mixedMoment B raw19248step1 raw19248step1Labels := by
      have ha : raw19248step1 = (fun i j => raw19248step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19248step1 raw19248step0; decide +kernel
      have hl : raw19248step1Labels = raw19248step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19248step0 raw19248step0Labels permutation73 permutation4
    mixedMoment B raw19248step1 raw19248step1Labels = mixedMoment B raw19248step2 raw19248step2Labels := by
      have ha : raw19248step2 = raw19248step1 := by apply Matrix.ext; unfold raw19248step2 raw19248step1; decide +kernel
      have hl : raw19248step1Labels = labelEmbedding7 ∘ raw19248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19248step1 raw19248step1Labels raw19248step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical19249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19249 raw19249Labels = mixedMoment B node5417 node5417Labels := by
  calc
    mixedMoment B raw19249 raw19249Labels = mixedMoment B raw19249step0 raw19249step0Labels := by
      have ha : raw19249step0 = (fun i j => raw19249 (permutation316 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19249step0 raw19249; decide +kernel
      have hl : raw19249step0Labels = raw19249Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19249 raw19249Labels permutation316 permutation4
    mixedMoment B raw19249step0 raw19249step0Labels = mixedMoment B raw19249step1 raw19249step1Labels := by
      have ha : raw19249step1 = raw19249step0 := by apply Matrix.ext; unfold raw19249step1 raw19249step0; decide +kernel
      have hl : raw19249step0Labels = labelEmbedding7 ∘ raw19249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19249step0 raw19249step0Labels raw19249step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5417 node5417Labels := by rfl

theorem canonical19250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19250 raw19250Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw19250 raw19250Labels = mixedMoment B raw19250step0 raw19250step0Labels := by
      have ha : raw19250step0 = (fun i j => raw19250 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19250step0 raw19250; decide +kernel
      have hl : raw19250step0Labels = raw19250Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19250 raw19250Labels permutation156 permutation3
    mixedMoment B raw19250step0 raw19250step0Labels = mixedMoment B raw19250step1 raw19250step1Labels := by
      have ha : raw19250step1 = raw19250step0 := by apply Matrix.ext; unfold raw19250step1 raw19250step0; decide +kernel
      have hl : raw19250step0Labels = labelEmbedding6 ∘ raw19250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19250step0 raw19250step0Labels raw19250step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical19251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19251 raw19251Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw19251 raw19251Labels = mixedMoment B raw19251step0 raw19251step0Labels := by
      have ha : raw19251step0 = (fun i j => raw19251 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19251step0 raw19251; decide +kernel
      have hl : raw19251step0Labels = raw19251Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19251 raw19251Labels permutation273 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

theorem canonical19252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19252 raw19252Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw19252 raw19252Labels = mixedMoment B raw19252step0 raw19252step0Labels := by
      have hz : ∀ j, raw19252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19252step0 = (fun i j => raw19252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19252step0 raw19252; decide +kernel
      have hl : raw19252step0Labels = raw19252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19252 raw19252Labels permutation434 hz
    mixedMoment B raw19252step0 raw19252step0Labels = mixedMoment B raw19252step1 raw19252step1Labels := by
      have ha : raw19252step1 = (fun i j => raw19252step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19252step1 raw19252step0; decide +kernel
      have hl : raw19252step1Labels = raw19252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19252step0 raw19252step0Labels permutation33 permutation3
    mixedMoment B raw19252step1 raw19252step1Labels = mixedMoment B raw19252step2 raw19252step2Labels := by
      have ha : raw19252step2 = raw19252step1 := by apply Matrix.ext; unfold raw19252step2 raw19252step1; decide +kernel
      have hl : raw19252step1Labels = labelEmbedding6 ∘ raw19252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19252step1 raw19252step1Labels raw19252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical19253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19253 raw19253Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw19253 raw19253Labels = mixedMoment B raw19253step0 raw19253step0Labels := by
      have hz : ∀ j, raw19253 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19253step0 = (fun i j => raw19253 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19253step0 raw19253; decide +kernel
      have hl : raw19253step0Labels = raw19253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19253 raw19253Labels permutation520 hz
    mixedMoment B raw19253step0 raw19253step0Labels = mixedMoment B raw19253step1 raw19253step1Labels := by
      have ha : raw19253step1 = (fun i j => raw19253step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19253step1 raw19253step0; decide +kernel
      have hl : raw19253step1Labels = raw19253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19253step0 raw19253step0Labels permutation33 permutation3
    mixedMoment B raw19253step1 raw19253step1Labels = mixedMoment B raw19253step2 raw19253step2Labels := by
      have ha : raw19253step2 = raw19253step1 := by apply Matrix.ext; unfold raw19253step2 raw19253step1; decide +kernel
      have hl : raw19253step1Labels = labelEmbedding6 ∘ raw19253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19253step1 raw19253step1Labels raw19253step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical19254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19254 raw19254Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw19254 raw19254Labels = mixedMoment B raw19254step0 raw19254step0Labels := by
      have ha : raw19254step0 = (fun i j => raw19254 (permutation252 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19254step0 raw19254; decide +kernel
      have hl : raw19254step0Labels = raw19254Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19254 raw19254Labels permutation252 permutation5
    mixedMoment B raw19254step0 raw19254step0Labels = mixedMoment B raw19254step1 raw19254step1Labels := by
      have ha : raw19254step1 = -raw19254step0 := by apply Matrix.ext; change ∀ i j, raw19254step1 i j = -(raw19254step0 i j); unfold raw19254step1 raw19254step0; decide +kernel
      have hl : raw19254step1Labels = raw19254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19254step1 raw19254step1Labels = mixedMoment B raw19254step2 raw19254step2Labels := by
      have ha : raw19254step2 = raw19254step1 := by apply Matrix.ext; unfold raw19254step2 raw19254step1; decide +kernel
      have hl : raw19254step1Labels = labelEmbedding8 ∘ raw19254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19254step1 raw19254step1Labels raw19254step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical19255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19255 raw19255Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw19255 raw19255Labels = mixedMoment B raw19255step0 raw19255step0Labels := by
      have ha : raw19255step0 = (fun i j => raw19255 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19255step0 raw19255; decide +kernel
      have hl : raw19255step0Labels = raw19255Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19255 raw19255Labels permutation195 permutation5
    mixedMoment B raw19255step0 raw19255step0Labels = mixedMoment B raw19255step1 raw19255step1Labels := by
      have ha : raw19255step1 = -raw19255step0 := by apply Matrix.ext; change ∀ i j, raw19255step1 i j = -(raw19255step0 i j); unfold raw19255step1 raw19255step0; decide +kernel
      have hl : raw19255step1Labels = raw19255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19255step1 raw19255step1Labels = mixedMoment B raw19255step2 raw19255step2Labels := by
      have ha : raw19255step2 = raw19255step1 := by apply Matrix.ext; unfold raw19255step2 raw19255step1; decide +kernel
      have hl : raw19255step1Labels = labelEmbedding8 ∘ raw19255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19255step1 raw19255step1Labels raw19255step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical19256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19256 raw19256Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw19256 raw19256Labels = mixedMoment B raw19256step0 raw19256step0Labels := by
      have ha : raw19256step0 = (fun i j => raw19256 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19256step0 raw19256; decide +kernel
      have hl : raw19256step0Labels = raw19256Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19256 raw19256Labels permutation157 permutation3
    mixedMoment B raw19256step0 raw19256step0Labels = mixedMoment B raw19256step1 raw19256step1Labels := by
      have ha : raw19256step1 = raw19256step0 := by apply Matrix.ext; unfold raw19256step1 raw19256step0; decide +kernel
      have hl : raw19256step0Labels = labelEmbedding6 ∘ raw19256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19256step0 raw19256step0Labels raw19256step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical19257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19257 raw19257Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw19257 raw19257Labels = mixedMoment B raw19257step0 raw19257step0Labels := by
      have ha : raw19257step0 = (fun i j => raw19257 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19257step0 raw19257; decide +kernel
      have hl : raw19257step0Labels = raw19257Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19257 raw19257Labels permutation195 permutation5
    mixedMoment B raw19257step0 raw19257step0Labels = mixedMoment B raw19257step1 raw19257step1Labels := by
      have ha : raw19257step1 = -raw19257step0 := by apply Matrix.ext; change ∀ i j, raw19257step1 i j = -(raw19257step0 i j); unfold raw19257step1 raw19257step0; decide +kernel
      have hl : raw19257step1Labels = raw19257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19257step1 raw19257step1Labels = mixedMoment B raw19257step2 raw19257step2Labels := by
      have ha : raw19257step2 = raw19257step1 := by apply Matrix.ext; unfold raw19257step2 raw19257step1; decide +kernel
      have hl : raw19257step1Labels = labelEmbedding8 ∘ raw19257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19257step1 raw19257step1Labels raw19257step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical19258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19258 raw19258Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw19258 raw19258Labels = mixedMoment B raw19258step0 raw19258step0Labels := by
      have hz : ∀ j, raw19258 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19258step0 = (fun i j => raw19258 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19258step0 raw19258; decide +kernel
      have hl : raw19258step0Labels = raw19258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19258 raw19258Labels permutation520 hz
    mixedMoment B raw19258step0 raw19258step0Labels = mixedMoment B raw19258step1 raw19258step1Labels := by
      have ha : raw19258step1 = (fun i j => raw19258step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19258step1 raw19258step0; decide +kernel
      have hl : raw19258step1Labels = raw19258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19258step0 raw19258step0Labels permutation127 permutation3
    mixedMoment B raw19258step1 raw19258step1Labels = mixedMoment B raw19258step2 raw19258step2Labels := by
      have ha : raw19258step2 = -raw19258step1 := by apply Matrix.ext; change ∀ i j, raw19258step2 i j = -(raw19258step1 i j); unfold raw19258step2 raw19258step1; decide +kernel
      have hl : raw19258step2Labels = raw19258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19258step2 raw19258step2Labels = mixedMoment B raw19258step3 raw19258step3Labels := by
      have ha : raw19258step3 = raw19258step2 := by apply Matrix.ext; unfold raw19258step3 raw19258step2; decide +kernel
      have hl : raw19258step2Labels = labelEmbedding6 ∘ raw19258step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19258step2 raw19258step2Labels raw19258step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical19259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19259 raw19259Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw19259 raw19259Labels = mixedMoment B raw19259step0 raw19259step0Labels := by
      have ha : raw19259step0 = (fun i j => raw19259 (permutation492 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19259step0 raw19259; decide +kernel
      have hl : raw19259step0Labels = raw19259Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19259 raw19259Labels permutation492 permutation5
    mixedMoment B raw19259step0 raw19259step0Labels = mixedMoment B raw19259step1 raw19259step1Labels := by
      have ha : raw19259step1 = raw19259step0 := by apply Matrix.ext; unfold raw19259step1 raw19259step0; decide +kernel
      have hl : raw19259step0Labels = labelEmbedding8 ∘ raw19259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19259step0 raw19259step0Labels raw19259step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical19260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19260 raw19260Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw19260 raw19260Labels = mixedMoment B raw19260step0 raw19260step0Labels := by
      have ha : raw19260step0 = (fun i j => raw19260 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19260step0 raw19260; decide +kernel
      have hl : raw19260step0Labels = raw19260Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19260 raw19260Labels permutation194 permutation5
    mixedMoment B raw19260step0 raw19260step0Labels = mixedMoment B raw19260step1 raw19260step1Labels := by
      have ha : raw19260step1 = -raw19260step0 := by apply Matrix.ext; change ∀ i j, raw19260step1 i j = -(raw19260step0 i j); unfold raw19260step1 raw19260step0; decide +kernel
      have hl : raw19260step1Labels = raw19260step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19260step1 raw19260step1Labels = mixedMoment B raw19260step2 raw19260step2Labels := by
      have ha : raw19260step2 = raw19260step1 := by apply Matrix.ext; unfold raw19260step2 raw19260step1; decide +kernel
      have hl : raw19260step1Labels = labelEmbedding8 ∘ raw19260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19260step1 raw19260step1Labels raw19260step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical19261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19261 raw19261Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw19261 raw19261Labels = mixedMoment B raw19261step0 raw19261step0Labels := by
      have ha : raw19261step0 = (fun i j => raw19261 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19261step0 raw19261; decide +kernel
      have hl : raw19261step0Labels = raw19261Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19261 raw19261Labels permutation156 permutation3
    mixedMoment B raw19261step0 raw19261step0Labels = mixedMoment B raw19261step1 raw19261step1Labels := by
      have ha : raw19261step1 = raw19261step0 := by apply Matrix.ext; unfold raw19261step1 raw19261step0; decide +kernel
      have hl : raw19261step0Labels = labelEmbedding6 ∘ raw19261step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19261step0 raw19261step0Labels raw19261step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical19262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19262 raw19262Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw19262 raw19262Labels = mixedMoment B raw19262step0 raw19262step0Labels := by
      have ha : raw19262step0 = (fun i j => raw19262 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19262step0 raw19262; decide +kernel
      have hl : raw19262step0Labels = raw19262Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19262 raw19262Labels permutation194 permutation5
    mixedMoment B raw19262step0 raw19262step0Labels = mixedMoment B raw19262step1 raw19262step1Labels := by
      have ha : raw19262step1 = -raw19262step0 := by apply Matrix.ext; change ∀ i j, raw19262step1 i j = -(raw19262step0 i j); unfold raw19262step1 raw19262step0; decide +kernel
      have hl : raw19262step1Labels = raw19262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19262step1 raw19262step1Labels = mixedMoment B raw19262step2 raw19262step2Labels := by
      have ha : raw19262step2 = raw19262step1 := by apply Matrix.ext; unfold raw19262step2 raw19262step1; decide +kernel
      have hl : raw19262step1Labels = labelEmbedding8 ∘ raw19262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19262step1 raw19262step1Labels raw19262step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical19263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19263 raw19263Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw19263 raw19263Labels = mixedMoment B raw19263step0 raw19263step0Labels := by
      have hz : ∀ j, raw19263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19263step0 = (fun i j => raw19263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19263step0 raw19263; decide +kernel
      have hl : raw19263step0Labels = raw19263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19263 raw19263Labels permutation434 hz
    mixedMoment B raw19263step0 raw19263step0Labels = mixedMoment B raw19263step1 raw19263step1Labels := by
      have ha : raw19263step1 = (fun i j => raw19263step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19263step1 raw19263step0; decide +kernel
      have hl : raw19263step1Labels = raw19263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19263step0 raw19263step0Labels permutation127 permutation3
    mixedMoment B raw19263step1 raw19263step1Labels = mixedMoment B raw19263step2 raw19263step2Labels := by
      have ha : raw19263step2 = -raw19263step1 := by apply Matrix.ext; change ∀ i j, raw19263step2 i j = -(raw19263step1 i j); unfold raw19263step2 raw19263step1; decide +kernel
      have hl : raw19263step2Labels = raw19263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19263step2 raw19263step2Labels = mixedMoment B raw19263step3 raw19263step3Labels := by
      have ha : raw19263step3 = raw19263step2 := by apply Matrix.ext; unfold raw19263step3 raw19263step2; decide +kernel
      have hl : raw19263step2Labels = labelEmbedding6 ∘ raw19263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19263step2 raw19263step2Labels raw19263step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical19264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19264 raw19264Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw19264 raw19264Labels = mixedMoment B raw19264step0 raw19264step0Labels := by
      have ha : raw19264step0 = (fun i j => raw19264 (permutation557 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19264step0 raw19264; decide +kernel
      have hl : raw19264step0Labels = raw19264Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19264 raw19264Labels permutation557 permutation5
    mixedMoment B raw19264step0 raw19264step0Labels = mixedMoment B raw19264step1 raw19264step1Labels := by
      have ha : raw19264step1 = raw19264step0 := by apply Matrix.ext; unfold raw19264step1 raw19264step0; decide +kernel
      have hl : raw19264step0Labels = labelEmbedding8 ∘ raw19264step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19264step0 raw19264step0Labels raw19264step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical19265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19265 raw19265Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw19265 raw19265Labels = mixedMoment B raw19265step0 raw19265step0Labels := by
      have ha : raw19265step0 = (fun i j => raw19265 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19265step0 raw19265; decide +kernel
      have hl : raw19265step0Labels = raw19265Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19265 raw19265Labels permutation176 permutation5
    mixedMoment B raw19265step0 raw19265step0Labels = mixedMoment B raw19265step1 raw19265step1Labels := by
      have ha : raw19265step1 = -raw19265step0 := by apply Matrix.ext; change ∀ i j, raw19265step1 i j = -(raw19265step0 i j); unfold raw19265step1 raw19265step0; decide +kernel
      have hl : raw19265step1Labels = raw19265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19265step1 raw19265step1Labels = mixedMoment B raw19265step2 raw19265step2Labels := by
      have ha : raw19265step2 = raw19265step1 := by apply Matrix.ext; unfold raw19265step2 raw19265step1; decide +kernel
      have hl : raw19265step1Labels = labelEmbedding8 ∘ raw19265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19265step1 raw19265step1Labels raw19265step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical19266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19266 raw19266Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw19266 raw19266Labels = mixedMoment B raw19266step0 raw19266step0Labels := by
      have ha : raw19266step0 = (fun i j => raw19266 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19266step0 raw19266; decide +kernel
      have hl : raw19266step0Labels = raw19266Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19266 raw19266Labels permutation152 permutation3
    mixedMoment B raw19266step0 raw19266step0Labels = mixedMoment B raw19266step1 raw19266step1Labels := by
      have ha : raw19266step1 = raw19266step0 := by apply Matrix.ext; unfold raw19266step1 raw19266step0; decide +kernel
      have hl : raw19266step0Labels = labelEmbedding6 ∘ raw19266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19266step0 raw19266step0Labels raw19266step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical19267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19267 raw19267Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw19267 raw19267Labels = mixedMoment B raw19267step0 raw19267step0Labels := by
      have ha : raw19267step0 = (fun i j => raw19267 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19267step0 raw19267; decide +kernel
      have hl : raw19267step0Labels = raw19267Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19267 raw19267Labels permutation176 permutation5
    mixedMoment B raw19267step0 raw19267step0Labels = mixedMoment B raw19267step1 raw19267step1Labels := by
      have ha : raw19267step1 = -raw19267step0 := by apply Matrix.ext; change ∀ i j, raw19267step1 i j = -(raw19267step0 i j); unfold raw19267step1 raw19267step0; decide +kernel
      have hl : raw19267step1Labels = raw19267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19267step1 raw19267step1Labels = mixedMoment B raw19267step2 raw19267step2Labels := by
      have ha : raw19267step2 = raw19267step1 := by apply Matrix.ext; unfold raw19267step2 raw19267step1; decide +kernel
      have hl : raw19267step1Labels = labelEmbedding8 ∘ raw19267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19267step1 raw19267step1Labels raw19267step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

theorem canonical19268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19268 raw19268Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw19268 raw19268Labels = mixedMoment B raw19268step0 raw19268step0Labels := by
      have hz : ∀ j, raw19268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19268step0 = (fun i j => raw19268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19268step0 raw19268; decide +kernel
      have hl : raw19268step0Labels = raw19268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19268 raw19268Labels permutation434 hz
    mixedMoment B raw19268step0 raw19268step0Labels = mixedMoment B raw19268step1 raw19268step1Labels := by
      have ha : raw19268step1 = (fun i j => raw19268step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19268step1 raw19268step0; decide +kernel
      have hl : raw19268step1Labels = raw19268step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19268step0 raw19268step0Labels permutation38 permutation5
    mixedMoment B raw19268step1 raw19268step1Labels = mixedMoment B raw19268step2 raw19268step2Labels := by
      have ha : raw19268step2 = -raw19268step1 := by apply Matrix.ext; change ∀ i j, raw19268step2 i j = -(raw19268step1 i j); unfold raw19268step2 raw19268step1; decide +kernel
      have hl : raw19268step2Labels = raw19268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19268step2 raw19268step2Labels = mixedMoment B raw19268step3 raw19268step3Labels := by
      have ha : raw19268step3 = raw19268step2 := by apply Matrix.ext; unfold raw19268step3 raw19268step2; decide +kernel
      have hl : raw19268step2Labels = labelEmbedding8 ∘ raw19268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19268step2 raw19268step2Labels raw19268step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical19269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19269 raw19269Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw19269 raw19269Labels = mixedMoment B raw19269step0 raw19269step0Labels := by
      have hz : ∀ j, raw19269 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19269step0 = (fun i j => raw19269 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19269step0 raw19269; decide +kernel
      have hl : raw19269step0Labels = raw19269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19269 raw19269Labels permutation520 hz
    mixedMoment B raw19269step0 raw19269step0Labels = mixedMoment B raw19269step1 raw19269step1Labels := by
      have ha : raw19269step1 = (fun i j => raw19269step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19269step1 raw19269step0; decide +kernel
      have hl : raw19269step1Labels = raw19269step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19269step0 raw19269step0Labels permutation38 permutation5
    mixedMoment B raw19269step1 raw19269step1Labels = mixedMoment B raw19269step2 raw19269step2Labels := by
      have ha : raw19269step2 = -raw19269step1 := by apply Matrix.ext; change ∀ i j, raw19269step2 i j = -(raw19269step1 i j); unfold raw19269step2 raw19269step1; decide +kernel
      have hl : raw19269step2Labels = raw19269step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19269step2 raw19269step2Labels = mixedMoment B raw19269step3 raw19269step3Labels := by
      have ha : raw19269step3 = raw19269step2 := by apply Matrix.ext; unfold raw19269step3 raw19269step2; decide +kernel
      have hl : raw19269step2Labels = labelEmbedding8 ∘ raw19269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19269step2 raw19269step2Labels raw19269step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

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

theorem canonical2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2388 raw2388Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw2388 raw2388Labels = mixedMoment B raw2388step0 raw2388step0Labels := by
      have ha : raw2388step0 = (fun i j => raw2388 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2388step0 raw2388; decide +kernel
      have hl : raw2388step0Labels = raw2388Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2388 raw2388Labels permutation152 permutation4
    mixedMoment B raw2388step0 raw2388step0Labels = mixedMoment B raw2388step1 raw2388step1Labels := by
      have ha : raw2388step1 = raw2388step0 := by apply Matrix.ext; unfold raw2388step1 raw2388step0; decide +kernel
      have hl : raw2388step0Labels = labelEmbedding7 ∘ raw2388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2388step0 raw2388step0Labels raw2388step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical2389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2389 raw2389Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw2389 raw2389Labels = mixedMoment B raw2389step0 raw2389step0Labels := by
      have ha : raw2389step0 = (fun i j => raw2389 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2389step0 raw2389; decide +kernel
      have hl : raw2389step0Labels = raw2389Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2389 raw2389Labels permutation152 permutation4
    _ = mixedMoment B node3687 node3687Labels := by rfl

theorem canonical2390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2390 raw2390Labels = mixedMoment B node3749 node3749Labels := by
  calc
    mixedMoment B raw2390 raw2390Labels = mixedMoment B raw2390step0 raw2390step0Labels := by
      have ha : raw2390step0 = (fun i j => raw2390 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2390step0 raw2390; decide +kernel
      have hl : raw2390step0Labels = raw2390Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2390 raw2390Labels permutation158 permutation6
    mixedMoment B raw2390step0 raw2390step0Labels = mixedMoment B raw2390step1 raw2390step1Labels := by
      have ha : raw2390step1 = -raw2390step0 := by apply Matrix.ext; change ∀ i j, raw2390step1 i j = -(raw2390step0 i j); unfold raw2390step1 raw2390step0; decide +kernel
      have hl : raw2390step1Labels = raw2390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2390step1 raw2390step1Labels = mixedMoment B raw2390step2 raw2390step2Labels := by
      have ha : raw2390step2 = raw2390step1 := by apply Matrix.ext; unfold raw2390step2 raw2390step1; decide +kernel
      have hl : raw2390step1Labels = labelEmbedding1 ∘ raw2390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2390step1 raw2390step1Labels raw2390step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3749 node3749Labels := by rfl

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

theorem canonical2406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2406 raw2406Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw2406 raw2406Labels = mixedMoment B raw2406step0 raw2406step0Labels := by
      have ha : raw2406step0 = (fun i j => raw2406 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2406step0 raw2406; decide +kernel
      have hl : raw2406step0Labels = raw2406Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2406 raw2406Labels permutation152 permutation4
    mixedMoment B raw2406step0 raw2406step0Labels = mixedMoment B raw2406step1 raw2406step1Labels := by
      have ha : raw2406step1 = raw2406step0 := by apply Matrix.ext; unfold raw2406step1 raw2406step0; decide +kernel
      have hl : raw2406step0Labels = labelEmbedding7 ∘ raw2406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2406step0 raw2406step0Labels raw2406step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

theorem canonical2407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2407 raw2407Labels = mixedMoment B node3701 node3701Labels := by
  calc
    mixedMoment B raw2407 raw2407Labels = mixedMoment B raw2407step0 raw2407step0Labels := by
      have ha : raw2407step0 = (fun i j => raw2407 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2407step0 raw2407; decide +kernel
      have hl : raw2407step0Labels = raw2407Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2407 raw2407Labels permutation152 permutation4
    _ = mixedMoment B node3701 node3701Labels := by rfl

theorem canonical2408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2408 raw2408Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw2408 raw2408Labels = mixedMoment B raw2408step0 raw2408step0Labels := by
      have ha : raw2408step0 = (fun i j => raw2408 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2408step0 raw2408; decide +kernel
      have hl : raw2408step0Labels = raw2408Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2408 raw2408Labels permutation152 permutation6
    mixedMoment B raw2408step0 raw2408step0Labels = mixedMoment B raw2408step1 raw2408step1Labels := by
      have ha : raw2408step1 = -raw2408step0 := by apply Matrix.ext; change ∀ i j, raw2408step1 i j = -(raw2408step0 i j); unfold raw2408step1 raw2408step0; decide +kernel
      have hl : raw2408step1Labels = raw2408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2408step1 raw2408step1Labels = mixedMoment B raw2408step2 raw2408step2Labels := by
      have ha : raw2408step2 = raw2408step1 := by apply Matrix.ext; unfold raw2408step2 raw2408step1; decide +kernel
      have hl : raw2408step1Labels = labelEmbedding1 ∘ raw2408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2408step1 raw2408step1Labels raw2408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3751 node3751Labels := by rfl

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

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

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2433 raw2433Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw2433 raw2433Labels = mixedMoment B raw2433step0 raw2433step0Labels := by
      have ha : raw2433step0 = (fun i j => raw2433 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2433step0 raw2433; decide +kernel
      have hl : raw2433step0Labels = raw2433Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2433 raw2433Labels permutation152 permutation4
    mixedMoment B raw2433step0 raw2433step0Labels = mixedMoment B raw2433step1 raw2433step1Labels := by
      have ha : raw2433step1 = raw2433step0 := by apply Matrix.ext; unfold raw2433step1 raw2433step0; decide +kernel
      have hl : raw2433step0Labels = labelEmbedding7 ∘ raw2433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2433step0 raw2433step0Labels raw2433step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2434 raw2434Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw2434 raw2434Labels = mixedMoment B raw2434step0 raw2434step0Labels := by
      have ha : raw2434step0 = (fun i j => raw2434 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2434step0 raw2434; decide +kernel
      have hl : raw2434step0Labels = raw2434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2434 raw2434Labels permutation152 permutation4
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2435 raw2435Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw2435 raw2435Labels = mixedMoment B raw2435step0 raw2435step0Labels := by
      have ha : raw2435step0 = (fun i j => raw2435 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2435step0 raw2435; decide +kernel
      have hl : raw2435step0Labels = raw2435Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2435 raw2435Labels permutation176 permutation6
    mixedMoment B raw2435step0 raw2435step0Labels = mixedMoment B raw2435step1 raw2435step1Labels := by
      have ha : raw2435step1 = -raw2435step0 := by apply Matrix.ext; change ∀ i j, raw2435step1 i j = -(raw2435step0 i j); unfold raw2435step1 raw2435step0; decide +kernel
      have hl : raw2435step1Labels = raw2435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2435step1 raw2435step1Labels = mixedMoment B raw2435step2 raw2435step2Labels := by
      have ha : raw2435step2 = raw2435step1 := by apply Matrix.ext; unfold raw2435step2 raw2435step1; decide +kernel
      have hl : raw2435step1Labels = labelEmbedding1 ∘ raw2435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2435step1 raw2435step1Labels raw2435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

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

theorem canonical2523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2523 raw2523Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw2523 raw2523Labels = mixedMoment B raw2523step0 raw2523step0Labels := by
      have ha : raw2523step0 = (fun i j => raw2523 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2523step0 raw2523; decide +kernel
      have hl : raw2523step0Labels = raw2523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2523 raw2523Labels permutation32 permutation4
    mixedMoment B raw2523step0 raw2523step0Labels = mixedMoment B raw2523step1 raw2523step1Labels := by
      have ha : raw2523step1 = raw2523step0 := by apply Matrix.ext; unfold raw2523step1 raw2523step0; decide +kernel
      have hl : raw2523step0Labels = labelEmbedding7 ∘ raw2523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2523step0 raw2523step0Labels raw2523step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2524 raw2524Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2524 raw2524Labels = mixedMoment B raw2524step0 raw2524step0Labels := by
      have ha : raw2524step0 = (fun i j => raw2524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2524step0 raw2524; decide +kernel
      have hl : raw2524step0Labels = raw2524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2524 raw2524Labels permutation32 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical2525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2525 raw2525Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2525 raw2525Labels = mixedMoment B raw2525step0 raw2525step0Labels := by
      have ha : raw2525step0 = (fun i j => raw2525 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2525step0 raw2525; decide +kernel
      have hl : raw2525step0Labels = raw2525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2525 raw2525Labels permutation143 permutation6
    mixedMoment B raw2525step0 raw2525step0Labels = mixedMoment B raw2525step1 raw2525step1Labels := by
      have ha : raw2525step1 = raw2525step0 := by apply Matrix.ext; unfold raw2525step1 raw2525step0; decide +kernel
      have hl : raw2525step0Labels = labelEmbedding1 ∘ raw2525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2525step0 raw2525step0Labels raw2525step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton5349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5349 node5349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3687 node3687Labels + mixedMoment B node3749 node3749Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2388 singletonSmall5349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5349) = raw2388Labels := by decide +kernel
  rw [hl, canonical2388 B hB] at h
  have hc0 : mixedMoment B raw2388 (Fin.cases (0 : Fin 2) singletonSmall5349) =
      mixedMoment B node3687 node3687Labels := by
    have ha : raw2388 = raw2389 := by apply Matrix.ext; unfold raw2388 raw2389; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5349 = raw2389Labels := by decide +kernel
    rw [ha, hj, canonical2389 B hB]
  have hc1 : mixedMoment B raw2388 (Fin.cases (1 : Fin 2) singletonSmall5349) =
      mixedMoment B node3749 node3749Labels := by
    have ha : raw2388 = raw2390 := by apply Matrix.ext; unfold raw2388 raw2390; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5349 = raw2390Labels := by decide +kernel
    rw [ha, hj, canonical2390 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5363 node5363Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3701 node3701Labels + mixedMoment B node3751 node3751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2406 singletonSmall5363
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5363) = raw2406Labels := by decide +kernel
  rw [hl, canonical2406 B hB] at h
  have hc0 : mixedMoment B raw2406 (Fin.cases (0 : Fin 2) singletonSmall5363) =
      mixedMoment B node3701 node3701Labels := by
    have ha : raw2406 = raw2407 := by apply Matrix.ext; unfold raw2406 raw2407; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5363 = raw2407Labels := by decide +kernel
    rw [ha, hj, canonical2407 B hB]
  have hc1 : mixedMoment B raw2406 (Fin.cases (1 : Fin 2) singletonSmall5363) =
      mixedMoment B node3751 node3751Labels := by
    have ha : raw2406 = raw2408 := by apply Matrix.ext; unfold raw2406 raw2408; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5363 = raw2408Labels := by decide +kernel
    rw [ha, hj, canonical2408 B hB]
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

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5380 node5380Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3721 node3721Labels + mixedMoment B node3836 node3836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2433 singletonSmall5380
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5380) = raw2433Labels := by decide +kernel
  rw [hl, canonical2433 B hB] at h
  have hc0 : mixedMoment B raw2433 (Fin.cases (0 : Fin 2) singletonSmall5380) =
      mixedMoment B node3721 node3721Labels := by
    have ha : raw2433 = raw2434 := by apply Matrix.ext; unfold raw2433 raw2434; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5380 = raw2434Labels := by decide +kernel
    rw [ha, hj, canonical2434 B hB]
  have hc1 : mixedMoment B raw2433 (Fin.cases (1 : Fin 2) singletonSmall5380) =
      mixedMoment B node3836 node3836Labels := by
    have ha : raw2433 = raw2435 := by apply Matrix.ext; unfold raw2433 raw2435; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5380 = raw2435Labels := by decide +kernel
    rw [ha, hj, canonical2435 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5432 node5432Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3850 node3850Labels + mixedMoment B node3850 node3850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2523 singletonSmall5432
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5432) = raw2523Labels := by decide +kernel
  rw [hl, canonical2523 B hB] at h
  have hc0 : mixedMoment B raw2523 (Fin.cases (0 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2524 := by apply Matrix.ext; unfold raw2523 raw2524; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5432 = raw2524Labels := by decide +kernel
    rw [ha, hj, canonical2524 B hB]
  have hc1 : mixedMoment B raw2523 (Fin.cases (1 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2525 := by apply Matrix.ext; unfold raw2523 raw2525; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5432 = raw2525Labels := by decide +kernel
    rw [ha, hj, canonical2525 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = 0 := by
  exact mixedMoment_alpha B hF node5481 node5481Labels 2 permutation158
    (by decide +kernel)

theorem zero5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = 0 := by
  exact mixedMoment_alpha B hF node5489 node5489Labels 2 permutation152
    (by decide +kernel)

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

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

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

theorem sound3687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3687 node3687Labels = Sparse.eval nodeValue3687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3687) = mixedMoment B node3687 node3687Labels := rfl
  simpa [nodeValue3687, Sparse.eval] using hc.symm

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

theorem sound3701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3701 node3701Labels = Sparse.eval nodeValue3701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3701) = mixedMoment B node3701 node3701Labels := rfl
  simpa [nodeValue3701, Sparse.eval] using hc.symm

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

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3749 node3749Labels = Sparse.eval nodeValue3749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3749) = mixedMoment B node3749 node3749Labels := rfl
  simpa [nodeValue3749, Sparse.eval] using hc.symm

theorem sound3751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3751 node3751Labels = Sparse.eval nodeValue3751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3751) = mixedMoment B node3751 node3751Labels := rfl
  simpa [nodeValue3751, Sparse.eval] using hc.symm

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

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

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

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

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

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

theorem sound4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4826 node4826Labels = Sparse.eval nodeValue4826 (mixedVector B) := by
  have h := singleton4826 B _hB
  rw [sound2046 B _hB _hF, sound2077 B _hB _hF] at h
  norm_num [nodeValue4826, nodeValue2046, nodeValue2077, Sparse.eval] at h ⊢
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

theorem sound5349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5349 node5349Labels = Sparse.eval nodeValue5349 (mixedVector B) := by
  have h := singleton5349 B _hB
  rw [sound3687 B _hB _hF, sound3749 B _hB _hF] at h
  norm_num [nodeValue5349, nodeValue3687, nodeValue3749, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5354 node5354Labels = Sparse.eval nodeValue5354 (mixedVector B) := by
  have h := singleton5354 B _hB
  rw [sound3692 B _hB _hF, sound3769 B _hB _hF] at h
  norm_num [nodeValue5354, nodeValue3692, nodeValue3769, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5363 node5363Labels = Sparse.eval nodeValue5363 (mixedVector B) := by
  have h := singleton5363 B _hB
  rw [sound3701 B _hB _hF, sound3751 B _hB _hF] at h
  norm_num [nodeValue5363, nodeValue3701, nodeValue3751, Sparse.eval] at h ⊢
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

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5380 node5380Labels = Sparse.eval nodeValue5380 (mixedVector B) := by
  have h := singleton5380 B _hB
  rw [sound3721 B _hB _hF, sound3836 B _hB _hF] at h
  norm_num [nodeValue5380, nodeValue3721, nodeValue3836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5400 node5400Labels = Sparse.eval nodeValue5400 (mixedVector B) := by
  have h := singleton5400 B _hB
  rw [sound3786 B _hB _hF, sound3799 B _hB _hF] at h
  norm_num [nodeValue5400, nodeValue3786, nodeValue3799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5432 node5432Labels = Sparse.eval nodeValue5432 (mixedVector B) := by
  have h := singleton5432 B _hB
  rw [sound3850 B _hB _hF] at h
  norm_num [nodeValue5432, nodeValue3850, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

theorem sound5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = Sparse.eval nodeValue5489 (mixedVector B) := by
  simpa only [nodeValue5489, Sparse.eval_nil] using zero5489 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1134 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 1) (sourceB1134 + difference 1 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 1) (sourceB1134 + difference 1 0) sourceC1134) = raw19240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19240; decide +kernel
    rw [ha]
    exact (canonical19240 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 2) (sourceB1134 + difference 2 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 2) (sourceB1134 + difference 2 0) sourceC1134) = raw19241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19241; decide +kernel
    rw [ha]
    exact (canonical19241 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 3) (sourceB1134 + difference 3 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 3) (sourceB1134 + difference 3 0) sourceC1134) = raw19242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19242; decide +kernel
    rw [ha]
    exact (canonical19242 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 4) (sourceB1134 + difference 4 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 4) (sourceB1134 + difference 4 0) sourceC1134) = raw19243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19243; decide +kernel
    rw [ha]
    exact (canonical19243 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1134 + difference 0 5) (sourceB1134 + difference 5 0) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1134 + difference 0 5) (sourceB1134 + difference 5 0) sourceC1134) = raw19244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19244; decide +kernel
    rw [ha]
    exact (canonical19244 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 0) (sourceB1134 + difference 0 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 0) (sourceB1134 + difference 0 1) sourceC1134) = raw19245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19245; decide +kernel
    rw [ha]
    exact (canonical19245 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 2) (sourceB1134 + difference 2 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 2) (sourceB1134 + difference 2 1) sourceC1134) = raw19246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19246; decide +kernel
    rw [ha]
    exact (canonical19246 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 3) (sourceB1134 + difference 3 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 3) (sourceB1134 + difference 3 1) sourceC1134) = raw19247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19247; decide +kernel
    rw [ha]
    exact (canonical19247 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 4) (sourceB1134 + difference 4 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 4) (sourceB1134 + difference 4 1) sourceC1134) = raw19248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19248; decide +kernel
    rw [ha]
    exact (canonical19248 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1134 + difference 1 5) (sourceB1134 + difference 5 1) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA1134 + difference 1 5) (sourceB1134 + difference 5 1) sourceC1134) = raw19249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19249; decide +kernel
    rw [ha]
    exact (canonical19249 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 0) (sourceB1134 + difference 0 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 0) (sourceB1134 + difference 0 2) sourceC1134) = raw19250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19250; decide +kernel
    rw [ha]
    exact (canonical19250 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 1) (sourceB1134 + difference 1 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 1) (sourceB1134 + difference 1 2) sourceC1134) = raw19251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19251; decide +kernel
    rw [ha]
    exact (canonical19251 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 3) (sourceB1134 + difference 3 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 3) (sourceB1134 + difference 3 2) sourceC1134) = raw19252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19252; decide +kernel
    rw [ha]
    exact (canonical19252 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 4) (sourceB1134 + difference 4 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 4) (sourceB1134 + difference 4 2) sourceC1134) = raw19253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19253; decide +kernel
    rw [ha]
    exact (canonical19253 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1134 + difference 2 5) (sourceB1134 + difference 5 2) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1134 + difference 2 5) (sourceB1134 + difference 5 2) sourceC1134) = raw19254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19254; decide +kernel
    rw [ha]
    exact (canonical19254 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 0) (sourceB1134 + difference 0 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 0) (sourceB1134 + difference 0 3) sourceC1134) = raw19255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19255; decide +kernel
    rw [ha]
    exact (canonical19255 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 1) (sourceB1134 + difference 1 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 1) (sourceB1134 + difference 1 3) sourceC1134) = raw19256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19256; decide +kernel
    rw [ha]
    exact (canonical19256 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 2) (sourceB1134 + difference 2 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 2) (sourceB1134 + difference 2 3) sourceC1134) = raw19257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19257; decide +kernel
    rw [ha]
    exact (canonical19257 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 4) (sourceB1134 + difference 4 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 4) (sourceB1134 + difference 4 3) sourceC1134) = raw19258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19258; decide +kernel
    rw [ha]
    exact (canonical19258 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1134 + difference 3 5) (sourceB1134 + difference 5 3) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1134 + difference 3 5) (sourceB1134 + difference 5 3) sourceC1134) = raw19259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19259; decide +kernel
    rw [ha]
    exact (canonical19259 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 0) (sourceB1134 + difference 0 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 0) (sourceB1134 + difference 0 4) sourceC1134) = raw19260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19260; decide +kernel
    rw [ha]
    exact (canonical19260 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 1) (sourceB1134 + difference 1 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 1) (sourceB1134 + difference 1 4) sourceC1134) = raw19261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19261; decide +kernel
    rw [ha]
    exact (canonical19261 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 2) (sourceB1134 + difference 2 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 2) (sourceB1134 + difference 2 4) sourceC1134) = raw19262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19262; decide +kernel
    rw [ha]
    exact (canonical19262 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 3) (sourceB1134 + difference 3 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 3) (sourceB1134 + difference 3 4) sourceC1134) = raw19263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19263; decide +kernel
    rw [ha]
    exact (canonical19263 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1134 + difference 4 5) (sourceB1134 + difference 5 4) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1134 + difference 4 5) (sourceB1134 + difference 5 4) sourceC1134) = raw19264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19264; decide +kernel
    rw [ha]
    exact (canonical19264 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 0) (sourceB1134 + difference 0 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 0) (sourceB1134 + difference 0 5) sourceC1134) = raw19265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19265; decide +kernel
    rw [ha]
    exact (canonical19265 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 1) (sourceB1134 + difference 1 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 1) (sourceB1134 + difference 1 5) sourceC1134) = raw19266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19266; decide +kernel
    rw [ha]
    exact (canonical19266 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 2) (sourceB1134 + difference 2 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 2) (sourceB1134 + difference 2 5) sourceC1134) = raw19267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19267; decide +kernel
    rw [ha]
    exact (canonical19267 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 3) (sourceB1134 + difference 3 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 3) (sourceB1134 + difference 3 5) sourceC1134) = raw19268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19268; decide +kernel
    rw [ha]
    exact (canonical19268 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1134 + difference 5 4) (sourceB1134 + difference 4 5) sourceC1134) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1134 + difference 5 4) (sourceB1134 + difference 4 5) sourceC1134) = raw19269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1134 sourceB1134 sourceC1134 difference raw19269; decide +kernel
    rw [ha]
    exact (canonical19269 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1134 sourceB1134 sourceC1134
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1134, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck986 : Integer.Sparse.reindex keyMap MixedData.row986 = numericRow986 := by decide +kernel

theorem numericCheck986 (x : Master → ℝ) : Integer.Sparse.eval numericRow986 x =
    (51840 : ℝ) * reducedSource986 x := by
  norm_num [numericRow986, reducedSource986, Integer.Sparse.eval, Sparse.eval, nodeValue4798, nodeValue4805, nodeValue4826, nodeValue4864, nodeValue5349, nodeValue5354, nodeValue5363, nodeValue5378, nodeValue5380, nodeValue5386, nodeValue5400, nodeValue5417, nodeValue5431, nodeValue5432, nodeValue5433, nodeValue5435, nodeValue5438, nodeValue5450, nodeValue5481, nodeValue5489, nodeValue5490]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource986 (mixedVector B) = 0 := by
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h5349 : mixedVector B (Sum.inr 5349) = Sparse.eval nodeValue5349 (mixedVector B) := by
    change mixedMoment B node5349 node5349Labels = _
    exact sound5349 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5363 : mixedVector B (Sum.inr 5363) = Sparse.eval nodeValue5363 (mixedVector B) := by
    change mixedMoment B node5363 node5363Labels = _
    exact sound5363 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386_e B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5417 : mixedVector B (Sum.inr 5417) = Sparse.eval nodeValue5417 (mixedVector B) := by
    change mixedMoment B node5417 node5417Labels = _
    exact sound5417_e B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  simpa only [sourceForm1134, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4798, h4805, h4826, h4864, h5349, h5354, h5363, h5378, h5380, h5386, h5400, h5417, h5431, h5432, h5433, h5435, h5438, h5450, h5481, h5489, h5490, reducedSource986] using sourceEq1134 B hB

theorem rowSound986_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row986 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck986, numericCheck986, reducedZero986 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound986_e_oai
