-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:26:41.538695+00:00
-- url     : https://prove2.me/submissions/8bf8d24d-bcc5-4958-8bc3-10a2a78cc68e

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
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5387_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1569 raw1569Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw1569 raw1569Labels = mixedMoment B raw1569step0 raw1569step0Labels := by
      have ha : raw1569step0 = (fun i j => raw1569 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1569step0 raw1569; decide +kernel
      have hl : raw1569step0Labels = raw1569Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1569 raw1569Labels permutation152 permutation4
    mixedMoment B raw1569step0 raw1569step0Labels = mixedMoment B raw1569step1 raw1569step1Labels := by
      have ha : raw1569step1 = raw1569step0 := by apply Matrix.ext; unfold raw1569step1 raw1569step0; decide +kernel
      have hl : raw1569step0Labels = labelEmbedding7 ∘ raw1569step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1569step0 raw1569step0Labels raw1569step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4685 node4685Labels := by rfl

theorem canonical1570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1570 raw1570Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw1570 raw1570Labels = mixedMoment B raw1570step0 raw1570step0Labels := by
      have ha : raw1570step0 = (fun i j => raw1570 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1570step0 raw1570; decide +kernel
      have hl : raw1570step0Labels = raw1570Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1570 raw1570Labels permutation152 permutation4
    _ = mixedMoment B node1811 node1811Labels := by rfl

theorem canonical1571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1571 raw1571Labels = mixedMoment B node2156 node2156Labels := by
  calc
    mixedMoment B raw1571 raw1571Labels = mixedMoment B raw1571step0 raw1571step0Labels := by
      have ha : raw1571step0 = (fun i j => raw1571 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1571step0 raw1571; decide +kernel
      have hl : raw1571step0Labels = raw1571Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1571 raw1571Labels permutation170 permutation6
    mixedMoment B raw1571step0 raw1571step0Labels = mixedMoment B raw1571step1 raw1571step1Labels := by
      have ha : raw1571step1 = -raw1571step0 := by apply Matrix.ext; change ∀ i j, raw1571step1 i j = -(raw1571step0 i j); unfold raw1571step1 raw1571step0; decide +kernel
      have hl : raw1571step1Labels = raw1571step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1571step1 raw1571step1Labels = mixedMoment B raw1571step2 raw1571step2Labels := by
      have ha : raw1571step2 = raw1571step1 := by apply Matrix.ext; unfold raw1571step2 raw1571step1; decide +kernel
      have hl : raw1571step1Labels = labelEmbedding1 ∘ raw1571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1571step1 raw1571step1Labels raw1571step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2156 node2156Labels := by rfl

theorem canonical1572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1572 raw1572Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw1572 raw1572Labels = mixedMoment B raw1572step0 raw1572step0Labels := by
      have ha : raw1572step0 = (fun i j => raw1572 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1572step0 raw1572; decide +kernel
      have hl : raw1572step0Labels = raw1572Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1572 raw1572Labels permutation32 permutation4
    mixedMoment B raw1572step0 raw1572step0Labels = mixedMoment B raw1572step1 raw1572step1Labels := by
      have ha : raw1572step1 = raw1572step0 := by apply Matrix.ext; unfold raw1572step1 raw1572step0; decide +kernel
      have hl : raw1572step0Labels = labelEmbedding7 ∘ raw1572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1572step0 raw1572step0Labels raw1572step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

theorem canonical1573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1573 raw1573Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw1573 raw1573Labels = mixedMoment B raw1573step0 raw1573step0Labels := by
      have ha : raw1573step0 = (fun i j => raw1573 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1573step0 raw1573; decide +kernel
      have hl : raw1573step0Labels = raw1573Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1573 raw1573Labels permutation32 permutation4
    _ = mixedMoment B node1812 node1812Labels := by rfl

theorem canonical1574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1574 raw1574Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw1574 raw1574Labels = mixedMoment B raw1574step0 raw1574step0Labels := by
      have ha : raw1574step0 = (fun i j => raw1574 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1574step0 raw1574; decide +kernel
      have hl : raw1574step0Labels = raw1574Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1574 raw1574Labels permutation32 permutation6
    mixedMoment B raw1574step0 raw1574step0Labels = mixedMoment B raw1574step1 raw1574step1Labels := by
      have ha : raw1574step1 = -raw1574step0 := by apply Matrix.ext; change ∀ i j, raw1574step1 i j = -(raw1574step0 i j); unfold raw1574step1 raw1574step0; decide +kernel
      have hl : raw1574step1Labels = raw1574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1574step1 raw1574step1Labels = mixedMoment B raw1574step2 raw1574step2Labels := by
      have ha : raw1574step2 = raw1574step1 := by apply Matrix.ext; unfold raw1574step2 raw1574step1; decide +kernel
      have hl : raw1574step1Labels = labelEmbedding1 ∘ raw1574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1574step1 raw1574step1Labels raw1574step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2165 node2165Labels := by rfl

theorem canonical1575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1575 raw1575Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw1575 raw1575Labels = mixedMoment B raw1575step0 raw1575step0Labels := by
      have ha : raw1575step0 = (fun i j => raw1575 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1575step0 raw1575; decide +kernel
      have hl : raw1575step0Labels = raw1575Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1575 raw1575Labels permutation32 permutation4
    mixedMoment B raw1575step0 raw1575step0Labels = mixedMoment B raw1575step1 raw1575step1Labels := by
      have ha : raw1575step1 = raw1575step0 := by apply Matrix.ext; unfold raw1575step1 raw1575step0; decide +kernel
      have hl : raw1575step0Labels = labelEmbedding7 ∘ raw1575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1575step0 raw1575step0Labels raw1575step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

theorem canonical1576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1576 raw1576Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw1576 raw1576Labels = mixedMoment B raw1576step0 raw1576step0Labels := by
      have ha : raw1576step0 = (fun i j => raw1576 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1576step0 raw1576; decide +kernel
      have hl : raw1576step0Labels = raw1576Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1576 raw1576Labels permutation32 permutation4
    _ = mixedMoment B node1814 node1814Labels := by rfl

theorem canonical1577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1577 raw1577Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw1577 raw1577Labels = mixedMoment B raw1577step0 raw1577step0Labels := by
      have ha : raw1577step0 = (fun i j => raw1577 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1577step0 raw1577; decide +kernel
      have hl : raw1577step0Labels = raw1577Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1577 raw1577Labels permutation34 permutation6
    mixedMoment B raw1577step0 raw1577step0Labels = mixedMoment B raw1577step1 raw1577step1Labels := by
      have ha : raw1577step1 = -raw1577step0 := by apply Matrix.ext; change ∀ i j, raw1577step1 i j = -(raw1577step0 i j); unfold raw1577step1 raw1577step0; decide +kernel
      have hl : raw1577step1Labels = raw1577step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1577step1 raw1577step1Labels = mixedMoment B raw1577step2 raw1577step2Labels := by
      have ha : raw1577step2 = raw1577step1 := by apply Matrix.ext; unfold raw1577step2 raw1577step1; decide +kernel
      have hl : raw1577step1Labels = labelEmbedding1 ∘ raw1577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1577step1 raw1577step1Labels raw1577step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

theorem canonical1626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1626 raw1626Labels = mixedMoment B node4723 node4723Labels := by
  calc
    mixedMoment B raw1626 raw1626Labels = mixedMoment B raw1626step0 raw1626step0Labels := by
      have ha : raw1626step0 = (fun i j => raw1626 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1626step0 raw1626; decide +kernel
      have hl : raw1626step0Labels = raw1626Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1626 raw1626Labels permutation152 permutation4
    mixedMoment B raw1626step0 raw1626step0Labels = mixedMoment B raw1626step1 raw1626step1Labels := by
      have ha : raw1626step1 = raw1626step0 := by apply Matrix.ext; unfold raw1626step1 raw1626step0; decide +kernel
      have hl : raw1626step0Labels = labelEmbedding7 ∘ raw1626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1626step0 raw1626step0Labels raw1626step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4723 node4723Labels := by rfl

theorem canonical1627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1627 raw1627Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw1627 raw1627Labels = mixedMoment B raw1627step0 raw1627step0Labels := by
      have ha : raw1627step0 = (fun i j => raw1627 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1627step0 raw1627; decide +kernel
      have hl : raw1627step0Labels = raw1627Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1627 raw1627Labels permutation152 permutation4
    _ = mixedMoment B node1877 node1877Labels := by rfl

theorem canonical1628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1628 raw1628Labels = mixedMoment B node1935 node1935Labels := by
  calc
    mixedMoment B raw1628 raw1628Labels = mixedMoment B raw1628step0 raw1628step0Labels := by
      have ha : raw1628step0 = (fun i j => raw1628 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1628step0 raw1628; decide +kernel
      have hl : raw1628step0Labels = raw1628Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1628 raw1628Labels permutation152 permutation6
    mixedMoment B raw1628step0 raw1628step0Labels = mixedMoment B raw1628step1 raw1628step1Labels := by
      have ha : raw1628step1 = -raw1628step0 := by apply Matrix.ext; change ∀ i j, raw1628step1 i j = -(raw1628step0 i j); unfold raw1628step1 raw1628step0; decide +kernel
      have hl : raw1628step1Labels = raw1628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1628step1 raw1628step1Labels = mixedMoment B raw1628step2 raw1628step2Labels := by
      have ha : raw1628step2 = raw1628step1 := by apply Matrix.ext; unfold raw1628step2 raw1628step1; decide +kernel
      have hl : raw1628step1Labels = labelEmbedding1 ∘ raw1628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1628step1 raw1628step1Labels raw1628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1935 node1935Labels := by rfl

theorem canonical1629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1629 raw1629Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw1629 raw1629Labels = mixedMoment B raw1629step0 raw1629step0Labels := by
      have ha : raw1629step0 = (fun i j => raw1629 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1629step0 raw1629; decide +kernel
      have hl : raw1629step0Labels = raw1629Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1629 raw1629Labels permutation152 permutation4
    mixedMoment B raw1629step0 raw1629step0Labels = mixedMoment B raw1629step1 raw1629step1Labels := by
      have ha : raw1629step1 = raw1629step0 := by apply Matrix.ext; unfold raw1629step1 raw1629step0; decide +kernel
      have hl : raw1629step0Labels = labelEmbedding7 ∘ raw1629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1629step0 raw1629step0Labels raw1629step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

theorem canonical1630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1630 raw1630Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw1630 raw1630Labels = mixedMoment B raw1630step0 raw1630step0Labels := by
      have ha : raw1630step0 = (fun i j => raw1630 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1630step0 raw1630; decide +kernel
      have hl : raw1630step0Labels = raw1630Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1630 raw1630Labels permutation152 permutation4
    _ = mixedMoment B node1878 node1878Labels := by rfl

theorem canonical1631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1631 raw1631Labels = mixedMoment B node1919 node1919Labels := by
  calc
    mixedMoment B raw1631 raw1631Labels = mixedMoment B raw1631step0 raw1631step0Labels := by
      have ha : raw1631step0 = (fun i j => raw1631 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1631step0 raw1631; decide +kernel
      have hl : raw1631step0Labels = raw1631Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1631 raw1631Labels permutation164 permutation6
    mixedMoment B raw1631step0 raw1631step0Labels = mixedMoment B raw1631step1 raw1631step1Labels := by
      have ha : raw1631step1 = -raw1631step0 := by apply Matrix.ext; change ∀ i j, raw1631step1 i j = -(raw1631step0 i j); unfold raw1631step1 raw1631step0; decide +kernel
      have hl : raw1631step1Labels = raw1631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1631step1 raw1631step1Labels = mixedMoment B raw1631step2 raw1631step2Labels := by
      have ha : raw1631step2 = raw1631step1 := by apply Matrix.ext; unfold raw1631step2 raw1631step1; decide +kernel
      have hl : raw1631step1Labels = labelEmbedding1 ∘ raw1631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1631step1 raw1631step1Labels raw1631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1919 node1919Labels := by rfl

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

theorem canonical1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1665 raw1665Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw1665 raw1665Labels = mixedMoment B raw1665step0 raw1665step0Labels := by
      have ha : raw1665step0 = (fun i j => raw1665 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1665step0 raw1665; decide +kernel
      have hl : raw1665step0Labels = raw1665Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1665 raw1665Labels permutation152 permutation4
    mixedMoment B raw1665step0 raw1665step0Labels = mixedMoment B raw1665step1 raw1665step1Labels := by
      have ha : raw1665step1 = raw1665step0 := by apply Matrix.ext; unfold raw1665step1 raw1665step0; decide +kernel
      have hl : raw1665step0Labels = labelEmbedding7 ∘ raw1665step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1665step0 raw1665step0Labels raw1665step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

theorem canonical1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1666 raw1666Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw1666 raw1666Labels = mixedMoment B raw1666step0 raw1666step0Labels := by
      have ha : raw1666step0 = (fun i j => raw1666 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1666step0 raw1666; decide +kernel
      have hl : raw1666step0Labels = raw1666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1666 raw1666Labels permutation152 permutation4
    _ = mixedMoment B node1925 node1925Labels := by rfl

theorem canonical1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1667 raw1667Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw1667 raw1667Labels = mixedMoment B raw1667step0 raw1667step0Labels := by
      have ha : raw1667step0 = (fun i j => raw1667 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1667step0 raw1667; decide +kernel
      have hl : raw1667step0Labels = raw1667Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1667 raw1667Labels permutation173 permutation6
    mixedMoment B raw1667step0 raw1667step0Labels = mixedMoment B raw1667step1 raw1667step1Labels := by
      have ha : raw1667step1 = -raw1667step0 := by apply Matrix.ext; change ∀ i j, raw1667step1 i j = -(raw1667step0 i j); unfold raw1667step1 raw1667step0; decide +kernel
      have hl : raw1667step1Labels = raw1667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1667step1 raw1667step1Labels = mixedMoment B raw1667step2 raw1667step2Labels := by
      have ha : raw1667step2 = raw1667step1 := by apply Matrix.ext; unfold raw1667step2 raw1667step1; decide +kernel
      have hl : raw1667step1Labels = labelEmbedding1 ∘ raw1667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1667step1 raw1667step1Labels raw1667step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1925 node1925Labels := by rfl

theorem canonical1779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1779 raw1779Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw1779 raw1779Labels = mixedMoment B raw1779step0 raw1779step0Labels := by
      have ha : raw1779step0 = (fun i j => raw1779 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1779step0 raw1779; decide +kernel
      have hl : raw1779step0Labels = raw1779Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1779 raw1779Labels permutation152 permutation4
    mixedMoment B raw1779step0 raw1779step0Labels = mixedMoment B raw1779step1 raw1779step1Labels := by
      have ha : raw1779step1 = raw1779step0 := by apply Matrix.ext; unfold raw1779step1 raw1779step0; decide +kernel
      have hl : raw1779step0Labels = labelEmbedding7 ∘ raw1779step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1779step0 raw1779step0Labels raw1779step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

theorem canonical1780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1780 raw1780Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw1780 raw1780Labels = mixedMoment B raw1780step0 raw1780step0Labels := by
      have ha : raw1780step0 = (fun i j => raw1780 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1780step0 raw1780; decide +kernel
      have hl : raw1780step0Labels = raw1780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1780 raw1780Labels permutation152 permutation4
    _ = mixedMoment B node2100 node2100Labels := by rfl

theorem canonical1781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1781 raw1781Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw1781 raw1781Labels = mixedMoment B raw1781step0 raw1781step0Labels := by
      have ha : raw1781step0 = (fun i j => raw1781 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1781step0 raw1781; decide +kernel
      have hl : raw1781step0Labels = raw1781Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1781 raw1781Labels permutation176 permutation6
    mixedMoment B raw1781step0 raw1781step0Labels = mixedMoment B raw1781step1 raw1781step1Labels := by
      have ha : raw1781step1 = -raw1781step0 := by apply Matrix.ext; change ∀ i j, raw1781step1 i j = -(raw1781step0 i j); unfold raw1781step1 raw1781step0; decide +kernel
      have hl : raw1781step1Labels = raw1781step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1781step1 raw1781step1Labels = mixedMoment B raw1781step2 raw1781step2Labels := by
      have ha : raw1781step2 = raw1781step1 := by apply Matrix.ext; unfold raw1781step2 raw1781step1; decide +kernel
      have hl : raw1781step1Labels = labelEmbedding1 ∘ raw1781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1781step1 raw1781step1Labels raw1781step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2100 node2100Labels := by rfl

theorem canonical1782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1782 raw1782Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw1782 raw1782Labels = mixedMoment B raw1782step0 raw1782step0Labels := by
      have ha : raw1782step0 = (fun i j => raw1782 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1782step0 raw1782; decide +kernel
      have hl : raw1782step0Labels = raw1782Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1782 raw1782Labels permutation32 permutation4
    mixedMoment B raw1782step0 raw1782step0Labels = mixedMoment B raw1782step1 raw1782step1Labels := by
      have ha : raw1782step1 = raw1782step0 := by apply Matrix.ext; unfold raw1782step1 raw1782step0; decide +kernel
      have hl : raw1782step0Labels = labelEmbedding7 ∘ raw1782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1782step0 raw1782step0Labels raw1782step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

theorem canonical1783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1783 raw1783Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw1783 raw1783Labels = mixedMoment B raw1783step0 raw1783step0Labels := by
      have ha : raw1783step0 = (fun i j => raw1783 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1783step0 raw1783; decide +kernel
      have hl : raw1783step0Labels = raw1783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1783 raw1783Labels permutation32 permutation4
    _ = mixedMoment B node2101 node2101Labels := by rfl

theorem canonical1784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1784 raw1784Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw1784 raw1784Labels = mixedMoment B raw1784step0 raw1784step0Labels := by
      have ha : raw1784step0 = (fun i j => raw1784 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1784step0 raw1784; decide +kernel
      have hl : raw1784step0Labels = raw1784Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1784 raw1784Labels permutation38 permutation6
    mixedMoment B raw1784step0 raw1784step0Labels = mixedMoment B raw1784step1 raw1784step1Labels := by
      have ha : raw1784step1 = -raw1784step0 := by apply Matrix.ext; change ∀ i j, raw1784step1 i j = -(raw1784step0 i j); unfold raw1784step1 raw1784step0; decide +kernel
      have hl : raw1784step1Labels = raw1784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1784step1 raw1784step1Labels = mixedMoment B raw1784step2 raw1784step2Labels := by
      have ha : raw1784step2 = raw1784step1 := by apply Matrix.ext; unfold raw1784step2 raw1784step1; decide +kernel
      have hl : raw1784step1Labels = labelEmbedding1 ∘ raw1784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1784step1 raw1784step1Labels raw1784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2101 node2101Labels := by rfl

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

theorem canonical1800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1800 raw1800Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw1800 raw1800Labels = mixedMoment B raw1800step0 raw1800step0Labels := by
      have ha : raw1800step0 = (fun i j => raw1800 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1800step0 raw1800; decide +kernel
      have hl : raw1800step0Labels = raw1800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1800 raw1800Labels permutation32 permutation4
    mixedMoment B raw1800step0 raw1800step0Labels = mixedMoment B raw1800step1 raw1800step1Labels := by
      have ha : raw1800step1 = raw1800step0 := by apply Matrix.ext; unfold raw1800step1 raw1800step0; decide +kernel
      have hl : raw1800step0Labels = labelEmbedding7 ∘ raw1800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1800step0 raw1800step0Labels raw1800step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1801 raw1801Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw1801 raw1801Labels = mixedMoment B raw1801step0 raw1801step0Labels := by
      have ha : raw1801step0 = (fun i j => raw1801 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1801step0 raw1801; decide +kernel
      have hl : raw1801step0Labels = raw1801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1801 raw1801Labels permutation32 permutation4
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1802 raw1802Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw1802 raw1802Labels = mixedMoment B raw1802step0 raw1802step0Labels := by
      have ha : raw1802step0 = (fun i j => raw1802 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1802step0 raw1802; decide +kernel
      have hl : raw1802step0Labels = raw1802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1802 raw1802Labels permutation50 permutation6
    mixedMoment B raw1802step0 raw1802step0Labels = mixedMoment B raw1802step1 raw1802step1Labels := by
      have ha : raw1802step1 = -raw1802step0 := by apply Matrix.ext; change ∀ i j, raw1802step1 i j = -(raw1802step0 i j); unfold raw1802step1 raw1802step0; decide +kernel
      have hl : raw1802step1Labels = raw1802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1802step1 raw1802step1Labels = mixedMoment B raw1802step2 raw1802step2Labels := by
      have ha : raw1802step2 = raw1802step1 := by apply Matrix.ext; unfold raw1802step2 raw1802step1; decide +kernel
      have hl : raw1802step1Labels = labelEmbedding1 ∘ raw1802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1802step1 raw1802step1Labels raw1802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1803 raw1803Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw1803 raw1803Labels = mixedMoment B raw1803step0 raw1803step0Labels := by
      have ha : raw1803step0 = (fun i j => raw1803 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1803step0 raw1803; decide +kernel
      have hl : raw1803step0Labels = raw1803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1803 raw1803Labels permutation8 permutation4
    mixedMoment B raw1803step0 raw1803step0Labels = mixedMoment B raw1803step1 raw1803step1Labels := by
      have ha : raw1803step1 = raw1803step0 := by apply Matrix.ext; unfold raw1803step1 raw1803step0; decide +kernel
      have hl : raw1803step0Labels = labelEmbedding7 ∘ raw1803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1803step0 raw1803step0Labels raw1803step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1804 raw1804Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw1804 raw1804Labels = mixedMoment B raw1804step0 raw1804step0Labels := by
      have ha : raw1804step0 = (fun i j => raw1804 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1804step0 raw1804; decide +kernel
      have hl : raw1804step0Labels = raw1804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1804 raw1804Labels permutation8 permutation4
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1805 raw1805Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw1805 raw1805Labels = mixedMoment B raw1805step0 raw1805step0Labels := by
      have ha : raw1805step0 = (fun i j => raw1805 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1805step0 raw1805; decide +kernel
      have hl : raw1805step0Labels = raw1805Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1805 raw1805Labels permutation8 permutation6
    mixedMoment B raw1805step0 raw1805step0Labels = mixedMoment B raw1805step1 raw1805step1Labels := by
      have ha : raw1805step1 = -raw1805step0 := by apply Matrix.ext; change ∀ i j, raw1805step1 i j = -(raw1805step0 i j); unfold raw1805step1 raw1805step0; decide +kernel
      have hl : raw1805step1Labels = raw1805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1805step1 raw1805step1Labels = mixedMoment B raw1805step2 raw1805step2Labels := by
      have ha : raw1805step2 = raw1805step1 := by apply Matrix.ext; unfold raw1805step2 raw1805step1; decide +kernel
      have hl : raw1805step1Labels = labelEmbedding1 ∘ raw1805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1805step1 raw1805step1Labels raw1805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical1806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1806 raw1806Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw1806 raw1806Labels = mixedMoment B raw1806step0 raw1806step0Labels := by
      have ha : raw1806step0 = (fun i j => raw1806 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1806step0 raw1806; decide +kernel
      have hl : raw1806step0Labels = raw1806Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1806 raw1806Labels permutation8 permutation4
    mixedMoment B raw1806step0 raw1806step0Labels = mixedMoment B raw1806step1 raw1806step1Labels := by
      have ha : raw1806step1 = raw1806step0 := by apply Matrix.ext; unfold raw1806step1 raw1806step0; decide +kernel
      have hl : raw1806step0Labels = labelEmbedding7 ∘ raw1806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1806step0 raw1806step0Labels raw1806step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1807 raw1807Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw1807 raw1807Labels = mixedMoment B raw1807step0 raw1807step0Labels := by
      have ha : raw1807step0 = (fun i j => raw1807 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1807step0 raw1807; decide +kernel
      have hl : raw1807step0Labels = raw1807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1807 raw1807Labels permutation8 permutation4
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical1808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1808 raw1808Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw1808 raw1808Labels = mixedMoment B raw1808step0 raw1808step0Labels := by
      have ha : raw1808step0 = (fun i j => raw1808 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1808step0 raw1808; decide +kernel
      have hl : raw1808step0Labels = raw1808Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1808 raw1808Labels permutation10 permutation6
    mixedMoment B raw1808step0 raw1808step0Labels = mixedMoment B raw1808step1 raw1808step1Labels := by
      have ha : raw1808step1 = -raw1808step0 := by apply Matrix.ext; change ∀ i j, raw1808step1 i j = -(raw1808step0 i j); unfold raw1808step1 raw1808step0; decide +kernel
      have hl : raw1808step1Labels = raw1808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1808step1 raw1808step1Labels = mixedMoment B raw1808step2 raw1808step2Labels := by
      have ha : raw1808step2 = raw1808step1 := by apply Matrix.ext; unfold raw1808step2 raw1808step1; decide +kernel
      have hl : raw1808step1Labels = labelEmbedding1 ∘ raw1808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1808step1 raw1808step1Labels raw1808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical1827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1827 raw1827Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw1827 raw1827Labels = mixedMoment B raw1827step0 raw1827step0Labels := by
      have ha : raw1827step0 = (fun i j => raw1827 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1827step0 raw1827; decide +kernel
      have hl : raw1827step0Labels = raw1827Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1827 raw1827Labels permutation8 permutation4
    mixedMoment B raw1827step0 raw1827step0Labels = mixedMoment B raw1827step1 raw1827step1Labels := by
      have ha : raw1827step1 = raw1827step0 := by apply Matrix.ext; unfold raw1827step1 raw1827step0; decide +kernel
      have hl : raw1827step0Labels = labelEmbedding7 ∘ raw1827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1827step0 raw1827step0Labels raw1827step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical1828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1828 raw1828Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1828 raw1828Labels = mixedMoment B raw1828step0 raw1828step0Labels := by
      have ha : raw1828step0 = (fun i j => raw1828 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1828step0 raw1828; decide +kernel
      have hl : raw1828step0Labels = raw1828Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1828 raw1828Labels permutation8 permutation4
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical1829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1829 raw1829Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1829 raw1829Labels = mixedMoment B raw1829step0 raw1829step0Labels := by
      have ha : raw1829step0 = (fun i j => raw1829 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1829step0 raw1829; decide +kernel
      have hl : raw1829step0Labels = raw1829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1829 raw1829Labels permutation13 permutation6
    mixedMoment B raw1829step0 raw1829step0Labels = mixedMoment B raw1829step1 raw1829step1Labels := by
      have ha : raw1829step1 = -raw1829step0 := by apply Matrix.ext; change ∀ i j, raw1829step1 i j = -(raw1829step0 i j); unfold raw1829step1 raw1829step0; decide +kernel
      have hl : raw1829step1Labels = raw1829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1829step1 raw1829step1Labels = mixedMoment B raw1829step2 raw1829step2Labels := by
      have ha : raw1829step2 = raw1829step1 := by apply Matrix.ext; unfold raw1829step2 raw1829step1; decide +kernel
      have hl : raw1829step1Labels = labelEmbedding1 ∘ raw1829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1829step1 raw1829step1Labels raw1829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19178 raw19178Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw19178 raw19178Labels = mixedMoment B raw19178step0 raw19178step0Labels := by
      have ha : raw19178step0 = (fun i j => raw19178 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19178step0 raw19178; decide +kernel
      have hl : raw19178step0Labels = raw19178Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19178 raw19178Labels permutation170 permutation3
    mixedMoment B raw19178step0 raw19178step0Labels = mixedMoment B raw19178step1 raw19178step1Labels := by
      have ha : raw19178step1 = raw19178step0 := by apply Matrix.ext; unfold raw19178step1 raw19178step0; decide +kernel
      have hl : raw19178step0Labels = labelEmbedding6 ∘ raw19178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19178step0 raw19178step0Labels raw19178step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

theorem canonical19183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19183 raw19183Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw19183 raw19183Labels = mixedMoment B raw19183step0 raw19183step0Labels := by
      have hz : ∀ j, raw19183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19183step0 = (fun i j => raw19183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19183step0 raw19183; decide +kernel
      have hl : raw19183step0Labels = raw19183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19183 raw19183Labels permutation346 hz
    mixedMoment B raw19183step0 raw19183step0Labels = mixedMoment B raw19183step1 raw19183step1Labels := by
      have ha : raw19183step1 = (fun i j => raw19183step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19183step1 raw19183step0; decide +kernel
      have hl : raw19183step1Labels = raw19183step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19183step0 raw19183step0Labels permutation37 permutation3
    mixedMoment B raw19183step1 raw19183step1Labels = mixedMoment B raw19183step2 raw19183step2Labels := by
      have ha : raw19183step2 = raw19183step1 := by apply Matrix.ext; unfold raw19183step2 raw19183step1; decide +kernel
      have hl : raw19183step1Labels = labelEmbedding6 ∘ raw19183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19183step1 raw19183step1Labels raw19183step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

theorem canonical19188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19188 raw19188Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw19188 raw19188Labels = mixedMoment B raw19188step0 raw19188step0Labels := by
      have hz : ∀ j, raw19188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19188step0 = (fun i j => raw19188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19188step0 raw19188; decide +kernel
      have hl : raw19188step0Labels = raw19188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19188 raw19188Labels permutation346 hz
    mixedMoment B raw19188step0 raw19188step0Labels = mixedMoment B raw19188step1 raw19188step1Labels := by
      have ha : raw19188step1 = (fun i j => raw19188step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19188step1 raw19188step0; decide +kernel
      have hl : raw19188step1Labels = raw19188step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19188step0 raw19188step0Labels permutation36 permutation3
    mixedMoment B raw19188step1 raw19188step1Labels = mixedMoment B raw19188step2 raw19188step2Labels := by
      have ha : raw19188step2 = raw19188step1 := by apply Matrix.ext; unfold raw19188step2 raw19188step1; decide +kernel
      have hl : raw19188step1Labels = labelEmbedding6 ∘ raw19188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19188step1 raw19188step1Labels raw19188step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

theorem canonical19193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19193 raw19193Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw19193 raw19193Labels = mixedMoment B raw19193step0 raw19193step0Labels := by
      have hz : ∀ j, raw19193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19193step0 = (fun i j => raw19193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19193step0 raw19193; decide +kernel
      have hl : raw19193step0Labels = raw19193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19193 raw19193Labels permutation346 hz
    mixedMoment B raw19193step0 raw19193step0Labels = mixedMoment B raw19193step1 raw19193step1Labels := by
      have ha : raw19193step1 = (fun i j => raw19193step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19193step1 raw19193step0; decide +kernel
      have hl : raw19193step1Labels = raw19193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19193step0 raw19193step0Labels permutation56 permutation2
    _ = mixedMoment B node5387 node5387Labels := by rfl

theorem canonical19194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19194 raw19194Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19194 raw19194Labels = mixedMoment B raw19194step0 raw19194step0Labels := by
      have ha : raw19194step0 = (fun i j => raw19194 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19194step0 raw19194; decide +kernel
      have hl : raw19194step0Labels = raw19194Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19194 raw19194Labels permutation176 permutation3
    mixedMoment B raw19194step0 raw19194step0Labels = mixedMoment B raw19194step1 raw19194step1Labels := by
      have ha : raw19194step1 = raw19194step0 := by apply Matrix.ext; unfold raw19194step1 raw19194step0; decide +kernel
      have hl : raw19194step0Labels = labelEmbedding6 ∘ raw19194step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19194step0 raw19194step0Labels raw19194step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

theorem canonical19195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19195 raw19195Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw19195 raw19195Labels = mixedMoment B raw19195step0 raw19195step0Labels := by
      have hz : ∀ j, raw19195 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19195step0 = (fun i j => raw19195 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19195step0 raw19195; decide +kernel
      have hl : raw19195step0Labels = raw19195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19195 raw19195Labels permutation520 hz
    mixedMoment B raw19195step0 raw19195step0Labels = mixedMoment B raw19195step1 raw19195step1Labels := by
      have hz : ∀ j, raw19195step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19195step1 = (fun i j => raw19195step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19195step1 raw19195step0; decide +kernel
      have hl : raw19195step1Labels = raw19195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19195step0 raw19195step0Labels permutation80 hz
    mixedMoment B raw19195step1 raw19195step1Labels = mixedMoment B raw19195step2 raw19195step2Labels := by
      have ha : raw19195step2 = (fun i j => raw19195step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19195step2 raw19195step1; decide +kernel
      have hl : raw19195step2Labels = raw19195step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19195step1 raw19195step1Labels permutation31 permutation2
    mixedMoment B raw19195step2 raw19195step2Labels = mixedMoment B raw19195step3 raw19195step3Labels := by
      have ha : raw19195step3 = -raw19195step2 := by apply Matrix.ext; change ∀ i j, raw19195step3 i j = -(raw19195step2 i j); unfold raw19195step3 raw19195step2; decide +kernel
      have hl : raw19195step3Labels = raw19195step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

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

theorem canonical2478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2478 raw2478Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw2478 raw2478Labels = mixedMoment B raw2478step0 raw2478step0Labels := by
      have ha : raw2478step0 = (fun i j => raw2478 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2478step0 raw2478; decide +kernel
      have hl : raw2478step0Labels = raw2478Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2478 raw2478Labels permutation152 permutation4
    mixedMoment B raw2478step0 raw2478step0Labels = mixedMoment B raw2478step1 raw2478step1Labels := by
      have ha : raw2478step1 = raw2478step0 := by apply Matrix.ext; unfold raw2478step1 raw2478step0; decide +kernel
      have hl : raw2478step0Labels = labelEmbedding7 ∘ raw2478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2478step0 raw2478step0Labels raw2478step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

theorem canonical2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2479 raw2479Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw2479 raw2479Labels = mixedMoment B raw2479step0 raw2479step0Labels := by
      have ha : raw2479step0 = (fun i j => raw2479 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2479step0 raw2479; decide +kernel
      have hl : raw2479step0Labels = raw2479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2479 raw2479Labels permutation152 permutation4
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2480 raw2480Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw2480 raw2480Labels = mixedMoment B raw2480step0 raw2480step0Labels := by
      have ha : raw2480step0 = (fun i j => raw2480 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2480step0 raw2480; decide +kernel
      have hl : raw2480step0Labels = raw2480Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2480 raw2480Labels permutation170 permutation6
    mixedMoment B raw2480step0 raw2480step0Labels = mixedMoment B raw2480step1 raw2480step1Labels := by
      have ha : raw2480step1 = -raw2480step0 := by apply Matrix.ext; change ∀ i j, raw2480step1 i j = -(raw2480step0 i j); unfold raw2480step1 raw2480step0; decide +kernel
      have hl : raw2480step1Labels = raw2480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2480step1 raw2480step1Labels = mixedMoment B raw2480step2 raw2480step2Labels := by
      have ha : raw2480step2 = raw2480step1 := by apply Matrix.ext; unfold raw2480step2 raw2480step1; decide +kernel
      have hl : raw2480step1Labels = labelEmbedding1 ∘ raw2480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2480step1 raw2480step1Labels raw2480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

theorem canonical2544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2544 raw2544Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2544 raw2544Labels = mixedMoment B raw2544step0 raw2544step0Labels := by
      have ha : raw2544step0 = (fun i j => raw2544 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2544step0 raw2544; decide +kernel
      have hl : raw2544step0Labels = raw2544Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2544 raw2544Labels permutation8 permutation4
    mixedMoment B raw2544step0 raw2544step0Labels = mixedMoment B raw2544step1 raw2544step1Labels := by
      have ha : raw2544step1 = raw2544step0 := by apply Matrix.ext; unfold raw2544step1 raw2544step0; decide +kernel
      have hl : raw2544step0Labels = labelEmbedding7 ∘ raw2544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2544step0 raw2544step0Labels raw2544step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2545 raw2545Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw2545 raw2545Labels = mixedMoment B raw2545step0 raw2545step0Labels := by
      have ha : raw2545step0 = (fun i j => raw2545 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2545step0 raw2545; decide +kernel
      have hl : raw2545step0Labels = raw2545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2545 raw2545Labels permutation8 permutation4
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2546 raw2546Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw2546 raw2546Labels = mixedMoment B raw2546step0 raw2546step0Labels := by
      have ha : raw2546step0 = (fun i j => raw2546 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2546step0 raw2546; decide +kernel
      have hl : raw2546step0Labels = raw2546Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2546 raw2546Labels permutation9 permutation6
    mixedMoment B raw2546step0 raw2546step0Labels = mixedMoment B raw2546step1 raw2546step1Labels := by
      have ha : raw2546step1 = -raw2546step0 := by apply Matrix.ext; change ∀ i j, raw2546step1 i j = -(raw2546step0 i j); unfold raw2546step1 raw2546step0; decide +kernel
      have hl : raw2546step1Labels = raw2546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2546step1 raw2546step1Labels = mixedMoment B raw2546step2 raw2546step2Labels := by
      have ha : raw2546step2 = raw2546step1 := by apply Matrix.ext; unfold raw2546step2 raw2546step1; decide +kernel
      have hl : raw2546step1Labels = labelEmbedding1 ∘ raw2546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2546step1 raw2546step1Labels raw2546step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical2550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2550 raw2550Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2550 raw2550Labels = mixedMoment B raw2550step0 raw2550step0Labels := by
      have ha : raw2550step0 = (fun i j => raw2550 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2550step0 raw2550; decide +kernel
      have hl : raw2550step0Labels = raw2550Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2550 raw2550Labels permutation32 permutation4
    mixedMoment B raw2550step0 raw2550step0Labels = mixedMoment B raw2550step1 raw2550step1Labels := by
      have ha : raw2550step1 = raw2550step0 := by apply Matrix.ext; unfold raw2550step1 raw2550step0; decide +kernel
      have hl : raw2550step0Labels = labelEmbedding7 ∘ raw2550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2550step0 raw2550step0Labels raw2550step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical2551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2551 raw2551Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2551 raw2551Labels = mixedMoment B raw2551step0 raw2551step0Labels := by
      have ha : raw2551step0 = (fun i j => raw2551 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2551step0 raw2551; decide +kernel
      have hl : raw2551step0Labels = raw2551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2551 raw2551Labels permutation32 permutation4
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2552 raw2552Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2552 raw2552Labels = mixedMoment B raw2552step0 raw2552step0Labels := by
      have ha : raw2552step0 = (fun i j => raw2552 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2552step0 raw2552; decide +kernel
      have hl : raw2552step0Labels = raw2552Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2552 raw2552Labels permutation38 permutation6
    mixedMoment B raw2552step0 raw2552step0Labels = mixedMoment B raw2552step1 raw2552step1Labels := by
      have ha : raw2552step1 = -raw2552step0 := by apply Matrix.ext; change ∀ i j, raw2552step1 i j = -(raw2552step0 i j); unfold raw2552step1 raw2552step0; decide +kernel
      have hl : raw2552step1Labels = raw2552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2552step1 raw2552step1Labels = mixedMoment B raw2552step2 raw2552step2Labels := by
      have ha : raw2552step2 = raw2552step1 := by apply Matrix.ext; unfold raw2552step2 raw2552step1; decide +kernel
      have hl : raw2552step1Labels = labelEmbedding1 ∘ raw2552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2552step1 raw2552step1Labels raw2552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31012 raw31012Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw31012 raw31012Labels = mixedMoment B raw31012step0 raw31012step0Labels := by
      have hz : ∀ j, raw31012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31012step0 = (fun i j => raw31012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31012step0 raw31012; decide +kernel
      have hl : raw31012step0Labels = raw31012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31012 raw31012Labels permutation434 hz
    mixedMoment B raw31012step0 raw31012step0Labels = mixedMoment B raw31012step1 raw31012step1Labels := by
      have hz : ∀ j, raw31012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31012step1 = (fun i j => raw31012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31012step1 raw31012step0; decide +kernel
      have hl : raw31012step1Labels = raw31012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31012step0 raw31012step0Labels permutation80 hz
    mixedMoment B raw31012step1 raw31012step1Labels = mixedMoment B raw31012step2 raw31012step2Labels := by
      have ha : raw31012step2 = (fun i j => raw31012step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31012step2 raw31012step1; decide +kernel
      have hl : raw31012step2Labels = raw31012step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31012step1 raw31012step1Labels permutation8 permutation3
    mixedMoment B raw31012step2 raw31012step2Labels = mixedMoment B raw31012step3 raw31012step3Labels := by
      have ha : raw31012step3 = raw31012step2 := by apply Matrix.ext; unfold raw31012step3 raw31012step2; decide +kernel
      have hl : raw31012step2Labels = labelEmbedding6 ∘ raw31012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31012step2 raw31012step2Labels raw31012step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical31017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31017 raw31017Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw31017 raw31017Labels = mixedMoment B raw31017step0 raw31017step0Labels := by
      have hz : ∀ j, raw31017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31017step0 = (fun i j => raw31017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31017step0 raw31017; decide +kernel
      have hl : raw31017step0Labels = raw31017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31017 raw31017Labels permutation346 hz
    mixedMoment B raw31017step0 raw31017step0Labels = mixedMoment B raw31017step1 raw31017step1Labels := by
      have ha : raw31017step1 = (fun i j => raw31017step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31017step1 raw31017step0; decide +kernel
      have hl : raw31017step1Labels = raw31017step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31017step0 raw31017step0Labels permutation33 permutation3
    mixedMoment B raw31017step1 raw31017step1Labels = mixedMoment B raw31017step2 raw31017step2Labels := by
      have ha : raw31017step2 = raw31017step1 := by apply Matrix.ext; unfold raw31017step2 raw31017step1; decide +kernel
      have hl : raw31017step1Labels = labelEmbedding6 ∘ raw31017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31017step1 raw31017step1Labels raw31017step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4238 node4238Labels := by rfl

theorem canonical31018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31018 raw31018Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw31018 raw31018Labels = mixedMoment B raw31018step0 raw31018step0Labels := by
      have hz : ∀ j, raw31018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31018step0 = (fun i j => raw31018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31018step0 raw31018; decide +kernel
      have hl : raw31018step0Labels = raw31018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31018 raw31018Labels permutation346 hz
    mixedMoment B raw31018step0 raw31018step0Labels = mixedMoment B raw31018step1 raw31018step1Labels := by
      have ha : raw31018step1 = (fun i j => raw31018step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31018step1 raw31018step0; decide +kernel
      have hl : raw31018step1Labels = raw31018step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31018step0 raw31018step0Labels permutation33 permutation3
    mixedMoment B raw31018step1 raw31018step1Labels = mixedMoment B raw31018step2 raw31018step2Labels := by
      have ha : raw31018step2 = raw31018step1 := by apply Matrix.ext; unfold raw31018step2 raw31018step1; decide +kernel
      have hl : raw31018step1Labels = labelEmbedding6 ∘ raw31018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31018step1 raw31018step1Labels raw31018step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

theorem canonical31019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31019 raw31019Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw31019 raw31019Labels = mixedMoment B raw31019step0 raw31019step0Labels := by
      have ha : raw31019step0 = (fun i j => raw31019 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31019step0 raw31019; decide +kernel
      have hl : raw31019step0Labels = raw31019Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31019 raw31019Labels permutation177 permutation3
    mixedMoment B raw31019step0 raw31019step0Labels = mixedMoment B raw31019step1 raw31019step1Labels := by
      have ha : raw31019step1 = raw31019step0 := by apply Matrix.ext; unfold raw31019step1 raw31019step0; decide +kernel
      have hl : raw31019step0Labels = labelEmbedding6 ∘ raw31019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31019step0 raw31019step0Labels raw31019step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33516 raw33516Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw33516 raw33516Labels = mixedMoment B raw33516step0 raw33516step0Labels := by
      have hz : ∀ j, raw33516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33516step0 = (fun i j => raw33516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33516step0 raw33516; decide +kernel
      have hl : raw33516step0Labels = raw33516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33516 raw33516Labels permutation346 hz
    mixedMoment B raw33516step0 raw33516step0Labels = mixedMoment B raw33516step1 raw33516step1Labels := by
      have ha : raw33516step1 = (fun i j => raw33516step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33516step1 raw33516step0; decide +kernel
      have hl : raw33516step1Labels = raw33516step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33516step0 raw33516step0Labels permutation36 permutation3
    mixedMoment B raw33516step1 raw33516step1Labels = mixedMoment B raw33516step2 raw33516step2Labels := by
      have ha : raw33516step2 = raw33516step1 := by apply Matrix.ext; unfold raw33516step2 raw33516step1; decide +kernel
      have hl : raw33516step1Labels = labelEmbedding6 ∘ raw33516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33516step1 raw33516step1Labels raw33516step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical33517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33517 raw33517Labels = mixedMoment B node4236 node4236Labels := by
  calc
    mixedMoment B raw33517 raw33517Labels = mixedMoment B raw33517step0 raw33517step0Labels := by
      have ha : raw33517step0 = (fun i j => raw33517 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33517step0 raw33517; decide +kernel
      have hl : raw33517step0Labels = raw33517Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33517 raw33517Labels permutation152 permutation3
    mixedMoment B raw33517step0 raw33517step0Labels = mixedMoment B raw33517step1 raw33517step1Labels := by
      have ha : raw33517step1 = raw33517step0 := by apply Matrix.ext; unfold raw33517step1 raw33517step0; decide +kernel
      have hl : raw33517step0Labels = labelEmbedding6 ∘ raw33517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33517step0 raw33517step0Labels raw33517step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4236 node4236Labels := by rfl

theorem canonical33518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33518 raw33518Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw33518 raw33518Labels = mixedMoment B raw33518step0 raw33518step0Labels := by
      have ha : raw33518step0 = (fun i j => raw33518 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33518step0 raw33518; decide +kernel
      have hl : raw33518step0Labels = raw33518Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33518 raw33518Labels permutation152 permutation3
    mixedMoment B raw33518step0 raw33518step0Labels = mixedMoment B raw33518step1 raw33518step1Labels := by
      have ha : raw33518step1 = raw33518step0 := by apply Matrix.ext; unfold raw33518step1 raw33518step0; decide +kernel
      have hl : raw33518step0Labels = labelEmbedding6 ∘ raw33518step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33518step0 raw33518step0Labels raw33518step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4685 node4685Labels := by rfl

theorem canonical33519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33519 raw33519Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw33519 raw33519Labels = mixedMoment B raw33519step0 raw33519step0Labels := by
      have hz : ∀ j, raw33519 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33519step0 = (fun i j => raw33519 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33519step0 raw33519; decide +kernel
      have hl : raw33519step0Labels = raw33519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33519 raw33519Labels permutation520 hz
    mixedMoment B raw33519step0 raw33519step0Labels = mixedMoment B raw33519step1 raw33519step1Labels := by
      have ha : raw33519step1 = (fun i j => raw33519step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33519step1 raw33519step0; decide +kernel
      have hl : raw33519step1Labels = raw33519step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33519step0 raw33519step0Labels permutation32 permutation3
    mixedMoment B raw33519step1 raw33519step1Labels = mixedMoment B raw33519step2 raw33519step2Labels := by
      have ha : raw33519step2 = raw33519step1 := by apply Matrix.ext; unfold raw33519step2 raw33519step1; decide +kernel
      have hl : raw33519step1Labels = labelEmbedding6 ∘ raw33519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33519step1 raw33519step1Labels raw33519step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical33520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33520 raw33520Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw33520 raw33520Labels = mixedMoment B raw33520step0 raw33520step0Labels := by
      have hz : ∀ j, raw33520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33520step0 = (fun i j => raw33520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33520step0 raw33520; decide +kernel
      have hl : raw33520step0Labels = raw33520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33520 raw33520Labels permutation346 hz
    mixedMoment B raw33520step0 raw33520step0Labels = mixedMoment B raw33520step1 raw33520step1Labels := by
      have ha : raw33520step1 = (fun i j => raw33520step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33520step1 raw33520step0; decide +kernel
      have hl : raw33520step1Labels = raw33520step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33520step0 raw33520step0Labels permutation35 permutation3
    mixedMoment B raw33520step1 raw33520step1Labels = mixedMoment B raw33520step2 raw33520step2Labels := by
      have ha : raw33520step2 = raw33520step1 := by apply Matrix.ext; unfold raw33520step2 raw33520step1; decide +kernel
      have hl : raw33520step1Labels = labelEmbedding6 ∘ raw33520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33520step1 raw33520step1Labels raw33520step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4238 node4238Labels := by rfl

theorem canonical33521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33521 raw33521Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw33521 raw33521Labels = mixedMoment B raw33521step0 raw33521step0Labels := by
      have hz : ∀ j, raw33521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33521step0 = (fun i j => raw33521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33521step0 raw33521; decide +kernel
      have hl : raw33521step0Labels = raw33521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33521 raw33521Labels permutation346 hz
    mixedMoment B raw33521step0 raw33521step0Labels = mixedMoment B raw33521step1 raw33521step1Labels := by
      have ha : raw33521step1 = (fun i j => raw33521step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33521step1 raw33521step0; decide +kernel
      have hl : raw33521step1Labels = raw33521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33521step0 raw33521step0Labels permutation35 permutation3
    mixedMoment B raw33521step1 raw33521step1Labels = mixedMoment B raw33521step2 raw33521step2Labels := by
      have ha : raw33521step2 = raw33521step1 := by apply Matrix.ext; unfold raw33521step2 raw33521step1; decide +kernel
      have hl : raw33521step1Labels = labelEmbedding6 ∘ raw33521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33521step1 raw33521step1Labels raw33521step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

theorem canonical33522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33522 raw33522Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw33522 raw33522Labels = mixedMoment B raw33522step0 raw33522step0Labels := by
      have ha : raw33522step0 = (fun i j => raw33522 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33522step0 raw33522; decide +kernel
      have hl : raw33522step0Labels = raw33522Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33522 raw33522Labels permutation179 permutation3
    mixedMoment B raw33522step0 raw33522step0Labels = mixedMoment B raw33522step1 raw33522step1Labels := by
      have ha : raw33522step1 = raw33522step0 := by apply Matrix.ext; unfold raw33522step1 raw33522step0; decide +kernel
      have hl : raw33522step0Labels = labelEmbedding6 ∘ raw33522step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33522step0 raw33522step0Labels raw33522step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

theorem canonical33523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33523 raw33523Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw33523 raw33523Labels = mixedMoment B raw33523step0 raw33523step0Labels := by
      have hz : ∀ j, raw33523 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33523step0 = (fun i j => raw33523 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33523step0 raw33523; decide +kernel
      have hl : raw33523step0Labels = raw33523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33523 raw33523Labels permutation520 hz
    mixedMoment B raw33523step0 raw33523step0Labels = mixedMoment B raw33523step1 raw33523step1Labels := by
      have hz : ∀ j, raw33523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33523step1 = (fun i j => raw33523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33523step1 raw33523step0; decide +kernel
      have hl : raw33523step1Labels = raw33523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33523step0 raw33523step0Labels permutation80 hz
    mixedMoment B raw33523step1 raw33523step1Labels = mixedMoment B raw33523step2 raw33523step2Labels := by
      have ha : raw33523step2 = (fun i j => raw33523step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33523step2 raw33523step1; decide +kernel
      have hl : raw33523step2Labels = raw33523step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33523step1 raw33523step1Labels permutation9 permutation3
    mixedMoment B raw33523step2 raw33523step2Labels = mixedMoment B raw33523step3 raw33523step3Labels := by
      have ha : raw33523step3 = raw33523step2 := by apply Matrix.ext; unfold raw33523step3 raw33523step2; decide +kernel
      have hl : raw33523step2Labels = labelEmbedding6 ∘ raw33523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33523step2 raw33523step2Labels raw33523step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical33524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33524 raw33524Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw33524 raw33524Labels = mixedMoment B raw33524step0 raw33524step0Labels := by
      have hz : ∀ j, raw33524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33524step0 = (fun i j => raw33524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33524step0 raw33524; decide +kernel
      have hl : raw33524step0Labels = raw33524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33524 raw33524Labels permutation346 hz
    mixedMoment B raw33524step0 raw33524step0Labels = mixedMoment B raw33524step1 raw33524step1Labels := by
      have ha : raw33524step1 = (fun i j => raw33524step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33524step1 raw33524step0; decide +kernel
      have hl : raw33524step1Labels = raw33524step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33524step0 raw33524step0Labels permutation32 permutation3
    mixedMoment B raw33524step1 raw33524step1Labels = mixedMoment B raw33524step2 raw33524step2Labels := by
      have ha : raw33524step2 = raw33524step1 := by apply Matrix.ext; unfold raw33524step2 raw33524step1; decide +kernel
      have hl : raw33524step1Labels = labelEmbedding6 ∘ raw33524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33524step1 raw33524step1Labels raw33524step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4237 node4237Labels := by rfl

theorem canonical33525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33525 raw33525Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw33525 raw33525Labels = mixedMoment B raw33525step0 raw33525step0Labels := by
      have hz : ∀ j, raw33525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33525step0 = (fun i j => raw33525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33525step0 raw33525; decide +kernel
      have hl : raw33525step0Labels = raw33525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33525 raw33525Labels permutation346 hz
    mixedMoment B raw33525step0 raw33525step0Labels = mixedMoment B raw33525step1 raw33525step1Labels := by
      have ha : raw33525step1 = (fun i j => raw33525step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33525step1 raw33525step0; decide +kernel
      have hl : raw33525step1Labels = raw33525step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33525step0 raw33525step0Labels permutation32 permutation3
    mixedMoment B raw33525step1 raw33525step1Labels = mixedMoment B raw33525step2 raw33525step2Labels := by
      have ha : raw33525step2 = raw33525step1 := by apply Matrix.ext; unfold raw33525step2 raw33525step1; decide +kernel
      have hl : raw33525step1Labels = labelEmbedding6 ∘ raw33525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33525step1 raw33525step1Labels raw33525step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

theorem canonical33526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33526 raw33526Labels = mixedMoment B node4723 node4723Labels := by
  calc
    mixedMoment B raw33526 raw33526Labels = mixedMoment B raw33526step0 raw33526step0Labels := by
      have ha : raw33526step0 = (fun i j => raw33526 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33526step0 raw33526; decide +kernel
      have hl : raw33526step0Labels = raw33526Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33526 raw33526Labels permutation176 permutation3
    mixedMoment B raw33526step0 raw33526step0Labels = mixedMoment B raw33526step1 raw33526step1Labels := by
      have ha : raw33526step1 = raw33526step0 := by apply Matrix.ext; unfold raw33526step1 raw33526step0; decide +kernel
      have hl : raw33526step0Labels = labelEmbedding6 ∘ raw33526step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33526step0 raw33526step0Labels raw33526step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4723 node4723Labels := by rfl

theorem canonical33527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33527 raw33527Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw33527 raw33527Labels = mixedMoment B raw33527step0 raw33527step0Labels := by
      have hz : ∀ j, raw33527 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33527step0 = (fun i j => raw33527 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33527step0 raw33527; decide +kernel
      have hl : raw33527step0Labels = raw33527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33527 raw33527Labels permutation520 hz
    mixedMoment B raw33527step0 raw33527step0Labels = mixedMoment B raw33527step1 raw33527step1Labels := by
      have hz : ∀ j, raw33527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33527step1 = (fun i j => raw33527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33527step1 raw33527step0; decide +kernel
      have hl : raw33527step1Labels = raw33527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33527step0 raw33527step0Labels permutation80 hz
    mixedMoment B raw33527step1 raw33527step1Labels = mixedMoment B raw33527step2 raw33527step2Labels := by
      have ha : raw33527step2 = (fun i j => raw33527step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33527step2 raw33527step1; decide +kernel
      have hl : raw33527step2Labels = raw33527step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33527step1 raw33527step1Labels permutation8 permutation3
    mixedMoment B raw33527step2 raw33527step2Labels = mixedMoment B raw33527step3 raw33527step3Labels := by
      have ha : raw33527step3 = raw33527step2 := by apply Matrix.ext; unfold raw33527step3 raw33527step2; decide +kernel
      have hl : raw33527step2Labels = labelEmbedding6 ∘ raw33527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33527step2 raw33527step2Labels raw33527step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

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

theorem canonical536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw536 raw536Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw536 raw536Labels = mixedMoment B raw536step0 raw536step0Labels := by
      have ha : raw536step0 = (fun i j => raw536 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw536step0 raw536; decide +kernel
      have hl : raw536step0Labels = raw536Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw536 raw536Labels permutation8 permutation5
    mixedMoment B raw536step0 raw536step0Labels = mixedMoment B raw536step1 raw536step1Labels := by
      have ha : raw536step1 = raw536step0 := by apply Matrix.ext; unfold raw536step1 raw536step0; decide +kernel
      have hl : raw536step0Labels = labelEmbedding1 ∘ raw536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw536step0 raw536step0Labels raw536step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

theorem canonical537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw537 raw537Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw537 raw537Labels = mixedMoment B raw537step0 raw537step0Labels := by
      have ha : raw537step0 = (fun i j => raw537 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw537step0 raw537; decide +kernel
      have hl : raw537step0Labels = raw537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw537 raw537Labels permutation8 permutation5
    _ = mixedMoment B node496 node496Labels := by rfl

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

theorem canonical942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw942 raw942Labels = mixedMoment B node4236 node4236Labels := by
  calc
    mixedMoment B raw942 raw942Labels = mixedMoment B raw942step0 raw942step0Labels := by
      have ha : raw942step0 = (fun i j => raw942 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw942step0 raw942; decide +kernel
      have hl : raw942step0Labels = raw942Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw942 raw942Labels permutation152 permutation4
    mixedMoment B raw942step0 raw942step0Labels = mixedMoment B raw942step1 raw942step1Labels := by
      have ha : raw942step1 = raw942step0 := by apply Matrix.ext; unfold raw942step1 raw942step0; decide +kernel
      have hl : raw942step0Labels = labelEmbedding7 ∘ raw942step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw942step0 raw942step0Labels raw942step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4236 node4236Labels := by rfl

theorem canonical943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw943 raw943Labels = mixedMoment B node736 node736Labels := by
  calc
    mixedMoment B raw943 raw943Labels = mixedMoment B raw943step0 raw943step0Labels := by
      have ha : raw943step0 = (fun i j => raw943 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw943step0 raw943; decide +kernel
      have hl : raw943step0Labels = raw943Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw943 raw943Labels permutation152 permutation4
    _ = mixedMoment B node736 node736Labels := by rfl

theorem canonical944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw944 raw944Labels = mixedMoment B node818 node818Labels := by
  calc
    mixedMoment B raw944 raw944Labels = mixedMoment B raw944step0 raw944step0Labels := by
      have ha : raw944step0 = (fun i j => raw944 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw944step0 raw944; decide +kernel
      have hl : raw944step0Labels = raw944Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw944 raw944Labels permutation246 permutation6
    mixedMoment B raw944step0 raw944step0Labels = mixedMoment B raw944step1 raw944step1Labels := by
      have ha : raw944step1 = -raw944step0 := by apply Matrix.ext; change ∀ i j, raw944step1 i j = -(raw944step0 i j); unfold raw944step1 raw944step0; decide +kernel
      have hl : raw944step1Labels = raw944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw944step1 raw944step1Labels = mixedMoment B raw944step2 raw944step2Labels := by
      have ha : raw944step2 = raw944step1 := by apply Matrix.ext; unfold raw944step2 raw944step1; decide +kernel
      have hl : raw944step1Labels = labelEmbedding1 ∘ raw944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw944step1 raw944step1Labels raw944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node818 node818Labels := by rfl

theorem canonical945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw945 raw945Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw945 raw945Labels = mixedMoment B raw945step0 raw945step0Labels := by
      have ha : raw945step0 = (fun i j => raw945 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw945step0 raw945; decide +kernel
      have hl : raw945step0Labels = raw945Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw945 raw945Labels permutation32 permutation4
    mixedMoment B raw945step0 raw945step0Labels = mixedMoment B raw945step1 raw945step1Labels := by
      have ha : raw945step1 = raw945step0 := by apply Matrix.ext; unfold raw945step1 raw945step0; decide +kernel
      have hl : raw945step0Labels = labelEmbedding7 ∘ raw945step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw945step0 raw945step0Labels raw945step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4237 node4237Labels := by rfl

theorem canonical946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw946 raw946Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw946 raw946Labels = mixedMoment B raw946step0 raw946step0Labels := by
      have ha : raw946step0 = (fun i j => raw946 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw946step0 raw946; decide +kernel
      have hl : raw946step0Labels = raw946Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw946 raw946Labels permutation32 permutation4
    _ = mixedMoment B node737 node737Labels := by rfl

theorem canonical947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw947 raw947Labels = mixedMoment B node840 node840Labels := by
  calc
    mixedMoment B raw947 raw947Labels = mixedMoment B raw947step0 raw947step0Labels := by
      have ha : raw947step0 = (fun i j => raw947 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw947step0 raw947; decide +kernel
      have hl : raw947step0Labels = raw947Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw947 raw947Labels permutation32 permutation6
    mixedMoment B raw947step0 raw947step0Labels = mixedMoment B raw947step1 raw947step1Labels := by
      have ha : raw947step1 = -raw947step0 := by apply Matrix.ext; change ∀ i j, raw947step1 i j = -(raw947step0 i j); unfold raw947step1 raw947step0; decide +kernel
      have hl : raw947step1Labels = raw947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw947step1 raw947step1Labels = mixedMoment B raw947step2 raw947step2Labels := by
      have ha : raw947step2 = raw947step1 := by apply Matrix.ext; unfold raw947step2 raw947step1; decide +kernel
      have hl : raw947step1Labels = labelEmbedding1 ∘ raw947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw947step1 raw947step1Labels raw947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node840 node840Labels := by rfl

theorem canonical948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw948 raw948Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw948 raw948Labels = mixedMoment B raw948step0 raw948step0Labels := by
      have ha : raw948step0 = (fun i j => raw948 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw948step0 raw948; decide +kernel
      have hl : raw948step0Labels = raw948Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw948 raw948Labels permutation32 permutation4
    mixedMoment B raw948step0 raw948step0Labels = mixedMoment B raw948step1 raw948step1Labels := by
      have ha : raw948step1 = raw948step0 := by apply Matrix.ext; unfold raw948step1 raw948step0; decide +kernel
      have hl : raw948step0Labels = labelEmbedding7 ∘ raw948step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw948step0 raw948step0Labels raw948step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4238 node4238Labels := by rfl

theorem canonical949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw949 raw949Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw949 raw949Labels = mixedMoment B raw949step0 raw949step0Labels := by
      have ha : raw949step0 = (fun i j => raw949 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw949step0 raw949; decide +kernel
      have hl : raw949step0Labels = raw949Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw949 raw949Labels permutation32 permutation4
    _ = mixedMoment B node738 node738Labels := by rfl

theorem canonical950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw950 raw950Labels = mixedMoment B node819 node819Labels := by
  calc
    mixedMoment B raw950 raw950Labels = mixedMoment B raw950step0 raw950step0Labels := by
      have ha : raw950step0 = (fun i j => raw950 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw950step0 raw950; decide +kernel
      have hl : raw950step0Labels = raw950Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw950 raw950Labels permutation44 permutation6
    mixedMoment B raw950step0 raw950step0Labels = mixedMoment B raw950step1 raw950step1Labels := by
      have ha : raw950step1 = -raw950step0 := by apply Matrix.ext; change ∀ i j, raw950step1 i j = -(raw950step0 i j); unfold raw950step1 raw950step0; decide +kernel
      have hl : raw950step1Labels = raw950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw950step1 raw950step1Labels = mixedMoment B raw950step2 raw950step2Labels := by
      have ha : raw950step2 = raw950step1 := by apply Matrix.ext; unfold raw950step2 raw950step1; decide +kernel
      have hl : raw950step1Labels = labelEmbedding1 ∘ raw950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw950step1 raw950step1Labels raw950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node819 node819Labels := by rfl

theorem canonical1002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1002 raw1002Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw1002 raw1002Labels = mixedMoment B raw1002step0 raw1002step0Labels := by
      have ha : raw1002step0 = (fun i j => raw1002 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1002step0 raw1002; decide +kernel
      have hl : raw1002step0Labels = raw1002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1002 raw1002Labels permutation32 permutation4
    mixedMoment B raw1002step0 raw1002step0Labels = mixedMoment B raw1002step1 raw1002step1Labels := by
      have ha : raw1002step1 = raw1002step0 := by apply Matrix.ext; unfold raw1002step1 raw1002step0; decide +kernel
      have hl : raw1002step0Labels = labelEmbedding7 ∘ raw1002step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1002step0 raw1002step0Labels raw1002step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

theorem canonical1003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1003 raw1003Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw1003 raw1003Labels = mixedMoment B raw1003step0 raw1003step0Labels := by
      have ha : raw1003step0 = (fun i j => raw1003 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1003step0 raw1003; decide +kernel
      have hl : raw1003step0Labels = raw1003Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1003 raw1003Labels permutation32 permutation4
    _ = mixedMoment B node827 node827Labels := by rfl

theorem canonical1004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1004 raw1004Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw1004 raw1004Labels = mixedMoment B raw1004step0 raw1004step0Labels := by
      have ha : raw1004step0 = (fun i j => raw1004 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1004step0 raw1004; decide +kernel
      have hl : raw1004step0Labels = raw1004Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1004 raw1004Labels permutation53 permutation6
    mixedMoment B raw1004step0 raw1004step0Labels = mixedMoment B raw1004step1 raw1004step1Labels := by
      have ha : raw1004step1 = -raw1004step0 := by apply Matrix.ext; change ∀ i j, raw1004step1 i j = -(raw1004step0 i j); unfold raw1004step1 raw1004step0; decide +kernel
      have hl : raw1004step1Labels = raw1004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1004step1 raw1004step1Labels = mixedMoment B raw1004step2 raw1004step2Labels := by
      have ha : raw1004step2 = raw1004step1 := by apply Matrix.ext; unfold raw1004step2 raw1004step1; decide +kernel
      have hl : raw1004step1Labels = labelEmbedding1 ∘ raw1004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1004step1 raw1004step1Labels raw1004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node827 node827Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10769 raw10769Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw10769 raw10769Labels = mixedMoment B raw10769step0 raw10769step0Labels := by
      have hz : ∀ j, raw10769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10769step0 = (fun i j => raw10769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10769step0 raw10769; decide +kernel
      have hl : raw10769step0Labels = raw10769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10769 raw10769Labels permutation434 hz
    mixedMoment B raw10769step0 raw10769step0Labels = mixedMoment B raw10769step1 raw10769step1Labels := by
      have hz : ∀ j, raw10769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10769step1 = (fun i j => raw10769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10769step1 raw10769step0; decide +kernel
      have hl : raw10769step1Labels = raw10769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10769step0 raw10769step0Labels permutation80 hz
    mixedMoment B raw10769step1 raw10769step1Labels = mixedMoment B raw10769step2 raw10769step2Labels := by
      have ha : raw10769step2 = (fun i j => raw10769step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10769step2 raw10769step1; decide +kernel
      have hl : raw10769step2Labels = raw10769step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10769step1 raw10769step1Labels permutation31 permutation2
    mixedMoment B raw10769step2 raw10769step2Labels = mixedMoment B raw10769step3 raw10769step3Labels := by
      have ha : raw10769step3 = -raw10769step2 := by apply Matrix.ext; change ∀ i j, raw10769step3 i j = -(raw10769step2 i j); unfold raw10769step3 raw10769step2; decide +kernel
      have hl : raw10769step3Labels = raw10769step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

theorem canonical10780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10780 raw10780Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10780 raw10780Labels = mixedMoment B raw10780step0 raw10780step0Labels := by
      have hz : ∀ j, raw10780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10780step0 = (fun i j => raw10780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10780step0 raw10780; decide +kernel
      have hl : raw10780step0Labels = raw10780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10780 raw10780Labels permutation434 hz
    mixedMoment B raw10780step0 raw10780step0Labels = mixedMoment B raw10780step1 raw10780step1Labels := by
      have ha : raw10780step1 = (fun i j => raw10780step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10780step1 raw10780step0; decide +kernel
      have hl : raw10780step1Labels = raw10780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10780step0 raw10780step0Labels permutation32 permutation3
    mixedMoment B raw10780step1 raw10780step1Labels = mixedMoment B raw10780step2 raw10780step2Labels := by
      have ha : raw10780step2 = raw10780step1 := by apply Matrix.ext; unfold raw10780step2 raw10780step1; decide +kernel
      have hl : raw10780step1Labels = labelEmbedding6 ∘ raw10780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10780step1 raw10780step1Labels raw10780step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical10784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10784 raw10784Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw10784 raw10784Labels = mixedMoment B raw10784step0 raw10784step0Labels := by
      have hz : ∀ j, raw10784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10784step0 = (fun i j => raw10784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10784step0 raw10784; decide +kernel
      have hl : raw10784step0Labels = raw10784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10784 raw10784Labels permutation346 hz
    mixedMoment B raw10784step0 raw10784step0Labels = mixedMoment B raw10784step1 raw10784step1Labels := by
      have ha : raw10784step1 = (fun i j => raw10784step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10784step1 raw10784step0; decide +kernel
      have hl : raw10784step1Labels = raw10784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10784step0 raw10784step0Labels permutation32 permutation3
    mixedMoment B raw10784step1 raw10784step1Labels = mixedMoment B raw10784step2 raw10784step2Labels := by
      have ha : raw10784step2 = raw10784step1 := by apply Matrix.ext; unfold raw10784step2 raw10784step1; decide +kernel
      have hl : raw10784step1Labels = labelEmbedding6 ∘ raw10784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10784step1 raw10784step1Labels raw10784step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

theorem canonical10786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10786 raw10786Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw10786 raw10786Labels = mixedMoment B raw10786step0 raw10786step0Labels := by
      have ha : raw10786step0 = (fun i j => raw10786 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10786step0 raw10786; decide +kernel
      have hl : raw10786step0Labels = raw10786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10786 raw10786Labels permutation176 permutation3
    mixedMoment B raw10786step0 raw10786step0Labels = mixedMoment B raw10786step1 raw10786step1Labels := by
      have ha : raw10786step1 = raw10786step0 := by apply Matrix.ext; unfold raw10786step1 raw10786step0; decide +kernel
      have hl : raw10786step0Labels = labelEmbedding6 ∘ raw10786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10786step0 raw10786step0Labels raw10786step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

theorem canonical10787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10787 raw10787Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw10787 raw10787Labels = mixedMoment B raw10787step0 raw10787step0Labels := by
      have hz : ∀ j, raw10787 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10787step0 = (fun i j => raw10787 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10787step0 raw10787; decide +kernel
      have hl : raw10787step0Labels = raw10787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10787 raw10787Labels permutation520 hz
    mixedMoment B raw10787step0 raw10787step0Labels = mixedMoment B raw10787step1 raw10787step1Labels := by
      have hz : ∀ j, raw10787step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10787step1 = (fun i j => raw10787step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10787step1 raw10787step0; decide +kernel
      have hl : raw10787step1Labels = raw10787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10787step0 raw10787step0Labels permutation80 hz
    mixedMoment B raw10787step1 raw10787step1Labels = mixedMoment B raw10787step2 raw10787step2Labels := by
      have ha : raw10787step2 = (fun i j => raw10787step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10787step2 raw10787step1; decide +kernel
      have hl : raw10787step2Labels = raw10787step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10787step1 raw10787step1Labels permutation8 permutation3
    mixedMoment B raw10787step2 raw10787step2Labels = mixedMoment B raw10787step3 raw10787step3Labels := by
      have ha : raw10787step3 = raw10787step2 := by apply Matrix.ext; unfold raw10787step3 raw10787step2; decide +kernel
      have hl : raw10787step2Labels = labelEmbedding6 ∘ raw10787step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10787step2 raw10787step2Labels raw10787step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

theorem canonical10788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10788 raw10788Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10788 raw10788Labels = mixedMoment B raw10788step0 raw10788step0Labels := by
      have hz : ∀ j, raw10788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10788step0 = (fun i j => raw10788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10788step0 raw10788; decide +kernel
      have hl : raw10788step0Labels = raw10788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10788 raw10788Labels permutation346 hz
    mixedMoment B raw10788step0 raw10788step0Labels = mixedMoment B raw10788step1 raw10788step1Labels := by
      have ha : raw10788step1 = (fun i j => raw10788step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10788step1 raw10788step0; decide +kernel
      have hl : raw10788step1Labels = raw10788step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10788step0 raw10788step0Labels permutation53 permutation5
    mixedMoment B raw10788step1 raw10788step1Labels = mixedMoment B raw10788step2 raw10788step2Labels := by
      have ha : raw10788step2 = -raw10788step1 := by apply Matrix.ext; change ∀ i j, raw10788step2 i j = -(raw10788step1 i j); unfold raw10788step2 raw10788step1; decide +kernel
      have hl : raw10788step2Labels = raw10788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10788step2 raw10788step2Labels = mixedMoment B raw10788step3 raw10788step3Labels := by
      have ha : raw10788step3 = raw10788step2 := by apply Matrix.ext; unfold raw10788step3 raw10788step2; decide +kernel
      have hl : raw10788step2Labels = labelEmbedding8 ∘ raw10788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10788step2 raw10788step2Labels raw10788step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical10790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10790 raw10790Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw10790 raw10790Labels = mixedMoment B raw10790step0 raw10790step0Labels := by
      have hz : ∀ j, raw10790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10790step0 = (fun i j => raw10790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10790step0 raw10790; decide +kernel
      have hl : raw10790step0Labels = raw10790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10790 raw10790Labels permutation434 hz
    mixedMoment B raw10790step0 raw10790step0Labels = mixedMoment B raw10790step1 raw10790step1Labels := by
      have hz : ∀ j, raw10790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10790step1 = (fun i j => raw10790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10790step1 raw10790step0; decide +kernel
      have hl : raw10790step1Labels = raw10790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10790step0 raw10790step0Labels permutation80 hz
    mixedMoment B raw10790step1 raw10790step1Labels = mixedMoment B raw10790step2 raw10790step2Labels := by
      have ha : raw10790step2 = (fun i j => raw10790step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10790step2 raw10790step1; decide +kernel
      have hl : raw10790step2Labels = raw10790step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10790step1 raw10790step1Labels permutation9 permutation3
    mixedMoment B raw10790step2 raw10790step2Labels = mixedMoment B raw10790step3 raw10790step3Labels := by
      have ha : raw10790step3 = raw10790step2 := by apply Matrix.ext; unfold raw10790step3 raw10790step2; decide +kernel
      have hl : raw10790step2Labels = labelEmbedding6 ∘ raw10790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10790step2 raw10790step2Labels raw10790step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

theorem canonical10795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10795 raw10795Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw10795 raw10795Labels = mixedMoment B raw10795step0 raw10795step0Labels := by
      have hz : ∀ j, raw10795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10795step0 = (fun i j => raw10795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10795step0 raw10795; decide +kernel
      have hl : raw10795step0Labels = raw10795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10795 raw10795Labels permutation434 hz
    mixedMoment B raw10795step0 raw10795step0Labels = mixedMoment B raw10795step1 raw10795step1Labels := by
      have hz : ∀ j, raw10795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10795step1 = (fun i j => raw10795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10795step1 raw10795step0; decide +kernel
      have hl : raw10795step1Labels = raw10795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10795step0 raw10795step0Labels permutation80 hz
    mixedMoment B raw10795step1 raw10795step1Labels = mixedMoment B raw10795step2 raw10795step2Labels := by
      have ha : raw10795step2 = (fun i j => raw10795step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10795step2 raw10795step1; decide +kernel
      have hl : raw10795step2Labels = raw10795step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10795step1 raw10795step1Labels permutation8 permutation3
    mixedMoment B raw10795step2 raw10795step2Labels = mixedMoment B raw10795step3 raw10795step3Labels := by
      have ha : raw10795step3 = raw10795step2 := by apply Matrix.ext; unfold raw10795step3 raw10795step2; decide +kernel
      have hl : raw10795step2Labels = labelEmbedding6 ∘ raw10795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10795step2 raw10795step2Labels raw10795step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3963 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3963 = injectiveMoment H node203 := by
  calc
    injectiveMoment H raw3963 = injectiveMoment H raw3963step0 := by
      have heq : raw3963step0 = -raw3963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3963).symm
    injectiveMoment H raw3963step0 = injectiveMoment H raw3963step1 := by
      have heq : raw3963step1 = (fun i j => raw3963step0 (permutation10 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3963step0 permutation10 permutation8
    _ = injectiveMoment H node203 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5141 = injectiveMoment H node46 := by
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

theorem canonical5185 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5185 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5185 = injectiveMoment H raw5185step0 := by
      have hz : ∀ j, raw5185 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5185step0 = (fun i j => raw5185 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185 permutation27 hz
    injectiveMoment H raw5185step0 = injectiveMoment H raw5185step1 := by
      have hz : ∀ j, raw5185step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5185step1 = (fun i j => raw5185step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5185step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9013 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9013 = injectiveMoment H raw9013step0 := by
      have hz : ∀ j, raw9013 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9013step0 = (fun i j => raw9013 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9013 permutation9 hz
    injectiveMoment H raw9013step0 = injectiveMoment H raw9013step1 := by
      have heq : raw9013step1 = (fun i j => raw9013step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9013step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound46 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node46 = Sparse.eval value46 (momentVector H) := by
  have heq : pivotMatrix46 = (fun u v => node46 (pivotPermutation46 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node46 = injectiveMoment H pivotMatrix46 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix46 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix46 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (1 : Fin 3) = raw5183 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5183 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix46 (2 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node46 + (injectiveMoment H (mergeFirst pivotMatrix46 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix46 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value46, value10, value11, value4, Sparse.eval] at hc ⊢
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

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

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

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

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

theorem sound203 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node203 = Sparse.eval value203 (momentVector H) := by
  have heq : pivotMatrix203 = (fun u v => node203 (pivotPermutation203 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node203 = injectiveMoment H pivotMatrix203 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix203 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix203 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (0 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (1 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix203 (2 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node203 + (injectiveMoment H (mergeFirst pivotMatrix203 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix203 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value203, value36, value41, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

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

theorem singlePair496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node496 node496Labels = Sparse.eval singlePairValue496 (familyPairVector B) := by
  have hp := single_label_three B hB node496
  have hl : node496Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node496 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 1) = PairSemantics.raw5185 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node496 PairSemantics.raw5185; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5185 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 2) = PairSemantics.raw9013 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node496 PairSemantics.raw9013; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9013 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value46 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 3) = PairSemantics.raw5141 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node496 PairSemantics.raw5141; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5141 hH).trans (PairSemantics.sound46 hH)
  have hm4 : familyPairMoment B (groupedColumns node496 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value203 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node496 (EqualityPatterns.family3.label 4) = PairSemantics.raw3963 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node496 PairSemantics.raw3963; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3963 hH).trans (PairSemantics.sound203 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue496, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value46, PairSemantics.value203, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3862 node3862Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node496 node496Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw536 singletonSmall3862
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3862) = raw536Labels := by decide +kernel
  rw [hl, canonical536 B hB] at h
  have hc0 : mixedMoment B raw536 (Fin.cases (0 : Fin 1) singletonSmall3862) =
      mixedMoment B node496 node496Labels := by
    have ha : raw536 = raw537 := by apply Matrix.ext; unfold raw536 raw537; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3862 = raw537Labels := by decide +kernel
    rw [ha, hj, canonical537 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4236 node4236Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node736 node736Labels + mixedMoment B node818 node818Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw942 singletonSmall4236
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4236) = raw942Labels := by decide +kernel
  rw [hl, canonical942 B hB] at h
  have hc0 : mixedMoment B raw942 (Fin.cases (0 : Fin 2) singletonSmall4236) =
      mixedMoment B node736 node736Labels := by
    have ha : raw942 = raw943 := by apply Matrix.ext; unfold raw942 raw943; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4236 = raw943Labels := by decide +kernel
    rw [ha, hj, canonical943 B hB]
  have hc1 : mixedMoment B raw942 (Fin.cases (1 : Fin 2) singletonSmall4236) =
      mixedMoment B node818 node818Labels := by
    have ha : raw942 = raw944 := by apply Matrix.ext; unfold raw942 raw944; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4236 = raw944Labels := by decide +kernel
    rw [ha, hj, canonical944 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4237 node4237Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node737 node737Labels + mixedMoment B node840 node840Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw945 singletonSmall4237
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4237) = raw945Labels := by decide +kernel
  rw [hl, canonical945 B hB] at h
  have hc0 : mixedMoment B raw945 (Fin.cases (0 : Fin 2) singletonSmall4237) =
      mixedMoment B node737 node737Labels := by
    have ha : raw945 = raw946 := by apply Matrix.ext; unfold raw945 raw946; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4237 = raw946Labels := by decide +kernel
    rw [ha, hj, canonical946 B hB]
  have hc1 : mixedMoment B raw945 (Fin.cases (1 : Fin 2) singletonSmall4237) =
      mixedMoment B node840 node840Labels := by
    have ha : raw945 = raw947 := by apply Matrix.ext; unfold raw945 raw947; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4237 = raw947Labels := by decide +kernel
    rw [ha, hj, canonical947 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4238 node4238Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node738 node738Labels + mixedMoment B node819 node819Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw948 singletonSmall4238
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4238) = raw948Labels := by decide +kernel
  rw [hl, canonical948 B hB] at h
  have hc0 : mixedMoment B raw948 (Fin.cases (0 : Fin 2) singletonSmall4238) =
      mixedMoment B node738 node738Labels := by
    have ha : raw948 = raw949 := by apply Matrix.ext; unfold raw948 raw949; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4238 = raw949Labels := by decide +kernel
    rw [ha, hj, canonical949 B hB]
  have hc1 : mixedMoment B raw948 (Fin.cases (1 : Fin 2) singletonSmall4238) =
      mixedMoment B node819 node819Labels := by
    have ha : raw948 = raw950 := by apply Matrix.ext; unfold raw948 raw950; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4238 = raw950Labels := by decide +kernel
    rw [ha, hj, canonical950 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4275 node4275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node827 node827Labels + mixedMoment B node827 node827Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1002 singletonSmall4275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4275) = raw1002Labels := by decide +kernel
  rw [hl, canonical1002 B hB] at h
  have hc0 : mixedMoment B raw1002 (Fin.cases (0 : Fin 2) singletonSmall4275) =
      mixedMoment B node827 node827Labels := by
    have ha : raw1002 = raw1003 := by apply Matrix.ext; unfold raw1002 raw1003; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4275 = raw1003Labels := by decide +kernel
    rw [ha, hj, canonical1003 B hB]
  have hc1 : mixedMoment B raw1002 (Fin.cases (1 : Fin 2) singletonSmall4275) =
      mixedMoment B node827 node827Labels := by
    have ha : raw1002 = raw1004 := by apply Matrix.ext; unfold raw1002 raw1004; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4275 = raw1004Labels := by decide +kernel
    rw [ha, hj, canonical1004 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4685 node4685Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1811 node1811Labels + mixedMoment B node2156 node2156Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1569 singletonSmall4685
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4685) = raw1569Labels := by decide +kernel
  rw [hl, canonical1569 B hB] at h
  have hc0 : mixedMoment B raw1569 (Fin.cases (0 : Fin 2) singletonSmall4685) =
      mixedMoment B node1811 node1811Labels := by
    have ha : raw1569 = raw1570 := by apply Matrix.ext; unfold raw1569 raw1570; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4685 = raw1570Labels := by decide +kernel
    rw [ha, hj, canonical1570 B hB]
  have hc1 : mixedMoment B raw1569 (Fin.cases (1 : Fin 2) singletonSmall4685) =
      mixedMoment B node2156 node2156Labels := by
    have ha : raw1569 = raw1571 := by apply Matrix.ext; unfold raw1569 raw1571; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4685 = raw1571Labels := by decide +kernel
    rw [ha, hj, canonical1571 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4686 node4686Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1812 node1812Labels + mixedMoment B node2165 node2165Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1572 singletonSmall4686
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4686) = raw1572Labels := by decide +kernel
  rw [hl, canonical1572 B hB] at h
  have hc0 : mixedMoment B raw1572 (Fin.cases (0 : Fin 2) singletonSmall4686) =
      mixedMoment B node1812 node1812Labels := by
    have ha : raw1572 = raw1573 := by apply Matrix.ext; unfold raw1572 raw1573; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4686 = raw1573Labels := by decide +kernel
    rw [ha, hj, canonical1573 B hB]
  have hc1 : mixedMoment B raw1572 (Fin.cases (1 : Fin 2) singletonSmall4686) =
      mixedMoment B node2165 node2165Labels := by
    have ha : raw1572 = raw1574 := by apply Matrix.ext; unfold raw1572 raw1574; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4686 = raw1574Labels := by decide +kernel
    rw [ha, hj, canonical1574 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4688 node4688Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1814 node1814Labels + mixedMoment B node2157 node2157Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1575 singletonSmall4688
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4688) = raw1575Labels := by decide +kernel
  rw [hl, canonical1575 B hB] at h
  have hc0 : mixedMoment B raw1575 (Fin.cases (0 : Fin 2) singletonSmall4688) =
      mixedMoment B node1814 node1814Labels := by
    have ha : raw1575 = raw1576 := by apply Matrix.ext; unfold raw1575 raw1576; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4688 = raw1576Labels := by decide +kernel
    rw [ha, hj, canonical1576 B hB]
  have hc1 : mixedMoment B raw1575 (Fin.cases (1 : Fin 2) singletonSmall4688) =
      mixedMoment B node2157 node2157Labels := by
    have ha : raw1575 = raw1577 := by apply Matrix.ext; unfold raw1575 raw1577; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4688 = raw1577Labels := by decide +kernel
    rw [ha, hj, canonical1577 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4723 node4723Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1877 node1877Labels + mixedMoment B node1935 node1935Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1626 singletonSmall4723
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4723) = raw1626Labels := by decide +kernel
  rw [hl, canonical1626 B hB] at h
  have hc0 : mixedMoment B raw1626 (Fin.cases (0 : Fin 2) singletonSmall4723) =
      mixedMoment B node1877 node1877Labels := by
    have ha : raw1626 = raw1627 := by apply Matrix.ext; unfold raw1626 raw1627; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4723 = raw1627Labels := by decide +kernel
    rw [ha, hj, canonical1627 B hB]
  have hc1 : mixedMoment B raw1626 (Fin.cases (1 : Fin 2) singletonSmall4723) =
      mixedMoment B node1935 node1935Labels := by
    have ha : raw1626 = raw1628 := by apply Matrix.ext; unfold raw1626 raw1628; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4723 = raw1628Labels := by decide +kernel
    rw [ha, hj, canonical1628 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4724 node4724Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1878 node1878Labels + mixedMoment B node1919 node1919Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1629 singletonSmall4724
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4724) = raw1629Labels := by decide +kernel
  rw [hl, canonical1629 B hB] at h
  have hc0 : mixedMoment B raw1629 (Fin.cases (0 : Fin 2) singletonSmall4724) =
      mixedMoment B node1878 node1878Labels := by
    have ha : raw1629 = raw1630 := by apply Matrix.ext; unfold raw1629 raw1630; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4724 = raw1630Labels := by decide +kernel
    rw [ha, hj, canonical1630 B hB]
  have hc1 : mixedMoment B raw1629 (Fin.cases (1 : Fin 2) singletonSmall4724) =
      mixedMoment B node1919 node1919Labels := by
    have ha : raw1629 = raw1631 := by apply Matrix.ext; unfold raw1629 raw1631; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4724 = raw1631Labels := by decide +kernel
    rw [ha, hj, canonical1631 B hB]
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

theorem singleton4746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4746 node4746Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1925 node1925Labels + mixedMoment B node1925 node1925Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1665 singletonSmall4746
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4746) = raw1665Labels := by decide +kernel
  rw [hl, canonical1665 B hB] at h
  have hc0 : mixedMoment B raw1665 (Fin.cases (0 : Fin 2) singletonSmall4746) =
      mixedMoment B node1925 node1925Labels := by
    have ha : raw1665 = raw1666 := by apply Matrix.ext; unfold raw1665 raw1666; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4746 = raw1666Labels := by decide +kernel
    rw [ha, hj, canonical1666 B hB]
  have hc1 : mixedMoment B raw1665 (Fin.cases (1 : Fin 2) singletonSmall4746) =
      mixedMoment B node1925 node1925Labels := by
    have ha : raw1665 = raw1667 := by apply Matrix.ext; unfold raw1665 raw1667; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4746 = raw1667Labels := by decide +kernel
    rw [ha, hj, canonical1667 B hB]
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

theorem singleton4859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4859 node4859Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2100 node2100Labels + mixedMoment B node2100 node2100Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1779 singletonSmall4859
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4859) = raw1779Labels := by decide +kernel
  rw [hl, canonical1779 B hB] at h
  have hc0 : mixedMoment B raw1779 (Fin.cases (0 : Fin 2) singletonSmall4859) =
      mixedMoment B node2100 node2100Labels := by
    have ha : raw1779 = raw1780 := by apply Matrix.ext; unfold raw1779 raw1780; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4859 = raw1780Labels := by decide +kernel
    rw [ha, hj, canonical1780 B hB]
  have hc1 : mixedMoment B raw1779 (Fin.cases (1 : Fin 2) singletonSmall4859) =
      mixedMoment B node2100 node2100Labels := by
    have ha : raw1779 = raw1781 := by apply Matrix.ext; unfold raw1779 raw1781; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4859 = raw1781Labels := by decide +kernel
    rw [ha, hj, canonical1781 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4860 node4860Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2101 node2101Labels + mixedMoment B node2101 node2101Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1782 singletonSmall4860
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4860) = raw1782Labels := by decide +kernel
  rw [hl, canonical1782 B hB] at h
  have hc0 : mixedMoment B raw1782 (Fin.cases (0 : Fin 2) singletonSmall4860) =
      mixedMoment B node2101 node2101Labels := by
    have ha : raw1782 = raw1783 := by apply Matrix.ext; unfold raw1782 raw1783; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4860 = raw1783Labels := by decide +kernel
    rw [ha, hj, canonical1783 B hB]
  have hc1 : mixedMoment B raw1782 (Fin.cases (1 : Fin 2) singletonSmall4860) =
      mixedMoment B node2101 node2101Labels := by
    have ha : raw1782 = raw1784 := by apply Matrix.ext; unfold raw1782 raw1784; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4860 = raw1784Labels := by decide +kernel
    rw [ha, hj, canonical1784 B hB]
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

theorem singleton4869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4869 node4869Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2110 node2110Labels + mixedMoment B node2275 node2275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1800 singletonSmall4869
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4869) = raw1800Labels := by decide +kernel
  rw [hl, canonical1800 B hB] at h
  have hc0 : mixedMoment B raw1800 (Fin.cases (0 : Fin 2) singletonSmall4869) =
      mixedMoment B node2110 node2110Labels := by
    have ha : raw1800 = raw1801 := by apply Matrix.ext; unfold raw1800 raw1801; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4869 = raw1801Labels := by decide +kernel
    rw [ha, hj, canonical1801 B hB]
  have hc1 : mixedMoment B raw1800 (Fin.cases (1 : Fin 2) singletonSmall4869) =
      mixedMoment B node2275 node2275Labels := by
    have ha : raw1800 = raw1802 := by apply Matrix.ext; unfold raw1800 raw1802; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4869 = raw1802Labels := by decide +kernel
    rw [ha, hj, canonical1802 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4871 node4871Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2112 node2112Labels + mixedMoment B node2287 node2287Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1803 singletonSmall4871
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4871) = raw1803Labels := by decide +kernel
  rw [hl, canonical1803 B hB] at h
  have hc0 : mixedMoment B raw1803 (Fin.cases (0 : Fin 2) singletonSmall4871) =
      mixedMoment B node2112 node2112Labels := by
    have ha : raw1803 = raw1804 := by apply Matrix.ext; unfold raw1803 raw1804; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4871 = raw1804Labels := by decide +kernel
    rw [ha, hj, canonical1804 B hB]
  have hc1 : mixedMoment B raw1803 (Fin.cases (1 : Fin 2) singletonSmall4871) =
      mixedMoment B node2287 node2287Labels := by
    have ha : raw1803 = raw1805 := by apply Matrix.ext; unfold raw1803 raw1805; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4871 = raw1805Labels := by decide +kernel
    rw [ha, hj, canonical1805 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4874 node4874Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2115 node2115Labels + mixedMoment B node2276 node2276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1806 singletonSmall4874
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4874) = raw1806Labels := by decide +kernel
  rw [hl, canonical1806 B hB] at h
  have hc0 : mixedMoment B raw1806 (Fin.cases (0 : Fin 2) singletonSmall4874) =
      mixedMoment B node2115 node2115Labels := by
    have ha : raw1806 = raw1807 := by apply Matrix.ext; unfold raw1806 raw1807; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4874 = raw1807Labels := by decide +kernel
    rw [ha, hj, canonical1807 B hB]
  have hc1 : mixedMoment B raw1806 (Fin.cases (1 : Fin 2) singletonSmall4874) =
      mixedMoment B node2276 node2276Labels := by
    have ha : raw1806 = raw1808 := by apply Matrix.ext; unfold raw1806 raw1808; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4874 = raw1808Labels := by decide +kernel
    rw [ha, hj, canonical1808 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4898 node4898Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2279 node2279Labels + mixedMoment B node2279 node2279Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1827 singletonSmall4898
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4898) = raw1827Labels := by decide +kernel
  rw [hl, canonical1827 B hB] at h
  have hc0 : mixedMoment B raw1827 (Fin.cases (0 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1828 := by apply Matrix.ext; unfold raw1827 raw1828; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4898 = raw1828Labels := by decide +kernel
    rw [ha, hj, canonical1828 B hB]
  have hc1 : mixedMoment B raw1827 (Fin.cases (1 : Fin 2) singletonSmall4898) =
      mixedMoment B node2279 node2279Labels := by
    have ha : raw1827 = raw1829 := by apply Matrix.ext; unfold raw1827 raw1829; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4898 = raw1829Labels := by decide +kernel
    rw [ha, hj, canonical1829 B hB]
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

theorem singleton5403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5403 node5403Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3789 node3789Labels + mixedMoment B node3810 node3810Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2478 singletonSmall5403
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5403) = raw2478Labels := by decide +kernel
  rw [hl, canonical2478 B hB] at h
  have hc0 : mixedMoment B raw2478 (Fin.cases (0 : Fin 2) singletonSmall5403) =
      mixedMoment B node3789 node3789Labels := by
    have ha : raw2478 = raw2479 := by apply Matrix.ext; unfold raw2478 raw2479; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5403 = raw2479Labels := by decide +kernel
    rw [ha, hj, canonical2479 B hB]
  have hc1 : mixedMoment B raw2478 (Fin.cases (1 : Fin 2) singletonSmall5403) =
      mixedMoment B node3810 node3810Labels := by
    have ha : raw2478 = raw2480 := by apply Matrix.ext; unfold raw2478 raw2480; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5403 = raw2480Labels := by decide +kernel
    rw [ha, hj, canonical2480 B hB]
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

theorem singleton5443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5443 node5443Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3862 node3862Labels + mixedMoment B node3907 node3907Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2544 singletonSmall5443
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5443) = raw2544Labels := by decide +kernel
  rw [hl, canonical2544 B hB] at h
  have hc0 : mixedMoment B raw2544 (Fin.cases (0 : Fin 2) singletonSmall5443) =
      mixedMoment B node3862 node3862Labels := by
    have ha : raw2544 = raw2545 := by apply Matrix.ext; unfold raw2544 raw2545; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5443 = raw2545Labels := by decide +kernel
    rw [ha, hj, canonical2545 B hB]
  have hc1 : mixedMoment B raw2544 (Fin.cases (1 : Fin 2) singletonSmall5443) =
      mixedMoment B node3907 node3907Labels := by
    have ha : raw2544 = raw2546 := by apply Matrix.ext; unfold raw2544 raw2546; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5443 = raw2546Labels := by decide +kernel
    rw [ha, hj, canonical2546 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5448 node5448Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3885 node3885Labels + mixedMoment B node3885 node3885Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2550 singletonSmall5448
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5448) = raw2550Labels := by decide +kernel
  rw [hl, canonical2550 B hB] at h
  have hc0 : mixedMoment B raw2550 (Fin.cases (0 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2551 := by apply Matrix.ext; unfold raw2550 raw2551; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5448 = raw2551Labels := by decide +kernel
    rw [ha, hj, canonical2551 B hB]
  have hc1 : mixedMoment B raw2550 (Fin.cases (1 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2552 := by apply Matrix.ext; unfold raw2550 raw2552; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5448 = raw2552Labels := by decide +kernel
    rw [ha, hj, canonical2552 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem sound496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node496 node496Labels = Sparse.eval nodeValue496 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue496 (familyPairVector B) := singlePair496 B _hB
    _ = _ := by norm_num [singlePairValue496, nodeValue496, Sparse.eval, mixedVector] <;> ring

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound3862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3862 node3862Labels = Sparse.eval nodeValue3862 (mixedVector B) := by
  have h := singleton3862 B _hB
  rw [sound496 B _hB _hF] at h
  norm_num [nodeValue3862, nodeValue496, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

theorem sound4898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4898 node4898Labels = Sparse.eval nodeValue4898 (mixedVector B) := by
  have h := singleton4898 B _hB
  rw [sound2279 B _hB _hF] at h
  norm_num [nodeValue4898, nodeValue2279, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5443 node5443Labels = Sparse.eval nodeValue5443 (mixedVector B) := by
  have h := singleton5443 B _hB
  rw [sound3862 B _hB _hF, sound3907 B _hB _hF] at h
  norm_num [nodeValue5443, nodeValue3862, nodeValue3907, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node736 node736Labels = Sparse.eval nodeValue736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 736) = mixedMoment B node736 node736Labels := rfl
  simpa [nodeValue736, Sparse.eval] using hc.symm

theorem sound737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node737 node737Labels = Sparse.eval nodeValue737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 737) = mixedMoment B node737 node737Labels := rfl
  simpa [nodeValue737, Sparse.eval] using hc.symm

theorem sound738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node738 node738Labels = Sparse.eval nodeValue738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 738) = mixedMoment B node738 node738Labels := rfl
  simpa [nodeValue738, Sparse.eval] using hc.symm

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

theorem sound818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node818 node818Labels = Sparse.eval nodeValue818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 818) = mixedMoment B node818 node818Labels := rfl
  simpa [nodeValue818, Sparse.eval] using hc.symm

theorem sound819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node819 node819Labels = Sparse.eval nodeValue819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 819) = mixedMoment B node819 node819Labels := rfl
  simpa [nodeValue819, Sparse.eval] using hc.symm

theorem sound827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node827 node827Labels = Sparse.eval nodeValue827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 827) = mixedMoment B node827 node827Labels := rfl
  simpa [nodeValue827, Sparse.eval] using hc.symm

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

theorem sound840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node840 node840Labels = Sparse.eval nodeValue840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 840) = mixedMoment B node840 node840Labels := rfl
  simpa [nodeValue840, Sparse.eval] using hc.symm

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

theorem sound1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1811 node1811Labels = Sparse.eval nodeValue1811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1811) = mixedMoment B node1811 node1811Labels := rfl
  simpa [nodeValue1811, Sparse.eval] using hc.symm

theorem sound1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1812 node1812Labels = Sparse.eval nodeValue1812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1812) = mixedMoment B node1812 node1812Labels := rfl
  simpa [nodeValue1812, Sparse.eval] using hc.symm

theorem sound1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1814 node1814Labels = Sparse.eval nodeValue1814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1814) = mixedMoment B node1814 node1814Labels := rfl
  simpa [nodeValue1814, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1877 node1877Labels = Sparse.eval nodeValue1877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1877) = mixedMoment B node1877 node1877Labels := rfl
  simpa [nodeValue1877, Sparse.eval] using hc.symm

theorem sound1878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1878 node1878Labels = Sparse.eval nodeValue1878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1878) = mixedMoment B node1878 node1878Labels := rfl
  simpa [nodeValue1878, Sparse.eval] using hc.symm

theorem sound1919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1919 node1919Labels = Sparse.eval nodeValue1919 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1919) = mixedMoment B node1919 node1919Labels := rfl
  simpa [nodeValue1919, Sparse.eval] using hc.symm

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

theorem sound1925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1925 node1925Labels = Sparse.eval nodeValue1925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1925) = mixedMoment B node1925 node1925Labels := rfl
  simpa [nodeValue1925, Sparse.eval] using hc.symm

theorem sound1935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1935 node1935Labels = Sparse.eval nodeValue1935 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1935) = mixedMoment B node1935 node1935Labels := rfl
  simpa [nodeValue1935, Sparse.eval] using hc.symm

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

theorem sound2100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2100 node2100Labels = Sparse.eval nodeValue2100 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2100) = mixedMoment B node2100 node2100Labels := rfl
  simpa [nodeValue2100, Sparse.eval] using hc.symm

theorem sound2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2101 node2101Labels = Sparse.eval nodeValue2101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2101) = mixedMoment B node2101 node2101Labels := rfl
  simpa [nodeValue2101, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

theorem sound2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2156 node2156Labels = Sparse.eval nodeValue2156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2156) = mixedMoment B node2156 node2156Labels := rfl
  simpa [nodeValue2156, Sparse.eval] using hc.symm

theorem sound2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2157 node2157Labels = Sparse.eval nodeValue2157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2157) = mixedMoment B node2157 node2157Labels := rfl
  simpa [nodeValue2157, Sparse.eval] using hc.symm

theorem sound2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2165 node2165Labels = Sparse.eval nodeValue2165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2165) = mixedMoment B node2165 node2165Labels := rfl
  simpa [nodeValue2165, Sparse.eval] using hc.symm

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

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

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

theorem sound3789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3789 node3789Labels = Sparse.eval nodeValue3789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3789) = mixedMoment B node3789 node3789Labels := rfl
  simpa [nodeValue3789, Sparse.eval] using hc.symm

theorem sound3810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3810 node3810Labels = Sparse.eval nodeValue3810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3810) = mixedMoment B node3810 node3810Labels := rfl
  simpa [nodeValue3810, Sparse.eval] using hc.symm

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

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

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

theorem sound4236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4236 node4236Labels = Sparse.eval nodeValue4236 (mixedVector B) := by
  have h := singleton4236 B _hB
  rw [sound736 B _hB _hF, sound818 B _hB _hF] at h
  norm_num [nodeValue4236, nodeValue736, nodeValue818, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4237 node4237Labels = Sparse.eval nodeValue4237 (mixedVector B) := by
  have h := singleton4237 B _hB
  rw [sound737 B _hB _hF, sound840 B _hB _hF] at h
  norm_num [nodeValue4237, nodeValue737, nodeValue840, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4238 node4238Labels = Sparse.eval nodeValue4238 (mixedVector B) := by
  have h := singleton4238 B _hB
  rw [sound738 B _hB _hF, sound819 B _hB _hF] at h
  norm_num [nodeValue4238, nodeValue738, nodeValue819, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4275 node4275Labels = Sparse.eval nodeValue4275 (mixedVector B) := by
  have h := singleton4275 B _hB
  rw [sound827 B _hB _hF] at h
  norm_num [nodeValue4275, nodeValue827, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4685 node4685Labels = Sparse.eval nodeValue4685 (mixedVector B) := by
  have h := singleton4685 B _hB
  rw [sound1811 B _hB _hF, sound2156 B _hB _hF] at h
  norm_num [nodeValue4685, nodeValue1811, nodeValue2156, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4686 node4686Labels = Sparse.eval nodeValue4686 (mixedVector B) := by
  have h := singleton4686 B _hB
  rw [sound1812 B _hB _hF, sound2165 B _hB _hF] at h
  norm_num [nodeValue4686, nodeValue1812, nodeValue2165, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4688 node4688Labels = Sparse.eval nodeValue4688 (mixedVector B) := by
  have h := singleton4688 B _hB
  rw [sound1814 B _hB _hF, sound2157 B _hB _hF] at h
  norm_num [nodeValue4688, nodeValue1814, nodeValue2157, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4723 node4723Labels = Sparse.eval nodeValue4723 (mixedVector B) := by
  have h := singleton4723 B _hB
  rw [sound1877 B _hB _hF, sound1935 B _hB _hF] at h
  norm_num [nodeValue4723, nodeValue1877, nodeValue1935, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4724 node4724Labels = Sparse.eval nodeValue4724 (mixedVector B) := by
  have h := singleton4724 B _hB
  rw [sound1878 B _hB _hF, sound1919 B _hB _hF] at h
  norm_num [nodeValue4724, nodeValue1878, nodeValue1919, Sparse.eval] at h ⊢
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

theorem sound4746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4746 node4746Labels = Sparse.eval nodeValue4746 (mixedVector B) := by
  have h := singleton4746 B _hB
  rw [sound1925 B _hB _hF] at h
  norm_num [nodeValue4746, nodeValue1925, Sparse.eval] at h ⊢
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

theorem sound4859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4859 node4859Labels = Sparse.eval nodeValue4859 (mixedVector B) := by
  have h := singleton4859 B _hB
  rw [sound2100 B _hB _hF] at h
  norm_num [nodeValue4859, nodeValue2100, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4860 node4860Labels = Sparse.eval nodeValue4860 (mixedVector B) := by
  have h := singleton4860 B _hB
  rw [sound2101 B _hB _hF] at h
  norm_num [nodeValue4860, nodeValue2101, Sparse.eval] at h ⊢
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

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4871 node4871Labels = Sparse.eval nodeValue4871 (mixedVector B) := by
  have h := singleton4871 B _hB
  rw [sound2112 B _hB _hF, sound2287 B _hB _hF] at h
  norm_num [nodeValue4871, nodeValue2112, nodeValue2287, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4874 node4874Labels = Sparse.eval nodeValue4874 (mixedVector B) := by
  have h := singleton4874 B _hB
  rw [sound2115 B _hB _hF, sound2276 B _hB _hF] at h
  norm_num [nodeValue4874, nodeValue2115, nodeValue2276, Sparse.eval] at h ⊢
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

theorem sound5403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5403 node5403Labels = Sparse.eval nodeValue5403 (mixedVector B) := by
  have h := singleton5403 B _hB
  rw [sound3789 B _hB _hF, sound3810 B _hB _hF] at h
  norm_num [nodeValue5403, nodeValue3789, nodeValue3810, Sparse.eval] at h ⊢
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

theorem sound5448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5448 node5448Labels = Sparse.eval nodeValue5448 (mixedVector B) := by
  have h := singleton5448 B _hB
  rw [sound3885 B _hB _hF] at h
  norm_num [nodeValue5448, nodeValue3885, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources76
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2442 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 1) (sourceB2442 + difference 1 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 1) (sourceB2442 + difference 1 0) sourceC2442) = raw19193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19193; decide +kernel
    rw [ha]
    exact (canonical19193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 2) (sourceB2442 + difference 2 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 2) (sourceB2442 + difference 2 0) sourceC2442) = raw19194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19194; decide +kernel
    rw [ha]
    exact (canonical19194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 3) (sourceB2442 + difference 3 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 3) (sourceB2442 + difference 3 0) sourceC2442) = raw10769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10769; decide +kernel
    rw [ha]
    exact (canonical10769 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 4) (sourceB2442 + difference 4 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 4) (sourceB2442 + difference 4 0) sourceC2442) = raw19195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19195; decide +kernel
    rw [ha]
    exact (canonical19195 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2442 + difference 0 5) (sourceB2442 + difference 5 0) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA2442 + difference 0 5) (sourceB2442 + difference 5 0) sourceC2442) = raw33516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33516; decide +kernel
    rw [ha]
    exact (canonical33516 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 0) (sourceB2442 + difference 0 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 0) (sourceB2442 + difference 0 1) sourceC2442) = raw10784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10784; decide +kernel
    rw [ha]
    exact (canonical10784 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 2) (sourceB2442 + difference 2 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 2) (sourceB2442 + difference 2 1) sourceC2442) = raw10786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10786; decide +kernel
    rw [ha]
    exact (canonical10786 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 3) (sourceB2442 + difference 3 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 3) (sourceB2442 + difference 3 1) sourceC2442) = raw31012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw31012; decide +kernel
    rw [ha]
    exact (canonical31012 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 4) (sourceB2442 + difference 4 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 4) (sourceB2442 + difference 4 1) sourceC2442) = raw10787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10787; decide +kernel
    rw [ha]
    exact (canonical10787 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2442 + difference 1 5) (sourceB2442 + difference 5 1) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2442 + difference 1 5) (sourceB2442 + difference 5 1) sourceC2442) = raw10788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10788; decide +kernel
    rw [ha]
    exact (canonical10788 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 0) (sourceB2442 + difference 0 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4236) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 0) (sourceB2442 + difference 0 2) sourceC2442) = raw33517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33517; decide +kernel
    rw [ha]
    exact (canonical33517 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 1) (sourceB2442 + difference 1 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 1) (sourceB2442 + difference 1 2) sourceC2442) = raw33518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33518; decide +kernel
    rw [ha]
    exact (canonical33518 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 3) (sourceB2442 + difference 3 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 3) (sourceB2442 + difference 3 2) sourceC2442) = raw10780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10780; decide +kernel
    rw [ha]
    exact (canonical10780 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 4) (sourceB2442 + difference 4 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 4) (sourceB2442 + difference 4 2) sourceC2442) = raw33519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33519; decide +kernel
    rw [ha]
    exact (canonical33519 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2442 + difference 2 5) (sourceB2442 + difference 5 2) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4859) := by
    have ha : (tripleCharges (sourceA2442 + difference 2 5) (sourceB2442 + difference 5 2) sourceC2442) = raw19178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19178; decide +kernel
    rw [ha]
    exact (canonical19178 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 0) (sourceB2442 + difference 0 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 0) (sourceB2442 + difference 0 3) sourceC2442) = raw33520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33520; decide +kernel
    rw [ha]
    exact (canonical33520 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 1) (sourceB2442 + difference 1 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 1) (sourceB2442 + difference 1 3) sourceC2442) = raw33521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33521; decide +kernel
    rw [ha]
    exact (canonical33521 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 2) (sourceB2442 + difference 2 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 2) (sourceB2442 + difference 2 3) sourceC2442) = raw33522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33522; decide +kernel
    rw [ha]
    exact (canonical33522 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 4) (sourceB2442 + difference 4 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 4) (sourceB2442 + difference 4 3) sourceC2442) = raw33523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33523; decide +kernel
    rw [ha]
    exact (canonical33523 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2442 + difference 3 5) (sourceB2442 + difference 5 3) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2442 + difference 3 5) (sourceB2442 + difference 5 3) sourceC2442) = raw19183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19183; decide +kernel
    rw [ha]
    exact (canonical19183 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 0) (sourceB2442 + difference 0 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 0) (sourceB2442 + difference 0 4) sourceC2442) = raw31017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw31017; decide +kernel
    rw [ha]
    exact (canonical31017 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 1) (sourceB2442 + difference 1 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 1) (sourceB2442 + difference 1 4) sourceC2442) = raw31018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw31018; decide +kernel
    rw [ha]
    exact (canonical31018 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 2) (sourceB2442 + difference 2 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 2) (sourceB2442 + difference 2 4) sourceC2442) = raw31019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw31019; decide +kernel
    rw [ha]
    exact (canonical31019 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 3) (sourceB2442 + difference 3 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 3) (sourceB2442 + difference 3 4) sourceC2442) = raw10790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10790; decide +kernel
    rw [ha]
    exact (canonical10790 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2442 + difference 4 5) (sourceB2442 + difference 5 4) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2442 + difference 4 5) (sourceB2442 + difference 5 4) sourceC2442) = raw19188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw19188; decide +kernel
    rw [ha]
    exact (canonical19188 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 0) (sourceB2442 + difference 0 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4237) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 0) (sourceB2442 + difference 0 5) sourceC2442) = raw33524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33524; decide +kernel
    rw [ha]
    exact (canonical33524 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 1) (sourceB2442 + difference 1 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 1) (sourceB2442 + difference 1 5) sourceC2442) = raw33525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33525; decide +kernel
    rw [ha]
    exact (canonical33525 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 2) (sourceB2442 + difference 2 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4723) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 2) (sourceB2442 + difference 2 5) sourceC2442) = raw33526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33526; decide +kernel
    rw [ha]
    exact (canonical33526 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 3) (sourceB2442 + difference 3 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 3) (sourceB2442 + difference 3 5) sourceC2442) = raw10795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw10795; decide +kernel
    rw [ha]
    exact (canonical10795 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2442 + difference 5 4) (sourceB2442 + difference 4 5) sourceC2442) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2442 + difference 5 4) (sourceB2442 + difference 4 5) sourceC2442) = raw33527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2442 sourceB2442 sourceC2442 difference raw33527; decide +kernel
    rw [ha]
    exact (canonical33527 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2442 sourceB2442 sourceC2442
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2442, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1963 : Integer.Sparse.reindex keyMap MixedData.row1963 = numericRow1963 := by decide +kernel

theorem numericCheck1963 (x : Master → ℝ) : Integer.Sparse.eval numericRow1963 x =
    (51840 : ℝ) * reducedSource1963 x := by
  norm_num [numericRow1963, reducedSource1963, Integer.Sparse.eval, Sparse.eval, nodeValue4236, nodeValue4237, nodeValue4238, nodeValue4275, nodeValue4685, nodeValue4686, nodeValue4688, nodeValue4723, nodeValue4724, nodeValue4746, nodeValue4859, nodeValue4860, nodeValue4869, nodeValue4871, nodeValue4874, nodeValue4898, nodeValue5387, nodeValue5403, nodeValue5443, nodeValue5448]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1963 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1963 (mixedVector B) = 0 := by
  have h4236 : mixedVector B (Sum.inr 4236) = Sparse.eval nodeValue4236 (mixedVector B) := by
    change mixedMoment B node4236 node4236Labels = _
    exact sound4236 B hB hF
  have h4237 : mixedVector B (Sum.inr 4237) = Sparse.eval nodeValue4237 (mixedVector B) := by
    change mixedMoment B node4237 node4237Labels = _
    exact sound4237 B hB hF
  have h4238 : mixedVector B (Sum.inr 4238) = Sparse.eval nodeValue4238 (mixedVector B) := by
    change mixedMoment B node4238 node4238Labels = _
    exact sound4238 B hB hF
  have h4275 : mixedVector B (Sum.inr 4275) = Sparse.eval nodeValue4275 (mixedVector B) := by
    change mixedMoment B node4275 node4275Labels = _
    exact sound4275 B hB hF
  have h4685 : mixedVector B (Sum.inr 4685) = Sparse.eval nodeValue4685 (mixedVector B) := by
    change mixedMoment B node4685 node4685Labels = _
    exact sound4685 B hB hF
  have h4686 : mixedVector B (Sum.inr 4686) = Sparse.eval nodeValue4686 (mixedVector B) := by
    change mixedMoment B node4686 node4686Labels = _
    exact sound4686 B hB hF
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4723 : mixedVector B (Sum.inr 4723) = Sparse.eval nodeValue4723 (mixedVector B) := by
    change mixedMoment B node4723 node4723Labels = _
    exact sound4723 B hB hF
  have h4724 : mixedVector B (Sum.inr 4724) = Sparse.eval nodeValue4724 (mixedVector B) := by
    change mixedMoment B node4724 node4724Labels = _
    exact sound4724 B hB hF
  have h4746 : mixedVector B (Sum.inr 4746) = Sparse.eval nodeValue4746 (mixedVector B) := by
    change mixedMoment B node4746 node4746Labels = _
    exact sound4746 B hB hF
  have h4859 : mixedVector B (Sum.inr 4859) = Sparse.eval nodeValue4859 (mixedVector B) := by
    change mixedMoment B node4859 node4859Labels = _
    exact sound4859 B hB hF
  have h4860 : mixedVector B (Sum.inr 4860) = Sparse.eval nodeValue4860 (mixedVector B) := by
    change mixedMoment B node4860 node4860Labels = _
    exact sound4860 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4874 : mixedVector B (Sum.inr 4874) = Sparse.eval nodeValue4874 (mixedVector B) := by
    change mixedMoment B node4874 node4874Labels = _
    exact sound4874 B hB hF
  have h4898 : mixedVector B (Sum.inr 4898) = Sparse.eval nodeValue4898 (mixedVector B) := by
    change mixedMoment B node4898 node4898Labels = _
    exact sound4898 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387_e B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  simpa only [sourceForm2442, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4236, h4237, h4238, h4275, h4685, h4686, h4688, h4723, h4724, h4746, h4859, h4860, h4869, h4871, h4874, h4898, h5387, h5403, h5443, h5448, reducedSource1963] using sourceEq2442 B hB

theorem rowSound1963_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1963 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1963, numericCheck1963, reducedZero1963 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e_oai
