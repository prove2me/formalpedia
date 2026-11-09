-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:32:51.054593+00:00
-- url     : https://prove2.me/submissions/5d77ec2a-e9ce-4775-9397-f36b60af0aae

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E117
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5172_e
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1335 raw1335Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw1335 raw1335Labels = mixedMoment B raw1335step0 raw1335step0Labels := by
      have ha : raw1335step0 = (fun i j => raw1335 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1335step0 raw1335; decide +kernel
      have hl : raw1335step0Labels = raw1335Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1335 raw1335Labels permutation152 permutation4
    mixedMoment B raw1335step0 raw1335step0Labels = mixedMoment B raw1335step1 raw1335step1Labels := by
      have ha : raw1335step1 = raw1335step0 := by apply Matrix.ext; unfold raw1335step1 raw1335step0; decide +kernel
      have hl : raw1335step0Labels = labelEmbedding7 ∘ raw1335step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1335step0 raw1335step0Labels raw1335step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

theorem canonical1336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1336 raw1336Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw1336 raw1336Labels = mixedMoment B raw1336step0 raw1336step0Labels := by
      have ha : raw1336step0 = (fun i j => raw1336 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1336step0 raw1336; decide +kernel
      have hl : raw1336step0Labels = raw1336Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1336 raw1336Labels permutation152 permutation4
    _ = mixedMoment B node1105 node1105Labels := by rfl

theorem canonical1337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1337 raw1337Labels = mixedMoment B node1887 node1887Labels := by
  calc
    mixedMoment B raw1337 raw1337Labels = mixedMoment B raw1337step0 raw1337step0Labels := by
      have ha : raw1337step0 = (fun i j => raw1337 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1337step0 raw1337; decide +kernel
      have hl : raw1337step0Labels = raw1337Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1337 raw1337Labels permutation688 permutation6
    mixedMoment B raw1337step0 raw1337step0Labels = mixedMoment B raw1337step1 raw1337step1Labels := by
      have ha : raw1337step1 = raw1337step0 := by apply Matrix.ext; unfold raw1337step1 raw1337step0; decide +kernel
      have hl : raw1337step0Labels = labelEmbedding1 ∘ raw1337step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1337step0 raw1337step0Labels raw1337step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1887 node1887Labels := by rfl

theorem canonical1347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1347 raw1347Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw1347 raw1347Labels = mixedMoment B raw1347step0 raw1347step0Labels := by
      have ha : raw1347step0 = (fun i j => raw1347 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1347step0 raw1347; decide +kernel
      have hl : raw1347step0Labels = raw1347Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1347 raw1347Labels permutation32 permutation4
    mixedMoment B raw1347step0 raw1347step0Labels = mixedMoment B raw1347step1 raw1347step1Labels := by
      have ha : raw1347step1 = raw1347step0 := by apply Matrix.ext; unfold raw1347step1 raw1347step0; decide +kernel
      have hl : raw1347step0Labels = labelEmbedding7 ∘ raw1347step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1347step0 raw1347step0Labels raw1347step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4525 node4525Labels := by rfl

theorem canonical1348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1348 raw1348Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw1348 raw1348Labels = mixedMoment B raw1348step0 raw1348step0Labels := by
      have ha : raw1348step0 = (fun i j => raw1348 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1348step0 raw1348; decide +kernel
      have hl : raw1348step0Labels = raw1348Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1348 raw1348Labels permutation32 permutation4
    _ = mixedMoment B node1109 node1109Labels := by rfl

theorem canonical1349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1349 raw1349Labels = mixedMoment B node1849 node1849Labels := by
  calc
    mixedMoment B raw1349 raw1349Labels = mixedMoment B raw1349step0 raw1349step0Labels := by
      have ha : raw1349step0 = (fun i j => raw1349 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1349step0 raw1349; decide +kernel
      have hl : raw1349step0Labels = raw1349Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1349 raw1349Labels permutation151 permutation6
    mixedMoment B raw1349step0 raw1349step0Labels = mixedMoment B raw1349step1 raw1349step1Labels := by
      have ha : raw1349step1 = raw1349step0 := by apply Matrix.ext; unfold raw1349step1 raw1349step0; decide +kernel
      have hl : raw1349step0Labels = labelEmbedding1 ∘ raw1349step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1349step0 raw1349step0Labels raw1349step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1849 node1849Labels := by rfl

theorem canonical1365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1365 raw1365Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw1365 raw1365Labels = mixedMoment B raw1365step0 raw1365step0Labels := by
      have ha : raw1365step0 = (fun i j => raw1365 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1365step0 raw1365; decide +kernel
      have hl : raw1365step0Labels = raw1365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1365 raw1365Labels permutation32 permutation4
    mixedMoment B raw1365step0 raw1365step0Labels = mixedMoment B raw1365step1 raw1365step1Labels := by
      have ha : raw1365step1 = raw1365step0 := by apply Matrix.ext; unfold raw1365step1 raw1365step0; decide +kernel
      have hl : raw1365step0Labels = labelEmbedding7 ∘ raw1365step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1365step0 raw1365step0Labels raw1365step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4543 node4543Labels := by rfl

theorem canonical1366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1366 raw1366Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw1366 raw1366Labels = mixedMoment B raw1366step0 raw1366step0Labels := by
      have ha : raw1366step0 = (fun i j => raw1366 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1366step0 raw1366; decide +kernel
      have hl : raw1366step0Labels = raw1366Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1366 raw1366Labels permutation32 permutation4
    _ = mixedMoment B node1128 node1128Labels := by rfl

theorem canonical1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1367 raw1367Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw1367 raw1367Labels = mixedMoment B raw1367step0 raw1367step0Labels := by
      have ha : raw1367step0 = (fun i j => raw1367 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1367step0 raw1367; decide +kernel
      have hl : raw1367step0Labels = raw1367Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1367 raw1367Labels permutation145 permutation6
    mixedMoment B raw1367step0 raw1367step0Labels = mixedMoment B raw1367step1 raw1367step1Labels := by
      have ha : raw1367step1 = raw1367step0 := by apply Matrix.ext; unfold raw1367step1 raw1367step0; decide +kernel
      have hl : raw1367step0Labels = labelEmbedding1 ∘ raw1367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1367step0 raw1367step0Labels raw1367step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1428 raw1428Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw1428 raw1428Labels = mixedMoment B raw1428step0 raw1428step0Labels := by
      have ha : raw1428step0 = (fun i j => raw1428 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1428step0 raw1428; decide +kernel
      have hl : raw1428step0Labels = raw1428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1428 raw1428Labels permutation8 permutation4
    mixedMoment B raw1428step0 raw1428step0Labels = mixedMoment B raw1428step1 raw1428step1Labels := by
      have ha : raw1428step1 = raw1428step0 := by apply Matrix.ext; unfold raw1428step1 raw1428step0; decide +kernel
      have hl : raw1428step0Labels = labelEmbedding7 ∘ raw1428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1428step0 raw1428step0Labels raw1428step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical1429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1429 raw1429Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw1429 raw1429Labels = mixedMoment B raw1429step0 raw1429step0Labels := by
      have ha : raw1429step0 = (fun i j => raw1429 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1429step0 raw1429; decide +kernel
      have hl : raw1429step0Labels = raw1429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1429 raw1429Labels permutation8 permutation4
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical1430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1430 raw1430Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw1430 raw1430Labels = mixedMoment B raw1430step0 raw1430step0Labels := by
      have ha : raw1430step0 = (fun i j => raw1430 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1430step0 raw1430; decide +kernel
      have hl : raw1430step0Labels = raw1430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1430 raw1430Labels permutation31 permutation6
    mixedMoment B raw1430step0 raw1430step0Labels = mixedMoment B raw1430step1 raw1430step1Labels := by
      have ha : raw1430step1 = raw1430step0 := by apply Matrix.ext; unfold raw1430step1 raw1430step0; decide +kernel
      have hl : raw1430step0Labels = labelEmbedding1 ∘ raw1430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1430step0 raw1430step0Labels raw1430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

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

theorem canonical1494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1494 raw1494Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw1494 raw1494Labels = mixedMoment B raw1494step0 raw1494step0Labels := by
      have ha : raw1494step0 = (fun i j => raw1494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1494step0 raw1494; decide +kernel
      have hl : raw1494step0Labels = raw1494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1494 raw1494Labels permutation32 permutation4
    mixedMoment B raw1494step0 raw1494step0Labels = mixedMoment B raw1494step1 raw1494step1Labels := by
      have ha : raw1494step1 = raw1494step0 := by apply Matrix.ext; unfold raw1494step1 raw1494step0; decide +kernel
      have hl : raw1494step0Labels = labelEmbedding7 ∘ raw1494step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1494step0 raw1494step0Labels raw1494step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

theorem canonical1495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1495 raw1495Labels = mixedMoment B node1767 node1767Labels := by
  calc
    mixedMoment B raw1495 raw1495Labels = mixedMoment B raw1495step0 raw1495step0Labels := by
      have ha : raw1495step0 = (fun i j => raw1495 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1495step0 raw1495; decide +kernel
      have hl : raw1495step0Labels = raw1495Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1495 raw1495Labels permutation32 permutation4
    _ = mixedMoment B node1767 node1767Labels := by rfl

theorem canonical1496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1496 raw1496Labels = mixedMoment B node1851 node1851Labels := by
  calc
    mixedMoment B raw1496 raw1496Labels = mixedMoment B raw1496step0 raw1496step0Labels := by
      have ha : raw1496step0 = (fun i j => raw1496 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1496step0 raw1496; decide +kernel
      have hl : raw1496step0Labels = raw1496Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1496 raw1496Labels permutation33 permutation6
    mixedMoment B raw1496step0 raw1496step0Labels = mixedMoment B raw1496step1 raw1496step1Labels := by
      have ha : raw1496step1 = -raw1496step0 := by apply Matrix.ext; change ∀ i j, raw1496step1 i j = -(raw1496step0 i j); unfold raw1496step1 raw1496step0; decide +kernel
      have hl : raw1496step1Labels = raw1496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1496step1 raw1496step1Labels = mixedMoment B raw1496step2 raw1496step2Labels := by
      have ha : raw1496step2 = raw1496step1 := by apply Matrix.ext; unfold raw1496step2 raw1496step1; decide +kernel
      have hl : raw1496step1Labels = labelEmbedding1 ∘ raw1496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1496step1 raw1496step1Labels raw1496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1851 node1851Labels := by rfl

theorem canonical1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1515 raw1515Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw1515 raw1515Labels = mixedMoment B raw1515step0 raw1515step0Labels := by
      have ha : raw1515step0 = (fun i j => raw1515 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1515step0 raw1515; decide +kernel
      have hl : raw1515step0Labels = raw1515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1515 raw1515Labels permutation32 permutation4
    mixedMoment B raw1515step0 raw1515step0Labels = mixedMoment B raw1515step1 raw1515step1Labels := by
      have ha : raw1515step1 = raw1515step0 := by apply Matrix.ext; unfold raw1515step1 raw1515step0; decide +kernel
      have hl : raw1515step0Labels = labelEmbedding7 ∘ raw1515step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1515step0 raw1515step0Labels raw1515step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

theorem canonical1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1516 raw1516Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw1516 raw1516Labels = mixedMoment B raw1516step0 raw1516step0Labels := by
      have ha : raw1516step0 = (fun i j => raw1516 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1516step0 raw1516; decide +kernel
      have hl : raw1516step0Labels = raw1516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1516 raw1516Labels permutation32 permutation4
    _ = mixedMoment B node1778 node1778Labels := by rfl

theorem canonical1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1517 raw1517Labels = mixedMoment B node1854 node1854Labels := by
  calc
    mixedMoment B raw1517 raw1517Labels = mixedMoment B raw1517step0 raw1517step0Labels := by
      have ha : raw1517step0 = (fun i j => raw1517 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1517step0 raw1517; decide +kernel
      have hl : raw1517step0Labels = raw1517Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1517 raw1517Labels permutation33 permutation6
    mixedMoment B raw1517step0 raw1517step0Labels = mixedMoment B raw1517step1 raw1517step1Labels := by
      have ha : raw1517step1 = -raw1517step0 := by apply Matrix.ext; change ∀ i j, raw1517step1 i j = -(raw1517step0 i j); unfold raw1517step1 raw1517step0; decide +kernel
      have hl : raw1517step1Labels = raw1517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1517step1 raw1517step1Labels = mixedMoment B raw1517step2 raw1517step2Labels := by
      have ha : raw1517step2 = raw1517step1 := by apply Matrix.ext; unfold raw1517step2 raw1517step1; decide +kernel
      have hl : raw1517step1Labels = labelEmbedding1 ∘ raw1517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1517step1 raw1517step1Labels raw1517step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1854 node1854Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical15180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15180 raw15180Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw15180 raw15180Labels = mixedMoment B raw15180step0 raw15180step0Labels := by
      have hz : ∀ j, raw15180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15180step0 = (fun i j => raw15180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15180step0 raw15180; decide +kernel
      have hl : raw15180step0Labels = raw15180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15180 raw15180Labels permutation346 hz
    mixedMoment B raw15180step0 raw15180step0Labels = mixedMoment B raw15180step1 raw15180step1Labels := by
      have ha : raw15180step1 = (fun i j => raw15180step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15180step1 raw15180step0; decide +kernel
      have hl : raw15180step1Labels = raw15180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15180step0 raw15180step0Labels permutation150 permutation3
    mixedMoment B raw15180step1 raw15180step1Labels = mixedMoment B raw15180step2 raw15180step2Labels := by
      have ha : raw15180step2 = -raw15180step1 := by apply Matrix.ext; change ∀ i j, raw15180step2 i j = -(raw15180step1 i j); unfold raw15180step2 raw15180step1; decide +kernel
      have hl : raw15180step2Labels = raw15180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15180step2 raw15180step2Labels = mixedMoment B raw15180step3 raw15180step3Labels := by
      have ha : raw15180step3 = raw15180step2 := by apply Matrix.ext; unfold raw15180step3 raw15180step2; decide +kernel
      have hl : raw15180step2Labels = labelEmbedding6 ∘ raw15180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15180step2 raw15180step2Labels raw15180step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical15181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15181 raw15181Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw15181 raw15181Labels = mixedMoment B raw15181step0 raw15181step0Labels := by
      have ha : raw15181step0 = (fun i j => raw15181 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15181step0 raw15181; decide +kernel
      have hl : raw15181step0Labels = raw15181Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15181 raw15181Labels permutation686 permutation3
    mixedMoment B raw15181step0 raw15181step0Labels = mixedMoment B raw15181step1 raw15181step1Labels := by
      have ha : raw15181step1 = -raw15181step0 := by apply Matrix.ext; change ∀ i j, raw15181step1 i j = -(raw15181step0 i j); unfold raw15181step1 raw15181step0; decide +kernel
      have hl : raw15181step1Labels = raw15181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15181step1 raw15181step1Labels = mixedMoment B raw15181step2 raw15181step2Labels := by
      have ha : raw15181step2 = raw15181step1 := by apply Matrix.ext; unfold raw15181step2 raw15181step1; decide +kernel
      have hl : raw15181step1Labels = labelEmbedding6 ∘ raw15181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15181step1 raw15181step1Labels raw15181step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical15182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15182 raw15182Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw15182 raw15182Labels = mixedMoment B raw15182step0 raw15182step0Labels := by
      have hz : ∀ j, raw15182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15182step0 = (fun i j => raw15182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15182step0 raw15182; decide +kernel
      have hl : raw15182step0Labels = raw15182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15182 raw15182Labels permutation346 hz
    mixedMoment B raw15182step0 raw15182step0Labels = mixedMoment B raw15182step1 raw15182step1Labels := by
      have ha : raw15182step1 = (fun i j => raw15182step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15182step1 raw15182step0; decide +kernel
      have hl : raw15182step1Labels = raw15182step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15182step0 raw15182step0Labels permutation149 permutation3
    mixedMoment B raw15182step1 raw15182step1Labels = mixedMoment B raw15182step2 raw15182step2Labels := by
      have ha : raw15182step2 = -raw15182step1 := by apply Matrix.ext; change ∀ i j, raw15182step2 i j = -(raw15182step1 i j); unfold raw15182step2 raw15182step1; decide +kernel
      have hl : raw15182step2Labels = raw15182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15182step2 raw15182step2Labels = mixedMoment B raw15182step3 raw15182step3Labels := by
      have ha : raw15182step3 = raw15182step2 := by apply Matrix.ext; unfold raw15182step3 raw15182step2; decide +kernel
      have hl : raw15182step2Labels = labelEmbedding6 ∘ raw15182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15182step2 raw15182step2Labels raw15182step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1593 raw1593Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw1593 raw1593Labels = mixedMoment B raw1593step0 raw1593step0Labels := by
      have ha : raw1593step0 = (fun i j => raw1593 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1593step0 raw1593; decide +kernel
      have hl : raw1593step0Labels = raw1593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1593 raw1593Labels permutation152 permutation4
    mixedMoment B raw1593step0 raw1593step0Labels = mixedMoment B raw1593step1 raw1593step1Labels := by
      have ha : raw1593step1 = raw1593step0 := by apply Matrix.ext; unfold raw1593step1 raw1593step0; decide +kernel
      have hl : raw1593step0Labels = labelEmbedding7 ∘ raw1593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1593step0 raw1593step0Labels raw1593step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

theorem canonical1594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1594 raw1594Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw1594 raw1594Labels = mixedMoment B raw1594step0 raw1594step0Labels := by
      have ha : raw1594step0 = (fun i j => raw1594 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1594step0 raw1594; decide +kernel
      have hl : raw1594step0Labels = raw1594Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1594 raw1594Labels permutation152 permutation4
    _ = mixedMoment B node1861 node1861Labels := by rfl

theorem canonical1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1595 raw1595Labels = mixedMoment B node1889 node1889Labels := by
  calc
    mixedMoment B raw1595 raw1595Labels = mixedMoment B raw1595step0 raw1595step0Labels := by
      have ha : raw1595step0 = (fun i j => raw1595 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1595step0 raw1595; decide +kernel
      have hl : raw1595step0Labels = raw1595Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1595 raw1595Labels permutation153 permutation6
    mixedMoment B raw1595step0 raw1595step0Labels = mixedMoment B raw1595step1 raw1595step1Labels := by
      have ha : raw1595step1 = -raw1595step0 := by apply Matrix.ext; change ∀ i j, raw1595step1 i j = -(raw1595step0 i j); unfold raw1595step1 raw1595step0; decide +kernel
      have hl : raw1595step1Labels = raw1595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1595step1 raw1595step1Labels = mixedMoment B raw1595step2 raw1595step2Labels := by
      have ha : raw1595step2 = raw1595step1 := by apply Matrix.ext; unfold raw1595step2 raw1595step1; decide +kernel
      have hl : raw1595step1Labels = labelEmbedding1 ∘ raw1595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1595step1 raw1595step1Labels raw1595step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1889 node1889Labels := by rfl

theorem canonical1602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1602 raw1602Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw1602 raw1602Labels = mixedMoment B raw1602step0 raw1602step0Labels := by
      have ha : raw1602step0 = (fun i j => raw1602 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1602step0 raw1602; decide +kernel
      have hl : raw1602step0Labels = raw1602Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1602 raw1602Labels permutation152 permutation4
    mixedMoment B raw1602step0 raw1602step0Labels = mixedMoment B raw1602step1 raw1602step1Labels := by
      have ha : raw1602step1 = raw1602step0 := by apply Matrix.ext; unfold raw1602step1 raw1602step0; decide +kernel
      have hl : raw1602step0Labels = labelEmbedding7 ∘ raw1602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1602step0 raw1602step0Labels raw1602step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

theorem canonical1603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1603 raw1603Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw1603 raw1603Labels = mixedMoment B raw1603step0 raw1603step0Labels := by
      have ha : raw1603step0 = (fun i j => raw1603 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1603step0 raw1603; decide +kernel
      have hl : raw1603step0Labels = raw1603Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1603 raw1603Labels permutation152 permutation4
    _ = mixedMoment B node1867 node1867Labels := by rfl

theorem canonical1604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1604 raw1604Labels = mixedMoment B node1891 node1891Labels := by
  calc
    mixedMoment B raw1604 raw1604Labels = mixedMoment B raw1604step0 raw1604step0Labels := by
      have ha : raw1604step0 = (fun i j => raw1604 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1604step0 raw1604; decide +kernel
      have hl : raw1604step0Labels = raw1604Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1604 raw1604Labels permutation153 permutation6
    mixedMoment B raw1604step0 raw1604step0Labels = mixedMoment B raw1604step1 raw1604step1Labels := by
      have ha : raw1604step1 = -raw1604step0 := by apply Matrix.ext; change ∀ i j, raw1604step1 i j = -(raw1604step0 i j); unfold raw1604step1 raw1604step0; decide +kernel
      have hl : raw1604step1Labels = raw1604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1604step1 raw1604step1Labels = mixedMoment B raw1604step2 raw1604step2Labels := by
      have ha : raw1604step2 = raw1604step1 := by apply Matrix.ext; unfold raw1604step2 raw1604step1; decide +kernel
      have hl : raw1604step1Labels = labelEmbedding1 ∘ raw1604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1604step1 raw1604step1Labels raw1604step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1891 node1891Labels := by rfl

theorem canonical1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1644 raw1644Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw1644 raw1644Labels = mixedMoment B raw1644step0 raw1644step0Labels := by
      have ha : raw1644step0 = (fun i j => raw1644 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1644step0 raw1644; decide +kernel
      have hl : raw1644step0Labels = raw1644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1644 raw1644Labels permutation152 permutation4
    mixedMoment B raw1644step0 raw1644step0Labels = mixedMoment B raw1644step1 raw1644step1Labels := by
      have ha : raw1644step1 = raw1644step0 := by apply Matrix.ext; unfold raw1644step1 raw1644step0; decide +kernel
      have hl : raw1644step0Labels = labelEmbedding7 ∘ raw1644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1644step0 raw1644step0Labels raw1644step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

theorem canonical1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1645 raw1645Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw1645 raw1645Labels = mixedMoment B raw1645step0 raw1645step0Labels := by
      have ha : raw1645step0 = (fun i j => raw1645 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1645step0 raw1645; decide +kernel
      have hl : raw1645step0Labels = raw1645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1645 raw1645Labels permutation152 permutation4
    _ = mixedMoment B node1898 node1898Labels := by rfl

theorem canonical1646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1646 raw1646Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw1646 raw1646Labels = mixedMoment B raw1646step0 raw1646step0Labels := by
      have ha : raw1646step0 = (fun i j => raw1646 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1646step0 raw1646; decide +kernel
      have hl : raw1646step0Labels = raw1646Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1646 raw1646Labels permutation152 permutation6
    mixedMoment B raw1646step0 raw1646step0Labels = mixedMoment B raw1646step1 raw1646step1Labels := by
      have ha : raw1646step1 = -raw1646step0 := by apply Matrix.ext; change ∀ i j, raw1646step1 i j = -(raw1646step0 i j); unfold raw1646step1 raw1646step0; decide +kernel
      have hl : raw1646step1Labels = raw1646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1646step1 raw1646step1Labels = mixedMoment B raw1646step2 raw1646step2Labels := by
      have ha : raw1646step2 = raw1646step1 := by apply Matrix.ext; unfold raw1646step2 raw1646step1; decide +kernel
      have hl : raw1646step1Labels = labelEmbedding1 ∘ raw1646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1646step1 raw1646step1Labels raw1646step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1940 node1940Labels := by rfl

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

theorem canonical1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1707 raw1707Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw1707 raw1707Labels = mixedMoment B raw1707step0 raw1707step0Labels := by
      have ha : raw1707step0 = (fun i j => raw1707 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1707step0 raw1707; decide +kernel
      have hl : raw1707step0Labels = raw1707Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1707 raw1707Labels permutation32 permutation4
    mixedMoment B raw1707step0 raw1707step0Labels = mixedMoment B raw1707step1 raw1707step1Labels := by
      have ha : raw1707step1 = raw1707step0 := by apply Matrix.ext; unfold raw1707step1 raw1707step0; decide +kernel
      have hl : raw1707step0Labels = labelEmbedding7 ∘ raw1707step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1707step0 raw1707step0Labels raw1707step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1708 raw1708Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw1708 raw1708Labels = mixedMoment B raw1708step0 raw1708step0Labels := by
      have ha : raw1708step0 = (fun i j => raw1708 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1708step0 raw1708; decide +kernel
      have hl : raw1708step0Labels = raw1708Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1708 raw1708Labels permutation32 permutation4
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1709 raw1709Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw1709 raw1709Labels = mixedMoment B raw1709step0 raw1709step0Labels := by
      have ha : raw1709step0 = (fun i j => raw1709 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1709step0 raw1709; decide +kernel
      have hl : raw1709step0Labels = raw1709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1709 raw1709Labels permutation33 permutation6
    mixedMoment B raw1709step0 raw1709step0Labels = mixedMoment B raw1709step1 raw1709step1Labels := by
      have ha : raw1709step1 = -raw1709step0 := by apply Matrix.ext; change ∀ i j, raw1709step1 i j = -(raw1709step0 i j); unfold raw1709step1 raw1709step0; decide +kernel
      have hl : raw1709step1Labels = raw1709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1709step1 raw1709step1Labels = mixedMoment B raw1709step2 raw1709step2Labels := by
      have ha : raw1709step2 = raw1709step1 := by apply Matrix.ext; unfold raw1709step2 raw1709step1; decide +kernel
      have hl : raw1709step1Labels = labelEmbedding1 ∘ raw1709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1709step1 raw1709step1Labels raw1709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

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

theorem canonical1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1773 raw1773Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw1773 raw1773Labels = mixedMoment B raw1773step0 raw1773step0Labels := by
      have ha : raw1773step0 = (fun i j => raw1773 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1773step0 raw1773; decide +kernel
      have hl : raw1773step0Labels = raw1773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1773 raw1773Labels permutation8 permutation4
    mixedMoment B raw1773step0 raw1773step0Labels = mixedMoment B raw1773step1 raw1773step1Labels := by
      have ha : raw1773step1 = raw1773step0 := by apply Matrix.ext; unfold raw1773step1 raw1773step0; decide +kernel
      have hl : raw1773step0Labels = labelEmbedding7 ∘ raw1773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1773step0 raw1773step0Labels raw1773step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1774 raw1774Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw1774 raw1774Labels = mixedMoment B raw1774step0 raw1774step0Labels := by
      have ha : raw1774step0 = (fun i j => raw1774 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1774step0 raw1774; decide +kernel
      have hl : raw1774step0Labels = raw1774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1774 raw1774Labels permutation8 permutation4
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical1775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1775 raw1775Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw1775 raw1775Labels = mixedMoment B raw1775step0 raw1775step0Labels := by
      have ha : raw1775step0 = (fun i j => raw1775 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1775step0 raw1775; decide +kernel
      have hl : raw1775step0Labels = raw1775Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1775 raw1775Labels permutation9 permutation6
    mixedMoment B raw1775step0 raw1775step0Labels = mixedMoment B raw1775step1 raw1775step1Labels := by
      have ha : raw1775step1 = -raw1775step0 := by apply Matrix.ext; change ∀ i j, raw1775step1 i j = -(raw1775step0 i j); unfold raw1775step1 raw1775step0; decide +kernel
      have hl : raw1775step1Labels = raw1775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1775step1 raw1775step1Labels = mixedMoment B raw1775step2 raw1775step2Labels := by
      have ha : raw1775step2 = raw1775step1 := by apply Matrix.ext; unfold raw1775step2 raw1775step1; decide +kernel
      have hl : raw1775step1Labels = labelEmbedding1 ∘ raw1775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1775step1 raw1775step1Labels raw1775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

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

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

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

theorem canonical2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2175 raw2175Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw2175 raw2175Labels = mixedMoment B raw2175step0 raw2175step0Labels := by
      have ha : raw2175step0 = (fun i j => raw2175 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2175step0 raw2175; decide +kernel
      have hl : raw2175step0Labels = raw2175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2175 raw2175Labels permutation152 permutation5
    mixedMoment B raw2175step0 raw2175step0Labels = mixedMoment B raw2175step1 raw2175step1Labels := by
      have ha : raw2175step1 = raw2175step0 := by apply Matrix.ext; unfold raw2175step1 raw2175step0; decide +kernel
      have hl : raw2175step0Labels = labelEmbedding8 ∘ raw2175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2175step0 raw2175step0Labels raw2175step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20934 raw20934Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw20934 raw20934Labels = mixedMoment B raw20934step0 raw20934step0Labels := by
      have ha : raw20934step0 = (fun i j => raw20934 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20934step0 raw20934; decide +kernel
      have hl : raw20934step0Labels = raw20934Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20934 raw20934Labels permutation160 permutation3
    mixedMoment B raw20934step0 raw20934step0Labels = mixedMoment B raw20934step1 raw20934step1Labels := by
      have ha : raw20934step1 = raw20934step0 := by apply Matrix.ext; unfold raw20934step1 raw20934step0; decide +kernel
      have hl : raw20934step0Labels = labelEmbedding6 ∘ raw20934step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20934step0 raw20934step0Labels raw20934step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

theorem canonical20937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20937 raw20937Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw20937 raw20937Labels = mixedMoment B raw20937step0 raw20937step0Labels := by
      have hz : ∀ j, raw20937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20937step0 = (fun i j => raw20937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20937step0 raw20937; decide +kernel
      have hl : raw20937step0Labels = raw20937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20937 raw20937Labels permutation346 hz
    mixedMoment B raw20937step0 raw20937step0Labels = mixedMoment B raw20937step1 raw20937step1Labels := by
      have ha : raw20937step1 = (fun i j => raw20937step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20937step1 raw20937step0; decide +kernel
      have hl : raw20937step1Labels = raw20937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20937step0 raw20937step0Labels permutation32 permutation3
    mixedMoment B raw20937step1 raw20937step1Labels = mixedMoment B raw20937step2 raw20937step2Labels := by
      have ha : raw20937step2 = raw20937step1 := by apply Matrix.ext; unfold raw20937step2 raw20937step1; decide +kernel
      have hl : raw20937step1Labels = labelEmbedding6 ∘ raw20937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20937step1 raw20937step1Labels raw20937step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4543 node4543Labels := by rfl

theorem canonical20940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20940 raw20940Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw20940 raw20940Labels = mixedMoment B raw20940step0 raw20940step0Labels := by
      have hz : ∀ j, raw20940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20940step0 = (fun i j => raw20940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20940step0 raw20940; decide +kernel
      have hl : raw20940step0Labels = raw20940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20940 raw20940Labels permutation346 hz
    mixedMoment B raw20940step0 raw20940step0Labels = mixedMoment B raw20940step1 raw20940step1Labels := by
      have ha : raw20940step1 = (fun i j => raw20940step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20940step1 raw20940step0; decide +kernel
      have hl : raw20940step1Labels = raw20940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20940step0 raw20940step0Labels permutation32 permutation3
    mixedMoment B raw20940step1 raw20940step1Labels = mixedMoment B raw20940step2 raw20940step2Labels := by
      have ha : raw20940step2 = raw20940step1 := by apply Matrix.ext; unfold raw20940step2 raw20940step1; decide +kernel
      have hl : raw20940step1Labels = labelEmbedding6 ∘ raw20940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20940step1 raw20940step1Labels raw20940step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4525 node4525Labels := by rfl

theorem canonical20944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20944 raw20944Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw20944 raw20944Labels = mixedMoment B raw20944step0 raw20944step0Labels := by
      have hz : ∀ j, raw20944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20944step0 = (fun i j => raw20944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20944step0 raw20944; decide +kernel
      have hl : raw20944step0Labels = raw20944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20944 raw20944Labels permutation346 hz
    mixedMoment B raw20944step0 raw20944step0Labels = mixedMoment B raw20944step1 raw20944step1Labels := by
      have ha : raw20944step1 = (fun i j => raw20944step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20944step1 raw20944step0; decide +kernel
      have hl : raw20944step1Labels = raw20944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20944step0 raw20944step0Labels permutation151 permutation3
    mixedMoment B raw20944step1 raw20944step1Labels = mixedMoment B raw20944step2 raw20944step2Labels := by
      have ha : raw20944step2 = -raw20944step1 := by apply Matrix.ext; change ∀ i j, raw20944step2 i j = -(raw20944step1 i j); unfold raw20944step2 raw20944step1; decide +kernel
      have hl : raw20944step2Labels = raw20944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20944step2 raw20944step2Labels = mixedMoment B raw20944step3 raw20944step3Labels := by
      have ha : raw20944step3 = raw20944step2 := by apply Matrix.ext; unfold raw20944step3 raw20944step2; decide +kernel
      have hl : raw20944step2Labels = labelEmbedding6 ∘ raw20944step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20944step2 raw20944step2Labels raw20944step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4202 node4202Labels := by rfl

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

theorem canonical2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2176 raw2176Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw2176 raw2176Labels = mixedMoment B raw2176step0 raw2176step0Labels := by
      have ha : raw2176step0 = (fun i j => raw2176 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2176step0 raw2176; decide +kernel
      have hl : raw2176step0Labels = raw2176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2176 raw2176Labels permutation154 permutation4
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2177 raw2177Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw2177 raw2177Labels = mixedMoment B raw2177step0 raw2177step0Labels := by
      have ha : raw2177step0 = (fun i j => raw2177 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2177step0 raw2177; decide +kernel
      have hl : raw2177step0Labels = raw2177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2177 raw2177Labels permutation162 permutation3
    mixedMoment B raw2177step0 raw2177step0Labels = mixedMoment B raw2177step1 raw2177step1Labels := by
      have ha : raw2177step1 = -raw2177step0 := by apply Matrix.ext; change ∀ i j, raw2177step1 i j = -(raw2177step0 i j); unfold raw2177step1 raw2177step0; decide +kernel
      have hl : raw2177step1Labels = raw2177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2177step1 raw2177step1Labels = mixedMoment B raw2177step2 raw2177step2Labels := by
      have ha : raw2177step2 = raw2177step1 := by apply Matrix.ext; unfold raw2177step2 raw2177step1; decide +kernel
      have hl : raw2177step1Labels = labelEmbedding1 ∘ raw2177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2177step1 raw2177step1Labels raw2177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2178 raw2178Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw2178 raw2178Labels = mixedMoment B raw2178step0 raw2178step0Labels := by
      have ha : raw2178step0 = (fun i j => raw2178 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2178step0 raw2178; decide +kernel
      have hl : raw2178step0Labels = raw2178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2178 raw2178Labels permutation32 permutation5
    mixedMoment B raw2178step0 raw2178step0Labels = mixedMoment B raw2178step1 raw2178step1Labels := by
      have ha : raw2178step1 = raw2178step0 := by apply Matrix.ext; unfold raw2178step1 raw2178step0; decide +kernel
      have hl : raw2178step0Labels = labelEmbedding8 ∘ raw2178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2178step0 raw2178step0Labels raw2178step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2179 raw2179Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw2179 raw2179Labels = mixedMoment B raw2179step0 raw2179step0Labels := by
      have ha : raw2179step0 = (fun i j => raw2179 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2179step0 raw2179; decide +kernel
      have hl : raw2179step0Labels = raw2179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2179 raw2179Labels permutation33 permutation4
    _ = mixedMoment B node2931 node2931Labels := by rfl

theorem canonical2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2180 raw2180Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw2180 raw2180Labels = mixedMoment B raw2180step0 raw2180step0Labels := by
      have ha : raw2180step0 = (fun i j => raw2180 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2180step0 raw2180; decide +kernel
      have hl : raw2180step0Labels = raw2180Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2180 raw2180Labels permutation34 permutation3
    mixedMoment B raw2180step0 raw2180step0Labels = mixedMoment B raw2180step1 raw2180step1Labels := by
      have ha : raw2180step1 = -raw2180step0 := by apply Matrix.ext; change ∀ i j, raw2180step1 i j = -(raw2180step0 i j); unfold raw2180step1 raw2180step0; decide +kernel
      have hl : raw2180step1Labels = raw2180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2180step1 raw2180step1Labels = mixedMoment B raw2180step2 raw2180step2Labels := by
      have ha : raw2180step2 = raw2180step1 := by apply Matrix.ext; unfold raw2180step2 raw2180step1; decide +kernel
      have hl : raw2180step1Labels = labelEmbedding1 ∘ raw2180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2180step1 raw2180step1Labels raw2180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

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

theorem canonical2304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2304 raw2304Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2304 raw2304Labels = mixedMoment B raw2304step0 raw2304step0Labels := by
      have ha : raw2304step0 = (fun i j => raw2304 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2304step0 raw2304; decide +kernel
      have hl : raw2304step0Labels = raw2304Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2304 raw2304Labels permutation8 permutation4
    mixedMoment B raw2304step0 raw2304step0Labels = mixedMoment B raw2304step1 raw2304step1Labels := by
      have ha : raw2304step1 = raw2304step0 := by apply Matrix.ext; unfold raw2304step1 raw2304step0; decide +kernel
      have hl : raw2304step0Labels = labelEmbedding7 ∘ raw2304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2304step0 raw2304step0Labels raw2304step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical2305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2305 raw2305Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw2305 raw2305Labels = mixedMoment B raw2305step0 raw2305step0Labels := by
      have ha : raw2305step0 = (fun i j => raw2305 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2305step0 raw2305; decide +kernel
      have hl : raw2305step0Labels = raw2305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2305 raw2305Labels permutation8 permutation4
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2306 raw2306Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw2306 raw2306Labels = mixedMoment B raw2306step0 raw2306step0Labels := by
      have ha : raw2306step0 = (fun i j => raw2306 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2306step0 raw2306; decide +kernel
      have hl : raw2306step0Labels = raw2306Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2306 raw2306Labels permutation12 permutation6
    mixedMoment B raw2306step0 raw2306step0Labels = mixedMoment B raw2306step1 raw2306step1Labels := by
      have ha : raw2306step1 = -raw2306step0 := by apply Matrix.ext; change ∀ i j, raw2306step1 i j = -(raw2306step0 i j); unfold raw2306step1 raw2306step0; decide +kernel
      have hl : raw2306step1Labels = raw2306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2306step1 raw2306step1Labels = mixedMoment B raw2306step2 raw2306step2Labels := by
      have ha : raw2306step2 = raw2306step1 := by apply Matrix.ext; unfold raw2306step2 raw2306step1; decide +kernel
      have hl : raw2306step1Labels = labelEmbedding1 ∘ raw2306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2306step1 raw2306step1Labels raw2306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3632 node3632Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw272 raw272Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw272 raw272Labels = mixedMoment B raw272step0 raw272step0Labels := by
      have ha : raw272step0 = (fun i j => raw272 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw272step0 raw272; decide +kernel
      have hl : raw272step0Labels = raw272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw272 raw272Labels permutation8 permutation5
    mixedMoment B raw272step0 raw272step0Labels = mixedMoment B raw272step1 raw272step1Labels := by
      have ha : raw272step1 = raw272step0 := by apply Matrix.ext; unfold raw272step1 raw272step0; decide +kernel
      have hl : raw272step0Labels = labelEmbedding1 ∘ raw272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw272step0 raw272step0Labels raw272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw273 raw273Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw273 raw273Labels = mixedMoment B raw273step0 raw273step0Labels := by
      have ha : raw273step0 = (fun i j => raw273 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw273step0 raw273; decide +kernel
      have hl : raw273step0Labels = raw273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw273 raw273Labels permutation8 permutation5
    _ = mixedMoment B node405 node405Labels := by rfl

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

theorem canonical2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2681 raw2681Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2681 raw2681Labels = mixedMoment B raw2681step0 raw2681step0Labels := by
      have hz : ∀ j, raw2681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2681step0 = (fun i j => raw2681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2681step0 raw2681; decide +kernel
      have hl : raw2681step0Labels = raw2681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2681 raw2681Labels permutation346 hz
    mixedMoment B raw2681step0 raw2681step0Labels = mixedMoment B raw2681step1 raw2681step1Labels := by
      have hz : ∀ j, raw2681step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2681step1 = (fun i j => raw2681step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2681step1 raw2681step0; decide +kernel
      have hl : raw2681step1Labels = raw2681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2681step0 raw2681step0Labels permutation56 hz
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical2682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2682 raw2682Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw2682 raw2682Labels = mixedMoment B raw2682step0 raw2682step0Labels := by
      have hz : ∀ j, raw2682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2682step0 = (fun i j => raw2682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2682step0 raw2682; decide +kernel
      have hl : raw2682step0Labels = raw2682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2682 raw2682Labels permutation346 hz
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2686 raw2686Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw2686 raw2686Labels = mixedMoment B raw2686step0 raw2686step0Labels := by
      have hz : ∀ j, raw2686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2686step0 = (fun i j => raw2686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2686step0 raw2686; decide +kernel
      have hl : raw2686step0Labels = raw2686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2686 raw2686Labels permutation346 hz
    mixedMoment B raw2686step0 raw2686step0Labels = mixedMoment B raw2686step1 raw2686step1Labels := by
      have hz : ∀ j, raw2686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2686step1 = (fun i j => raw2686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2686step1 raw2686step0; decide +kernel
      have hl : raw2686step1Labels = raw2686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2686step0 raw2686step0Labels permutation56 hz
    mixedMoment B raw2686step1 raw2686step1Labels = mixedMoment B raw2686step2 raw2686step2Labels := by
      have ha : raw2686step2 = (fun i j => raw2686step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2686step2 raw2686step1; decide +kernel
      have hl : raw2686step2Labels = raw2686step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2686step1 raw2686step1Labels permutation29 permutation3
    mixedMoment B raw2686step2 raw2686step2Labels = mixedMoment B raw2686step3 raw2686step3Labels := by
      have ha : raw2686step3 = -raw2686step2 := by apply Matrix.ext; change ∀ i j, raw2686step3 i j = -(raw2686step2 i j); unfold raw2686step3 raw2686step2; decide +kernel
      have hl : raw2686step3Labels = raw2686step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2686step3 raw2686step3Labels = mixedMoment B raw2686step4 raw2686step4Labels := by
      have ha : raw2686step4 = raw2686step3 := by apply Matrix.ext; unfold raw2686step4 raw2686step3; decide +kernel
      have hl : raw2686step3Labels = labelEmbedding6 ∘ raw2686step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2686step3 raw2686step3Labels raw2686step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2687 raw2687Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw2687 raw2687Labels = mixedMoment B raw2687step0 raw2687step0Labels := by
      have hz : ∀ j, raw2687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2687step0 = (fun i j => raw2687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2687step0 raw2687; decide +kernel
      have hl : raw2687step0Labels = raw2687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2687 raw2687Labels permutation346 hz
    mixedMoment B raw2687step0 raw2687step0Labels = mixedMoment B raw2687step1 raw2687step1Labels := by
      have ha : raw2687step1 = (fun i j => raw2687step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2687step1 raw2687step0; decide +kernel
      have hl : raw2687step1Labels = raw2687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2687step0 raw2687step0Labels permutation145 permutation3
    mixedMoment B raw2687step1 raw2687step1Labels = mixedMoment B raw2687step2 raw2687step2Labels := by
      have ha : raw2687step2 = -raw2687step1 := by apply Matrix.ext; change ∀ i j, raw2687step2 i j = -(raw2687step1 i j); unfold raw2687step2 raw2687step1; decide +kernel
      have hl : raw2687step2Labels = raw2687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2687step2 raw2687step2Labels = mixedMoment B raw2687step3 raw2687step3Labels := by
      have ha : raw2687step3 = raw2687step2 := by apply Matrix.ext; unfold raw2687step3 raw2687step2; decide +kernel
      have hl : raw2687step2Labels = labelEmbedding6 ∘ raw2687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2687step2 raw2687step2Labels raw2687step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28000 raw28000Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw28000 raw28000Labels = mixedMoment B raw28000step0 raw28000step0Labels := by
      have ha : raw28000step0 = (fun i j => raw28000 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28000step0 raw28000; decide +kernel
      have hl : raw28000step0Labels = raw28000Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28000 raw28000Labels permutation646 permutation3
    mixedMoment B raw28000step0 raw28000step0Labels = mixedMoment B raw28000step1 raw28000step1Labels := by
      have ha : raw28000step1 = -raw28000step0 := by apply Matrix.ext; change ∀ i j, raw28000step1 i j = -(raw28000step0 i j); unfold raw28000step1 raw28000step0; decide +kernel
      have hl : raw28000step1Labels = raw28000step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28000step1 raw28000step1Labels = mixedMoment B raw28000step2 raw28000step2Labels := by
      have ha : raw28000step2 = raw28000step1 := by apply Matrix.ext; unfold raw28000step2 raw28000step1; decide +kernel
      have hl : raw28000step1Labels = labelEmbedding6 ∘ raw28000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28000step1 raw28000step1Labels raw28000step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

theorem canonical28001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28001 raw28001Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw28001 raw28001Labels = mixedMoment B raw28001step0 raw28001step0Labels := by
      have ha : raw28001step0 = (fun i j => raw28001 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28001step0 raw28001; decide +kernel
      have hl : raw28001step0Labels = raw28001Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28001 raw28001Labels permutation644 permutation3
    mixedMoment B raw28001step0 raw28001step0Labels = mixedMoment B raw28001step1 raw28001step1Labels := by
      have ha : raw28001step1 = -raw28001step0 := by apply Matrix.ext; change ∀ i j, raw28001step1 i j = -(raw28001step0 i j); unfold raw28001step1 raw28001step0; decide +kernel
      have hl : raw28001step1Labels = raw28001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28001step1 raw28001step1Labels = mixedMoment B raw28001step2 raw28001step2Labels := by
      have ha : raw28001step2 = raw28001step1 := by apply Matrix.ext; unfold raw28001step2 raw28001step1; decide +kernel
      have hl : raw28001step1Labels = labelEmbedding6 ∘ raw28001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28001step1 raw28001step1Labels raw28001step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

theorem canonical28002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28002 raw28002Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw28002 raw28002Labels = mixedMoment B raw28002step0 raw28002step0Labels := by
      have hz : ∀ j, raw28002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28002step0 = (fun i j => raw28002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28002step0 raw28002; decide +kernel
      have hl : raw28002step0Labels = raw28002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28002 raw28002Labels permutation346 hz
    mixedMoment B raw28002step0 raw28002step0Labels = mixedMoment B raw28002step1 raw28002step1Labels := by
      have ha : raw28002step1 = (fun i j => raw28002step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28002step1 raw28002step0; decide +kernel
      have hl : raw28002step1Labels = raw28002step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28002step0 raw28002step0Labels permutation145 permutation3
    mixedMoment B raw28002step1 raw28002step1Labels = mixedMoment B raw28002step2 raw28002step2Labels := by
      have ha : raw28002step2 = -raw28002step1 := by apply Matrix.ext; change ∀ i j, raw28002step2 i j = -(raw28002step1 i j); unfold raw28002step2 raw28002step1; decide +kernel
      have hl : raw28002step2Labels = raw28002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28002step2 raw28002step2Labels = mixedMoment B raw28002step3 raw28002step3Labels := by
      have ha : raw28002step3 = raw28002step2 := by apply Matrix.ext; unfold raw28002step3 raw28002step2; decide +kernel
      have hl : raw28002step2Labels = labelEmbedding6 ∘ raw28002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28002step2 raw28002step2Labels raw28002step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical28003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28003 raw28003Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw28003 raw28003Labels = mixedMoment B raw28003step0 raw28003step0Labels := by
      have ha : raw28003step0 = (fun i j => raw28003 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28003step0 raw28003; decide +kernel
      have hl : raw28003step0Labels = raw28003Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28003 raw28003Labels permutation662 permutation3
    mixedMoment B raw28003step0 raw28003step0Labels = mixedMoment B raw28003step1 raw28003step1Labels := by
      have ha : raw28003step1 = -raw28003step0 := by apply Matrix.ext; change ∀ i j, raw28003step1 i j = -(raw28003step0 i j); unfold raw28003step1 raw28003step0; decide +kernel
      have hl : raw28003step1Labels = raw28003step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28003step1 raw28003step1Labels = mixedMoment B raw28003step2 raw28003step2Labels := by
      have ha : raw28003step2 = raw28003step1 := by apply Matrix.ext; unfold raw28003step2 raw28003step1; decide +kernel
      have hl : raw28003step1Labels = labelEmbedding6 ∘ raw28003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28003step1 raw28003step1Labels raw28003step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4764 node4764Labels := by rfl

theorem canonical28004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28004 raw28004Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw28004 raw28004Labels = mixedMoment B raw28004step0 raw28004step0Labels := by
      have hz : ∀ j, raw28004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28004step0 = (fun i j => raw28004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28004step0 raw28004; decide +kernel
      have hl : raw28004step0Labels = raw28004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28004 raw28004Labels permutation346 hz
    mixedMoment B raw28004step0 raw28004step0Labels = mixedMoment B raw28004step1 raw28004step1Labels := by
      have ha : raw28004step1 = (fun i j => raw28004step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28004step1 raw28004step0; decide +kernel
      have hl : raw28004step1Labels = raw28004step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28004step0 raw28004step0Labels permutation151 permutation3
    mixedMoment B raw28004step1 raw28004step1Labels = mixedMoment B raw28004step2 raw28004step2Labels := by
      have ha : raw28004step2 = -raw28004step1 := by apply Matrix.ext; change ∀ i j, raw28004step2 i j = -(raw28004step1 i j); unfold raw28004step2 raw28004step1; decide +kernel
      have hl : raw28004step2Labels = raw28004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28004step2 raw28004step2Labels = mixedMoment B raw28004step3 raw28004step3Labels := by
      have ha : raw28004step3 = raw28004step2 := by apply Matrix.ext; unfold raw28004step3 raw28004step2; decide +kernel
      have hl : raw28004step2Labels = labelEmbedding6 ∘ raw28004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28004step2 raw28004step2Labels raw28004step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

theorem canonical28005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28005 raw28005Labels = mixedMoment B node4633 node4633Labels := by
  calc
    mixedMoment B raw28005 raw28005Labels = mixedMoment B raw28005step0 raw28005step0Labels := by
      have ha : raw28005step0 = (fun i j => raw28005 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28005step0 raw28005; decide +kernel
      have hl : raw28005step0Labels = raw28005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28005 raw28005Labels permutation686 permutation3
    mixedMoment B raw28005step0 raw28005step0Labels = mixedMoment B raw28005step1 raw28005step1Labels := by
      have ha : raw28005step1 = -raw28005step0 := by apply Matrix.ext; change ∀ i j, raw28005step1 i j = -(raw28005step0 i j); unfold raw28005step1 raw28005step0; decide +kernel
      have hl : raw28005step1Labels = raw28005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28005step1 raw28005step1Labels = mixedMoment B raw28005step2 raw28005step2Labels := by
      have ha : raw28005step2 = raw28005step1 := by apply Matrix.ext; unfold raw28005step2 raw28005step1; decide +kernel
      have hl : raw28005step1Labels = labelEmbedding6 ∘ raw28005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28005step1 raw28005step1Labels raw28005step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4633 node4633Labels := by rfl

theorem canonical28006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28006 raw28006Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw28006 raw28006Labels = mixedMoment B raw28006step0 raw28006step0Labels := by
      have hz : ∀ j, raw28006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28006step0 = (fun i j => raw28006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28006step0 raw28006; decide +kernel
      have hl : raw28006step0Labels = raw28006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28006 raw28006Labels permutation346 hz
    mixedMoment B raw28006step0 raw28006step0Labels = mixedMoment B raw28006step1 raw28006step1Labels := by
      have ha : raw28006step1 = (fun i j => raw28006step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28006step1 raw28006step0; decide +kernel
      have hl : raw28006step1Labels = raw28006step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28006step0 raw28006step0Labels permutation149 permutation3
    mixedMoment B raw28006step1 raw28006step1Labels = mixedMoment B raw28006step2 raw28006step2Labels := by
      have ha : raw28006step2 = -raw28006step1 := by apply Matrix.ext; change ∀ i j, raw28006step2 i j = -(raw28006step1 i j); unfold raw28006step2 raw28006step1; decide +kernel
      have hl : raw28006step2Labels = raw28006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28006step2 raw28006step2Labels = mixedMoment B raw28006step3 raw28006step3Labels := by
      have ha : raw28006step3 = raw28006step2 := by apply Matrix.ext; unfold raw28006step3 raw28006step2; decide +kernel
      have hl : raw28006step2Labels = labelEmbedding6 ∘ raw28006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28006step2 raw28006step2Labels raw28006step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

theorem canonical28007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28007 raw28007Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw28007 raw28007Labels = mixedMoment B raw28007step0 raw28007step0Labels := by
      have hz : ∀ j, raw28007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28007step0 = (fun i j => raw28007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28007step0 raw28007; decide +kernel
      have hl : raw28007step0Labels = raw28007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28007 raw28007Labels permutation346 hz
    mixedMoment B raw28007step0 raw28007step0Labels = mixedMoment B raw28007step1 raw28007step1Labels := by
      have ha : raw28007step1 = (fun i j => raw28007step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28007step1 raw28007step0; decide +kernel
      have hl : raw28007step1Labels = raw28007step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28007step0 raw28007step0Labels permutation151 permutation3
    mixedMoment B raw28007step1 raw28007step1Labels = mixedMoment B raw28007step2 raw28007step2Labels := by
      have ha : raw28007step2 = -raw28007step1 := by apply Matrix.ext; change ∀ i j, raw28007step2 i j = -(raw28007step1 i j); unfold raw28007step2 raw28007step1; decide +kernel
      have hl : raw28007step2Labels = raw28007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28007step2 raw28007step2Labels = mixedMoment B raw28007step3 raw28007step3Labels := by
      have ha : raw28007step3 = raw28007step2 := by apply Matrix.ext; unfold raw28007step3 raw28007step2; decide +kernel
      have hl : raw28007step2Labels = labelEmbedding6 ∘ raw28007step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28007step2 raw28007step2Labels raw28007step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4205 node4205Labels := by rfl

theorem canonical28008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28008 raw28008Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw28008 raw28008Labels = mixedMoment B raw28008step0 raw28008step0Labels := by
      have ha : raw28008step0 = (fun i j => raw28008 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28008step0 raw28008; decide +kernel
      have hl : raw28008step0Labels = raw28008Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28008 raw28008Labels permutation686 permutation3
    mixedMoment B raw28008step0 raw28008step0Labels = mixedMoment B raw28008step1 raw28008step1Labels := by
      have ha : raw28008step1 = -raw28008step0 := by apply Matrix.ext; change ∀ i j, raw28008step1 i j = -(raw28008step0 i j); unfold raw28008step1 raw28008step0; decide +kernel
      have hl : raw28008step1Labels = raw28008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28008step1 raw28008step1Labels = mixedMoment B raw28008step2 raw28008step2Labels := by
      have ha : raw28008step2 = raw28008step1 := by apply Matrix.ext; unfold raw28008step2 raw28008step1; decide +kernel
      have hl : raw28008step1Labels = labelEmbedding6 ∘ raw28008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28008step1 raw28008step1Labels raw28008step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4199 node4199Labels := by rfl

theorem canonical28009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28009 raw28009Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw28009 raw28009Labels = mixedMoment B raw28009step0 raw28009step0Labels := by
      have hz : ∀ j, raw28009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28009step0 = (fun i j => raw28009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28009step0 raw28009; decide +kernel
      have hl : raw28009step0Labels = raw28009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28009 raw28009Labels permutation346 hz
    mixedMoment B raw28009step0 raw28009step0Labels = mixedMoment B raw28009step1 raw28009step1Labels := by
      have ha : raw28009step1 = (fun i j => raw28009step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28009step1 raw28009step0; decide +kernel
      have hl : raw28009step1Labels = raw28009step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28009step0 raw28009step0Labels permutation149 permutation3
    mixedMoment B raw28009step1 raw28009step1Labels = mixedMoment B raw28009step2 raw28009step2Labels := by
      have ha : raw28009step2 = -raw28009step1 := by apply Matrix.ext; change ∀ i j, raw28009step2 i j = -(raw28009step1 i j); unfold raw28009step2 raw28009step1; decide +kernel
      have hl : raw28009step2Labels = raw28009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28009step2 raw28009step2Labels = mixedMoment B raw28009step3 raw28009step3Labels := by
      have ha : raw28009step3 = raw28009step2 := by apply Matrix.ext; unfold raw28009step3 raw28009step2; decide +kernel
      have hl : raw28009step2Labels = labelEmbedding6 ∘ raw28009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28009step2 raw28009step2Labels raw28009step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

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

theorem canonical4610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4610 raw4610Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw4610 raw4610Labels = mixedMoment B raw4610step0 raw4610step0Labels := by
      have ha : raw4610step0 = (fun i j => raw4610 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4610step0 raw4610; decide +kernel
      have hl : raw4610step0Labels = raw4610Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4610 raw4610Labels permutation640 permutation3
    mixedMoment B raw4610step0 raw4610step0Labels = mixedMoment B raw4610step1 raw4610step1Labels := by
      have ha : raw4610step1 = -raw4610step0 := by apply Matrix.ext; change ∀ i j, raw4610step1 i j = -(raw4610step0 i j); unfold raw4610step1 raw4610step0; decide +kernel
      have hl : raw4610step1Labels = raw4610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4610step1 raw4610step1Labels = mixedMoment B raw4610step2 raw4610step2Labels := by
      have ha : raw4610step2 = raw4610step1 := by apply Matrix.ext; unfold raw4610step2 raw4610step1; decide +kernel
      have hl : raw4610step1Labels = labelEmbedding6 ∘ raw4610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4610step1 raw4610step1Labels raw4610step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

theorem canonical4614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4614 raw4614Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4614 raw4614Labels = mixedMoment B raw4614step0 raw4614step0Labels := by
      have hz : ∀ j, raw4614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4614step0 = (fun i j => raw4614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4614step0 raw4614; decide +kernel
      have hl : raw4614step0Labels = raw4614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4614 raw4614Labels permutation346 hz
    mixedMoment B raw4614step0 raw4614step0Labels = mixedMoment B raw4614step1 raw4614step1Labels := by
      have ha : raw4614step1 = (fun i j => raw4614step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4614step1 raw4614step0; decide +kernel
      have hl : raw4614step1Labels = raw4614step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4614step0 raw4614step0Labels permutation145 permutation3
    mixedMoment B raw4614step1 raw4614step1Labels = mixedMoment B raw4614step2 raw4614step2Labels := by
      have ha : raw4614step2 = -raw4614step1 := by apply Matrix.ext; change ∀ i j, raw4614step2 i j = -(raw4614step1 i j); unfold raw4614step2 raw4614step1; decide +kernel
      have hl : raw4614step2Labels = raw4614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4614step2 raw4614step2Labels = mixedMoment B raw4614step3 raw4614step3Labels := by
      have ha : raw4614step3 = raw4614step2 := by apply Matrix.ext; unfold raw4614step3 raw4614step2; decide +kernel
      have hl : raw4614step2Labels = labelEmbedding6 ∘ raw4614step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4614step2 raw4614step2Labels raw4614step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical4617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4617 raw4617Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw4617 raw4617Labels = mixedMoment B raw4617step0 raw4617step0Labels := by
      have hz : ∀ j, raw4617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4617step0 = (fun i j => raw4617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4617step0 raw4617; decide +kernel
      have hl : raw4617step0Labels = raw4617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4617 raw4617Labels permutation346 hz
    mixedMoment B raw4617step0 raw4617step0Labels = mixedMoment B raw4617step1 raw4617step1Labels := by
      have hz : ∀ j, raw4617step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4617step1 = (fun i j => raw4617step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4617step1 raw4617step0; decide +kernel
      have hl : raw4617step1Labels = raw4617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4617step0 raw4617step0Labels permutation56 hz
    mixedMoment B raw4617step1 raw4617step1Labels = mixedMoment B raw4617step2 raw4617step2Labels := by
      have ha : raw4617step2 = (fun i j => raw4617step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4617step2 raw4617step1; decide +kernel
      have hl : raw4617step2Labels = raw4617step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4617step1 raw4617step1Labels permutation8 permutation3
    mixedMoment B raw4617step2 raw4617step2Labels = mixedMoment B raw4617step3 raw4617step3Labels := by
      have ha : raw4617step3 = raw4617step2 := by apply Matrix.ext; unfold raw4617step3 raw4617step2; decide +kernel
      have hl : raw4617step2Labels = labelEmbedding6 ∘ raw4617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4617step2 raw4617step2Labels raw4617step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical4619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4619 raw4619Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4619 raw4619Labels = mixedMoment B raw4619step0 raw4619step0Labels := by
      have hz : ∀ j, raw4619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4619step0 = (fun i j => raw4619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4619step0 raw4619; decide +kernel
      have hl : raw4619step0Labels = raw4619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4619 raw4619Labels permutation265 hz
    mixedMoment B raw4619step0 raw4619step0Labels = mixedMoment B raw4619step1 raw4619step1Labels := by
      have ha : raw4619step1 = (fun i j => raw4619step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4619step1 raw4619step0; decide +kernel
      have hl : raw4619step1Labels = raw4619step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4619step0 raw4619step0Labels permutation151 permutation3
    mixedMoment B raw4619step1 raw4619step1Labels = mixedMoment B raw4619step2 raw4619step2Labels := by
      have ha : raw4619step2 = -raw4619step1 := by apply Matrix.ext; change ∀ i j, raw4619step2 i j = -(raw4619step1 i j); unfold raw4619step2 raw4619step1; decide +kernel
      have hl : raw4619step2Labels = raw4619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4619step2 raw4619step2Labels = mixedMoment B raw4619step3 raw4619step3Labels := by
      have ha : raw4619step3 = raw4619step2 := by apply Matrix.ext; unfold raw4619step3 raw4619step2; decide +kernel
      have hl : raw4619step2Labels = labelEmbedding6 ∘ raw4619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4619step2 raw4619step2Labels raw4619step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical4620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4620 raw4620Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw4620 raw4620Labels = mixedMoment B raw4620step0 raw4620step0Labels := by
      have hz : ∀ j, raw4620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4620step0 = (fun i j => raw4620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4620step0 raw4620; decide +kernel
      have hl : raw4620step0Labels = raw4620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4620 raw4620Labels permutation346 hz
    mixedMoment B raw4620step0 raw4620step0Labels = mixedMoment B raw4620step1 raw4620step1Labels := by
      have hz : ∀ j, raw4620step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4620step1 = (fun i j => raw4620step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4620step1 raw4620step0; decide +kernel
      have hl : raw4620step1Labels = raw4620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4620step0 raw4620step0Labels permutation56 hz
    mixedMoment B raw4620step1 raw4620step1Labels = mixedMoment B raw4620step2 raw4620step2Labels := by
      have ha : raw4620step2 = (fun i j => raw4620step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4620step2 raw4620step1; decide +kernel
      have hl : raw4620step2Labels = raw4620step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4620step1 raw4620step1Labels permutation31 permutation3
    mixedMoment B raw4620step2 raw4620step2Labels = mixedMoment B raw4620step3 raw4620step3Labels := by
      have ha : raw4620step3 = -raw4620step2 := by apply Matrix.ext; change ∀ i j, raw4620step3 i j = -(raw4620step2 i j); unfold raw4620step3 raw4620step2; decide +kernel
      have hl : raw4620step3Labels = raw4620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4620step3 raw4620step3Labels = mixedMoment B raw4620step4 raw4620step4Labels := by
      have ha : raw4620step4 = raw4620step3 := by apply Matrix.ext; unfold raw4620step4 raw4620step3; decide +kernel
      have hl : raw4620step3Labels = labelEmbedding6 ∘ raw4620step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4620step3 raw4620step3Labels raw4620step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical4622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4622 raw4622Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw4622 raw4622Labels = mixedMoment B raw4622step0 raw4622step0Labels := by
      have hz : ∀ j, raw4622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4622step0 = (fun i j => raw4622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4622step0 raw4622; decide +kernel
      have hl : raw4622step0Labels = raw4622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4622 raw4622Labels permutation346 hz
    mixedMoment B raw4622step0 raw4622step0Labels = mixedMoment B raw4622step1 raw4622step1Labels := by
      have ha : raw4622step1 = (fun i j => raw4622step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4622step1 raw4622step0; decide +kernel
      have hl : raw4622step1Labels = raw4622step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4622step0 raw4622step0Labels permutation145 permutation3
    mixedMoment B raw4622step1 raw4622step1Labels = mixedMoment B raw4622step2 raw4622step2Labels := by
      have ha : raw4622step2 = -raw4622step1 := by apply Matrix.ext; change ∀ i j, raw4622step2 i j = -(raw4622step1 i j); unfold raw4622step2 raw4622step1; decide +kernel
      have hl : raw4622step2Labels = raw4622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4622step2 raw4622step2Labels = mixedMoment B raw4622step3 raw4622step3Labels := by
      have ha : raw4622step3 = raw4622step2 := by apply Matrix.ext; unfold raw4622step3 raw4622step2; decide +kernel
      have hl : raw4622step2Labels = labelEmbedding6 ∘ raw4622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4622step2 raw4622step2Labels raw4622step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

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

theorem canonical870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw870 raw870Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw870 raw870Labels = mixedMoment B raw870step0 raw870step0Labels := by
      have ha : raw870step0 = (fun i j => raw870 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw870step0 raw870; decide +kernel
      have hl : raw870step0Labels = raw870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw870 raw870Labels permutation32 permutation4
    mixedMoment B raw870step0 raw870step0Labels = mixedMoment B raw870step1 raw870step1Labels := by
      have ha : raw870step1 = raw870step0 := by apply Matrix.ext; unfold raw870step1 raw870step0; decide +kernel
      have hl : raw870step0Labels = labelEmbedding7 ∘ raw870step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw870step0 raw870step0Labels raw870step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4202 node4202Labels := by rfl

theorem canonical871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw871 raw871Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw871 raw871Labels = mixedMoment B raw871step0 raw871step0Labels := by
      have ha : raw871step0 = (fun i j => raw871 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw871step0 raw871; decide +kernel
      have hl : raw871step0Labels = raw871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw871 raw871Labels permutation32 permutation4
    _ = mixedMoment B node705 node705Labels := by rfl

theorem canonical872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw872 raw872Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw872 raw872Labels = mixedMoment B raw872step0 raw872step0Labels := by
      have ha : raw872step0 = (fun i j => raw872 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw872step0 raw872; decide +kernel
      have hl : raw872step0Labels = raw872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw872 raw872Labels permutation32 permutation6
    mixedMoment B raw872step0 raw872step0Labels = mixedMoment B raw872step1 raw872step1Labels := by
      have ha : raw872step1 = -raw872step0 := by apply Matrix.ext; change ∀ i j, raw872step1 i j = -(raw872step0 i j); unfold raw872step1 raw872step0; decide +kernel
      have hl : raw872step1Labels = raw872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw872step1 raw872step1Labels = mixedMoment B raw872step2 raw872step2Labels := by
      have ha : raw872step2 = raw872step1 := by apply Matrix.ext; unfold raw872step2 raw872step1; decide +kernel
      have hl : raw872step1Labels = labelEmbedding1 ∘ raw872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw872step1 raw872step1Labels raw872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node762 node762Labels := by rfl

theorem canonical879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw879 raw879Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw879 raw879Labels = mixedMoment B raw879step0 raw879step0Labels := by
      have ha : raw879step0 = (fun i j => raw879 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw879step0 raw879; decide +kernel
      have hl : raw879step0Labels = raw879Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw879 raw879Labels permutation32 permutation4
    mixedMoment B raw879step0 raw879step0Labels = mixedMoment B raw879step1 raw879step1Labels := by
      have ha : raw879step1 = raw879step0 := by apply Matrix.ext; unfold raw879step1 raw879step0; decide +kernel
      have hl : raw879step0Labels = labelEmbedding7 ∘ raw879step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw879step0 raw879step0Labels raw879step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4205 node4205Labels := by rfl

theorem canonical880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw880 raw880Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw880 raw880Labels = mixedMoment B raw880step0 raw880step0Labels := by
      have ha : raw880step0 = (fun i j => raw880 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw880step0 raw880; decide +kernel
      have hl : raw880step0Labels = raw880Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw880 raw880Labels permutation32 permutation4
    _ = mixedMoment B node708 node708Labels := by rfl

theorem canonical881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw881 raw881Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw881 raw881Labels = mixedMoment B raw881step0 raw881step0Labels := by
      have ha : raw881step0 = (fun i j => raw881 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw881step0 raw881; decide +kernel
      have hl : raw881step0Labels = raw881Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw881 raw881Labels permutation33 permutation6
    mixedMoment B raw881step0 raw881step0Labels = mixedMoment B raw881step1 raw881step1Labels := by
      have ha : raw881step1 = -raw881step0 := by apply Matrix.ext; change ∀ i j, raw881step1 i j = -(raw881step0 i j); unfold raw881step1 raw881step0; decide +kernel
      have hl : raw881step1Labels = raw881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw881step1 raw881step1Labels = mixedMoment B raw881step2 raw881step2Labels := by
      have ha : raw881step2 = raw881step1 := by apply Matrix.ext; unfold raw881step2 raw881step1; decide +kernel
      have hl : raw881step1Labels = labelEmbedding1 ∘ raw881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw881step1 raw881step1Labels raw881step2Labels labelEmbedding1 hl
    _ = mixedMoment B node764 node764Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7973 raw7973Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw7973 raw7973Labels = mixedMoment B raw7973step0 raw7973step0Labels := by
      have ha : raw7973step0 = (fun i j => raw7973 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7973step0 raw7973; decide +kernel
      have hl : raw7973step0Labels = raw7973Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7973 raw7973Labels permutation158 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical7977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7977 raw7977Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw7977 raw7977Labels = mixedMoment B raw7977step0 raw7977step0Labels := by
      have hz : ∀ j, raw7977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7977step0 = (fun i j => raw7977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7977step0 raw7977; decide +kernel
      have hl : raw7977step0Labels = raw7977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7977 raw7977Labels permutation346 hz
    _ = mixedMoment B node5172 node5172Labels := by rfl

theorem canonical7981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7981 raw7981Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw7981 raw7981Labels = mixedMoment B raw7981step0 raw7981step0Labels := by
      have hz : ∀ j, raw7981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7981step0 = (fun i j => raw7981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7981step0 raw7981; decide +kernel
      have hl : raw7981step0Labels = raw7981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7981 raw7981Labels permutation346 hz
    mixedMoment B raw7981step0 raw7981step0Labels = mixedMoment B raw7981step1 raw7981step1Labels := by
      have ha : raw7981step1 = (fun i j => raw7981step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7981step1 raw7981step0; decide +kernel
      have hl : raw7981step1Labels = raw7981step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7981step0 raw7981step0Labels permutation33 permutation2
    _ = mixedMoment B node5152 node5152Labels := by rfl

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

theorem canonical903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw903 raw903Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw903 raw903Labels = mixedMoment B raw903step0 raw903step0Labels := by
      have ha : raw903step0 = (fun i j => raw903 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw903step0 raw903; decide +kernel
      have hl : raw903step0Labels = raw903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw903 raw903Labels permutation32 permutation4
    mixedMoment B raw903step0 raw903step0Labels = mixedMoment B raw903step1 raw903step1Labels := by
      have ha : raw903step1 = raw903step0 := by apply Matrix.ext; unfold raw903step1 raw903step0; decide +kernel
      have hl : raw903step0Labels = labelEmbedding7 ∘ raw903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw903step0 raw903step0Labels raw903step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

theorem canonical904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw904 raw904Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw904 raw904Labels = mixedMoment B raw904step0 raw904step0Labels := by
      have ha : raw904step0 = (fun i j => raw904 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw904step0 raw904; decide +kernel
      have hl : raw904step0Labels = raw904Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw904 raw904Labels permutation32 permutation4
    _ = mixedMoment B node720 node720Labels := by rfl

theorem canonical905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw905 raw905Labels = mixedMoment B node769 node769Labels := by
  calc
    mixedMoment B raw905 raw905Labels = mixedMoment B raw905step0 raw905step0Labels := by
      have ha : raw905step0 = (fun i j => raw905 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw905step0 raw905; decide +kernel
      have hl : raw905step0Labels = raw905Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw905 raw905Labels permutation33 permutation6
    mixedMoment B raw905step0 raw905step0Labels = mixedMoment B raw905step1 raw905step1Labels := by
      have ha : raw905step1 = -raw905step0 := by apply Matrix.ext; change ∀ i j, raw905step1 i j = -(raw905step0 i j); unfold raw905step1 raw905step0; decide +kernel
      have hl : raw905step1Labels = raw905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw905step1 raw905step1Labels = mixedMoment B raw905step2 raw905step2Labels := by
      have ha : raw905step2 = raw905step1 := by apply Matrix.ext; unfold raw905step2 raw905step1; decide +kernel
      have hl : raw905step1Labels = labelEmbedding1 ∘ raw905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw905step1 raw905step1Labels raw905step2Labels labelEmbedding1 hl
    _ = mixedMoment B node769 node769Labels := by rfl

theorem canonical978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw978 raw978Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw978 raw978Labels = mixedMoment B raw978step0 raw978step0Labels := by
      have ha : raw978step0 = (fun i j => raw978 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw978step0 raw978; decide +kernel
      have hl : raw978step0Labels = raw978Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw978 raw978Labels permutation32 permutation4
    mixedMoment B raw978step0 raw978step0Labels = mixedMoment B raw978step1 raw978step1Labels := by
      have ha : raw978step1 = raw978step0 := by apply Matrix.ext; unfold raw978step1 raw978step0; decide +kernel
      have hl : raw978step0Labels = labelEmbedding7 ∘ raw978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw978step0 raw978step0Labels raw978step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

theorem canonical979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw979 raw979Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw979 raw979Labels = mixedMoment B raw979step0 raw979step0Labels := by
      have ha : raw979step0 = (fun i j => raw979 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw979step0 raw979; decide +kernel
      have hl : raw979step0Labels = raw979Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw979 raw979Labels permutation32 permutation4
    _ = mixedMoment B node787 node787Labels := by rfl

theorem canonical980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw980 raw980Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw980 raw980Labels = mixedMoment B raw980step0 raw980step0Labels := by
      have ha : raw980step0 = (fun i j => raw980 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw980step0 raw980; decide +kernel
      have hl : raw980step0Labels = raw980Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw980 raw980Labels permutation32 permutation6
    mixedMoment B raw980step0 raw980step0Labels = mixedMoment B raw980step1 raw980step1Labels := by
      have ha : raw980step1 = -raw980step0 := by apply Matrix.ext; change ∀ i j, raw980step1 i j = -(raw980step0 i j); unfold raw980step1 raw980step0; decide +kernel
      have hl : raw980step1Labels = raw980step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw980step1 raw980step1Labels = mixedMoment B raw980step2 raw980step2Labels := by
      have ha : raw980step2 = raw980step1 := by apply Matrix.ext; unfold raw980step2 raw980step1; decide +kernel
      have hl : raw980step1Labels = labelEmbedding1 ∘ raw980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw980step1 raw980step1Labels raw980step2Labels labelEmbedding1 hl
    _ = mixedMoment B node847 node847Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5204 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5204 = injectiveMoment H raw5204step0 := by
      have hz : ∀ j, raw5204 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5204step0 = (fun i j => raw5204 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5204 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw782 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw782 = injectiveMoment H raw782step0 := by
      have heq : raw782step0 = -raw782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw782).symm
    injectiveMoment H raw782step0 = injectiveMoment H raw782step1 := by
      have heq : raw782step1 = (fun i j => raw782step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw782step0 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

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

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node405 node405Labels = Sparse.eval singlePairValue405 (familyPairVector B) := by
  have hp := single_label_three B hB node405
  have hl : node405Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node405 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node405 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node405 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node405 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value185 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 4) = PairSemantics.raw782 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node405 PairSemantics.raw782; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical782 hH).trans (PairSemantics.sound185 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue405, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value185, Sparse.eval] at hp ⊢
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

theorem singleton2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2768 node2768Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw272 singletonSmall2768
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2768) = raw272Labels := by decide +kernel
  rw [hl, canonical272 B hB] at h
  have hc0 : mixedMoment B raw272 (Fin.cases (0 : Fin 1) singletonSmall2768) =
      mixedMoment B node405 node405Labels := by
    have ha : raw272 = raw273 := by apply Matrix.ext; unfold raw272 raw273; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2768 = raw273Labels := by decide +kernel
    rw [ha, hj, canonical273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4202 node4202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node705 node705Labels + mixedMoment B node762 node762Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw870 singletonSmall4202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4202) = raw870Labels := by decide +kernel
  rw [hl, canonical870 B hB] at h
  have hc0 : mixedMoment B raw870 (Fin.cases (0 : Fin 2) singletonSmall4202) =
      mixedMoment B node705 node705Labels := by
    have ha : raw870 = raw871 := by apply Matrix.ext; unfold raw870 raw871; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4202 = raw871Labels := by decide +kernel
    rw [ha, hj, canonical871 B hB]
  have hc1 : mixedMoment B raw870 (Fin.cases (1 : Fin 2) singletonSmall4202) =
      mixedMoment B node762 node762Labels := by
    have ha : raw870 = raw872 := by apply Matrix.ext; unfold raw870 raw872; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4202 = raw872Labels := by decide +kernel
    rw [ha, hj, canonical872 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4205 node4205Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node708 node708Labels + mixedMoment B node764 node764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw879 singletonSmall4205
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4205) = raw879Labels := by decide +kernel
  rw [hl, canonical879 B hB] at h
  have hc0 : mixedMoment B raw879 (Fin.cases (0 : Fin 2) singletonSmall4205) =
      mixedMoment B node708 node708Labels := by
    have ha : raw879 = raw880 := by apply Matrix.ext; unfold raw879 raw880; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4205 = raw880Labels := by decide +kernel
    rw [ha, hj, canonical880 B hB]
  have hc1 : mixedMoment B raw879 (Fin.cases (1 : Fin 2) singletonSmall4205) =
      mixedMoment B node764 node764Labels := by
    have ha : raw879 = raw881 := by apply Matrix.ext; unfold raw879 raw881; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4205 = raw881Labels := by decide +kernel
    rw [ha, hj, canonical881 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4219 node4219Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node720 node720Labels + mixedMoment B node769 node769Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw903 singletonSmall4219
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4219) = raw903Labels := by decide +kernel
  rw [hl, canonical903 B hB] at h
  have hc0 : mixedMoment B raw903 (Fin.cases (0 : Fin 2) singletonSmall4219) =
      mixedMoment B node720 node720Labels := by
    have ha : raw903 = raw904 := by apply Matrix.ext; unfold raw903 raw904; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4219 = raw904Labels := by decide +kernel
    rw [ha, hj, canonical904 B hB]
  have hc1 : mixedMoment B raw903 (Fin.cases (1 : Fin 2) singletonSmall4219) =
      mixedMoment B node769 node769Labels := by
    have ha : raw903 = raw905 := by apply Matrix.ext; unfold raw903 raw905; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4219 = raw905Labels := by decide +kernel
    rw [ha, hj, canonical905 B hB]
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

theorem singleton4253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4253 node4253Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node787 node787Labels + mixedMoment B node847 node847Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw978 singletonSmall4253
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4253) = raw978Labels := by decide +kernel
  rw [hl, canonical978 B hB] at h
  have hc0 : mixedMoment B raw978 (Fin.cases (0 : Fin 2) singletonSmall4253) =
      mixedMoment B node787 node787Labels := by
    have ha : raw978 = raw979 := by apply Matrix.ext; unfold raw978 raw979; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4253 = raw979Labels := by decide +kernel
    rw [ha, hj, canonical979 B hB]
  have hc1 : mixedMoment B raw978 (Fin.cases (1 : Fin 2) singletonSmall4253) =
      mixedMoment B node847 node847Labels := by
    have ha : raw978 = raw980 := by apply Matrix.ext; unfold raw978 raw980; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4253 = raw980Labels := by decide +kernel
    rw [ha, hj, canonical980 B hB]
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

theorem singleton4521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4521 node4521Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1105 node1105Labels + mixedMoment B node1887 node1887Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1335 singletonSmall4521
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4521) = raw1335Labels := by decide +kernel
  rw [hl, canonical1335 B hB] at h
  have hc0 : mixedMoment B raw1335 (Fin.cases (0 : Fin 2) singletonSmall4521) =
      mixedMoment B node1105 node1105Labels := by
    have ha : raw1335 = raw1336 := by apply Matrix.ext; unfold raw1335 raw1336; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4521 = raw1336Labels := by decide +kernel
    rw [ha, hj, canonical1336 B hB]
  have hc1 : mixedMoment B raw1335 (Fin.cases (1 : Fin 2) singletonSmall4521) =
      mixedMoment B node1887 node1887Labels := by
    have ha : raw1335 = raw1337 := by apply Matrix.ext; unfold raw1335 raw1337; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4521 = raw1337Labels := by decide +kernel
    rw [ha, hj, canonical1337 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4525 node4525Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1109 node1109Labels + mixedMoment B node1849 node1849Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1347 singletonSmall4525
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4525) = raw1347Labels := by decide +kernel
  rw [hl, canonical1347 B hB] at h
  have hc0 : mixedMoment B raw1347 (Fin.cases (0 : Fin 2) singletonSmall4525) =
      mixedMoment B node1109 node1109Labels := by
    have ha : raw1347 = raw1348 := by apply Matrix.ext; unfold raw1347 raw1348; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4525 = raw1348Labels := by decide +kernel
    rw [ha, hj, canonical1348 B hB]
  have hc1 : mixedMoment B raw1347 (Fin.cases (1 : Fin 2) singletonSmall4525) =
      mixedMoment B node1849 node1849Labels := by
    have ha : raw1347 = raw1349 := by apply Matrix.ext; unfold raw1347 raw1349; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4525 = raw1349Labels := by decide +kernel
    rw [ha, hj, canonical1349 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4543 node4543Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1128 node1128Labels + mixedMoment B node2184 node2184Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1365 singletonSmall4543
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4543) = raw1365Labels := by decide +kernel
  rw [hl, canonical1365 B hB] at h
  have hc0 : mixedMoment B raw1365 (Fin.cases (0 : Fin 2) singletonSmall4543) =
      mixedMoment B node1128 node1128Labels := by
    have ha : raw1365 = raw1366 := by apply Matrix.ext; unfold raw1365 raw1366; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4543 = raw1366Labels := by decide +kernel
    rw [ha, hj, canonical1366 B hB]
  have hc1 : mixedMoment B raw1365 (Fin.cases (1 : Fin 2) singletonSmall4543) =
      mixedMoment B node2184 node2184Labels := by
    have ha : raw1365 = raw1367 := by apply Matrix.ext; unfold raw1365 raw1367; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4543 = raw1367Labels := by decide +kernel
    rw [ha, hj, canonical1367 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4605 node4605Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1239 node1239Labels + mixedMoment B node2226 node2226Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1428 singletonSmall4605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4605) = raw1428Labels := by decide +kernel
  rw [hl, canonical1428 B hB] at h
  have hc0 : mixedMoment B raw1428 (Fin.cases (0 : Fin 2) singletonSmall4605) =
      mixedMoment B node1239 node1239Labels := by
    have ha : raw1428 = raw1429 := by apply Matrix.ext; unfold raw1428 raw1429; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4605 = raw1429Labels := by decide +kernel
    rw [ha, hj, canonical1429 B hB]
  have hc1 : mixedMoment B raw1428 (Fin.cases (1 : Fin 2) singletonSmall4605) =
      mixedMoment B node2226 node2226Labels := by
    have ha : raw1428 = raw1430 := by apply Matrix.ext; unfold raw1428 raw1430; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4605 = raw1430Labels := by decide +kernel
    rw [ha, hj, canonical1430 B hB]
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

theorem singleton4638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4638 node4638Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1767 node1767Labels + mixedMoment B node1851 node1851Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1494 singletonSmall4638
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4638) = raw1494Labels := by decide +kernel
  rw [hl, canonical1494 B hB] at h
  have hc0 : mixedMoment B raw1494 (Fin.cases (0 : Fin 2) singletonSmall4638) =
      mixedMoment B node1767 node1767Labels := by
    have ha : raw1494 = raw1495 := by apply Matrix.ext; unfold raw1494 raw1495; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4638 = raw1495Labels := by decide +kernel
    rw [ha, hj, canonical1495 B hB]
  have hc1 : mixedMoment B raw1494 (Fin.cases (1 : Fin 2) singletonSmall4638) =
      mixedMoment B node1851 node1851Labels := by
    have ha : raw1494 = raw1496 := by apply Matrix.ext; unfold raw1494 raw1496; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4638 = raw1496Labels := by decide +kernel
    rw [ha, hj, canonical1496 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4650 node4650Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1778 node1778Labels + mixedMoment B node1854 node1854Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1515 singletonSmall4650
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4650) = raw1515Labels := by decide +kernel
  rw [hl, canonical1515 B hB] at h
  have hc0 : mixedMoment B raw1515 (Fin.cases (0 : Fin 2) singletonSmall4650) =
      mixedMoment B node1778 node1778Labels := by
    have ha : raw1515 = raw1516 := by apply Matrix.ext; unfold raw1515 raw1516; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4650 = raw1516Labels := by decide +kernel
    rw [ha, hj, canonical1516 B hB]
  have hc1 : mixedMoment B raw1515 (Fin.cases (1 : Fin 2) singletonSmall4650) =
      mixedMoment B node1854 node1854Labels := by
    have ha : raw1515 = raw1517 := by apply Matrix.ext; unfold raw1515 raw1517; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4650 = raw1517Labels := by decide +kernel
    rw [ha, hj, canonical1517 B hB]
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

theorem singleton4707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4707 node4707Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1861 node1861Labels + mixedMoment B node1889 node1889Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1593 singletonSmall4707
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4707) = raw1593Labels := by decide +kernel
  rw [hl, canonical1593 B hB] at h
  have hc0 : mixedMoment B raw1593 (Fin.cases (0 : Fin 2) singletonSmall4707) =
      mixedMoment B node1861 node1861Labels := by
    have ha : raw1593 = raw1594 := by apply Matrix.ext; unfold raw1593 raw1594; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4707 = raw1594Labels := by decide +kernel
    rw [ha, hj, canonical1594 B hB]
  have hc1 : mixedMoment B raw1593 (Fin.cases (1 : Fin 2) singletonSmall4707) =
      mixedMoment B node1889 node1889Labels := by
    have ha : raw1593 = raw1595 := by apply Matrix.ext; unfold raw1593 raw1595; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4707 = raw1595Labels := by decide +kernel
    rw [ha, hj, canonical1595 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4713 node4713Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1867 node1867Labels + mixedMoment B node1891 node1891Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1602 singletonSmall4713
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4713) = raw1602Labels := by decide +kernel
  rw [hl, canonical1602 B hB] at h
  have hc0 : mixedMoment B raw1602 (Fin.cases (0 : Fin 2) singletonSmall4713) =
      mixedMoment B node1867 node1867Labels := by
    have ha : raw1602 = raw1603 := by apply Matrix.ext; unfold raw1602 raw1603; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4713 = raw1603Labels := by decide +kernel
    rw [ha, hj, canonical1603 B hB]
  have hc1 : mixedMoment B raw1602 (Fin.cases (1 : Fin 2) singletonSmall4713) =
      mixedMoment B node1891 node1891Labels := by
    have ha : raw1602 = raw1604 := by apply Matrix.ext; unfold raw1602 raw1604; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4713 = raw1604Labels := by decide +kernel
    rw [ha, hj, canonical1604 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4729 node4729Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1898 node1898Labels + mixedMoment B node1940 node1940Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1644 singletonSmall4729
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4729) = raw1644Labels := by decide +kernel
  rw [hl, canonical1644 B hB] at h
  have hc0 : mixedMoment B raw1644 (Fin.cases (0 : Fin 2) singletonSmall4729) =
      mixedMoment B node1898 node1898Labels := by
    have ha : raw1644 = raw1645 := by apply Matrix.ext; unfold raw1644 raw1645; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4729 = raw1645Labels := by decide +kernel
    rw [ha, hj, canonical1645 B hB]
  have hc1 : mixedMoment B raw1644 (Fin.cases (1 : Fin 2) singletonSmall4729) =
      mixedMoment B node1940 node1940Labels := by
    have ha : raw1644 = raw1646 := by apply Matrix.ext; unfold raw1644 raw1646; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4729 = raw1646Labels := by decide +kernel
    rw [ha, hj, canonical1646 B hB]
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

theorem singleton4770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4770 node4770Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1970 node1970Labels + mixedMoment B node2186 node2186Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1707 singletonSmall4770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4770) = raw1707Labels := by decide +kernel
  rw [hl, canonical1707 B hB] at h
  have hc0 : mixedMoment B raw1707 (Fin.cases (0 : Fin 2) singletonSmall4770) =
      mixedMoment B node1970 node1970Labels := by
    have ha : raw1707 = raw1708 := by apply Matrix.ext; unfold raw1707 raw1708; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4770 = raw1708Labels := by decide +kernel
    rw [ha, hj, canonical1708 B hB]
  have hc1 : mixedMoment B raw1707 (Fin.cases (1 : Fin 2) singletonSmall4770) =
      mixedMoment B node2186 node2186Labels := by
    have ha : raw1707 = raw1709 := by apply Matrix.ext; unfold raw1707 raw1709; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4770 = raw1709Labels := by decide +kernel
    rw [ha, hj, canonical1709 B hB]
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

theorem singleton4843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4843 node4843Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2062 node2062Labels + mixedMoment B node2230 node2230Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1773 singletonSmall4843
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4843) = raw1773Labels := by decide +kernel
  rw [hl, canonical1773 B hB] at h
  have hc0 : mixedMoment B raw1773 (Fin.cases (0 : Fin 2) singletonSmall4843) =
      mixedMoment B node2062 node2062Labels := by
    have ha : raw1773 = raw1774 := by apply Matrix.ext; unfold raw1773 raw1774; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4843 = raw1774Labels := by decide +kernel
    rw [ha, hj, canonical1774 B hB]
  have hc1 : mixedMoment B raw1773 (Fin.cases (1 : Fin 2) singletonSmall4843) =
      mixedMoment B node2230 node2230Labels := by
    have ha : raw1773 = raw1775 := by apply Matrix.ext; unfold raw1773 raw1775; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4843 = raw1775Labels := by decide +kernel
    rw [ha, hj, canonical1775 B hB]
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

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
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

theorem singleton5149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5149 node5149Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2924 node2924Labels + mixedMoment B node3605 node3605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2175 singletonSmall5149
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5149) = raw2175Labels := by decide +kernel
  rw [hl, canonical2175 B hB] at h
  have hc0 : mixedMoment B raw2175 (Fin.cases (0 : Fin 2) singletonSmall5149) =
      mixedMoment B node2924 node2924Labels := by
    have ha : raw2175 = raw2176 := by apply Matrix.ext; unfold raw2175 raw2176; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5149 = raw2176Labels := by decide +kernel
    rw [ha, hj, canonical2176 B hB]
  have hc1 : mixedMoment B raw2175 (Fin.cases (1 : Fin 2) singletonSmall5149) =
      mixedMoment B node3605 node3605Labels := by
    have ha : raw2175 = raw2177 := by apply Matrix.ext; unfold raw2175 raw2177; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5149 = raw2177Labels := by decide +kernel
    rw [ha, hj, canonical2177 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5152 node5152Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2931 node2931Labels + mixedMoment B node3612 node3612Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2178 singletonSmall5152
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5152) = raw2178Labels := by decide +kernel
  rw [hl, canonical2178 B hB] at h
  have hc0 : mixedMoment B raw2178 (Fin.cases (0 : Fin 2) singletonSmall5152) =
      mixedMoment B node2931 node2931Labels := by
    have ha : raw2178 = raw2179 := by apply Matrix.ext; unfold raw2178 raw2179; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5152 = raw2179Labels := by decide +kernel
    rw [ha, hj, canonical2179 B hB]
  have hc1 : mixedMoment B raw2178 (Fin.cases (1 : Fin 2) singletonSmall5152) =
      mixedMoment B node3612 node3612Labels := by
    have ha : raw2178 = raw2180 := by apply Matrix.ext; unfold raw2178 raw2180; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5152 = raw2180Labels := by decide +kernel
    rw [ha, hj, canonical2180 B hB]
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

theorem singleton5294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5294 node5294Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2768 node2768Labels + mixedMoment B node3632 node3632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2304 singletonSmall5294
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5294) = raw2304Labels := by decide +kernel
  rw [hl, canonical2304 B hB] at h
  have hc0 : mixedMoment B raw2304 (Fin.cases (0 : Fin 2) singletonSmall5294) =
      mixedMoment B node2768 node2768Labels := by
    have ha : raw2304 = raw2305 := by apply Matrix.ext; unfold raw2304 raw2305; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5294 = raw2305Labels := by decide +kernel
    rw [ha, hj, canonical2305 B hB]
  have hc1 : mixedMoment B raw2304 (Fin.cases (1 : Fin 2) singletonSmall5294) =
      mixedMoment B node3632 node3632Labels := by
    have ha : raw2304 = raw2306 := by apply Matrix.ext; unfold raw2304 raw2306; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5294 = raw2306Labels := by decide +kernel
    rw [ha, hj, canonical2306 B hB]
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

theorem sound705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node705 node705Labels = Sparse.eval nodeValue705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 705) = mixedMoment B node705 node705Labels := rfl
  simpa [nodeValue705, Sparse.eval] using hc.symm

theorem sound708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node708 node708Labels = Sparse.eval nodeValue708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 708) = mixedMoment B node708 node708Labels := rfl
  simpa [nodeValue708, Sparse.eval] using hc.symm

theorem sound720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node720 node720Labels = Sparse.eval nodeValue720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 720) = mixedMoment B node720 node720Labels := rfl
  simpa [nodeValue720, Sparse.eval] using hc.symm

theorem sound760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node760 node760Labels = Sparse.eval nodeValue760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 760) = mixedMoment B node760 node760Labels := rfl
  simpa [nodeValue760, Sparse.eval] using hc.symm

theorem sound762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node762 node762Labels = Sparse.eval nodeValue762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 762) = mixedMoment B node762 node762Labels := rfl
  simpa [nodeValue762, Sparse.eval] using hc.symm

theorem sound764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node764 node764Labels = Sparse.eval nodeValue764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 764) = mixedMoment B node764 node764Labels := rfl
  simpa [nodeValue764, Sparse.eval] using hc.symm

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

theorem sound769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node769 node769Labels = Sparse.eval nodeValue769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 769) = mixedMoment B node769 node769Labels := rfl
  simpa [nodeValue769, Sparse.eval] using hc.symm

theorem sound787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node787 node787Labels = Sparse.eval nodeValue787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 787) = mixedMoment B node787 node787Labels := rfl
  simpa [nodeValue787, Sparse.eval] using hc.symm

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

theorem sound847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node847 node847Labels = Sparse.eval nodeValue847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 847) = mixedMoment B node847 node847Labels := rfl
  simpa [nodeValue847, Sparse.eval] using hc.symm

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

theorem sound1105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1105 node1105Labels = Sparse.eval nodeValue1105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1105) = mixedMoment B node1105 node1105Labels := rfl
  simpa [nodeValue1105, Sparse.eval] using hc.symm

theorem sound1109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1109 node1109Labels = Sparse.eval nodeValue1109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1109) = mixedMoment B node1109 node1109Labels := rfl
  simpa [nodeValue1109, Sparse.eval] using hc.symm

theorem sound1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1128 node1128Labels = Sparse.eval nodeValue1128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1128) = mixedMoment B node1128 node1128Labels := rfl
  simpa [nodeValue1128, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

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

theorem sound1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1767 node1767Labels = Sparse.eval nodeValue1767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1767) = mixedMoment B node1767 node1767Labels := rfl
  simpa [nodeValue1767, Sparse.eval] using hc.symm

theorem sound1778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1778 node1778Labels = Sparse.eval nodeValue1778 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1778) = mixedMoment B node1778 node1778Labels := rfl
  simpa [nodeValue1778, Sparse.eval] using hc.symm

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

theorem sound1847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1847 node1847Labels = Sparse.eval nodeValue1847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1847) = mixedMoment B node1847 node1847Labels := rfl
  simpa [nodeValue1847, Sparse.eval] using hc.symm

theorem sound1849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1849 node1849Labels = Sparse.eval nodeValue1849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1849) = mixedMoment B node1849 node1849Labels := rfl
  simpa [nodeValue1849, Sparse.eval] using hc.symm

theorem sound1851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1851 node1851Labels = Sparse.eval nodeValue1851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1851) = mixedMoment B node1851 node1851Labels := rfl
  simpa [nodeValue1851, Sparse.eval] using hc.symm

theorem sound1854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1854 node1854Labels = Sparse.eval nodeValue1854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1854) = mixedMoment B node1854 node1854Labels := rfl
  simpa [nodeValue1854, Sparse.eval] using hc.symm

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

theorem sound1861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1861 node1861Labels = Sparse.eval nodeValue1861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1861) = mixedMoment B node1861 node1861Labels := rfl
  simpa [nodeValue1861, Sparse.eval] using hc.symm

theorem sound1867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1867 node1867Labels = Sparse.eval nodeValue1867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1867) = mixedMoment B node1867 node1867Labels := rfl
  simpa [nodeValue1867, Sparse.eval] using hc.symm

theorem sound1887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1887 node1887Labels = Sparse.eval nodeValue1887 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1887) = mixedMoment B node1887 node1887Labels := rfl
  simpa [nodeValue1887, Sparse.eval] using hc.symm

theorem sound1889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1889 node1889Labels = Sparse.eval nodeValue1889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1889) = mixedMoment B node1889 node1889Labels := rfl
  simpa [nodeValue1889, Sparse.eval] using hc.symm

theorem sound1891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1891 node1891Labels = Sparse.eval nodeValue1891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1891) = mixedMoment B node1891 node1891Labels := rfl
  simpa [nodeValue1891, Sparse.eval] using hc.symm

theorem sound1898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1898 node1898Labels = Sparse.eval nodeValue1898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1898) = mixedMoment B node1898 node1898Labels := rfl
  simpa [nodeValue1898, Sparse.eval] using hc.symm

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

theorem sound1940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1940 node1940Labels = Sparse.eval nodeValue1940 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1940) = mixedMoment B node1940 node1940Labels := rfl
  simpa [nodeValue1940, Sparse.eval] using hc.symm

theorem sound1964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1964 node1964Labels = Sparse.eval nodeValue1964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1964) = mixedMoment B node1964 node1964Labels := rfl
  simpa [nodeValue1964, Sparse.eval] using hc.symm

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

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

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

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

theorem sound2182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2182 node2182Labels = Sparse.eval nodeValue2182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2182) = mixedMoment B node2182 node2182Labels := rfl
  simpa [nodeValue2182, Sparse.eval] using hc.symm

theorem sound2184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2184 node2184Labels = Sparse.eval nodeValue2184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2184) = mixedMoment B node2184 node2184Labels := rfl
  simpa [nodeValue2184, Sparse.eval] using hc.symm

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

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

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

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

theorem sound405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node405 node405Labels = Sparse.eval nodeValue405 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue405 (familyPairVector B) := singlePair405 B _hB
    _ = _ := by
      norm_num [singlePairValue405, nodeValue405, Sparse.eval, mixedVector]
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

theorem sound2768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2768 node2768Labels = Sparse.eval nodeValue2768 (mixedVector B) := by
  have h := singleton2768 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue2768, nodeValue405, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

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

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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

theorem sound4202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4202 node4202Labels = Sparse.eval nodeValue4202 (mixedVector B) := by
  have h := singleton4202 B _hB
  rw [sound705 B _hB _hF, sound762 B _hB _hF] at h
  norm_num [nodeValue4202, nodeValue705, nodeValue762, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4205 node4205Labels = Sparse.eval nodeValue4205 (mixedVector B) := by
  have h := singleton4205 B _hB
  rw [sound708 B _hB _hF, sound764 B _hB _hF] at h
  norm_num [nodeValue4205, nodeValue708, nodeValue764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4219 node4219Labels = Sparse.eval nodeValue4219 (mixedVector B) := by
  have h := singleton4219 B _hB
  rw [sound720 B _hB _hF, sound769 B _hB _hF] at h
  norm_num [nodeValue4219, nodeValue720, nodeValue769, Sparse.eval] at h ⊢
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

theorem sound4253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4253 node4253Labels = Sparse.eval nodeValue4253 (mixedVector B) := by
  have h := singleton4253 B _hB
  rw [sound787 B _hB _hF, sound847 B _hB _hF] at h
  norm_num [nodeValue4253, nodeValue787, nodeValue847, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4521 node4521Labels = Sparse.eval nodeValue4521 (mixedVector B) := by
  have h := singleton4521 B _hB
  rw [sound1105 B _hB _hF, sound1887 B _hB _hF] at h
  norm_num [nodeValue4521, nodeValue1105, nodeValue1887, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4525 node4525Labels = Sparse.eval nodeValue4525 (mixedVector B) := by
  have h := singleton4525 B _hB
  rw [sound1109 B _hB _hF, sound1849 B _hB _hF] at h
  norm_num [nodeValue4525, nodeValue1109, nodeValue1849, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4543 node4543Labels = Sparse.eval nodeValue4543 (mixedVector B) := by
  have h := singleton4543 B _hB
  rw [sound1128 B _hB _hF, sound2184 B _hB _hF] at h
  norm_num [nodeValue4543, nodeValue1128, nodeValue2184, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4605 node4605Labels = Sparse.eval nodeValue4605 (mixedVector B) := by
  have h := singleton4605 B _hB
  rw [sound1239 B _hB _hF, sound2226 B _hB _hF] at h
  norm_num [nodeValue4605, nodeValue1239, nodeValue2226, Sparse.eval] at h ⊢
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

theorem sound4638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4638 node4638Labels = Sparse.eval nodeValue4638 (mixedVector B) := by
  have h := singleton4638 B _hB
  rw [sound1767 B _hB _hF, sound1851 B _hB _hF] at h
  norm_num [nodeValue4638, nodeValue1767, nodeValue1851, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4650 node4650Labels = Sparse.eval nodeValue4650 (mixedVector B) := by
  have h := singleton4650 B _hB
  rw [sound1778 B _hB _hF, sound1854 B _hB _hF] at h
  norm_num [nodeValue4650, nodeValue1778, nodeValue1854, Sparse.eval] at h ⊢
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

theorem sound4707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4707 node4707Labels = Sparse.eval nodeValue4707 (mixedVector B) := by
  have h := singleton4707 B _hB
  rw [sound1861 B _hB _hF, sound1889 B _hB _hF] at h
  norm_num [nodeValue4707, nodeValue1861, nodeValue1889, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4713 node4713Labels = Sparse.eval nodeValue4713 (mixedVector B) := by
  have h := singleton4713 B _hB
  rw [sound1867 B _hB _hF, sound1891 B _hB _hF] at h
  norm_num [nodeValue4713, nodeValue1867, nodeValue1891, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4729 node4729Labels = Sparse.eval nodeValue4729 (mixedVector B) := by
  have h := singleton4729 B _hB
  rw [sound1898 B _hB _hF, sound1940 B _hB _hF] at h
  norm_num [nodeValue4729, nodeValue1898, nodeValue1940, Sparse.eval] at h ⊢
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

theorem sound4770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4770 node4770Labels = Sparse.eval nodeValue4770 (mixedVector B) := by
  have h := singleton4770 B _hB
  rw [sound1970 B _hB _hF, sound2186 B _hB _hF] at h
  norm_num [nodeValue4770, nodeValue1970, nodeValue2186, Sparse.eval] at h ⊢
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

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4843 node4843Labels = Sparse.eval nodeValue4843 (mixedVector B) := by
  have h := singleton4843 B _hB
  rw [sound2062 B _hB _hF, sound2230 B _hB _hF] at h
  norm_num [nodeValue4843, nodeValue2062, nodeValue2230, Sparse.eval] at h ⊢
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

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
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

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5152 node5152Labels = Sparse.eval nodeValue5152 (mixedVector B) := by
  have h := singleton5152 B _hB
  rw [sound2931 B _hB _hF, sound3612 B _hB _hF] at h
  norm_num [nodeValue5152, nodeValue2931, nodeValue3612, Sparse.eval] at h ⊢
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

theorem sound5294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5294 node5294Labels = Sparse.eval nodeValue5294 (mixedVector B) := by
  have h := singleton5294 B _hB
  rw [sound2768 B _hB _hF, sound3632 B _hB _hF] at h
  norm_num [nodeValue5294, nodeValue2768, nodeValue3632, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1971 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1971 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 1) (sourceB1971 + difference 1 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 1) (sourceB1971 + difference 1 0) sourceC1971) = raw15180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw15180; decide +kernel
    rw [ha]
    exact (canonical15180 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 2) (sourceB1971 + difference 2 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 2) (sourceB1971 + difference 2 0) sourceC1971) = raw15181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw15181; decide +kernel
    rw [ha]
    exact (canonical15181 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 3) (sourceB1971 + difference 3 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 3) (sourceB1971 + difference 3 0) sourceC1971) = raw15182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw15182; decide +kernel
    rw [ha]
    exact (canonical15182 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 4) (sourceB1971 + difference 4 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 4) (sourceB1971 + difference 4 0) sourceC1971) = raw2687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw2687; decide +kernel
    rw [ha]
    exact (canonical2687 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1971 + difference 0 5) (sourceB1971 + difference 5 0) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1971 + difference 0 5) (sourceB1971 + difference 5 0) sourceC1971) = raw2682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw2682; decide +kernel
    rw [ha]
    exact (canonical2682 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 0) (sourceB1971 + difference 0 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 0) (sourceB1971 + difference 0 1) sourceC1971) = raw4617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4617; decide +kernel
    rw [ha]
    exact (canonical4617 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 2) (sourceB1971 + difference 2 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 2) (sourceB1971 + difference 2 1) sourceC1971) = raw4619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4619; decide +kernel
    rw [ha]
    exact (canonical4619 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 3) (sourceB1971 + difference 3 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 3) (sourceB1971 + difference 3 1) sourceC1971) = raw4620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4620; decide +kernel
    rw [ha]
    exact (canonical4620 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 4) (sourceB1971 + difference 4 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 4) (sourceB1971 + difference 4 1) sourceC1971) = raw2686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw2686; decide +kernel
    rw [ha]
    exact (canonical2686 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1971 + difference 1 5) (sourceB1971 + difference 5 1) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1971 + difference 1 5) (sourceB1971 + difference 5 1) sourceC1971) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 0) (sourceB1971 + difference 0 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 0) (sourceB1971 + difference 0 2) sourceC1971) = raw20934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw20934; decide +kernel
    rw [ha]
    exact (canonical20934 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 1) (sourceB1971 + difference 1 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4707) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 1) (sourceB1971 + difference 1 2) sourceC1971) = raw28000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28000; decide +kernel
    rw [ha]
    exact (canonical28000 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 3) (sourceB1971 + difference 3 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 3) (sourceB1971 + difference 3 2) sourceC1971) = raw28001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28001; decide +kernel
    rw [ha]
    exact (canonical28001 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 4) (sourceB1971 + difference 4 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 4) (sourceB1971 + difference 4 2) sourceC1971) = raw4610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4610; decide +kernel
    rw [ha]
    exact (canonical4610 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1971 + difference 2 5) (sourceB1971 + difference 5 2) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1971 + difference 2 5) (sourceB1971 + difference 5 2) sourceC1971) = raw7973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw7973; decide +kernel
    rw [ha]
    exact (canonical7973 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 0) (sourceB1971 + difference 0 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 0) (sourceB1971 + difference 0 3) sourceC1971) = raw20937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw20937; decide +kernel
    rw [ha]
    exact (canonical20937 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 1) (sourceB1971 + difference 1 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 1) (sourceB1971 + difference 1 3) sourceC1971) = raw28002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28002; decide +kernel
    rw [ha]
    exact (canonical28002 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 2) (sourceB1971 + difference 2 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4764) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 2) (sourceB1971 + difference 2 3) sourceC1971) = raw28003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28003; decide +kernel
    rw [ha]
    exact (canonical28003 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 4) (sourceB1971 + difference 4 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 4) (sourceB1971 + difference 4 3) sourceC1971) = raw4614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4614; decide +kernel
    rw [ha]
    exact (canonical4614 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1971 + difference 3 5) (sourceB1971 + difference 5 3) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1971 + difference 3 5) (sourceB1971 + difference 5 3) sourceC1971) = raw7977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw7977; decide +kernel
    rw [ha]
    exact (canonical7977 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 0) (sourceB1971 + difference 0 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 0) (sourceB1971 + difference 0 4) sourceC1971) = raw20940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw20940; decide +kernel
    rw [ha]
    exact (canonical20940 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 1) (sourceB1971 + difference 1 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4638) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 1) (sourceB1971 + difference 1 4) sourceC1971) = raw28004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28004; decide +kernel
    rw [ha]
    exact (canonical28004 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 2) (sourceB1971 + difference 2 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4633) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 2) (sourceB1971 + difference 2 4) sourceC1971) = raw28005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28005; decide +kernel
    rw [ha]
    exact (canonical28005 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 3) (sourceB1971 + difference 3 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 3) (sourceB1971 + difference 3 4) sourceC1971) = raw28006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28006; decide +kernel
    rw [ha]
    exact (canonical28006 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1971 + difference 4 5) (sourceB1971 + difference 5 4) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1971 + difference 4 5) (sourceB1971 + difference 5 4) sourceC1971) = raw7981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw7981; decide +kernel
    rw [ha]
    exact (canonical7981 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 0) (sourceB1971 + difference 0 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 0) (sourceB1971 + difference 0 5) sourceC1971) = raw20944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw20944; decide +kernel
    rw [ha]
    exact (canonical20944 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 1) (sourceB1971 + difference 1 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4205) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 1) (sourceB1971 + difference 1 5) sourceC1971) = raw28007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28007; decide +kernel
    rw [ha]
    exact (canonical28007 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 2) (sourceB1971 + difference 2 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4199) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 2) (sourceB1971 + difference 2 5) sourceC1971) = raw28008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28008; decide +kernel
    rw [ha]
    exact (canonical28008 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 3) (sourceB1971 + difference 3 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 3) (sourceB1971 + difference 3 5) sourceC1971) = raw28009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw28009; decide +kernel
    rw [ha]
    exact (canonical28009 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1971 + difference 5 4) (sourceB1971 + difference 4 5) sourceC1971) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1971 + difference 5 4) (sourceB1971 + difference 4 5) sourceC1971) = raw4622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1971 sourceB1971 sourceC1971 difference raw4622; decide +kernel
    rw [ha]
    exact (canonical4622 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1971 sourceB1971 sourceC1971
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1971, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1672 : Integer.Sparse.reindex keyMap MixedData.row1672 = numericRow1672 := by decide +kernel

theorem numericCheck1672 (x : Master → ℝ) : Integer.Sparse.eval numericRow1672 x =
    (17280 : ℝ) * reducedSource1672 x := by
  norm_num [numericRow1672, reducedSource1672, Integer.Sparse.eval, Sparse.eval, nodeValue4199, nodeValue4202, nodeValue4205, nodeValue4219, nodeValue4253, nodeValue4521, nodeValue4525, nodeValue4543, nodeValue4605, nodeValue4633, nodeValue4638, nodeValue4650, nodeValue4707, nodeValue4713, nodeValue4729, nodeValue4764, nodeValue4770, nodeValue4805, nodeValue4807, nodeValue4810, nodeValue4839, nodeValue4843, nodeValue4889, nodeValue4890, nodeValue5149, nodeValue5152, nodeValue5172, nodeValue5294, nodeValue5435]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1672 (mixedVector B) = 0 := by
  have h4199 : mixedVector B (Sum.inr 4199) = Sparse.eval nodeValue4199 (mixedVector B) := by
    change mixedMoment B node4199 node4199Labels = _
    exact sound4199 B hB hF
  have h4202 : mixedVector B (Sum.inr 4202) = Sparse.eval nodeValue4202 (mixedVector B) := by
    change mixedMoment B node4202 node4202Labels = _
    exact sound4202 B hB hF
  have h4205 : mixedVector B (Sum.inr 4205) = Sparse.eval nodeValue4205 (mixedVector B) := by
    change mixedMoment B node4205 node4205Labels = _
    exact sound4205 B hB hF
  have h4219 : mixedVector B (Sum.inr 4219) = Sparse.eval nodeValue4219 (mixedVector B) := by
    change mixedMoment B node4219 node4219Labels = _
    exact sound4219 B hB hF
  have h4253 : mixedVector B (Sum.inr 4253) = Sparse.eval nodeValue4253 (mixedVector B) := by
    change mixedMoment B node4253 node4253Labels = _
    exact sound4253 B hB hF
  have h4521 : mixedVector B (Sum.inr 4521) = Sparse.eval nodeValue4521 (mixedVector B) := by
    change mixedMoment B node4521 node4521Labels = _
    exact sound4521 B hB hF
  have h4525 : mixedVector B (Sum.inr 4525) = Sparse.eval nodeValue4525 (mixedVector B) := by
    change mixedMoment B node4525 node4525Labels = _
    exact sound4525 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4633 : mixedVector B (Sum.inr 4633) = Sparse.eval nodeValue4633 (mixedVector B) := by
    change mixedMoment B node4633 node4633Labels = _
    exact sound4633 B hB hF
  have h4638 : mixedVector B (Sum.inr 4638) = Sparse.eval nodeValue4638 (mixedVector B) := by
    change mixedMoment B node4638 node4638Labels = _
    exact sound4638 B hB hF
  have h4650 : mixedVector B (Sum.inr 4650) = Sparse.eval nodeValue4650 (mixedVector B) := by
    change mixedMoment B node4650 node4650Labels = _
    exact sound4650 B hB hF
  have h4707 : mixedVector B (Sum.inr 4707) = Sparse.eval nodeValue4707 (mixedVector B) := by
    change mixedMoment B node4707 node4707Labels = _
    exact sound4707 B hB hF
  have h4713 : mixedVector B (Sum.inr 4713) = Sparse.eval nodeValue4713 (mixedVector B) := by
    change mixedMoment B node4713 node4713Labels = _
    exact sound4713 B hB hF
  have h4729 : mixedVector B (Sum.inr 4729) = Sparse.eval nodeValue4729 (mixedVector B) := by
    change mixedMoment B node4729 node4729Labels = _
    exact sound4729 B hB hF
  have h4764 : mixedVector B (Sum.inr 4764) = Sparse.eval nodeValue4764 (mixedVector B) := by
    change mixedMoment B node4764 node4764Labels = _
    exact sound4764 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5172 : mixedVector B (Sum.inr 5172) = Sparse.eval nodeValue5172 (mixedVector B) := by
    change mixedMoment B node5172 node5172Labels = _
    exact sound5172_e B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  simpa only [sourceForm1971, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4199, h4202, h4205, h4219, h4253, h4521, h4525, h4543, h4605, h4633, h4638, h4650, h4707, h4713, h4729, h4764, h4770, h4805, h4807, h4810, h4839, h4843, h4889, h4890, h5149, h5152, h5172, h5294, h5435, reducedSource1672] using sourceEq1971 B hB

theorem rowSound1672_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1672 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1672, numericCheck1672, reducedZero1672 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e_oai
