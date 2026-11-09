-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:04:25.884921+00:00
-- url     : https://prove2.me/submissions/242cfe37-fd3f-4d19-bac8-5d3366f56562

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E114
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical76 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw76 raw76Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw76 raw76Labels = mixedMoment B raw76step0 raw76step0Labels := by
      have ha : raw76step0 = (fun i j => raw76 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw76step0 raw76; decide +kernel
      have hl : raw76step0Labels = raw76Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw76 raw76Labels permutation8 permutation5
    mixedMoment B raw76step0 raw76step0Labels = mixedMoment B raw76step1 raw76step1Labels := by
      have ha : raw76step1 = raw76step0 := by apply Matrix.ext; unfold raw76step1 raw76step0; decide +kernel
      have hl : raw76step0Labels = labelEmbedding1 ∘ raw76step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw76step0 raw76step0Labels raw76step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1300 node1300Labels := by rfl

theorem canonical77 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw77 raw77Labels = mixedMoment B node156 node156Labels := by
  calc
    mixedMoment B raw77 raw77Labels = mixedMoment B raw77step0 raw77step0Labels := by
      have ha : raw77step0 = (fun i j => raw77 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw77step0 raw77; decide +kernel
      have hl : raw77step0Labels = raw77Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw77 raw77Labels permutation8 permutation5
    _ = mixedMoment B node156 node156Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1314 raw1314Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw1314 raw1314Labels = mixedMoment B raw1314step0 raw1314step0Labels := by
      have ha : raw1314step0 = (fun i j => raw1314 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1314step0 raw1314; decide +kernel
      have hl : raw1314step0Labels = raw1314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1314 raw1314Labels permutation32 permutation4
    mixedMoment B raw1314step0 raw1314step0Labels = mixedMoment B raw1314step1 raw1314step1Labels := by
      have ha : raw1314step1 = raw1314step0 := by apply Matrix.ext; unfold raw1314step1 raw1314step0; decide +kernel
      have hl : raw1314step0Labels = labelEmbedding7 ∘ raw1314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1314step0 raw1314step0Labels raw1314step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

theorem canonical1315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1315 raw1315Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw1315 raw1315Labels = mixedMoment B raw1315step0 raw1315step0Labels := by
      have ha : raw1315step0 = (fun i j => raw1315 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1315step0 raw1315; decide +kernel
      have hl : raw1315step0Labels = raw1315Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1315 raw1315Labels permutation32 permutation4
    _ = mixedMoment B node1098 node1098Labels := by rfl

theorem canonical1316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1316 raw1316Labels = mixedMoment B node1894 node1894Labels := by
  calc
    mixedMoment B raw1316 raw1316Labels = mixedMoment B raw1316step0 raw1316step0Labels := by
      have ha : raw1316step0 = (fun i j => raw1316 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1316step0 raw1316; decide +kernel
      have hl : raw1316step0Labels = raw1316Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1316 raw1316Labels permutation151 permutation6
    mixedMoment B raw1316step0 raw1316step0Labels = mixedMoment B raw1316step1 raw1316step1Labels := by
      have ha : raw1316step1 = raw1316step0 := by apply Matrix.ext; unfold raw1316step1 raw1316step0; decide +kernel
      have hl : raw1316step0Labels = labelEmbedding1 ∘ raw1316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1316step0 raw1316step0Labels raw1316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1894 node1894Labels := by rfl

theorem canonical1329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1329 raw1329Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw1329 raw1329Labels = mixedMoment B raw1329step0 raw1329step0Labels := by
      have ha : raw1329step0 = (fun i j => raw1329 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1329step0 raw1329; decide +kernel
      have hl : raw1329step0Labels = raw1329Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1329 raw1329Labels permutation8 permutation4
    mixedMoment B raw1329step0 raw1329step0Labels = mixedMoment B raw1329step1 raw1329step1Labels := by
      have ha : raw1329step1 = raw1329step0 := by apply Matrix.ext; unfold raw1329step1 raw1329step0; decide +kernel
      have hl : raw1329step0Labels = labelEmbedding7 ∘ raw1329step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1329step0 raw1329step0Labels raw1329step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

theorem canonical1330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1330 raw1330Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw1330 raw1330Labels = mixedMoment B raw1330step0 raw1330step0Labels := by
      have ha : raw1330step0 = (fun i j => raw1330 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1330step0 raw1330; decide +kernel
      have hl : raw1330step0Labels = raw1330Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1330 raw1330Labels permutation8 permutation4
    _ = mixedMoment B node1103 node1103Labels := by rfl

theorem canonical1331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1331 raw1331Labels = mixedMoment B node1858 node1858Labels := by
  calc
    mixedMoment B raw1331 raw1331Labels = mixedMoment B raw1331step0 raw1331step0Labels := by
      have ha : raw1331step0 = (fun i j => raw1331 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1331step0 raw1331; decide +kernel
      have hl : raw1331step0Labels = raw1331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1331 raw1331Labels permutation31 permutation6
    mixedMoment B raw1331step0 raw1331step0Labels = mixedMoment B raw1331step1 raw1331step1Labels := by
      have ha : raw1331step1 = raw1331step0 := by apply Matrix.ext; unfold raw1331step1 raw1331step0; decide +kernel
      have hl : raw1331step0Labels = labelEmbedding1 ∘ raw1331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1331step0 raw1331step0Labels raw1331step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1858 node1858Labels := by rfl

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

theorem canonical1416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1416 raw1416Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw1416 raw1416Labels = mixedMoment B raw1416step0 raw1416step0Labels := by
      have ha : raw1416step0 = (fun i j => raw1416 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1416step0 raw1416; decide +kernel
      have hl : raw1416step0Labels = raw1416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1416 raw1416Labels permutation32 permutation4
    mixedMoment B raw1416step0 raw1416step0Labels = mixedMoment B raw1416step1 raw1416step1Labels := by
      have ha : raw1416step1 = raw1416step0 := by apply Matrix.ext; unfold raw1416step1 raw1416step0; decide +kernel
      have hl : raw1416step0Labels = labelEmbedding7 ∘ raw1416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1416step0 raw1416step0Labels raw1416step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

theorem canonical1417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1417 raw1417Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw1417 raw1417Labels = mixedMoment B raw1417step0 raw1417step0Labels := by
      have ha : raw1417step0 = (fun i j => raw1417 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1417step0 raw1417; decide +kernel
      have hl : raw1417step0Labels = raw1417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1417 raw1417Labels permutation32 permutation4
    _ = mixedMoment B node1202 node1202Labels := by rfl

theorem canonical1418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1418 raw1418Labels = mixedMoment B node1942 node1942Labels := by
  calc
    mixedMoment B raw1418 raw1418Labels = mixedMoment B raw1418step0 raw1418step0Labels := by
      have ha : raw1418step0 = (fun i j => raw1418 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1418step0 raw1418; decide +kernel
      have hl : raw1418step0Labels = raw1418Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1418 raw1418Labels permutation149 permutation6
    mixedMoment B raw1418step0 raw1418step0Labels = mixedMoment B raw1418step1 raw1418step1Labels := by
      have ha : raw1418step1 = raw1418step0 := by apply Matrix.ext; unfold raw1418step1 raw1418step0; decide +kernel
      have hl : raw1418step0Labels = labelEmbedding1 ∘ raw1418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1418step0 raw1418step0Labels raw1418step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1942 node1942Labels := by rfl

theorem canonical1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1425 raw1425Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw1425 raw1425Labels = mixedMoment B raw1425step0 raw1425step0Labels := by
      have ha : raw1425step0 = (fun i j => raw1425 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1425step0 raw1425; decide +kernel
      have hl : raw1425step0Labels = raw1425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1425 raw1425Labels permutation32 permutation4
    mixedMoment B raw1425step0 raw1425step0Labels = mixedMoment B raw1425step1 raw1425step1Labels := by
      have ha : raw1425step1 = raw1425step0 := by apply Matrix.ext; unfold raw1425step1 raw1425step0; decide +kernel
      have hl : raw1425step0Labels = labelEmbedding7 ∘ raw1425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1425step0 raw1425step0Labels raw1425step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical1426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1426 raw1426Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw1426 raw1426Labels = mixedMoment B raw1426step0 raw1426step0Labels := by
      have ha : raw1426step0 = (fun i j => raw1426 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1426step0 raw1426; decide +kernel
      have hl : raw1426step0Labels = raw1426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1426 raw1426Labels permutation32 permutation4
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical1427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1427 raw1427Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw1427 raw1427Labels = mixedMoment B raw1427step0 raw1427step0Labels := by
      have ha : raw1427step0 = (fun i j => raw1427 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1427step0 raw1427; decide +kernel
      have hl : raw1427step0Labels = raw1427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1427 raw1427Labels permutation32 permutation6
    mixedMoment B raw1427step0 raw1427step0Labels = mixedMoment B raw1427step1 raw1427step1Labels := by
      have ha : raw1427step1 = -raw1427step0 := by apply Matrix.ext; change ∀ i j, raw1427step1 i j = -(raw1427step0 i j); unfold raw1427step1 raw1427step0; decide +kernel
      have hl : raw1427step1Labels = raw1427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1427step1 raw1427step1Labels = mixedMoment B raw1427step2 raw1427step2Labels := by
      have ha : raw1427step2 = raw1427step1 := by apply Matrix.ext; unfold raw1427step2 raw1427step1; decide +kernel
      have hl : raw1427step1Labels = labelEmbedding1 ∘ raw1427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1427step1 raw1427step1Labels raw1427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

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

theorem canonical1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1437 raw1437Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw1437 raw1437Labels = mixedMoment B raw1437step0 raw1437step0Labels := by
      have ha : raw1437step0 = (fun i j => raw1437 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1437step0 raw1437; decide +kernel
      have hl : raw1437step0Labels = raw1437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1437 raw1437Labels permutation8 permutation4
    mixedMoment B raw1437step0 raw1437step0Labels = mixedMoment B raw1437step1 raw1437step1Labels := by
      have ha : raw1437step1 = raw1437step0 := by apply Matrix.ext; unfold raw1437step1 raw1437step0; decide +kernel
      have hl : raw1437step0Labels = labelEmbedding7 ∘ raw1437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1437step0 raw1437step0Labels raw1437step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1438 raw1438Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw1438 raw1438Labels = mixedMoment B raw1438step0 raw1438step0Labels := by
      have ha : raw1438step0 = (fun i j => raw1438 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1438step0 raw1438; decide +kernel
      have hl : raw1438step0Labels = raw1438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1438 raw1438Labels permutation8 permutation4
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical1439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1439 raw1439Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw1439 raw1439Labels = mixedMoment B raw1439step0 raw1439step0Labels := by
      have ha : raw1439step0 = (fun i j => raw1439 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1439step0 raw1439; decide +kernel
      have hl : raw1439step0Labels = raw1439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1439 raw1439Labels permutation8 permutation6
    mixedMoment B raw1439step0 raw1439step0Labels = mixedMoment B raw1439step1 raw1439step1Labels := by
      have ha : raw1439step1 = -raw1439step0 := by apply Matrix.ext; change ∀ i j, raw1439step1 i j = -(raw1439step0 i j); unfold raw1439step1 raw1439step0; decide +kernel
      have hl : raw1439step1Labels = raw1439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1439step1 raw1439step1Labels = mixedMoment B raw1439step2 raw1439step2Labels := by
      have ha : raw1439step2 = raw1439step1 := by apply Matrix.ext; unfold raw1439step2 raw1439step1; decide +kernel
      have hl : raw1439step1Labels = labelEmbedding1 ∘ raw1439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1439step1 raw1439step1Labels raw1439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical1452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1452 raw1452Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw1452 raw1452Labels = mixedMoment B raw1452step0 raw1452step0Labels := by
      have ha : raw1452step0 = (fun i j => raw1452 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1452step0 raw1452; decide +kernel
      have hl : raw1452step0Labels = raw1452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1452 raw1452Labels permutation8 permutation4
    mixedMoment B raw1452step0 raw1452step0Labels = mixedMoment B raw1452step1 raw1452step1Labels := by
      have ha : raw1452step1 = raw1452step0 := by apply Matrix.ext; unfold raw1452step1 raw1452step0; decide +kernel
      have hl : raw1452step0Labels = labelEmbedding7 ∘ raw1452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1452step0 raw1452step0Labels raw1452step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

theorem canonical1453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1453 raw1453Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw1453 raw1453Labels = mixedMoment B raw1453step0 raw1453step0Labels := by
      have ha : raw1453step0 = (fun i j => raw1453 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1453step0 raw1453; decide +kernel
      have hl : raw1453step0Labels = raw1453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1453 raw1453Labels permutation8 permutation4
    _ = mixedMoment B node1300 node1300Labels := by rfl

theorem canonical1454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1454 raw1454Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw1454 raw1454Labels = mixedMoment B raw1454step0 raw1454step0Labels := by
      have ha : raw1454step0 = (fun i j => raw1454 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1454step0 raw1454; decide +kernel
      have hl : raw1454step0Labels = raw1454Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1454 raw1454Labels permutation8 permutation6
    mixedMoment B raw1454step0 raw1454step0Labels = mixedMoment B raw1454step1 raw1454step1Labels := by
      have ha : raw1454step1 = -raw1454step0 := by apply Matrix.ext; change ∀ i j, raw1454step1 i j = -(raw1454step0 i j); unfold raw1454step1 raw1454step0; decide +kernel
      have hl : raw1454step1Labels = raw1454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1454step1 raw1454step1Labels = mixedMoment B raw1454step2 raw1454step2Labels := by
      have ha : raw1454step2 = raw1454step1 := by apply Matrix.ext; unfold raw1454step2 raw1454step1; decide +kernel
      have hl : raw1454step1Labels = labelEmbedding1 ∘ raw1454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1454step1 raw1454step1Labels raw1454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3308 node3308Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20930 raw20930Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw20930 raw20930Labels = mixedMoment B raw20930step0 raw20930step0Labels := by
      have hz : ∀ j, raw20930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20930step0 = (fun i j => raw20930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20930step0 raw20930; decide +kernel
      have hl : raw20930step0Labels = raw20930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20930 raw20930Labels permutation346 hz
    mixedMoment B raw20930step0 raw20930step0Labels = mixedMoment B raw20930step1 raw20930step1Labels := by
      have ha : raw20930step1 = (fun i j => raw20930step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20930step1 raw20930step0; decide +kernel
      have hl : raw20930step1Labels = raw20930step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20930step0 raw20930step0Labels permutation40 permutation3
    mixedMoment B raw20930step1 raw20930step1Labels = mixedMoment B raw20930step2 raw20930step2Labels := by
      have ha : raw20930step2 = raw20930step1 := by apply Matrix.ext; unfold raw20930step2 raw20930step1; decide +kernel
      have hl : raw20930step1Labels = labelEmbedding6 ∘ raw20930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20930step1 raw20930step1Labels raw20930step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

theorem canonical20931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20931 raw20931Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw20931 raw20931Labels = mixedMoment B raw20931step0 raw20931step0Labels := by
      have ha : raw20931step0 = (fun i j => raw20931 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20931step0 raw20931; decide +kernel
      have hl : raw20931step0Labels = raw20931Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20931 raw20931Labels permutation184 permutation3
    mixedMoment B raw20931step0 raw20931step0Labels = mixedMoment B raw20931step1 raw20931step1Labels := by
      have ha : raw20931step1 = raw20931step0 := by apply Matrix.ext; unfold raw20931step1 raw20931step0; decide +kernel
      have hl : raw20931step0Labels = labelEmbedding6 ∘ raw20931step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20931step0 raw20931step0Labels raw20931step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

theorem canonical20932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20932 raw20932Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw20932 raw20932Labels = mixedMoment B raw20932step0 raw20932step0Labels := by
      have hz : ∀ j, raw20932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20932step0 = (fun i j => raw20932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20932step0 raw20932; decide +kernel
      have hl : raw20932step0Labels = raw20932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20932 raw20932Labels permutation346 hz
    mixedMoment B raw20932step0 raw20932step0Labels = mixedMoment B raw20932step1 raw20932step1Labels := by
      have ha : raw20932step1 = (fun i j => raw20932step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20932step1 raw20932step0; decide +kernel
      have hl : raw20932step1Labels = raw20932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20932step0 raw20932step0Labels permutation40 permutation3
    mixedMoment B raw20932step1 raw20932step1Labels = mixedMoment B raw20932step2 raw20932step2Labels := by
      have ha : raw20932step2 = raw20932step1 := by apply Matrix.ext; unfold raw20932step2 raw20932step1; decide +kernel
      have hl : raw20932step1Labels = labelEmbedding6 ∘ raw20932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20932step1 raw20932step1Labels raw20932step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

theorem canonical20933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20933 raw20933Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw20933 raw20933Labels = mixedMoment B raw20933step0 raw20933step0Labels := by
      have hz : ∀ j, raw20933 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20933step0 = (fun i j => raw20933 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20933step0 raw20933; decide +kernel
      have hl : raw20933step0Labels = raw20933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20933 raw20933Labels permutation265 hz
    mixedMoment B raw20933step0 raw20933step0Labels = mixedMoment B raw20933step1 raw20933step1Labels := by
      have ha : raw20933step1 = (fun i j => raw20933step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20933step1 raw20933step0; decide +kernel
      have hl : raw20933step1Labels = raw20933step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20933step0 raw20933step0Labels permutation40 permutation3
    mixedMoment B raw20933step1 raw20933step1Labels = mixedMoment B raw20933step2 raw20933step2Labels := by
      have ha : raw20933step2 = raw20933step1 := by apply Matrix.ext; unfold raw20933step2 raw20933step1; decide +kernel
      have hl : raw20933step1Labels = labelEmbedding6 ∘ raw20933step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20933step1 raw20933step1Labels raw20933step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

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

theorem canonical20935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20935 raw20935Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw20935 raw20935Labels = mixedMoment B raw20935step0 raw20935step0Labels := by
      have hz : ∀ j, raw20935 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20935step0 = (fun i j => raw20935 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20935step0 raw20935; decide +kernel
      have hl : raw20935step0Labels = raw20935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20935 raw20935Labels permutation265 hz
    mixedMoment B raw20935step0 raw20935step0Labels = mixedMoment B raw20935step1 raw20935step1Labels := by
      have ha : raw20935step1 = (fun i j => raw20935step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20935step1 raw20935step0; decide +kernel
      have hl : raw20935step1Labels = raw20935step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20935step0 raw20935step0Labels permutation40 permutation3
    mixedMoment B raw20935step1 raw20935step1Labels = mixedMoment B raw20935step2 raw20935step2Labels := by
      have ha : raw20935step2 = raw20935step1 := by apply Matrix.ext; unfold raw20935step2 raw20935step1; decide +kernel
      have hl : raw20935step1Labels = labelEmbedding6 ∘ raw20935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20935step1 raw20935step1Labels raw20935step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

theorem canonical20936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20936 raw20936Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw20936 raw20936Labels = mixedMoment B raw20936step0 raw20936step0Labels := by
      have hz : ∀ j, raw20936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20936step0 = (fun i j => raw20936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20936step0 raw20936; decide +kernel
      have hl : raw20936step0Labels = raw20936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20936 raw20936Labels permutation346 hz
    mixedMoment B raw20936step0 raw20936step0Labels = mixedMoment B raw20936step1 raw20936step1Labels := by
      have hz : ∀ j, raw20936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20936step1 = (fun i j => raw20936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20936step1 raw20936step0; decide +kernel
      have hl : raw20936step1Labels = raw20936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20936step0 raw20936step0Labels permutation56 hz
    mixedMoment B raw20936step1 raw20936step1Labels = mixedMoment B raw20936step2 raw20936step2Labels := by
      have ha : raw20936step2 = (fun i j => raw20936step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20936step2 raw20936step1; decide +kernel
      have hl : raw20936step2Labels = raw20936step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20936step1 raw20936step1Labels permutation8 permutation3
    mixedMoment B raw20936step2 raw20936step2Labels = mixedMoment B raw20936step3 raw20936step3Labels := by
      have ha : raw20936step3 = raw20936step2 := by apply Matrix.ext; unfold raw20936step3 raw20936step2; decide +kernel
      have hl : raw20936step2Labels = labelEmbedding6 ∘ raw20936step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20936step2 raw20936step2Labels raw20936step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4174 node4174Labels := by rfl

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

theorem canonical20938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20938 raw20938Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw20938 raw20938Labels = mixedMoment B raw20938step0 raw20938step0Labels := by
      have hz : ∀ j, raw20938 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20938step0 = (fun i j => raw20938 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20938step0 raw20938; decide +kernel
      have hl : raw20938step0Labels = raw20938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20938 raw20938Labels permutation265 hz
    mixedMoment B raw20938step0 raw20938step0Labels = mixedMoment B raw20938step1 raw20938step1Labels := by
      have ha : raw20938step1 = (fun i j => raw20938step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20938step1 raw20938step0; decide +kernel
      have hl : raw20938step1Labels = raw20938step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20938step0 raw20938step0Labels permutation32 permutation3
    mixedMoment B raw20938step1 raw20938step1Labels = mixedMoment B raw20938step2 raw20938step2Labels := by
      have ha : raw20938step2 = raw20938step1 := by apply Matrix.ext; unfold raw20938step2 raw20938step1; decide +kernel
      have hl : raw20938step1Labels = labelEmbedding6 ∘ raw20938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20938step1 raw20938step1Labels raw20938step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4543 node4543Labels := by rfl

theorem canonical20939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20939 raw20939Labels = mixedMoment B node4147 node4147Labels := by
  calc
    mixedMoment B raw20939 raw20939Labels = mixedMoment B raw20939step0 raw20939step0Labels := by
      have hz : ∀ j, raw20939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20939step0 = (fun i j => raw20939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20939step0 raw20939; decide +kernel
      have hl : raw20939step0Labels = raw20939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20939 raw20939Labels permutation346 hz
    mixedMoment B raw20939step0 raw20939step0Labels = mixedMoment B raw20939step1 raw20939step1Labels := by
      have hz : ∀ j, raw20939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20939step1 = (fun i j => raw20939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20939step1 raw20939step0; decide +kernel
      have hl : raw20939step1Labels = raw20939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20939step0 raw20939step0Labels permutation56 hz
    mixedMoment B raw20939step1 raw20939step1Labels = mixedMoment B raw20939step2 raw20939step2Labels := by
      have ha : raw20939step2 = (fun i j => raw20939step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20939step2 raw20939step1; decide +kernel
      have hl : raw20939step2Labels = raw20939step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20939step1 raw20939step1Labels permutation8 permutation3
    mixedMoment B raw20939step2 raw20939step2Labels = mixedMoment B raw20939step3 raw20939step3Labels := by
      have ha : raw20939step3 = raw20939step2 := by apply Matrix.ext; unfold raw20939step3 raw20939step2; decide +kernel
      have hl : raw20939step2Labels = labelEmbedding6 ∘ raw20939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20939step2 raw20939step2Labels raw20939step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4147 node4147Labels := by rfl

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

theorem canonical20941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20941 raw20941Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw20941 raw20941Labels = mixedMoment B raw20941step0 raw20941step0Labels := by
      have hz : ∀ j, raw20941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20941step0 = (fun i j => raw20941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20941step0 raw20941; decide +kernel
      have hl : raw20941step0Labels = raw20941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20941 raw20941Labels permutation265 hz
    mixedMoment B raw20941step0 raw20941step0Labels = mixedMoment B raw20941step1 raw20941step1Labels := by
      have ha : raw20941step1 = (fun i j => raw20941step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20941step1 raw20941step0; decide +kernel
      have hl : raw20941step1Labels = raw20941step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20941step0 raw20941step0Labels permutation32 permutation3
    mixedMoment B raw20941step1 raw20941step1Labels = mixedMoment B raw20941step2 raw20941step2Labels := by
      have ha : raw20941step2 = raw20941step1 := by apply Matrix.ext; unfold raw20941step2 raw20941step1; decide +kernel
      have hl : raw20941step1Labels = labelEmbedding6 ∘ raw20941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20941step1 raw20941step1Labels raw20941step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4525 node4525Labels := by rfl

theorem canonical20942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20942 raw20942Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw20942 raw20942Labels = mixedMoment B raw20942step0 raw20942step0Labels := by
      have hz : ∀ j, raw20942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20942step0 = (fun i j => raw20942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20942step0 raw20942; decide +kernel
      have hl : raw20942step0Labels = raw20942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20942 raw20942Labels permutation346 hz
    mixedMoment B raw20942step0 raw20942step0Labels = mixedMoment B raw20942step1 raw20942step1Labels := by
      have hz : ∀ j, raw20942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20942step1 = (fun i j => raw20942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20942step1 raw20942step0; decide +kernel
      have hl : raw20942step1Labels = raw20942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20942step0 raw20942step0Labels permutation56 hz
    mixedMoment B raw20942step1 raw20942step1Labels = mixedMoment B raw20942step2 raw20942step2Labels := by
      have ha : raw20942step2 = (fun i j => raw20942step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20942step2 raw20942step1; decide +kernel
      have hl : raw20942step2Labels = raw20942step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20942step1 raw20942step1Labels permutation8 permutation3
    mixedMoment B raw20942step2 raw20942step2Labels = mixedMoment B raw20942step3 raw20942step3Labels := by
      have ha : raw20942step3 = raw20942step2 := by apply Matrix.ext; unfold raw20942step3 raw20942step2; decide +kernel
      have hl : raw20942step2Labels = labelEmbedding6 ∘ raw20942step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20942step2 raw20942step2Labels raw20942step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

theorem canonical20943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20943 raw20943Labels = mixedMoment B node4142 node4142Labels := by
  calc
    mixedMoment B raw20943 raw20943Labels = mixedMoment B raw20943step0 raw20943step0Labels := by
      have hz : ∀ j, raw20943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20943step0 = (fun i j => raw20943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20943step0 raw20943; decide +kernel
      have hl : raw20943step0Labels = raw20943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20943 raw20943Labels permutation346 hz
    mixedMoment B raw20943step0 raw20943step0Labels = mixedMoment B raw20943step1 raw20943step1Labels := by
      have hz : ∀ j, raw20943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20943step1 = (fun i j => raw20943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20943step1 raw20943step0; decide +kernel
      have hl : raw20943step1Labels = raw20943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20943step0 raw20943step0Labels permutation56 hz
    mixedMoment B raw20943step1 raw20943step1Labels = mixedMoment B raw20943step2 raw20943step2Labels := by
      have ha : raw20943step2 = (fun i j => raw20943step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20943step2 raw20943step1; decide +kernel
      have hl : raw20943step2Labels = raw20943step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20943step1 raw20943step1Labels permutation8 permutation3
    mixedMoment B raw20943step2 raw20943step2Labels = mixedMoment B raw20943step3 raw20943step3Labels := by
      have ha : raw20943step3 = raw20943step2 := by apply Matrix.ext; unfold raw20943step3 raw20943step2; decide +kernel
      have hl : raw20943step2Labels = labelEmbedding6 ∘ raw20943step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20943step2 raw20943step2Labels raw20943step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4142 node4142Labels := by rfl

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

theorem canonical20945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20945 raw20945Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw20945 raw20945Labels = mixedMoment B raw20945step0 raw20945step0Labels := by
      have hz : ∀ j, raw20945 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20945step0 = (fun i j => raw20945 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20945step0 raw20945; decide +kernel
      have hl : raw20945step0Labels = raw20945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20945 raw20945Labels permutation265 hz
    mixedMoment B raw20945step0 raw20945step0Labels = mixedMoment B raw20945step1 raw20945step1Labels := by
      have ha : raw20945step1 = (fun i j => raw20945step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20945step1 raw20945step0; decide +kernel
      have hl : raw20945step1Labels = raw20945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20945step0 raw20945step0Labels permutation151 permutation3
    mixedMoment B raw20945step1 raw20945step1Labels = mixedMoment B raw20945step2 raw20945step2Labels := by
      have ha : raw20945step2 = -raw20945step1 := by apply Matrix.ext; change ∀ i j, raw20945step2 i j = -(raw20945step1 i j); unfold raw20945step2 raw20945step1; decide +kernel
      have hl : raw20945step2Labels = raw20945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20945step2 raw20945step2Labels = mixedMoment B raw20945step3 raw20945step3Labels := by
      have ha : raw20945step3 = raw20945step2 := by apply Matrix.ext; unfold raw20945step3 raw20945step2; decide +kernel
      have hl : raw20945step2Labels = labelEmbedding6 ∘ raw20945step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20945step2 raw20945step2Labels raw20945step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4202 node4202Labels := by rfl

theorem canonical20946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20946 raw20946Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw20946 raw20946Labels = mixedMoment B raw20946step0 raw20946step0Labels := by
      have hz : ∀ j, raw20946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20946step0 = (fun i j => raw20946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20946step0 raw20946; decide +kernel
      have hl : raw20946step0Labels = raw20946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20946 raw20946Labels permutation346 hz
    mixedMoment B raw20946step0 raw20946step0Labels = mixedMoment B raw20946step1 raw20946step1Labels := by
      have hz : ∀ j, raw20946step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20946step1 = (fun i j => raw20946step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20946step1 raw20946step0; decide +kernel
      have hl : raw20946step1Labels = raw20946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20946step0 raw20946step0Labels permutation56 hz
    mixedMoment B raw20946step1 raw20946step1Labels = mixedMoment B raw20946step2 raw20946step2Labels := by
      have ha : raw20946step2 = (fun i j => raw20946step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20946step2 raw20946step1; decide +kernel
      have hl : raw20946step2Labels = raw20946step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20946step1 raw20946step1Labels permutation31 permutation3
    mixedMoment B raw20946step2 raw20946step2Labels = mixedMoment B raw20946step3 raw20946step3Labels := by
      have ha : raw20946step3 = -raw20946step2 := by apply Matrix.ext; change ∀ i j, raw20946step3 i j = -(raw20946step2 i j); unfold raw20946step3 raw20946step2; decide +kernel
      have hl : raw20946step3Labels = raw20946step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20946step3 raw20946step3Labels = mixedMoment B raw20946step4 raw20946step4Labels := by
      have ha : raw20946step4 = raw20946step3 := by apply Matrix.ext; unfold raw20946step4 raw20946step3; decide +kernel
      have hl : raw20946step3Labels = labelEmbedding6 ∘ raw20946step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20946step3 raw20946step3Labels raw20946step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4225 node4225Labels := by rfl

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

theorem canonical4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4605 raw4605Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw4605 raw4605Labels = mixedMoment B raw4605step0 raw4605step0Labels := by
      have hz : ∀ j, raw4605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4605step0 = (fun i j => raw4605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4605step0 raw4605; decide +kernel
      have hl : raw4605step0Labels = raw4605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4605 raw4605Labels permutation346 hz
    mixedMoment B raw4605step0 raw4605step0Labels = mixedMoment B raw4605step1 raw4605step1Labels := by
      have ha : raw4605step1 = (fun i j => raw4605step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4605step1 raw4605step0; decide +kernel
      have hl : raw4605step1Labels = raw4605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4605step0 raw4605step0Labels permutation40 permutation3
    mixedMoment B raw4605step1 raw4605step1Labels = mixedMoment B raw4605step2 raw4605step2Labels := by
      have ha : raw4605step2 = raw4605step1 := by apply Matrix.ext; unfold raw4605step2 raw4605step1; decide +kernel
      have hl : raw4605step1Labels = labelEmbedding6 ∘ raw4605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4605step1 raw4605step1Labels raw4605step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

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

theorem canonical4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4609 raw4609Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw4609 raw4609Labels = mixedMoment B raw4609step0 raw4609step0Labels := by
      have hz : ∀ j, raw4609 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4609step0 = (fun i j => raw4609 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4609step0 raw4609; decide +kernel
      have hl : raw4609step0Labels = raw4609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4609 raw4609Labels permutation265 hz
    mixedMoment B raw4609step0 raw4609step0Labels = mixedMoment B raw4609step1 raw4609step1Labels := by
      have ha : raw4609step1 = (fun i j => raw4609step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4609step1 raw4609step0; decide +kernel
      have hl : raw4609step1Labels = raw4609step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4609step0 raw4609step0Labels permutation40 permutation3
    mixedMoment B raw4609step1 raw4609step1Labels = mixedMoment B raw4609step2 raw4609step2Labels := by
      have ha : raw4609step2 = raw4609step1 := by apply Matrix.ext; unfold raw4609step2 raw4609step1; decide +kernel
      have hl : raw4609step1Labels = labelEmbedding6 ∘ raw4609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4609step1 raw4609step1Labels raw4609step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

theorem canonical4613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4613 raw4613Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw4613 raw4613Labels = mixedMoment B raw4613step0 raw4613step0Labels := by
      have hz : ∀ j, raw4613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4613step0 = (fun i j => raw4613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4613step0 raw4613; decide +kernel
      have hl : raw4613step0Labels = raw4613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4613 raw4613Labels permutation346 hz
    mixedMoment B raw4613step0 raw4613step0Labels = mixedMoment B raw4613step1 raw4613step1Labels := by
      have hz : ∀ j, raw4613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4613step1 = (fun i j => raw4613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4613step1 raw4613step0; decide +kernel
      have hl : raw4613step1Labels = raw4613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4613step0 raw4613step0Labels permutation56 hz
    mixedMoment B raw4613step1 raw4613step1Labels = mixedMoment B raw4613step2 raw4613step2Labels := by
      have ha : raw4613step2 = (fun i j => raw4613step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4613step2 raw4613step1; decide +kernel
      have hl : raw4613step2Labels = raw4613step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4613step1 raw4613step1Labels permutation10 permutation3
    mixedMoment B raw4613step2 raw4613step2Labels = mixedMoment B raw4613step3 raw4613step3Labels := by
      have ha : raw4613step3 = raw4613step2 := by apply Matrix.ext; unfold raw4613step3 raw4613step2; decide +kernel
      have hl : raw4613step2Labels = labelEmbedding6 ∘ raw4613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4613step2 raw4613step2Labels raw4613step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical4618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4618 raw4618Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4618 raw4618Labels = mixedMoment B raw4618step0 raw4618step0Labels := by
      have hz : ∀ j, raw4618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4618step0 = (fun i j => raw4618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4618step0 raw4618; decide +kernel
      have hl : raw4618step0Labels = raw4618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4618 raw4618Labels permutation346 hz
    mixedMoment B raw4618step0 raw4618step0Labels = mixedMoment B raw4618step1 raw4618step1Labels := by
      have ha : raw4618step1 = (fun i j => raw4618step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4618step1 raw4618step0; decide +kernel
      have hl : raw4618step1Labels = raw4618step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4618step0 raw4618step0Labels permutation151 permutation3
    mixedMoment B raw4618step1 raw4618step1Labels = mixedMoment B raw4618step2 raw4618step2Labels := by
      have ha : raw4618step2 = -raw4618step1 := by apply Matrix.ext; change ∀ i j, raw4618step2 i j = -(raw4618step1 i j); unfold raw4618step2 raw4618step1; decide +kernel
      have hl : raw4618step2Labels = raw4618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4618step2 raw4618step2Labels = mixedMoment B raw4618step3 raw4618step3Labels := by
      have ha : raw4618step3 = raw4618step2 := by apply Matrix.ext; unfold raw4618step3 raw4618step2; decide +kernel
      have hl : raw4618step2Labels = labelEmbedding6 ∘ raw4618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4618step2 raw4618step2Labels raw4618step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

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

theorem canonical4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4621 raw4621Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw4621 raw4621Labels = mixedMoment B raw4621step0 raw4621step0Labels := by
      have hz : ∀ j, raw4621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4621step0 = (fun i j => raw4621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4621step0 raw4621; decide +kernel
      have hl : raw4621step0Labels = raw4621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4621 raw4621Labels permutation346 hz
    mixedMoment B raw4621step0 raw4621step0Labels = mixedMoment B raw4621step1 raw4621step1Labels := by
      have hz : ∀ j, raw4621step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4621step1 = (fun i j => raw4621step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4621step1 raw4621step0; decide +kernel
      have hl : raw4621step1Labels = raw4621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4621step0 raw4621step0Labels permutation56 hz
    mixedMoment B raw4621step1 raw4621step1Labels = mixedMoment B raw4621step2 raw4621step2Labels := by
      have ha : raw4621step2 = (fun i j => raw4621step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4621step2 raw4621step1; decide +kernel
      have hl : raw4621step2Labels = raw4621step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4621step1 raw4621step1Labels permutation29 permutation3
    mixedMoment B raw4621step2 raw4621step2Labels = mixedMoment B raw4621step3 raw4621step3Labels := by
      have ha : raw4621step3 = -raw4621step2 := by apply Matrix.ext; change ∀ i j, raw4621step3 i j = -(raw4621step2 i j); unfold raw4621step3 raw4621step2; decide +kernel
      have hl : raw4621step3Labels = raw4621step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4621step3 raw4621step3Labels = mixedMoment B raw4621step4 raw4621step4Labels := by
      have ha : raw4621step4 = raw4621step3 := by apply Matrix.ext; unfold raw4621step4 raw4621step3; decide +kernel
      have hl : raw4621step3Labels = labelEmbedding6 ∘ raw4621step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4621step3 raw4621step3Labels raw4621step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw759 raw759Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw759 raw759Labels = mixedMoment B raw759step0 raw759step0Labels := by
      have ha : raw759step0 = (fun i j => raw759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw759step0 raw759; decide +kernel
      have hl : raw759step0Labels = raw759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw759 raw759Labels permutation32 permutation4
    mixedMoment B raw759step0 raw759step0Labels = mixedMoment B raw759step1 raw759step1Labels := by
      have ha : raw759step1 = raw759step0 := by apply Matrix.ext; unfold raw759step1 raw759step0; decide +kernel
      have hl : raw759step0Labels = labelEmbedding7 ∘ raw759step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw759step0 raw759step0Labels raw759step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

theorem canonical760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw760 raw760Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw760 raw760Labels = mixedMoment B raw760step0 raw760step0Labels := by
      have ha : raw760step0 = (fun i j => raw760 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw760step0 raw760; decide +kernel
      have hl : raw760step0Labels = raw760Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw760 raw760Labels permutation32 permutation4
    _ = mixedMoment B node568 node568Labels := by rfl

theorem canonical761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw761 raw761Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw761 raw761Labels = mixedMoment B raw761step0 raw761step0Labels := by
      have ha : raw761step0 = (fun i j => raw761 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw761step0 raw761; decide +kernel
      have hl : raw761step0Labels = raw761Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw761 raw761Labels permutation32 permutation6
    mixedMoment B raw761step0 raw761step0Labels = mixedMoment B raw761step1 raw761step1Labels := by
      have ha : raw761step1 = -raw761step0 := by apply Matrix.ext; change ∀ i j, raw761step1 i j = -(raw761step0 i j); unfold raw761step1 raw761step0; decide +kernel
      have hl : raw761step1Labels = raw761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw761step1 raw761step1Labels = mixedMoment B raw761step2 raw761step2Labels := by
      have ha : raw761step2 = raw761step1 := by apply Matrix.ext; unfold raw761step2 raw761step1; decide +kernel
      have hl : raw761step1Labels = labelEmbedding1 ∘ raw761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw761step1 raw761step1Labels raw761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

theorem canonical765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw765 raw765Labels = mixedMoment B node4142 node4142Labels := by
  calc
    mixedMoment B raw765 raw765Labels = mixedMoment B raw765step0 raw765step0Labels := by
      have ha : raw765step0 = (fun i j => raw765 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw765step0 raw765; decide +kernel
      have hl : raw765step0Labels = raw765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw765 raw765Labels permutation8 permutation4
    mixedMoment B raw765step0 raw765step0Labels = mixedMoment B raw765step1 raw765step1Labels := by
      have ha : raw765step1 = raw765step0 := by apply Matrix.ext; unfold raw765step1 raw765step0; decide +kernel
      have hl : raw765step0Labels = labelEmbedding7 ∘ raw765step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw765step0 raw765step0Labels raw765step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4142 node4142Labels := by rfl

theorem canonical766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw766 raw766Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw766 raw766Labels = mixedMoment B raw766step0 raw766step0Labels := by
      have ha : raw766step0 = (fun i j => raw766 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw766step0 raw766; decide +kernel
      have hl : raw766step0Labels = raw766Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw766 raw766Labels permutation8 permutation4
    _ = mixedMoment B node570 node570Labels := by rfl

theorem canonical767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw767 raw767Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw767 raw767Labels = mixedMoment B raw767step0 raw767step0Labels := by
      have ha : raw767step0 = (fun i j => raw767 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw767step0 raw767; decide +kernel
      have hl : raw767step0Labels = raw767Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw767 raw767Labels permutation31 permutation6
    mixedMoment B raw767step0 raw767step0Labels = mixedMoment B raw767step1 raw767step1Labels := by
      have ha : raw767step1 = raw767step0 := by apply Matrix.ext; unfold raw767step1 raw767step0; decide +kernel
      have hl : raw767step0Labels = labelEmbedding1 ∘ raw767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw767step0 raw767step0Labels raw767step1Labels labelEmbedding1 hl
    _ = mixedMoment B node765 node765Labels := by rfl

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

theorem canonical780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw780 raw780Labels = mixedMoment B node4147 node4147Labels := by
  calc
    mixedMoment B raw780 raw780Labels = mixedMoment B raw780step0 raw780step0Labels := by
      have ha : raw780step0 = (fun i j => raw780 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw780step0 raw780; decide +kernel
      have hl : raw780step0Labels = raw780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw780 raw780Labels permutation8 permutation4
    mixedMoment B raw780step0 raw780step0Labels = mixedMoment B raw780step1 raw780step1Labels := by
      have ha : raw780step1 = raw780step0 := by apply Matrix.ext; unfold raw780step1 raw780step0; decide +kernel
      have hl : raw780step0Labels = labelEmbedding7 ∘ raw780step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw780step0 raw780step0Labels raw780step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4147 node4147Labels := by rfl

theorem canonical781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw781 raw781Labels = mixedMoment B node575 node575Labels := by
  calc
    mixedMoment B raw781 raw781Labels = mixedMoment B raw781step0 raw781step0Labels := by
      have ha : raw781step0 = (fun i j => raw781 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw781step0 raw781; decide +kernel
      have hl : raw781step0Labels = raw781Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw781 raw781Labels permutation8 permutation4
    _ = mixedMoment B node575 node575Labels := by rfl

theorem canonical782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw782 raw782Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw782 raw782Labels = mixedMoment B raw782step0 raw782step0Labels := by
      have ha : raw782step0 = (fun i j => raw782 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw782step0 raw782; decide +kernel
      have hl : raw782step0Labels = raw782Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw782 raw782Labels permutation8 permutation6
    mixedMoment B raw782step0 raw782step0Labels = mixedMoment B raw782step1 raw782step1Labels := by
      have ha : raw782step1 = -raw782step0 := by apply Matrix.ext; change ∀ i j, raw782step1 i j = -(raw782step0 i j); unfold raw782step1 raw782step0; decide +kernel
      have hl : raw782step1Labels = raw782step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw782step1 raw782step1Labels = mixedMoment B raw782step2 raw782step2Labels := by
      have ha : raw782step2 = raw782step1 := by apply Matrix.ext; unfold raw782step2 raw782step1; decide +kernel
      have hl : raw782step1Labels = labelEmbedding1 ∘ raw782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw782step1 raw782step1Labels raw782step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1495 node1495Labels := by rfl

theorem canonical807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw807 raw807Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw807 raw807Labels = mixedMoment B raw807step0 raw807step0Labels := by
      have ha : raw807step0 = (fun i j => raw807 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw807step0 raw807; decide +kernel
      have hl : raw807step0Labels = raw807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw807 raw807Labels permutation8 permutation4
    mixedMoment B raw807step0 raw807step0Labels = mixedMoment B raw807step1 raw807step1Labels := by
      have ha : raw807step1 = raw807step0 := by apply Matrix.ext; unfold raw807step1 raw807step0; decide +kernel
      have hl : raw807step0Labels = labelEmbedding7 ∘ raw807step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw807step0 raw807step0Labels raw807step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4174 node4174Labels := by rfl

theorem canonical808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw808 raw808Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw808 raw808Labels = mixedMoment B raw808step0 raw808step0Labels := by
      have ha : raw808step0 = (fun i j => raw808 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw808step0 raw808; decide +kernel
      have hl : raw808step0Labels = raw808Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw808 raw808Labels permutation8 permutation4
    _ = mixedMoment B node602 node602Labels := by rfl

theorem canonical809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw809 raw809Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw809 raw809Labels = mixedMoment B raw809step0 raw809step0Labels := by
      have ha : raw809step0 = (fun i j => raw809 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw809step0 raw809; decide +kernel
      have hl : raw809step0Labels = raw809Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw809 raw809Labels permutation8 permutation6
    mixedMoment B raw809step0 raw809step0Labels = mixedMoment B raw809step1 raw809step1Labels := by
      have ha : raw809step1 = -raw809step0 := by apply Matrix.ext; change ∀ i j, raw809step1 i j = -(raw809step0 i j); unfold raw809step1 raw809step0; decide +kernel
      have hl : raw809step1Labels = raw809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw809step1 raw809step1Labels = mixedMoment B raw809step2 raw809step2Labels := by
      have ha : raw809step2 = raw809step1 := by apply Matrix.ext; unfold raw809step2 raw809step1; decide +kernel
      have hl : raw809step1Labels = labelEmbedding1 ∘ raw809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw809step1 raw809step1Labels raw809step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

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

theorem canonical7968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7968 raw7968Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw7968 raw7968Labels = mixedMoment B raw7968step0 raw7968step0Labels := by
      have hz : ∀ j, raw7968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7968step0 = (fun i j => raw7968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7968step0 raw7968; decide +kernel
      have hl : raw7968step0Labels = raw7968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7968 raw7968Labels permutation346 hz
    mixedMoment B raw7968step0 raw7968step0Labels = mixedMoment B raw7968step1 raw7968step1Labels := by
      have ha : raw7968step1 = (fun i j => raw7968step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7968step1 raw7968step0; decide +kernel
      have hl : raw7968step1Labels = raw7968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7968step0 raw7968step0Labels permutation40 permutation3
    mixedMoment B raw7968step1 raw7968step1Labels = mixedMoment B raw7968step2 raw7968step2Labels := by
      have ha : raw7968step2 = raw7968step1 := by apply Matrix.ext; unfold raw7968step2 raw7968step1; decide +kernel
      have hl : raw7968step1Labels = labelEmbedding6 ∘ raw7968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7968step1 raw7968step1Labels raw7968step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical7972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7972 raw7972Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw7972 raw7972Labels = mixedMoment B raw7972step0 raw7972step0Labels := by
      have hz : ∀ j, raw7972 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7972step0 = (fun i j => raw7972 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7972step0 raw7972; decide +kernel
      have hl : raw7972step0Labels = raw7972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7972 raw7972Labels permutation265 hz
    mixedMoment B raw7972step0 raw7972step0Labels = mixedMoment B raw7972step1 raw7972step1Labels := by
      have ha : raw7972step1 = (fun i j => raw7972step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7972step1 raw7972step0; decide +kernel
      have hl : raw7972step1Labels = raw7972step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7972step0 raw7972step0Labels permutation40 permutation3
    mixedMoment B raw7972step1 raw7972step1Labels = mixedMoment B raw7972step2 raw7972step2Labels := by
      have ha : raw7972step2 = raw7972step1 := by apply Matrix.ext; unfold raw7972step2 raw7972step1; decide +kernel
      have hl : raw7972step1Labels = labelEmbedding6 ∘ raw7972step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7972step1 raw7972step1Labels raw7972step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical7976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7976 raw7976Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw7976 raw7976Labels = mixedMoment B raw7976step0 raw7976step0Labels := by
      have hz : ∀ j, raw7976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7976step0 = (fun i j => raw7976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7976step0 raw7976; decide +kernel
      have hl : raw7976step0Labels = raw7976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7976 raw7976Labels permutation346 hz
    mixedMoment B raw7976step0 raw7976step0Labels = mixedMoment B raw7976step1 raw7976step1Labels := by
      have hz : ∀ j, raw7976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7976step1 = (fun i j => raw7976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7976step1 raw7976step0; decide +kernel
      have hl : raw7976step1Labels = raw7976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7976step0 raw7976step0Labels permutation56 hz
    mixedMoment B raw7976step1 raw7976step1Labels = mixedMoment B raw7976step2 raw7976step2Labels := by
      have ha : raw7976step2 = (fun i j => raw7976step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7976step2 raw7976step1; decide +kernel
      have hl : raw7976step2Labels = raw7976step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7976step1 raw7976step1Labels permutation8 permutation3
    mixedMoment B raw7976step2 raw7976step2Labels = mixedMoment B raw7976step3 raw7976step3Labels := by
      have ha : raw7976step3 = raw7976step2 := by apply Matrix.ext; unfold raw7976step3 raw7976step2; decide +kernel
      have hl : raw7976step2Labels = labelEmbedding6 ∘ raw7976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7976step2 raw7976step2Labels raw7976step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

theorem canonical7980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7980 raw7980Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw7980 raw7980Labels = mixedMoment B raw7980step0 raw7980step0Labels := by
      have hz : ∀ j, raw7980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7980step0 = (fun i j => raw7980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7980step0 raw7980; decide +kernel
      have hl : raw7980step0Labels = raw7980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7980 raw7980Labels permutation346 hz
    mixedMoment B raw7980step0 raw7980step0Labels = mixedMoment B raw7980step1 raw7980step1Labels := by
      have hz : ∀ j, raw7980step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7980step1 = (fun i j => raw7980step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7980step1 raw7980step0; decide +kernel
      have hl : raw7980step1Labels = raw7980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7980step0 raw7980step0Labels permutation56 hz
    mixedMoment B raw7980step1 raw7980step1Labels = mixedMoment B raw7980step2 raw7980step2Labels := by
      have ha : raw7980step2 = (fun i j => raw7980step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7980step2 raw7980step1; decide +kernel
      have hl : raw7980step2Labels = raw7980step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7980step1 raw7980step1Labels permutation8 permutation3
    mixedMoment B raw7980step2 raw7980step2Labels = mixedMoment B raw7980step3 raw7980step3Labels := by
      have ha : raw7980step3 = raw7980step2 := by apply Matrix.ext; unfold raw7980step3 raw7980step2; decide +kernel
      have hl : raw7980step2Labels = labelEmbedding6 ∘ raw7980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7980step2 raw7980step2Labels raw7980step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

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

theorem canonical915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw915 raw915Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw915 raw915Labels = mixedMoment B raw915step0 raw915step0Labels := by
      have ha : raw915step0 = (fun i j => raw915 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw915step0 raw915; decide +kernel
      have hl : raw915step0Labels = raw915Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw915 raw915Labels permutation8 permutation4
    mixedMoment B raw915step0 raw915step0Labels = mixedMoment B raw915step1 raw915step1Labels := by
      have ha : raw915step1 = raw915step0 := by apply Matrix.ext; unfold raw915step1 raw915step0; decide +kernel
      have hl : raw915step0Labels = labelEmbedding7 ∘ raw915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw915step0 raw915step0Labels raw915step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4225 node4225Labels := by rfl

theorem canonical916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw916 raw916Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw916 raw916Labels = mixedMoment B raw916step0 raw916step0Labels := by
      have ha : raw916step0 = (fun i j => raw916 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw916step0 raw916; decide +kernel
      have hl : raw916step0Labels = raw916Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw916 raw916Labels permutation8 permutation4
    _ = mixedMoment B node726 node726Labels := by rfl

theorem canonical917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw917 raw917Labels = mixedMoment B node774 node774Labels := by
  calc
    mixedMoment B raw917 raw917Labels = mixedMoment B raw917step0 raw917step0Labels := by
      have ha : raw917step0 = (fun i j => raw917 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw917step0 raw917; decide +kernel
      have hl : raw917step0Labels = raw917Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw917 raw917Labels permutation8 permutation6
    mixedMoment B raw917step0 raw917step0Labels = mixedMoment B raw917step1 raw917step1Labels := by
      have ha : raw917step1 = -raw917step0 := by apply Matrix.ext; change ∀ i j, raw917step1 i j = -(raw917step0 i j); unfold raw917step1 raw917step0; decide +kernel
      have hl : raw917step1Labels = raw917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw917step1 raw917step1Labels = mixedMoment B raw917step2 raw917step2Labels := by
      have ha : raw917step2 = raw917step1 := by apply Matrix.ext; unfold raw917step2 raw917step1; decide +kernel
      have hl : raw917step1Labels = labelEmbedding1 ∘ raw917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw917step1 raw917step1Labels raw917step2Labels labelEmbedding1 hl
    _ = mixedMoment B node774 node774Labels := by rfl

theorem canonical987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw987 raw987Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw987 raw987Labels = mixedMoment B raw987step0 raw987step0Labels := by
      have ha : raw987step0 = (fun i j => raw987 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw987step0 raw987; decide +kernel
      have hl : raw987step0Labels = raw987Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw987 raw987Labels permutation8 permutation4
    mixedMoment B raw987step0 raw987step0Labels = mixedMoment B raw987step1 raw987step1Labels := by
      have ha : raw987step1 = raw987step0 := by apply Matrix.ext; unfold raw987step1 raw987step0; decide +kernel
      have hl : raw987step0Labels = labelEmbedding7 ∘ raw987step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw987step0 raw987step0Labels raw987step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

theorem canonical988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw988 raw988Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw988 raw988Labels = mixedMoment B raw988step0 raw988step0Labels := by
      have ha : raw988step0 = (fun i j => raw988 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw988step0 raw988; decide +kernel
      have hl : raw988step0Labels = raw988Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw988 raw988Labels permutation8 permutation4
    _ = mixedMoment B node791 node791Labels := by rfl

theorem canonical989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw989 raw989Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw989 raw989Labels = mixedMoment B raw989step0 raw989step0Labels := by
      have ha : raw989step0 = (fun i j => raw989 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw989step0 raw989; decide +kernel
      have hl : raw989step0Labels = raw989Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw989 raw989Labels permutation8 permutation6
    mixedMoment B raw989step0 raw989step0Labels = mixedMoment B raw989step1 raw989step1Labels := by
      have ha : raw989step1 = -raw989step0 := by apply Matrix.ext; change ∀ i j, raw989step1 i j = -(raw989step0 i j); unfold raw989step1 raw989step0; decide +kernel
      have hl : raw989step1Labels = raw989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw989step1 raw989step1Labels = mixedMoment B raw989step2 raw989step2Labels := by
      have ha : raw989step2 = raw989step1 := by apply Matrix.ext; unfold raw989step2 raw989step1; decide +kernel
      have hl : raw989step1Labels = labelEmbedding1 ∘ raw989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw989step1 raw989step1Labels raw989step2Labels labelEmbedding1 hl
    _ = mixedMoment B node849 node849Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical174 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw174 = injectiveMoment H node145 := by
  calc
    injectiveMoment H raw174 = injectiveMoment H raw174step0 := by
      have heq : raw174step0 = -raw174 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw174).symm
    injectiveMoment H raw174step0 = injectiveMoment H raw174step1 := by
      have heq : raw174step1 = (fun i j => raw174step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw174step0 permutation9 permutation8
    _ = injectiveMoment H node145 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

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

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

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

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

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

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1420 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1420 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1420 = injectiveMoment H raw1420step0 := by
      have heq : raw1420step0 = raw1420.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1420).symm
    injectiveMoment H raw1420step0 = injectiveMoment H raw1420step1 := by
      have heq : raw1420step1 = (fun i j => raw1420step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1420step0 permutation7 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

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

theorem sound145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node145 = Sparse.eval value145 (momentVector H) := by
  have heq : pivotMatrix145 = (fun u v => node145 (pivotPermutation145 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node145 = injectiveMoment H pivotMatrix145 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix145 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix145 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (0 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (1 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix145 (2 : Fin 3) = raw1420 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1420 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node145 + (injectiveMoment H (mergeFirst pivotMatrix145 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix145 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value145, value31, value52, value57, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node156 node156Labels = Sparse.eval singlePairValue156 (familyPairVector B) := by
  have hp := single_label_three B hB node156
  have hl : node156Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node156 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node156 PairSemantics.raw5169
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 2) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node156 PairSemantics.raw5204
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node156 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node156 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value145 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node156 (EqualityPatterns.family3.label 4) = PairSemantics.raw174 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node156 PairSemantics.raw174
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical174 hH).trans (PairSemantics.sound145 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue156, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value16, PairSemantics.value145, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1300 node1300Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node156 node156Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw76 singletonSmall1300
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1300) = raw76Labels := by decide +kernel
  rw [hl, canonical76 B hB] at h
  have hc0 : mixedMoment B raw76 (Fin.cases (0 : Fin 1) singletonSmall1300) =
      mixedMoment B node156 node156Labels := by
    have ha : raw76 = raw77 := by apply Matrix.ext; unfold raw76 raw77; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1300 = raw77Labels := by decide +kernel
    rw [ha, hj, canonical77 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4140 node4140Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node568 node568Labels + mixedMoment B node1489 node1489Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw759 singletonSmall4140
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4140) = raw759Labels := by decide +kernel
  rw [hl, canonical759 B hB] at h
  have hc0 : mixedMoment B raw759 (Fin.cases (0 : Fin 2) singletonSmall4140) =
      mixedMoment B node568 node568Labels := by
    have ha : raw759 = raw760 := by apply Matrix.ext; unfold raw759 raw760; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4140 = raw760Labels := by decide +kernel
    rw [ha, hj, canonical760 B hB]
  have hc1 : mixedMoment B raw759 (Fin.cases (1 : Fin 2) singletonSmall4140) =
      mixedMoment B node1489 node1489Labels := by
    have ha : raw759 = raw761 := by apply Matrix.ext; unfold raw759 raw761; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4140 = raw761Labels := by decide +kernel
    rw [ha, hj, canonical761 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4142 node4142Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node570 node570Labels + mixedMoment B node765 node765Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw765 singletonSmall4142
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4142) = raw765Labels := by decide +kernel
  rw [hl, canonical765 B hB] at h
  have hc0 : mixedMoment B raw765 (Fin.cases (0 : Fin 2) singletonSmall4142) =
      mixedMoment B node570 node570Labels := by
    have ha : raw765 = raw766 := by apply Matrix.ext; unfold raw765 raw766; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4142 = raw766Labels := by decide +kernel
    rw [ha, hj, canonical766 B hB]
  have hc1 : mixedMoment B raw765 (Fin.cases (1 : Fin 2) singletonSmall4142) =
      mixedMoment B node765 node765Labels := by
    have ha : raw765 = raw767 := by apply Matrix.ext; unfold raw765 raw767; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4142 = raw767Labels := by decide +kernel
    rw [ha, hj, canonical767 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4147 node4147Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node575 node575Labels + mixedMoment B node1495 node1495Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw780 singletonSmall4147
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4147) = raw780Labels := by decide +kernel
  rw [hl, canonical780 B hB] at h
  have hc0 : mixedMoment B raw780 (Fin.cases (0 : Fin 2) singletonSmall4147) =
      mixedMoment B node575 node575Labels := by
    have ha : raw780 = raw781 := by apply Matrix.ext; unfold raw780 raw781; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4147 = raw781Labels := by decide +kernel
    rw [ha, hj, canonical781 B hB]
  have hc1 : mixedMoment B raw780 (Fin.cases (1 : Fin 2) singletonSmall4147) =
      mixedMoment B node1495 node1495Labels := by
    have ha : raw780 = raw782 := by apply Matrix.ext; unfold raw780 raw782; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4147 = raw782Labels := by decide +kernel
    rw [ha, hj, canonical782 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem singleton4174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4174 node4174Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node602 node602Labels + mixedMoment B node1509 node1509Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw807 singletonSmall4174
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4174) = raw807Labels := by decide +kernel
  rw [hl, canonical807 B hB] at h
  have hc0 : mixedMoment B raw807 (Fin.cases (0 : Fin 2) singletonSmall4174) =
      mixedMoment B node602 node602Labels := by
    have ha : raw807 = raw808 := by apply Matrix.ext; unfold raw807 raw808; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4174 = raw808Labels := by decide +kernel
    rw [ha, hj, canonical808 B hB]
  have hc1 : mixedMoment B raw807 (Fin.cases (1 : Fin 2) singletonSmall4174) =
      mixedMoment B node1509 node1509Labels := by
    have ha : raw807 = raw809 := by apply Matrix.ext; unfold raw807 raw809; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4174 = raw809Labels := by decide +kernel
    rw [ha, hj, canonical809 B hB]
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

theorem singleton4225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4225 node4225Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node726 node726Labels + mixedMoment B node774 node774Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw915 singletonSmall4225
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4225) = raw915Labels := by decide +kernel
  rw [hl, canonical915 B hB] at h
  have hc0 : mixedMoment B raw915 (Fin.cases (0 : Fin 2) singletonSmall4225) =
      mixedMoment B node726 node726Labels := by
    have ha : raw915 = raw916 := by apply Matrix.ext; unfold raw915 raw916; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4225 = raw916Labels := by decide +kernel
    rw [ha, hj, canonical916 B hB]
  have hc1 : mixedMoment B raw915 (Fin.cases (1 : Fin 2) singletonSmall4225) =
      mixedMoment B node774 node774Labels := by
    have ha : raw915 = raw917 := by apply Matrix.ext; unfold raw915 raw917; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4225 = raw917Labels := by decide +kernel
    rw [ha, hj, canonical917 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4257 node4257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node791 node791Labels + mixedMoment B node849 node849Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw987 singletonSmall4257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4257) = raw987Labels := by decide +kernel
  rw [hl, canonical987 B hB] at h
  have hc0 : mixedMoment B raw987 (Fin.cases (0 : Fin 2) singletonSmall4257) =
      mixedMoment B node791 node791Labels := by
    have ha : raw987 = raw988 := by apply Matrix.ext; unfold raw987 raw988; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4257 = raw988Labels := by decide +kernel
    rw [ha, hj, canonical988 B hB]
  have hc1 : mixedMoment B raw987 (Fin.cases (1 : Fin 2) singletonSmall4257) =
      mixedMoment B node849 node849Labels := by
    have ha : raw987 = raw989 := by apply Matrix.ext; unfold raw987 raw989; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4257 = raw989Labels := by decide +kernel
    rw [ha, hj, canonical989 B hB]
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

theorem singleton4514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4514 node4514Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1098 node1098Labels + mixedMoment B node1894 node1894Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1314 singletonSmall4514
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4514) = raw1314Labels := by decide +kernel
  rw [hl, canonical1314 B hB] at h
  have hc0 : mixedMoment B raw1314 (Fin.cases (0 : Fin 2) singletonSmall4514) =
      mixedMoment B node1098 node1098Labels := by
    have ha : raw1314 = raw1315 := by apply Matrix.ext; unfold raw1314 raw1315; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4514 = raw1315Labels := by decide +kernel
    rw [ha, hj, canonical1315 B hB]
  have hc1 : mixedMoment B raw1314 (Fin.cases (1 : Fin 2) singletonSmall4514) =
      mixedMoment B node1894 node1894Labels := by
    have ha : raw1314 = raw1316 := by apply Matrix.ext; unfold raw1314 raw1316; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4514 = raw1316Labels := by decide +kernel
    rw [ha, hj, canonical1316 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4519 node4519Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1103 node1103Labels + mixedMoment B node1858 node1858Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1329 singletonSmall4519
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4519) = raw1329Labels := by decide +kernel
  rw [hl, canonical1329 B hB] at h
  have hc0 : mixedMoment B raw1329 (Fin.cases (0 : Fin 2) singletonSmall4519) =
      mixedMoment B node1103 node1103Labels := by
    have ha : raw1329 = raw1330 := by apply Matrix.ext; unfold raw1329 raw1330; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4519 = raw1330Labels := by decide +kernel
    rw [ha, hj, canonical1330 B hB]
  have hc1 : mixedMoment B raw1329 (Fin.cases (1 : Fin 2) singletonSmall4519) =
      mixedMoment B node1858 node1858Labels := by
    have ha : raw1329 = raw1331 := by apply Matrix.ext; unfold raw1329 raw1331; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4519 = raw1331Labels := by decide +kernel
    rw [ha, hj, canonical1331 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4583 node4583Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1202 node1202Labels + mixedMoment B node1942 node1942Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1416 singletonSmall4583
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4583) = raw1416Labels := by decide +kernel
  rw [hl, canonical1416 B hB] at h
  have hc0 : mixedMoment B raw1416 (Fin.cases (0 : Fin 2) singletonSmall4583) =
      mixedMoment B node1202 node1202Labels := by
    have ha : raw1416 = raw1417 := by apply Matrix.ext; unfold raw1416 raw1417; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4583 = raw1417Labels := by decide +kernel
    rw [ha, hj, canonical1417 B hB]
  have hc1 : mixedMoment B raw1416 (Fin.cases (1 : Fin 2) singletonSmall4583) =
      mixedMoment B node1942 node1942Labels := by
    have ha : raw1416 = raw1418 := by apply Matrix.ext; unfold raw1416 raw1418; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4583 = raw1418Labels := by decide +kernel
    rw [ha, hj, canonical1418 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4602 node4602Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1236 node1236Labels + mixedMoment B node3293 node3293Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1425 singletonSmall4602
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4602) = raw1425Labels := by decide +kernel
  rw [hl, canonical1425 B hB] at h
  have hc0 : mixedMoment B raw1425 (Fin.cases (0 : Fin 2) singletonSmall4602) =
      mixedMoment B node1236 node1236Labels := by
    have ha : raw1425 = raw1426 := by apply Matrix.ext; unfold raw1425 raw1426; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4602 = raw1426Labels := by decide +kernel
    rw [ha, hj, canonical1426 B hB]
  have hc1 : mixedMoment B raw1425 (Fin.cases (1 : Fin 2) singletonSmall4602) =
      mixedMoment B node3293 node3293Labels := by
    have ha : raw1425 = raw1427 := by apply Matrix.ext; unfold raw1425 raw1427; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4602 = raw1427Labels := by decide +kernel
    rw [ha, hj, canonical1427 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4612 node4612Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1246 node1246Labels + mixedMoment B node3301 node3301Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1437 singletonSmall4612
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4612) = raw1437Labels := by decide +kernel
  rw [hl, canonical1437 B hB] at h
  have hc0 : mixedMoment B raw1437 (Fin.cases (0 : Fin 2) singletonSmall4612) =
      mixedMoment B node1246 node1246Labels := by
    have ha : raw1437 = raw1438 := by apply Matrix.ext; unfold raw1437 raw1438; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4612 = raw1438Labels := by decide +kernel
    rw [ha, hj, canonical1438 B hB]
  have hc1 : mixedMoment B raw1437 (Fin.cases (1 : Fin 2) singletonSmall4612) =
      mixedMoment B node3301 node3301Labels := by
    have ha : raw1437 = raw1439 := by apply Matrix.ext; unfold raw1437 raw1439; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4612 = raw1439Labels := by decide +kernel
    rw [ha, hj, canonical1439 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4623 node4623Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1300 node1300Labels + mixedMoment B node3308 node3308Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1452 singletonSmall4623
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4623) = raw1452Labels := by decide +kernel
  rw [hl, canonical1452 B hB] at h
  have hc0 : mixedMoment B raw1452 (Fin.cases (0 : Fin 2) singletonSmall4623) =
      mixedMoment B node1300 node1300Labels := by
    have ha : raw1452 = raw1453 := by apply Matrix.ext; unfold raw1452 raw1453; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4623 = raw1453Labels := by decide +kernel
    rw [ha, hj, canonical1453 B hB]
  have hc1 : mixedMoment B raw1452 (Fin.cases (1 : Fin 2) singletonSmall4623) =
      mixedMoment B node3308 node3308Labels := by
    have ha : raw1452 = raw1454 := by apply Matrix.ext; unfold raw1452 raw1454; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4623 = raw1454Labels := by decide +kernel
    rw [ha, hj, canonical1454 B hB]
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

theorem sound726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node726 node726Labels = Sparse.eval nodeValue726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 726) = mixedMoment B node726 node726Labels := rfl
  simpa [nodeValue726, Sparse.eval] using hc.symm

theorem sound762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node762 node762Labels = Sparse.eval nodeValue762 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 762) = mixedMoment B node762 node762Labels := rfl
  simpa [nodeValue762, Sparse.eval] using hc.symm

theorem sound765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node765 node765Labels = Sparse.eval nodeValue765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 765) = mixedMoment B node765 node765Labels := rfl
  simpa [nodeValue765, Sparse.eval] using hc.symm

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

theorem sound774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node774 node774Labels = Sparse.eval nodeValue774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 774) = mixedMoment B node774 node774Labels := rfl
  simpa [nodeValue774, Sparse.eval] using hc.symm

theorem sound791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node791 node791Labels = Sparse.eval nodeValue791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 791) = mixedMoment B node791 node791Labels := rfl
  simpa [nodeValue791, Sparse.eval] using hc.symm

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

theorem sound849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node849 node849Labels = Sparse.eval nodeValue849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 849) = mixedMoment B node849 node849Labels := rfl
  simpa [nodeValue849, Sparse.eval] using hc.symm

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

theorem sound1098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1098 node1098Labels = Sparse.eval nodeValue1098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1098) = mixedMoment B node1098 node1098Labels := rfl
  simpa [nodeValue1098, Sparse.eval] using hc.symm

theorem sound1103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1103 node1103Labels = Sparse.eval nodeValue1103 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1103) = mixedMoment B node1103 node1103Labels := rfl
  simpa [nodeValue1103, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node156 node156Labels = Sparse.eval nodeValue156 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue156 (familyPairVector B) := singlePair156 B _hB
    _ = _ := by
      norm_num [singlePairValue156, nodeValue156, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1202 node1202Labels = Sparse.eval nodeValue1202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1202) = mixedMoment B node1202 node1202Labels := rfl
  simpa [nodeValue1202, Sparse.eval] using hc.symm

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

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1300 node1300Labels = Sparse.eval nodeValue1300 (mixedVector B) := by
  have h := singleton1300 B _hB
  rw [sound156 B _hB _hF] at h
  norm_num [nodeValue1300, nodeValue156, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1489 node1489Labels = Sparse.eval nodeValue1489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1489) = mixedMoment B node1489 node1489Labels := rfl
  simpa [nodeValue1489, Sparse.eval] using hc.symm

theorem sound1495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1495 node1495Labels = Sparse.eval nodeValue1495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1495) = mixedMoment B node1495 node1495Labels := rfl
  simpa [nodeValue1495, Sparse.eval] using hc.symm

theorem sound1509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1509 node1509Labels = Sparse.eval nodeValue1509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1509) = mixedMoment B node1509 node1509Labels := rfl
  simpa [nodeValue1509, Sparse.eval] using hc.symm

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

theorem sound1849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1849 node1849Labels = Sparse.eval nodeValue1849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1849) = mixedMoment B node1849 node1849Labels := rfl
  simpa [nodeValue1849, Sparse.eval] using hc.symm

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

theorem sound1858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1858 node1858Labels = Sparse.eval nodeValue1858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1858) = mixedMoment B node1858 node1858Labels := rfl
  simpa [nodeValue1858, Sparse.eval] using hc.symm

theorem sound1887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1887 node1887Labels = Sparse.eval nodeValue1887 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1887) = mixedMoment B node1887 node1887Labels := rfl
  simpa [nodeValue1887, Sparse.eval] using hc.symm

theorem sound1894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1894 node1894Labels = Sparse.eval nodeValue1894 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1894) = mixedMoment B node1894 node1894Labels := rfl
  simpa [nodeValue1894, Sparse.eval] using hc.symm

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

theorem sound1942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1942 node1942Labels = Sparse.eval nodeValue1942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1942) = mixedMoment B node1942 node1942Labels := rfl
  simpa [nodeValue1942, Sparse.eval] using hc.symm

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

theorem sound2184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2184 node2184Labels = Sparse.eval nodeValue2184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2184) = mixedMoment B node2184 node2184Labels := rfl
  simpa [nodeValue2184, Sparse.eval] using hc.symm

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

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3308 node3308Labels = Sparse.eval nodeValue3308 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3308) = mixedMoment B node3308 node3308Labels := rfl
  simpa [nodeValue3308, Sparse.eval] using hc.symm

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

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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

theorem sound568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node568 node568Labels = Sparse.eval nodeValue568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 568) = mixedMoment B node568 node568Labels := rfl
  simpa [nodeValue568, Sparse.eval] using hc.symm

theorem sound570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node570 node570Labels = Sparse.eval nodeValue570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 570) = mixedMoment B node570 node570Labels := rfl
  simpa [nodeValue570, Sparse.eval] using hc.symm

theorem sound575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node575 node575Labels = Sparse.eval nodeValue575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 575) = mixedMoment B node575 node575Labels := rfl
  simpa [nodeValue575, Sparse.eval] using hc.symm

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

theorem sound602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node602 node602Labels = Sparse.eval nodeValue602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 602) = mixedMoment B node602 node602Labels := rfl
  simpa [nodeValue602, Sparse.eval] using hc.symm

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

theorem sound4140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4140 node4140Labels = Sparse.eval nodeValue4140 (mixedVector B) := by
  have h := singleton4140 B _hB
  rw [sound568 B _hB _hF, sound1489 B _hB _hF] at h
  norm_num [nodeValue4140, nodeValue568, nodeValue1489, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4142 node4142Labels = Sparse.eval nodeValue4142 (mixedVector B) := by
  have h := singleton4142 B _hB
  rw [sound570 B _hB _hF, sound765 B _hB _hF] at h
  norm_num [nodeValue4142, nodeValue570, nodeValue765, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4147 node4147Labels = Sparse.eval nodeValue4147 (mixedVector B) := by
  have h := singleton4147 B _hB
  rw [sound575 B _hB _hF, sound1495 B _hB _hF] at h
  norm_num [nodeValue4147, nodeValue575, nodeValue1495, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4174 node4174Labels = Sparse.eval nodeValue4174 (mixedVector B) := by
  have h := singleton4174 B _hB
  rw [sound602 B _hB _hF, sound1509 B _hB _hF] at h
  norm_num [nodeValue4174, nodeValue602, nodeValue1509, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4202 node4202Labels = Sparse.eval nodeValue4202 (mixedVector B) := by
  have h := singleton4202 B _hB
  rw [sound705 B _hB _hF, sound762 B _hB _hF] at h
  norm_num [nodeValue4202, nodeValue705, nodeValue762, Sparse.eval] at h ⊢
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

theorem sound4225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4225 node4225Labels = Sparse.eval nodeValue4225 (mixedVector B) := by
  have h := singleton4225 B _hB
  rw [sound726 B _hB _hF, sound774 B _hB _hF] at h
  norm_num [nodeValue4225, nodeValue726, nodeValue774, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4257 node4257Labels = Sparse.eval nodeValue4257 (mixedVector B) := by
  have h := singleton4257 B _hB
  rw [sound791 B _hB _hF, sound849 B _hB _hF] at h
  norm_num [nodeValue4257, nodeValue791, nodeValue849, Sparse.eval] at h ⊢
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

theorem sound4514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4514 node4514Labels = Sparse.eval nodeValue4514 (mixedVector B) := by
  have h := singleton4514 B _hB
  rw [sound1098 B _hB _hF, sound1894 B _hB _hF] at h
  norm_num [nodeValue4514, nodeValue1098, nodeValue1894, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4519 node4519Labels = Sparse.eval nodeValue4519 (mixedVector B) := by
  have h := singleton4519 B _hB
  rw [sound1103 B _hB _hF, sound1858 B _hB _hF] at h
  norm_num [nodeValue4519, nodeValue1103, nodeValue1858, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4583 node4583Labels = Sparse.eval nodeValue4583 (mixedVector B) := by
  have h := singleton4583 B _hB
  rw [sound1202 B _hB _hF, sound1942 B _hB _hF] at h
  norm_num [nodeValue4583, nodeValue1202, nodeValue1942, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4623 node4623Labels = Sparse.eval nodeValue4623 (mixedVector B) := by
  have h := singleton4623 B _hB
  rw [sound1300 B _hB _hF, sound3308 B _hB _hF] at h
  norm_num [nodeValue4623, nodeValue1300, nodeValue3308, Sparse.eval] at h ⊢
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

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources40
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1303 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 1) (sourceB1303 + difference 1 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 1) (sourceB1303 + difference 1 0) sourceC1303) = raw4618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4618; decide +kernel
    rw [ha]
    exact (canonical4618 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 2) (sourceB1303 + difference 2 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 2) (sourceB1303 + difference 2 0) sourceC1303) = raw4619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4619; decide +kernel
    rw [ha]
    exact (canonical4619 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 3) (sourceB1303 + difference 3 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 3) (sourceB1303 + difference 3 0) sourceC1303) = raw4620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4620; decide +kernel
    rw [ha]
    exact (canonical4620 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 4) (sourceB1303 + difference 4 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 4) (sourceB1303 + difference 4 0) sourceC1303) = raw2686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw2686; decide +kernel
    rw [ha]
    exact (canonical2686 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1303 + difference 0 5) (sourceB1303 + difference 5 0) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1303 + difference 0 5) (sourceB1303 + difference 5 0) sourceC1303) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 0) (sourceB1303 + difference 0 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 0) (sourceB1303 + difference 0 1) sourceC1303) = raw20930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20930; decide +kernel
    rw [ha]
    exact (canonical20930 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 2) (sourceB1303 + difference 2 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 2) (sourceB1303 + difference 2 1) sourceC1303) = raw20931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20931; decide +kernel
    rw [ha]
    exact (canonical20931 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 3) (sourceB1303 + difference 3 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 3) (sourceB1303 + difference 3 1) sourceC1303) = raw20932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20932; decide +kernel
    rw [ha]
    exact (canonical20932 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 4) (sourceB1303 + difference 4 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 4) (sourceB1303 + difference 4 1) sourceC1303) = raw4605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4605; decide +kernel
    rw [ha]
    exact (canonical4605 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1303 + difference 1 5) (sourceB1303 + difference 5 1) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1303 + difference 1 5) (sourceB1303 + difference 5 1) sourceC1303) = raw7968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw7968; decide +kernel
    rw [ha]
    exact (canonical7968 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 0) (sourceB1303 + difference 0 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 0) (sourceB1303 + difference 0 2) sourceC1303) = raw20933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20933; decide +kernel
    rw [ha]
    exact (canonical20933 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 1) (sourceB1303 + difference 1 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 1) (sourceB1303 + difference 1 2) sourceC1303) = raw20934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20934; decide +kernel
    rw [ha]
    exact (canonical20934 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 3) (sourceB1303 + difference 3 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 3) (sourceB1303 + difference 3 2) sourceC1303) = raw20935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20935; decide +kernel
    rw [ha]
    exact (canonical20935 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 4) (sourceB1303 + difference 4 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 4) (sourceB1303 + difference 4 2) sourceC1303) = raw4609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4609; decide +kernel
    rw [ha]
    exact (canonical4609 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1303 + difference 2 5) (sourceB1303 + difference 5 2) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1303 + difference 2 5) (sourceB1303 + difference 5 2) sourceC1303) = raw7972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw7972; decide +kernel
    rw [ha]
    exact (canonical7972 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 0) (sourceB1303 + difference 0 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 0) (sourceB1303 + difference 0 3) sourceC1303) = raw20936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20936; decide +kernel
    rw [ha]
    exact (canonical20936 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 1) (sourceB1303 + difference 1 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 1) (sourceB1303 + difference 1 3) sourceC1303) = raw20937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20937; decide +kernel
    rw [ha]
    exact (canonical20937 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 2) (sourceB1303 + difference 2 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 2) (sourceB1303 + difference 2 3) sourceC1303) = raw20938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20938; decide +kernel
    rw [ha]
    exact (canonical20938 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 4) (sourceB1303 + difference 4 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 4) (sourceB1303 + difference 4 3) sourceC1303) = raw4613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4613; decide +kernel
    rw [ha]
    exact (canonical4613 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1303 + difference 3 5) (sourceB1303 + difference 5 3) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1303 + difference 3 5) (sourceB1303 + difference 5 3) sourceC1303) = raw7976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw7976; decide +kernel
    rw [ha]
    exact (canonical7976 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 0) (sourceB1303 + difference 0 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4147) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 0) (sourceB1303 + difference 0 4) sourceC1303) = raw20939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20939; decide +kernel
    rw [ha]
    exact (canonical20939 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 1) (sourceB1303 + difference 1 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 1) (sourceB1303 + difference 1 4) sourceC1303) = raw20940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20940; decide +kernel
    rw [ha]
    exact (canonical20940 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 2) (sourceB1303 + difference 2 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 2) (sourceB1303 + difference 2 4) sourceC1303) = raw20941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20941; decide +kernel
    rw [ha]
    exact (canonical20941 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 3) (sourceB1303 + difference 3 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4519) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 3) (sourceB1303 + difference 3 4) sourceC1303) = raw20942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20942; decide +kernel
    rw [ha]
    exact (canonical20942 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1303 + difference 4 5) (sourceB1303 + difference 5 4) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1303 + difference 4 5) (sourceB1303 + difference 5 4) sourceC1303) = raw7980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw7980; decide +kernel
    rw [ha]
    exact (canonical7980 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 0) (sourceB1303 + difference 0 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4142) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 0) (sourceB1303 + difference 0 5) sourceC1303) = raw20943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20943; decide +kernel
    rw [ha]
    exact (canonical20943 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 1) (sourceB1303 + difference 1 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 1) (sourceB1303 + difference 1 5) sourceC1303) = raw20944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20944; decide +kernel
    rw [ha]
    exact (canonical20944 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 2) (sourceB1303 + difference 2 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 2) (sourceB1303 + difference 2 5) sourceC1303) = raw20945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20945; decide +kernel
    rw [ha]
    exact (canonical20945 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 3) (sourceB1303 + difference 3 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4225) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 3) (sourceB1303 + difference 3 5) sourceC1303) = raw20946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw20946; decide +kernel
    rw [ha]
    exact (canonical20946 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1303 + difference 5 4) (sourceB1303 + difference 4 5) sourceC1303) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1303 + difference 5 4) (sourceB1303 + difference 4 5) sourceC1303) = raw4621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1303 sourceB1303 sourceC1303 difference raw4621; decide +kernel
    rw [ha]
    exact (canonical4621 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1303 sourceB1303 sourceC1303
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1303, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1130 : Integer.Sparse.reindex keyMap MixedData.row1130 = numericRow1130 := by decide +kernel

theorem numericCheck1130 (x : Master → ℝ) : Integer.Sparse.eval numericRow1130 x =
    (8640 : ℝ) * reducedSource1130 x := by
  norm_num [numericRow1130, reducedSource1130, Integer.Sparse.eval, Sparse.eval, nodeValue4140, nodeValue4142, nodeValue4147, nodeValue4174, nodeValue4202, nodeValue4225, nodeValue4257, nodeValue4514, nodeValue4519, nodeValue4521, nodeValue4525, nodeValue4543, nodeValue4583, nodeValue4602, nodeValue4605, nodeValue4612, nodeValue4623, nodeValue4807, nodeValue4843, nodeValue4890, nodeValue5294]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1130 (mixedVector B) = 0 := by
  have h4140 : mixedVector B (Sum.inr 4140) = Sparse.eval nodeValue4140 (mixedVector B) := by
    change mixedMoment B node4140 node4140Labels = _
    exact sound4140 B hB hF
  have h4142 : mixedVector B (Sum.inr 4142) = Sparse.eval nodeValue4142 (mixedVector B) := by
    change mixedMoment B node4142 node4142Labels = _
    exact sound4142 B hB hF
  have h4147 : mixedVector B (Sum.inr 4147) = Sparse.eval nodeValue4147 (mixedVector B) := by
    change mixedMoment B node4147 node4147Labels = _
    exact sound4147 B hB hF
  have h4174 : mixedVector B (Sum.inr 4174) = Sparse.eval nodeValue4174 (mixedVector B) := by
    change mixedMoment B node4174 node4174Labels = _
    exact sound4174 B hB hF
  have h4202 : mixedVector B (Sum.inr 4202) = Sparse.eval nodeValue4202 (mixedVector B) := by
    change mixedMoment B node4202 node4202Labels = _
    exact sound4202 B hB hF
  have h4225 : mixedVector B (Sum.inr 4225) = Sparse.eval nodeValue4225 (mixedVector B) := by
    change mixedMoment B node4225 node4225Labels = _
    exact sound4225 B hB hF
  have h4257 : mixedVector B (Sum.inr 4257) = Sparse.eval nodeValue4257 (mixedVector B) := by
    change mixedMoment B node4257 node4257Labels = _
    exact sound4257 B hB hF
  have h4514 : mixedVector B (Sum.inr 4514) = Sparse.eval nodeValue4514 (mixedVector B) := by
    change mixedMoment B node4514 node4514Labels = _
    exact sound4514 B hB hF
  have h4519 : mixedVector B (Sum.inr 4519) = Sparse.eval nodeValue4519 (mixedVector B) := by
    change mixedMoment B node4519 node4519Labels = _
    exact sound4519 B hB hF
  have h4521 : mixedVector B (Sum.inr 4521) = Sparse.eval nodeValue4521 (mixedVector B) := by
    change mixedMoment B node4521 node4521Labels = _
    exact sound4521 B hB hF
  have h4525 : mixedVector B (Sum.inr 4525) = Sparse.eval nodeValue4525 (mixedVector B) := by
    change mixedMoment B node4525 node4525Labels = _
    exact sound4525 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4583 : mixedVector B (Sum.inr 4583) = Sparse.eval nodeValue4583 (mixedVector B) := by
    change mixedMoment B node4583 node4583Labels = _
    exact sound4583 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1303, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4140, h4142, h4147, h4174, h4202, h4225, h4257, h4514, h4519, h4521, h4525, h4543, h4583, h4602, h4605, h4612, h4623, h4807, h4843, h4890, h5294, reducedSource1130] using sourceEq1303 B hB

theorem rowSound1130_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1130 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1130, numericCheck1130, reducedZero1130 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e_oai
