-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:18:45.637343+00:00
-- url     : https://prove2.me/submissions/d865e24c-a1ce-41b3-9e79-e164a0c2542b

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
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E105
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

theorem canonical1548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1548 raw1548Labels = mixedMoment B node4673 node4673Labels := by
  calc
    mixedMoment B raw1548 raw1548Labels = mixedMoment B raw1548step0 raw1548step0Labels := by
      have ha : raw1548step0 = (fun i j => raw1548 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1548step0 raw1548; decide +kernel
      have hl : raw1548step0Labels = raw1548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1548 raw1548Labels permutation32 permutation4
    mixedMoment B raw1548step0 raw1548step0Labels = mixedMoment B raw1548step1 raw1548step1Labels := by
      have ha : raw1548step1 = raw1548step0 := by apply Matrix.ext; unfold raw1548step1 raw1548step0; decide +kernel
      have hl : raw1548step0Labels = labelEmbedding7 ∘ raw1548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1548step0 raw1548step0Labels raw1548step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4673 node4673Labels := by rfl

theorem canonical1549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1549 raw1549Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw1549 raw1549Labels = mixedMoment B raw1549step0 raw1549step0Labels := by
      have ha : raw1549step0 = (fun i j => raw1549 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1549step0 raw1549; decide +kernel
      have hl : raw1549step0Labels = raw1549Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1549 raw1549Labels permutation32 permutation4
    _ = mixedMoment B node1799 node1799Labels := by rfl

theorem canonical1550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1550 raw1550Labels = mixedMoment B node1920 node1920Labels := by
  calc
    mixedMoment B raw1550 raw1550Labels = mixedMoment B raw1550step0 raw1550step0Labels := by
      have ha : raw1550step0 = (fun i j => raw1550 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1550step0 raw1550; decide +kernel
      have hl : raw1550step0Labels = raw1550Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1550 raw1550Labels permutation149 permutation6
    mixedMoment B raw1550step0 raw1550step0Labels = mixedMoment B raw1550step1 raw1550step1Labels := by
      have ha : raw1550step1 = raw1550step0 := by apply Matrix.ext; unfold raw1550step1 raw1550step0; decide +kernel
      have hl : raw1550step0Labels = labelEmbedding1 ∘ raw1550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1550step0 raw1550step0Labels raw1550step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1920 node1920Labels := by rfl

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

theorem canonical1581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1581 raw1581Labels = mixedMoment B node4691 node4691Labels := by
  calc
    mixedMoment B raw1581 raw1581Labels = mixedMoment B raw1581step0 raw1581step0Labels := by
      have ha : raw1581step0 = (fun i j => raw1581 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1581step0 raw1581; decide +kernel
      have hl : raw1581step0Labels = raw1581Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1581 raw1581Labels permutation8 permutation4
    mixedMoment B raw1581step0 raw1581step0Labels = mixedMoment B raw1581step1 raw1581step1Labels := by
      have ha : raw1581step1 = raw1581step0 := by apply Matrix.ext; unfold raw1581step1 raw1581step0; decide +kernel
      have hl : raw1581step0Labels = labelEmbedding7 ∘ raw1581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1581step0 raw1581step0Labels raw1581step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4691 node4691Labels := by rfl

theorem canonical1582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1582 raw1582Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw1582 raw1582Labels = mixedMoment B raw1582step0 raw1582step0Labels := by
      have ha : raw1582step0 = (fun i j => raw1582 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1582step0 raw1582; decide +kernel
      have hl : raw1582step0Labels = raw1582Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1582 raw1582Labels permutation8 permutation4
    _ = mixedMoment B node1817 node1817Labels := by rfl

theorem canonical1583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1583 raw1583Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw1583 raw1583Labels = mixedMoment B raw1583step0 raw1583step0Labels := by
      have ha : raw1583step0 = (fun i j => raw1583 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1583step0 raw1583; decide +kernel
      have hl : raw1583step0Labels = raw1583Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1583 raw1583Labels permutation31 permutation6
    mixedMoment B raw1583step0 raw1583step0Labels = mixedMoment B raw1583step1 raw1583step1Labels := by
      have ha : raw1583step1 = raw1583step0 := by apply Matrix.ext; unfold raw1583step1 raw1583step0; decide +kernel
      have hl : raw1583step0Labels = labelEmbedding1 ∘ raw1583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1583step0 raw1583step0Labels raw1583step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2159 node2159Labels := by rfl

theorem canonical1587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1587 raw1587Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw1587 raw1587Labels = mixedMoment B raw1587step0 raw1587step0Labels := by
      have ha : raw1587step0 = (fun i j => raw1587 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1587step0 raw1587; decide +kernel
      have hl : raw1587step0Labels = raw1587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1587 raw1587Labels permutation8 permutation4
    mixedMoment B raw1587step0 raw1587step0Labels = mixedMoment B raw1587step1 raw1587step1Labels := by
      have ha : raw1587step1 = raw1587step0 := by apply Matrix.ext; unfold raw1587step1 raw1587step0; decide +kernel
      have hl : raw1587step0Labels = labelEmbedding7 ∘ raw1587step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1587step0 raw1587step0Labels raw1587step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

theorem canonical1588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1588 raw1588Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw1588 raw1588Labels = mixedMoment B raw1588step0 raw1588step0Labels := by
      have ha : raw1588step0 = (fun i j => raw1588 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1588step0 raw1588; decide +kernel
      have hl : raw1588step0Labels = raw1588Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1588 raw1588Labels permutation8 permutation4
    _ = mixedMoment B node1819 node1819Labels := by rfl

theorem canonical1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1589 raw1589Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw1589 raw1589Labels = mixedMoment B raw1589step0 raw1589step0Labels := by
      have ha : raw1589step0 = (fun i j => raw1589 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1589step0 raw1589; decide +kernel
      have hl : raw1589step0Labels = raw1589Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1589 raw1589Labels permutation9 permutation6
    mixedMoment B raw1589step0 raw1589step0Labels = mixedMoment B raw1589step1 raw1589step1Labels := by
      have ha : raw1589step1 = -raw1589step0 := by apply Matrix.ext; change ∀ i j, raw1589step1 i j = -(raw1589step0 i j); unfold raw1589step1 raw1589step0; decide +kernel
      have hl : raw1589step1Labels = raw1589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1589step1 raw1589step1Labels = mixedMoment B raw1589step2 raw1589step2Labels := by
      have ha : raw1589step2 = raw1589step1 := by apply Matrix.ext; unfold raw1589step2 raw1589step1; decide +kernel
      have hl : raw1589step1Labels = labelEmbedding1 ∘ raw1589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1589step1 raw1589step1Labels raw1589step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

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

theorem canonical1638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1638 raw1638Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw1638 raw1638Labels = mixedMoment B raw1638step0 raw1638step0Labels := by
      have ha : raw1638step0 = (fun i j => raw1638 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1638step0 raw1638; decide +kernel
      have hl : raw1638step0Labels = raw1638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1638 raw1638Labels permutation32 permutation4
    mixedMoment B raw1638step0 raw1638step0Labels = mixedMoment B raw1638step1 raw1638step1Labels := by
      have ha : raw1638step1 = raw1638step0 := by apply Matrix.ext; unfold raw1638step1 raw1638step0; decide +kernel
      have hl : raw1638step0Labels = labelEmbedding7 ∘ raw1638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1638step0 raw1638step0Labels raw1638step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

theorem canonical1639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1639 raw1639Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw1639 raw1639Labels = mixedMoment B raw1639step0 raw1639step0Labels := by
      have ha : raw1639step0 = (fun i j => raw1639 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1639step0 raw1639; decide +kernel
      have hl : raw1639step0Labels = raw1639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1639 raw1639Labels permutation32 permutation4
    _ = mixedMoment B node1881 node1881Labels := by rfl

theorem canonical1640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1640 raw1640Labels = mixedMoment B node1939 node1939Labels := by
  calc
    mixedMoment B raw1640 raw1640Labels = mixedMoment B raw1640step0 raw1640step0Labels := by
      have ha : raw1640step0 = (fun i j => raw1640 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1640step0 raw1640; decide +kernel
      have hl : raw1640step0Labels = raw1640Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1640 raw1640Labels permutation33 permutation6
    mixedMoment B raw1640step0 raw1640step0Labels = mixedMoment B raw1640step1 raw1640step1Labels := by
      have ha : raw1640step1 = -raw1640step0 := by apply Matrix.ext; change ∀ i j, raw1640step1 i j = -(raw1640step0 i j); unfold raw1640step1 raw1640step0; decide +kernel
      have hl : raw1640step1Labels = raw1640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1640step1 raw1640step1Labels = mixedMoment B raw1640step2 raw1640step2Labels := by
      have ha : raw1640step2 = raw1640step1 := by apply Matrix.ext; unfold raw1640step2 raw1640step1; decide +kernel
      have hl : raw1640step1Labels = labelEmbedding1 ∘ raw1640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1640step1 raw1640step1Labels raw1640step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1939 node1939Labels := by rfl

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

theorem canonical1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1671 raw1671Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw1671 raw1671Labels = mixedMoment B raw1671step0 raw1671step0Labels := by
      have ha : raw1671step0 = (fun i j => raw1671 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1671step0 raw1671; decide +kernel
      have hl : raw1671step0Labels = raw1671Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1671 raw1671Labels permutation32 permutation4
    mixedMoment B raw1671step0 raw1671step0Labels = mixedMoment B raw1671step1 raw1671step1Labels := by
      have ha : raw1671step1 = raw1671step0 := by apply Matrix.ext; unfold raw1671step1 raw1671step0; decide +kernel
      have hl : raw1671step0Labels = labelEmbedding7 ∘ raw1671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1671step0 raw1671step0Labels raw1671step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

theorem canonical1672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1672 raw1672Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw1672 raw1672Labels = mixedMoment B raw1672step0 raw1672step0Labels := by
      have ha : raw1672step0 = (fun i j => raw1672 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1672step0 raw1672; decide +kernel
      have hl : raw1672step0Labels = raw1672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1672 raw1672Labels permutation32 permutation4
    _ = mixedMoment B node1928 node1928Labels := by rfl

theorem canonical1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1673 raw1673Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw1673 raw1673Labels = mixedMoment B raw1673step0 raw1673step0Labels := by
      have ha : raw1673step0 = (fun i j => raw1673 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1673step0 raw1673; decide +kernel
      have hl : raw1673step0Labels = raw1673Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1673 raw1673Labels permutation34 permutation6
    mixedMoment B raw1673step0 raw1673step0Labels = mixedMoment B raw1673step1 raw1673step1Labels := by
      have ha : raw1673step1 = -raw1673step0 := by apply Matrix.ext; change ∀ i j, raw1673step1 i j = -(raw1673step0 i j); unfold raw1673step1 raw1673step0; decide +kernel
      have hl : raw1673step1Labels = raw1673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1673step1 raw1673step1Labels = mixedMoment B raw1673step2 raw1673step2Labels := by
      have ha : raw1673step2 = raw1673step1 := by apply Matrix.ext; unfold raw1673step2 raw1673step1; decide +kernel
      have hl : raw1673step1Labels = labelEmbedding1 ∘ raw1673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1673step1 raw1673step1Labels raw1673step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1928 node1928Labels := by rfl

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

theorem canonical1785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1785 raw1785Labels = mixedMoment B node4862 node4862Labels := by
  calc
    mixedMoment B raw1785 raw1785Labels = mixedMoment B raw1785step0 raw1785step0Labels := by
      have ha : raw1785step0 = (fun i j => raw1785 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1785step0 raw1785; decide +kernel
      have hl : raw1785step0Labels = raw1785Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1785 raw1785Labels permutation8 permutation4
    mixedMoment B raw1785step0 raw1785step0Labels = mixedMoment B raw1785step1 raw1785step1Labels := by
      have ha : raw1785step1 = raw1785step0 := by apply Matrix.ext; unfold raw1785step1 raw1785step0; decide +kernel
      have hl : raw1785step0Labels = labelEmbedding7 ∘ raw1785step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1785step0 raw1785step0Labels raw1785step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4862 node4862Labels := by rfl

theorem canonical1786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1786 raw1786Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw1786 raw1786Labels = mixedMoment B raw1786step0 raw1786step0Labels := by
      have ha : raw1786step0 = (fun i j => raw1786 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1786step0 raw1786; decide +kernel
      have hl : raw1786step0Labels = raw1786Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1786 raw1786Labels permutation8 permutation4
    _ = mixedMoment B node2103 node2103Labels := by rfl

theorem canonical1787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1787 raw1787Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw1787 raw1787Labels = mixedMoment B raw1787step0 raw1787step0Labels := by
      have ha : raw1787step0 = (fun i j => raw1787 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1787step0 raw1787; decide +kernel
      have hl : raw1787step0Labels = raw1787Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1787 raw1787Labels permutation29 permutation6
    mixedMoment B raw1787step0 raw1787step0Labels = mixedMoment B raw1787step1 raw1787step1Labels := by
      have ha : raw1787step1 = raw1787step0 := by apply Matrix.ext; unfold raw1787step1 raw1787step0; decide +kernel
      have hl : raw1787step0Labels = labelEmbedding1 ∘ raw1787step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1787step0 raw1787step0Labels raw1787step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2103 node2103Labels := by rfl

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

theorem canonical19191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19191 raw19191Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw19191 raw19191Labels = mixedMoment B raw19191step0 raw19191step0Labels := by
      have hz : ∀ j, raw19191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19191step0 = (fun i j => raw19191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19191step0 raw19191; decide +kernel
      have hl : raw19191step0Labels = raw19191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19191 raw19191Labels permutation434 hz
    mixedMoment B raw19191step0 raw19191step0Labels = mixedMoment B raw19191step1 raw19191step1Labels := by
      have hz : ∀ j, raw19191step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19191step1 = (fun i j => raw19191step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19191step1 raw19191step0; decide +kernel
      have hl : raw19191step1Labels = raw19191step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19191step0 raw19191step0Labels permutation80 hz
    mixedMoment B raw19191step1 raw19191step1Labels = mixedMoment B raw19191step2 raw19191step2Labels := by
      have ha : raw19191step2 = (fun i j => raw19191step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19191step2 raw19191step1; decide +kernel
      have hl : raw19191step2Labels = raw19191step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19191step1 raw19191step1Labels permutation9 permutation3
    mixedMoment B raw19191step2 raw19191step2Labels = mixedMoment B raw19191step3 raw19191step3Labels := by
      have ha : raw19191step3 = raw19191step2 := by apply Matrix.ext; unfold raw19191step3 raw19191step2; decide +kernel
      have hl : raw19191step2Labels = labelEmbedding6 ∘ raw19191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19191step2 raw19191step2Labels raw19191step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

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

theorem canonical2439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2439 raw2439Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw2439 raw2439Labels = mixedMoment B raw2439step0 raw2439step0Labels := by
      have ha : raw2439step0 = (fun i j => raw2439 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2439step0 raw2439; decide +kernel
      have hl : raw2439step0Labels = raw2439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2439 raw2439Labels permutation32 permutation4
    mixedMoment B raw2439step0 raw2439step0Labels = mixedMoment B raw2439step1 raw2439step1Labels := by
      have ha : raw2439step1 = raw2439step0 := by apply Matrix.ext; unfold raw2439step1 raw2439step0; decide +kernel
      have hl : raw2439step0Labels = labelEmbedding7 ∘ raw2439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2439step0 raw2439step0Labels raw2439step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2440 raw2440Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw2440 raw2440Labels = mixedMoment B raw2440step0 raw2440step0Labels := by
      have ha : raw2440step0 = (fun i j => raw2440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2440step0 raw2440; decide +kernel
      have hl : raw2440step0Labels = raw2440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2440 raw2440Labels permutation32 permutation4
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical2441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2441 raw2441Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw2441 raw2441Labels = mixedMoment B raw2441step0 raw2441step0Labels := by
      have ha : raw2441step0 = (fun i j => raw2441 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2441step0 raw2441; decide +kernel
      have hl : raw2441step0Labels = raw2441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2441 raw2441Labels permutation149 permutation6
    mixedMoment B raw2441step0 raw2441step0Labels = mixedMoment B raw2441step1 raw2441step1Labels := by
      have ha : raw2441step1 = raw2441step0 := by apply Matrix.ext; unfold raw2441step1 raw2441step0; decide +kernel
      have hl : raw2441step0Labels = labelEmbedding1 ∘ raw2441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2441step0 raw2441step0Labels raw2441step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical2451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2451 raw2451Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw2451 raw2451Labels = mixedMoment B raw2451step0 raw2451step0Labels := by
      have ha : raw2451step0 = (fun i j => raw2451 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2451step0 raw2451; decide +kernel
      have hl : raw2451step0Labels = raw2451Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2451 raw2451Labels permutation8 permutation4
    mixedMoment B raw2451step0 raw2451step0Labels = mixedMoment B raw2451step1 raw2451step1Labels := by
      have ha : raw2451step1 = raw2451step0 := by apply Matrix.ext; unfold raw2451step1 raw2451step0; decide +kernel
      have hl : raw2451step0Labels = labelEmbedding7 ∘ raw2451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2451step0 raw2451step0Labels raw2451step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5389 node5389Labels := by rfl

theorem canonical2452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2452 raw2452Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw2452 raw2452Labels = mixedMoment B raw2452step0 raw2452step0Labels := by
      have ha : raw2452step0 = (fun i j => raw2452 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2452step0 raw2452; decide +kernel
      have hl : raw2452step0Labels = raw2452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2452 raw2452Labels permutation8 permutation4
    _ = mixedMoment B node3740 node3740Labels := by rfl

theorem canonical2453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2453 raw2453Labels = mixedMoment B node3893 node3893Labels := by
  calc
    mixedMoment B raw2453 raw2453Labels = mixedMoment B raw2453step0 raw2453step0Labels := by
      have ha : raw2453step0 = (fun i j => raw2453 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2453step0 raw2453; decide +kernel
      have hl : raw2453step0Labels = raw2453Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2453 raw2453Labels permutation24 permutation3
    mixedMoment B raw2453step0 raw2453step0Labels = mixedMoment B raw2453step1 raw2453step1Labels := by
      have ha : raw2453step1 = raw2453step0 := by apply Matrix.ext; unfold raw2453step1 raw2453step0; decide +kernel
      have hl : raw2453step0Labels = labelEmbedding1 ∘ raw2453step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2453step0 raw2453step0Labels raw2453step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3893 node3893Labels := by rfl

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

theorem canonical2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2553 raw2553Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw2553 raw2553Labels = mixedMoment B raw2553step0 raw2553step0Labels := by
      have ha : raw2553step0 = (fun i j => raw2553 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2553step0 raw2553; decide +kernel
      have hl : raw2553step0Labels = raw2553Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2553 raw2553Labels permutation8 permutation4
    mixedMoment B raw2553step0 raw2553step0Labels = mixedMoment B raw2553step1 raw2553step1Labels := by
      have ha : raw2553step1 = raw2553step0 := by apply Matrix.ext; unfold raw2553step1 raw2553step0; decide +kernel
      have hl : raw2553step0Labels = labelEmbedding7 ∘ raw2553step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2553step0 raw2553step0Labels raw2553step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

theorem canonical2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2554 raw2554Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw2554 raw2554Labels = mixedMoment B raw2554step0 raw2554step0Labels := by
      have ha : raw2554step0 = (fun i j => raw2554 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2554step0 raw2554; decide +kernel
      have hl : raw2554step0Labels = raw2554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2554 raw2554Labels permutation8 permutation4
    _ = mixedMoment B node3886 node3886Labels := by rfl

theorem canonical2555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2555 raw2555Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw2555 raw2555Labels = mixedMoment B raw2555step0 raw2555step0Labels := by
      have ha : raw2555step0 = (fun i j => raw2555 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2555step0 raw2555; decide +kernel
      have hl : raw2555step0Labels = raw2555Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2555 raw2555Labels permutation29 permutation6
    mixedMoment B raw2555step0 raw2555step0Labels = mixedMoment B raw2555step1 raw2555step1Labels := by
      have ha : raw2555step1 = raw2555step0 := by apply Matrix.ext; unfold raw2555step1 raw2555step0; decide +kernel
      have hl : raw2555step0Labels = labelEmbedding1 ∘ raw2555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2555step0 raw2555step0Labels raw2555step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3886 node3886Labels := by rfl

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

theorem canonical31009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31009 raw31009Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw31009 raw31009Labels = mixedMoment B raw31009step0 raw31009step0Labels := by
      have hz : ∀ j, raw31009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31009step0 = (fun i j => raw31009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31009step0 raw31009; decide +kernel
      have hl : raw31009step0Labels = raw31009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31009 raw31009Labels permutation434 hz
    mixedMoment B raw31009step0 raw31009step0Labels = mixedMoment B raw31009step1 raw31009step1Labels := by
      have hz : ∀ j, raw31009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31009step1 = (fun i j => raw31009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31009step1 raw31009step0; decide +kernel
      have hl : raw31009step1Labels = raw31009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31009step0 raw31009step0Labels permutation80 hz
    mixedMoment B raw31009step1 raw31009step1Labels = mixedMoment B raw31009step2 raw31009step2Labels := by
      have ha : raw31009step2 = (fun i j => raw31009step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31009step2 raw31009step1; decide +kernel
      have hl : raw31009step2Labels = raw31009step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31009step1 raw31009step1Labels permutation14 permutation2
    _ = mixedMoment B node5389 node5389Labels := by rfl

theorem canonical31010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31010 raw31010Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw31010 raw31010Labels = mixedMoment B raw31010step0 raw31010step0Labels := by
      have hz : ∀ j, raw31010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31010step0 = (fun i j => raw31010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31010step0 raw31010; decide +kernel
      have hl : raw31010step0Labels = raw31010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31010 raw31010Labels permutation434 hz
    mixedMoment B raw31010step0 raw31010step0Labels = mixedMoment B raw31010step1 raw31010step1Labels := by
      have ha : raw31010step1 = (fun i j => raw31010step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31010step1 raw31010step0; decide +kernel
      have hl : raw31010step1Labels = raw31010step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31010step0 raw31010step0Labels permutation125 permutation3
    mixedMoment B raw31010step1 raw31010step1Labels = mixedMoment B raw31010step2 raw31010step2Labels := by
      have ha : raw31010step2 = -raw31010step1 := by apply Matrix.ext; change ∀ i j, raw31010step2 i j = -(raw31010step1 i j); unfold raw31010step2 raw31010step1; decide +kernel
      have hl : raw31010step2Labels = raw31010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31010step2 raw31010step2Labels = mixedMoment B raw31010step3 raw31010step3Labels := by
      have ha : raw31010step3 = raw31010step2 := by apply Matrix.ext; unfold raw31010step3 raw31010step2; decide +kernel
      have hl : raw31010step2Labels = labelEmbedding6 ∘ raw31010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31010step2 raw31010step2Labels raw31010step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

theorem canonical31011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31011 raw31011Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw31011 raw31011Labels = mixedMoment B raw31011step0 raw31011step0Labels := by
      have hz : ∀ j, raw31011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31011step0 = (fun i j => raw31011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31011step0 raw31011; decide +kernel
      have hl : raw31011step0Labels = raw31011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31011 raw31011Labels permutation346 hz
    mixedMoment B raw31011step0 raw31011step0Labels = mixedMoment B raw31011step1 raw31011step1Labels := by
      have ha : raw31011step1 = (fun i j => raw31011step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31011step1 raw31011step0; decide +kernel
      have hl : raw31011step1Labels = raw31011step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31011step0 raw31011step0Labels permutation125 permutation3
    mixedMoment B raw31011step1 raw31011step1Labels = mixedMoment B raw31011step2 raw31011step2Labels := by
      have ha : raw31011step2 = -raw31011step1 := by apply Matrix.ext; change ∀ i j, raw31011step2 i j = -(raw31011step1 i j); unfold raw31011step2 raw31011step1; decide +kernel
      have hl : raw31011step2Labels = raw31011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31011step2 raw31011step2Labels = mixedMoment B raw31011step3 raw31011step3Labels := by
      have ha : raw31011step3 = raw31011step2 := by apply Matrix.ext; unfold raw31011step3 raw31011step2; decide +kernel
      have hl : raw31011step2Labels = labelEmbedding6 ∘ raw31011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31011step2 raw31011step2Labels raw31011step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

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

theorem canonical31013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31013 raw31013Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw31013 raw31013Labels = mixedMoment B raw31013step0 raw31013step0Labels := by
      have hz : ∀ j, raw31013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31013step0 = (fun i j => raw31013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31013step0 raw31013; decide +kernel
      have hl : raw31013step0Labels = raw31013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31013 raw31013Labels permutation434 hz
    mixedMoment B raw31013step0 raw31013step0Labels = mixedMoment B raw31013step1 raw31013step1Labels := by
      have ha : raw31013step1 = (fun i j => raw31013step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31013step1 raw31013step0; decide +kernel
      have hl : raw31013step1Labels = raw31013step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31013step0 raw31013step0Labels permutation33 permutation3
    mixedMoment B raw31013step1 raw31013step1Labels = mixedMoment B raw31013step2 raw31013step2Labels := by
      have ha : raw31013step2 = raw31013step1 := by apply Matrix.ext; unfold raw31013step2 raw31013step1; decide +kernel
      have hl : raw31013step1Labels = labelEmbedding6 ∘ raw31013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31013step1 raw31013step1Labels raw31013step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4238 node4238Labels := by rfl

theorem canonical31014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31014 raw31014Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw31014 raw31014Labels = mixedMoment B raw31014step0 raw31014step0Labels := by
      have hz : ∀ j, raw31014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31014step0 = (fun i j => raw31014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31014step0 raw31014; decide +kernel
      have hl : raw31014step0Labels = raw31014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31014 raw31014Labels permutation434 hz
    mixedMoment B raw31014step0 raw31014step0Labels = mixedMoment B raw31014step1 raw31014step1Labels := by
      have ha : raw31014step1 = (fun i j => raw31014step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31014step1 raw31014step0; decide +kernel
      have hl : raw31014step1Labels = raw31014step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31014step0 raw31014step0Labels permutation33 permutation3
    mixedMoment B raw31014step1 raw31014step1Labels = mixedMoment B raw31014step2 raw31014step2Labels := by
      have ha : raw31014step2 = raw31014step1 := by apply Matrix.ext; unfold raw31014step2 raw31014step1; decide +kernel
      have hl : raw31014step1Labels = labelEmbedding6 ∘ raw31014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31014step1 raw31014step1Labels raw31014step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

theorem canonical31015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31015 raw31015Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw31015 raw31015Labels = mixedMoment B raw31015step0 raw31015step0Labels := by
      have ha : raw31015step0 = (fun i j => raw31015 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31015step0 raw31015; decide +kernel
      have hl : raw31015step0Labels = raw31015Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31015 raw31015Labels permutation201 permutation3
    mixedMoment B raw31015step0 raw31015step0Labels = mixedMoment B raw31015step1 raw31015step1Labels := by
      have ha : raw31015step1 = raw31015step0 := by apply Matrix.ext; unfold raw31015step1 raw31015step0; decide +kernel
      have hl : raw31015step0Labels = labelEmbedding6 ∘ raw31015step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31015step0 raw31015step0Labels raw31015step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

theorem canonical31016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31016 raw31016Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw31016 raw31016Labels = mixedMoment B raw31016step0 raw31016step0Labels := by
      have hz : ∀ j, raw31016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31016step0 = (fun i j => raw31016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31016step0 raw31016; decide +kernel
      have hl : raw31016step0Labels = raw31016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31016 raw31016Labels permutation434 hz
    mixedMoment B raw31016step0 raw31016step0Labels = mixedMoment B raw31016step1 raw31016step1Labels := by
      have ha : raw31016step1 = (fun i j => raw31016step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31016step1 raw31016step0; decide +kernel
      have hl : raw31016step1Labels = raw31016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31016step0 raw31016step0Labels permutation36 permutation3
    mixedMoment B raw31016step1 raw31016step1Labels = mixedMoment B raw31016step2 raw31016step2Labels := by
      have ha : raw31016step2 = raw31016step1 := by apply Matrix.ext; unfold raw31016step2 raw31016step1; decide +kernel
      have hl : raw31016step1Labels = labelEmbedding6 ∘ raw31016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31016step1 raw31016step1Labels raw31016step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

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

theorem canonical31020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31020 raw31020Labels = mixedMoment B node4241 node4241Labels := by
  calc
    mixedMoment B raw31020 raw31020Labels = mixedMoment B raw31020step0 raw31020step0Labels := by
      have hz : ∀ j, raw31020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31020step0 = (fun i j => raw31020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31020step0 raw31020; decide +kernel
      have hl : raw31020step0Labels = raw31020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31020 raw31020Labels permutation434 hz
    mixedMoment B raw31020step0 raw31020step0Labels = mixedMoment B raw31020step1 raw31020step1Labels := by
      have hz : ∀ j, raw31020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31020step1 = (fun i j => raw31020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31020step1 raw31020step0; decide +kernel
      have hl : raw31020step1Labels = raw31020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31020step0 raw31020step0Labels permutation80 hz
    mixedMoment B raw31020step1 raw31020step1Labels = mixedMoment B raw31020step2 raw31020step2Labels := by
      have ha : raw31020step2 = (fun i j => raw31020step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31020step2 raw31020step1; decide +kernel
      have hl : raw31020step2Labels = raw31020step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31020step1 raw31020step1Labels permutation9 permutation3
    mixedMoment B raw31020step2 raw31020step2Labels = mixedMoment B raw31020step3 raw31020step3Labels := by
      have ha : raw31020step3 = raw31020step2 := by apply Matrix.ext; unfold raw31020step3 raw31020step2; decide +kernel
      have hl : raw31020step2Labels = labelEmbedding6 ∘ raw31020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31020step2 raw31020step2Labels raw31020step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4241 node4241Labels := by rfl

theorem canonical31021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31021 raw31021Labels = mixedMoment B node4691 node4691Labels := by
  calc
    mixedMoment B raw31021 raw31021Labels = mixedMoment B raw31021step0 raw31021step0Labels := by
      have hz : ∀ j, raw31021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31021step0 = (fun i j => raw31021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31021step0 raw31021; decide +kernel
      have hl : raw31021step0Labels = raw31021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31021 raw31021Labels permutation434 hz
    mixedMoment B raw31021step0 raw31021step0Labels = mixedMoment B raw31021step1 raw31021step1Labels := by
      have hz : ∀ j, raw31021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31021step1 = (fun i j => raw31021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31021step1 raw31021step0; decide +kernel
      have hl : raw31021step1Labels = raw31021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31021step0 raw31021step0Labels permutation80 hz
    mixedMoment B raw31021step1 raw31021step1Labels = mixedMoment B raw31021step2 raw31021step2Labels := by
      have ha : raw31021step2 = (fun i j => raw31021step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31021step2 raw31021step1; decide +kernel
      have hl : raw31021step2Labels = raw31021step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31021step1 raw31021step1Labels permutation9 permutation3
    mixedMoment B raw31021step2 raw31021step2Labels = mixedMoment B raw31021step3 raw31021step3Labels := by
      have ha : raw31021step3 = raw31021step2 := by apply Matrix.ext; unfold raw31021step3 raw31021step2; decide +kernel
      have hl : raw31021step2Labels = labelEmbedding6 ∘ raw31021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31021step2 raw31021step2Labels raw31021step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4691 node4691Labels := by rfl

theorem canonical31022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31022 raw31022Labels = mixedMoment B node4673 node4673Labels := by
  calc
    mixedMoment B raw31022 raw31022Labels = mixedMoment B raw31022step0 raw31022step0Labels := by
      have hz : ∀ j, raw31022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31022step0 = (fun i j => raw31022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31022step0 raw31022; decide +kernel
      have hl : raw31022step0Labels = raw31022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31022 raw31022Labels permutation434 hz
    mixedMoment B raw31022step0 raw31022step0Labels = mixedMoment B raw31022step1 raw31022step1Labels := by
      have ha : raw31022step1 = (fun i j => raw31022step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31022step1 raw31022step0; decide +kernel
      have hl : raw31022step1Labels = raw31022step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31022step0 raw31022step0Labels permutation125 permutation3
    mixedMoment B raw31022step1 raw31022step1Labels = mixedMoment B raw31022step2 raw31022step2Labels := by
      have ha : raw31022step2 = -raw31022step1 := by apply Matrix.ext; change ∀ i j, raw31022step2 i j = -(raw31022step1 i j); unfold raw31022step2 raw31022step1; decide +kernel
      have hl : raw31022step2Labels = raw31022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31022step2 raw31022step2Labels = mixedMoment B raw31022step3 raw31022step3Labels := by
      have ha : raw31022step3 = raw31022step2 := by apply Matrix.ext; unfold raw31022step3 raw31022step2; decide +kernel
      have hl : raw31022step2Labels = labelEmbedding6 ∘ raw31022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31022step2 raw31022step2Labels raw31022step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4673 node4673Labels := by rfl

theorem canonical31023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31023 raw31023Labels = mixedMoment B node4673 node4673Labels := by
  calc
    mixedMoment B raw31023 raw31023Labels = mixedMoment B raw31023step0 raw31023step0Labels := by
      have hz : ∀ j, raw31023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31023step0 = (fun i j => raw31023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31023step0 raw31023; decide +kernel
      have hl : raw31023step0Labels = raw31023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31023 raw31023Labels permutation346 hz
    mixedMoment B raw31023step0 raw31023step0Labels = mixedMoment B raw31023step1 raw31023step1Labels := by
      have ha : raw31023step1 = (fun i j => raw31023step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31023step1 raw31023step0; decide +kernel
      have hl : raw31023step1Labels = raw31023step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31023step0 raw31023step0Labels permutation125 permutation3
    mixedMoment B raw31023step1 raw31023step1Labels = mixedMoment B raw31023step2 raw31023step2Labels := by
      have ha : raw31023step2 = -raw31023step1 := by apply Matrix.ext; change ∀ i j, raw31023step2 i j = -(raw31023step1 i j); unfold raw31023step2 raw31023step1; decide +kernel
      have hl : raw31023step2Labels = raw31023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31023step2 raw31023step2Labels = mixedMoment B raw31023step3 raw31023step3Labels := by
      have ha : raw31023step3 = raw31023step2 := by apply Matrix.ext; unfold raw31023step3 raw31023step2; decide +kernel
      have hl : raw31023step2Labels = labelEmbedding6 ∘ raw31023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31023step2 raw31023step2Labels raw31023step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4673 node4673Labels := by rfl

theorem canonical31024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31024 raw31024Labels = mixedMoment B node4862 node4862Labels := by
  calc
    mixedMoment B raw31024 raw31024Labels = mixedMoment B raw31024step0 raw31024step0Labels := by
      have hz : ∀ j, raw31024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31024step0 = (fun i j => raw31024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31024step0 raw31024; decide +kernel
      have hl : raw31024step0Labels = raw31024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31024 raw31024Labels permutation434 hz
    mixedMoment B raw31024step0 raw31024step0Labels = mixedMoment B raw31024step1 raw31024step1Labels := by
      have hz : ∀ j, raw31024step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31024step1 = (fun i j => raw31024step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31024step1 raw31024step0; decide +kernel
      have hl : raw31024step1Labels = raw31024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31024step0 raw31024step0Labels permutation80 hz
    mixedMoment B raw31024step1 raw31024step1Labels = mixedMoment B raw31024step2 raw31024step2Labels := by
      have ha : raw31024step2 = (fun i j => raw31024step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31024step2 raw31024step1; decide +kernel
      have hl : raw31024step2Labels = raw31024step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31024step1 raw31024step1Labels permutation9 permutation3
    mixedMoment B raw31024step2 raw31024step2Labels = mixedMoment B raw31024step3 raw31024step3Labels := by
      have ha : raw31024step3 = raw31024step2 := by apply Matrix.ext; unfold raw31024step3 raw31024step2; decide +kernel
      have hl : raw31024step2Labels = labelEmbedding6 ∘ raw31024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31024step2 raw31024step2Labels raw31024step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4862 node4862Labels := by rfl

theorem canonical31025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31025 raw31025Labels = mixedMoment B node4243 node4243Labels := by
  calc
    mixedMoment B raw31025 raw31025Labels = mixedMoment B raw31025step0 raw31025step0Labels := by
      have hz : ∀ j, raw31025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31025step0 = (fun i j => raw31025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31025step0 raw31025; decide +kernel
      have hl : raw31025step0Labels = raw31025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31025 raw31025Labels permutation434 hz
    mixedMoment B raw31025step0 raw31025step0Labels = mixedMoment B raw31025step1 raw31025step1Labels := by
      have hz : ∀ j, raw31025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31025step1 = (fun i j => raw31025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31025step1 raw31025step0; decide +kernel
      have hl : raw31025step1Labels = raw31025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31025step0 raw31025step0Labels permutation80 hz
    mixedMoment B raw31025step1 raw31025step1Labels = mixedMoment B raw31025step2 raw31025step2Labels := by
      have ha : raw31025step2 = (fun i j => raw31025step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31025step2 raw31025step1; decide +kernel
      have hl : raw31025step2Labels = raw31025step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31025step1 raw31025step1Labels permutation8 permutation3
    mixedMoment B raw31025step2 raw31025step2Labels = mixedMoment B raw31025step3 raw31025step3Labels := by
      have ha : raw31025step3 = raw31025step2 := by apply Matrix.ext; unfold raw31025step3 raw31025step2; decide +kernel
      have hl : raw31025step2Labels = labelEmbedding6 ∘ raw31025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31025step2 raw31025step2Labels raw31025step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4243 node4243Labels := by rfl

theorem canonical31026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31026 raw31026Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw31026 raw31026Labels = mixedMoment B raw31026step0 raw31026step0Labels := by
      have hz : ∀ j, raw31026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31026step0 = (fun i j => raw31026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31026step0 raw31026; decide +kernel
      have hl : raw31026step0Labels = raw31026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31026 raw31026Labels permutation434 hz
    mixedMoment B raw31026step0 raw31026step0Labels = mixedMoment B raw31026step1 raw31026step1Labels := by
      have hz : ∀ j, raw31026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31026step1 = (fun i j => raw31026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31026step1 raw31026step0; decide +kernel
      have hl : raw31026step1Labels = raw31026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31026step0 raw31026step0Labels permutation80 hz
    mixedMoment B raw31026step1 raw31026step1Labels = mixedMoment B raw31026step2 raw31026step2Labels := by
      have ha : raw31026step2 = (fun i j => raw31026step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31026step2 raw31026step1; decide +kernel
      have hl : raw31026step2Labels = raw31026step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31026step1 raw31026step1Labels permutation8 permutation3
    mixedMoment B raw31026step2 raw31026step2Labels = mixedMoment B raw31026step3 raw31026step3Labels := by
      have ha : raw31026step3 = raw31026step2 := by apply Matrix.ext; unfold raw31026step3 raw31026step2; decide +kernel
      have hl : raw31026step2Labels = labelEmbedding6 ∘ raw31026step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31026step2 raw31026step2Labels raw31026step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

theorem canonical31027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31027 raw31027Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw31027 raw31027Labels = mixedMoment B raw31027step0 raw31027step0Labels := by
      have hz : ∀ j, raw31027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31027step0 = (fun i j => raw31027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31027step0 raw31027; decide +kernel
      have hl : raw31027step0Labels = raw31027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31027 raw31027Labels permutation434 hz
    mixedMoment B raw31027step0 raw31027step0Labels = mixedMoment B raw31027step1 raw31027step1Labels := by
      have ha : raw31027step1 = (fun i j => raw31027step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31027step1 raw31027step0; decide +kernel
      have hl : raw31027step1Labels = raw31027step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31027step0 raw31027step0Labels permutation38 permutation3
    mixedMoment B raw31027step1 raw31027step1Labels = mixedMoment B raw31027step2 raw31027step2Labels := by
      have ha : raw31027step2 = raw31027step1 := by apply Matrix.ext; unfold raw31027step2 raw31027step1; decide +kernel
      have hl : raw31027step1Labels = labelEmbedding6 ∘ raw31027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31027step1 raw31027step1Labels raw31027step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

theorem canonical31028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31028 raw31028Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw31028 raw31028Labels = mixedMoment B raw31028step0 raw31028step0Labels := by
      have hz : ∀ j, raw31028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31028step0 = (fun i j => raw31028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31028step0 raw31028; decide +kernel
      have hl : raw31028step0Labels = raw31028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31028 raw31028Labels permutation346 hz
    mixedMoment B raw31028step0 raw31028step0Labels = mixedMoment B raw31028step1 raw31028step1Labels := by
      have ha : raw31028step1 = (fun i j => raw31028step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31028step1 raw31028step0; decide +kernel
      have hl : raw31028step1Labels = raw31028step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31028step0 raw31028step0Labels permutation38 permutation3
    mixedMoment B raw31028step1 raw31028step1Labels = mixedMoment B raw31028step2 raw31028step2Labels := by
      have ha : raw31028step2 = raw31028step1 := by apply Matrix.ext; unfold raw31028step2 raw31028step1; decide +kernel
      have hl : raw31028step1Labels = labelEmbedding6 ∘ raw31028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31028step1 raw31028step1Labels raw31028step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw500 raw500Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw500 raw500Labels = mixedMoment B raw500step0 raw500step0Labels := by
      have ha : raw500step0 = (fun i j => raw500 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw500step0 raw500; decide +kernel
      have hl : raw500step0Labels = raw500Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw500 raw500Labels permutation8 permutation5
    mixedMoment B raw500step0 raw500step0Labels = mixedMoment B raw500step1 raw500step1Labels := by
      have ha : raw500step1 = raw500step0 := by apply Matrix.ext; unfold raw500step1 raw500step0; decide +kernel
      have hl : raw500step0Labels = labelEmbedding1 ∘ raw500step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw500step0 raw500step0Labels raw500step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3740 node3740Labels := by rfl

theorem canonical501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw501 raw501Labels = mixedMoment B node451 node451Labels := by
  calc
    mixedMoment B raw501 raw501Labels = mixedMoment B raw501step0 raw501step0Labels := by
      have ha : raw501step0 = (fun i j => raw501 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw501step0 raw501; decide +kernel
      have hl : raw501step0Labels = raw501Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw501 raw501Labels permutation15 permutation4
    _ = mixedMoment B node451 node451Labels := by rfl

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

theorem canonical957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw957 raw957Labels = mixedMoment B node4241 node4241Labels := by
  calc
    mixedMoment B raw957 raw957Labels = mixedMoment B raw957step0 raw957step0Labels := by
      have ha : raw957step0 = (fun i j => raw957 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw957step0 raw957; decide +kernel
      have hl : raw957step0Labels = raw957Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw957 raw957Labels permutation8 permutation4
    mixedMoment B raw957step0 raw957step0Labels = mixedMoment B raw957step1 raw957step1Labels := by
      have ha : raw957step1 = raw957step0 := by apply Matrix.ext; unfold raw957step1 raw957step0; decide +kernel
      have hl : raw957step0Labels = labelEmbedding7 ∘ raw957step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw957step0 raw957step0Labels raw957step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4241 node4241Labels := by rfl

theorem canonical958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw958 raw958Labels = mixedMoment B node741 node741Labels := by
  calc
    mixedMoment B raw958 raw958Labels = mixedMoment B raw958step0 raw958step0Labels := by
      have ha : raw958step0 = (fun i j => raw958 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw958step0 raw958; decide +kernel
      have hl : raw958step0Labels = raw958Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw958 raw958Labels permutation8 permutation4
    _ = mixedMoment B node741 node741Labels := by rfl

theorem canonical959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw959 raw959Labels = mixedMoment B node820 node820Labels := by
  calc
    mixedMoment B raw959 raw959Labels = mixedMoment B raw959step0 raw959step0Labels := by
      have ha : raw959step0 = (fun i j => raw959 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw959step0 raw959; decide +kernel
      have hl : raw959step0Labels = raw959Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw959 raw959Labels permutation10 permutation6
    mixedMoment B raw959step0 raw959step0Labels = mixedMoment B raw959step1 raw959step1Labels := by
      have ha : raw959step1 = -raw959step0 := by apply Matrix.ext; change ∀ i j, raw959step1 i j = -(raw959step0 i j); unfold raw959step1 raw959step0; decide +kernel
      have hl : raw959step1Labels = raw959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw959step1 raw959step1Labels = mixedMoment B raw959step2 raw959step2Labels := by
      have ha : raw959step2 = raw959step1 := by apply Matrix.ext; unfold raw959step2 raw959step1; decide +kernel
      have hl : raw959step1Labels = labelEmbedding1 ∘ raw959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw959step1 raw959step1Labels raw959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node820 node820Labels := by rfl

theorem canonical963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw963 raw963Labels = mixedMoment B node4243 node4243Labels := by
  calc
    mixedMoment B raw963 raw963Labels = mixedMoment B raw963step0 raw963step0Labels := by
      have ha : raw963step0 = (fun i j => raw963 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw963step0 raw963; decide +kernel
      have hl : raw963step0Labels = raw963Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw963 raw963Labels permutation8 permutation4
    mixedMoment B raw963step0 raw963step0Labels = mixedMoment B raw963step1 raw963step1Labels := by
      have ha : raw963step1 = raw963step0 := by apply Matrix.ext; unfold raw963step1 raw963step0; decide +kernel
      have hl : raw963step0Labels = labelEmbedding7 ∘ raw963step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw963step0 raw963step0Labels raw963step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4243 node4243Labels := by rfl

theorem canonical964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw964 raw964Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw964 raw964Labels = mixedMoment B raw964step0 raw964step0Labels := by
      have ha : raw964step0 = (fun i j => raw964 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw964step0 raw964; decide +kernel
      have hl : raw964step0Labels = raw964Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw964 raw964Labels permutation8 permutation4
    _ = mixedMoment B node743 node743Labels := by rfl

theorem canonical965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw965 raw965Labels = mixedMoment B node844 node844Labels := by
  calc
    mixedMoment B raw965 raw965Labels = mixedMoment B raw965step0 raw965step0Labels := by
      have ha : raw965step0 = (fun i j => raw965 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw965step0 raw965; decide +kernel
      have hl : raw965step0Labels = raw965Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw965 raw965Labels permutation9 permutation6
    mixedMoment B raw965step0 raw965step0Labels = mixedMoment B raw965step1 raw965step1Labels := by
      have ha : raw965step1 = -raw965step0 := by apply Matrix.ext; change ∀ i j, raw965step1 i j = -(raw965step0 i j); unfold raw965step1 raw965step0; decide +kernel
      have hl : raw965step1Labels = raw965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw965step1 raw965step1Labels = mixedMoment B raw965step2 raw965step2Labels := by
      have ha : raw965step2 = raw965step1 := by apply Matrix.ext; unfold raw965step2 raw965step1; decide +kernel
      have hl : raw965step1Labels = labelEmbedding1 ∘ raw965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw965step1 raw965step1Labels raw965step2Labels labelEmbedding1 hl
    _ = mixedMoment B node844 node844Labels := by rfl

theorem canonical1008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1008 raw1008Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw1008 raw1008Labels = mixedMoment B raw1008step0 raw1008step0Labels := by
      have ha : raw1008step0 = (fun i j => raw1008 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1008step0 raw1008; decide +kernel
      have hl : raw1008step0Labels = raw1008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1008 raw1008Labels permutation8 permutation4
    mixedMoment B raw1008step0 raw1008step0Labels = mixedMoment B raw1008step1 raw1008step1Labels := by
      have ha : raw1008step1 = raw1008step0 := by apply Matrix.ext; unfold raw1008step1 raw1008step0; decide +kernel
      have hl : raw1008step0Labels = labelEmbedding7 ∘ raw1008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1008step0 raw1008step0Labels raw1008step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

theorem canonical1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1009 raw1009Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw1009 raw1009Labels = mixedMoment B raw1009step0 raw1009step0Labels := by
      have ha : raw1009step0 = (fun i j => raw1009 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1009step0 raw1009; decide +kernel
      have hl : raw1009step0Labels = raw1009Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1009 raw1009Labels permutation8 permutation4
    _ = mixedMoment B node830 node830Labels := by rfl

theorem canonical1010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1010 raw1010Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw1010 raw1010Labels = mixedMoment B raw1010step0 raw1010step0Labels := by
      have ha : raw1010step0 = (fun i j => raw1010 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1010step0 raw1010; decide +kernel
      have hl : raw1010step0Labels = raw1010Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1010 raw1010Labels permutation10 permutation6
    mixedMoment B raw1010step0 raw1010step0Labels = mixedMoment B raw1010step1 raw1010step1Labels := by
      have ha : raw1010step1 = -raw1010step0 := by apply Matrix.ext; change ∀ i j, raw1010step1 i j = -(raw1010step0 i j); unfold raw1010step1 raw1010step0; decide +kernel
      have hl : raw1010step1Labels = raw1010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1010step1 raw1010step1Labels = mixedMoment B raw1010step2 raw1010step2Labels := by
      have ha : raw1010step2 = raw1010step1 := by apply Matrix.ext; unfold raw1010step2 raw1010step1; decide +kernel
      have hl : raw1010step1Labels = labelEmbedding1 ∘ raw1010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1010step1 raw1010step1Labels raw1010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node830 node830Labels := by rfl

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

theorem canonical10785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10785 raw10785Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10785 raw10785Labels = mixedMoment B raw10785step0 raw10785step0Labels := by
      have hz : ∀ j, raw10785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10785step0 = (fun i j => raw10785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10785step0 raw10785; decide +kernel
      have hl : raw10785step0Labels = raw10785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10785 raw10785Labels permutation346 hz
    mixedMoment B raw10785step0 raw10785step0Labels = mixedMoment B raw10785step1 raw10785step1Labels := by
      have ha : raw10785step1 = (fun i j => raw10785step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10785step1 raw10785step0; decide +kernel
      have hl : raw10785step1Labels = raw10785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10785step0 raw10785step0Labels permutation32 permutation3
    mixedMoment B raw10785step1 raw10785step1Labels = mixedMoment B raw10785step2 raw10785step2Labels := by
      have ha : raw10785step2 = raw10785step1 := by apply Matrix.ext; unfold raw10785step2 raw10785step1; decide +kernel
      have hl : raw10785step1Labels = labelEmbedding6 ∘ raw10785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10785step1 raw10785step1Labels raw10785step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical10789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10789 raw10789Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw10789 raw10789Labels = mixedMoment B raw10789step0 raw10789step0Labels := by
      have hz : ∀ j, raw10789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10789step0 = (fun i j => raw10789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10789step0 raw10789; decide +kernel
      have hl : raw10789step0Labels = raw10789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10789 raw10789Labels permutation434 hz
    mixedMoment B raw10789step0 raw10789step0Labels = mixedMoment B raw10789step1 raw10789step1Labels := by
      have hz : ∀ j, raw10789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10789step1 = (fun i j => raw10789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10789step1 raw10789step0; decide +kernel
      have hl : raw10789step1Labels = raw10789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10789step0 raw10789step0Labels permutation80 hz
    mixedMoment B raw10789step1 raw10789step1Labels = mixedMoment B raw10789step2 raw10789step2Labels := by
      have ha : raw10789step2 = (fun i j => raw10789step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10789step2 raw10789step1; decide +kernel
      have hl : raw10789step2Labels = raw10789step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10789step1 raw10789step1Labels permutation9 permutation3
    mixedMoment B raw10789step2 raw10789step2Labels = mixedMoment B raw10789step3 raw10789step3Labels := by
      have ha : raw10789step3 = raw10789step2 := by apply Matrix.ext; unfold raw10789step3 raw10789step2; decide +kernel
      have hl : raw10789step2Labels = labelEmbedding6 ∘ raw10789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10789step2 raw10789step2Labels raw10789step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

theorem canonical10791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10791 raw10791Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw10791 raw10791Labels = mixedMoment B raw10791step0 raw10791step0Labels := by
      have hz : ∀ j, raw10791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10791step0 = (fun i j => raw10791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10791step0 raw10791; decide +kernel
      have hl : raw10791step0Labels = raw10791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10791 raw10791Labels permutation434 hz
    mixedMoment B raw10791step0 raw10791step0Labels = mixedMoment B raw10791step1 raw10791step1Labels := by
      have ha : raw10791step1 = (fun i j => raw10791step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10791step1 raw10791step0; decide +kernel
      have hl : raw10791step1Labels = raw10791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10791step0 raw10791step0Labels permutation39 permutation3
    mixedMoment B raw10791step1 raw10791step1Labels = mixedMoment B raw10791step2 raw10791step2Labels := by
      have ha : raw10791step2 = raw10791step1 := by apply Matrix.ext; unfold raw10791step2 raw10791step1; decide +kernel
      have hl : raw10791step1Labels = labelEmbedding6 ∘ raw10791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10791step1 raw10791step1Labels raw10791step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

theorem canonical10792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10792 raw10792Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw10792 raw10792Labels = mixedMoment B raw10792step0 raw10792step0Labels := by
      have hz : ∀ j, raw10792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10792step0 = (fun i j => raw10792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10792step0 raw10792; decide +kernel
      have hl : raw10792step0Labels = raw10792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10792 raw10792Labels permutation346 hz
    mixedMoment B raw10792step0 raw10792step0Labels = mixedMoment B raw10792step1 raw10792step1Labels := by
      have ha : raw10792step1 = (fun i j => raw10792step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10792step1 raw10792step0; decide +kernel
      have hl : raw10792step1Labels = raw10792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10792step0 raw10792step0Labels permutation39 permutation3
    mixedMoment B raw10792step1 raw10792step1Labels = mixedMoment B raw10792step2 raw10792step2Labels := by
      have ha : raw10792step2 = raw10792step1 := by apply Matrix.ext; unfold raw10792step2 raw10792step1; decide +kernel
      have hl : raw10792step1Labels = labelEmbedding6 ∘ raw10792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10792step1 raw10792step1Labels raw10792step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

theorem canonical10793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10793 raw10793Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw10793 raw10793Labels = mixedMoment B raw10793step0 raw10793step0Labels := by
      have hz : ∀ j, raw10793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10793step0 = (fun i j => raw10793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10793step0 raw10793; decide +kernel
      have hl : raw10793step0Labels = raw10793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10793 raw10793Labels permutation434 hz
    mixedMoment B raw10793step0 raw10793step0Labels = mixedMoment B raw10793step1 raw10793step1Labels := by
      have hz : ∀ j, raw10793step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10793step1 = (fun i j => raw10793step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10793step1 raw10793step0; decide +kernel
      have hl : raw10793step1Labels = raw10793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10793step0 raw10793step0Labels permutation80 hz
    mixedMoment B raw10793step1 raw10793step1Labels = mixedMoment B raw10793step2 raw10793step2Labels := by
      have ha : raw10793step2 = (fun i j => raw10793step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10793step2 raw10793step1; decide +kernel
      have hl : raw10793step2Labels = raw10793step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10793step1 raw10793step1Labels permutation12 permutation5
    mixedMoment B raw10793step2 raw10793step2Labels = mixedMoment B raw10793step3 raw10793step3Labels := by
      have ha : raw10793step3 = -raw10793step2 := by apply Matrix.ext; change ∀ i j, raw10793step3 i j = -(raw10793step2 i j); unfold raw10793step3 raw10793step2; decide +kernel
      have hl : raw10793step3Labels = raw10793step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10793step3 raw10793step3Labels = mixedMoment B raw10793step4 raw10793step4Labels := by
      have ha : raw10793step4 = raw10793step3 := by apply Matrix.ext; unfold raw10793step4 raw10793step3; decide +kernel
      have hl : raw10793step3Labels = labelEmbedding8 ∘ raw10793step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10793step3 raw10793step3Labels raw10793step4Labels labelEmbedding8 hl
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical3892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3892 = injectiveMoment H node197 := by
  calc
    injectiveMoment H raw3892 = injectiveMoment H raw3892step0 := by
      have heq : raw3892step0 = (fun i j => raw3892 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3892 permutation25 permutation6
    _ = injectiveMoment H node197 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5116 = injectiveMoment H node45 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8987 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8987 = injectiveMoment H raw8987step0 := by
      have hz : ∀ j, raw8987 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8987step0 = (fun i j => raw8987 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8987 permutation27 hz
    injectiveMoment H raw8987step0 = injectiveMoment H raw8987step1 := by
      have hz : ∀ j, raw8987step0 (permutation3 0) j = 0 := by decide +kernel
      have heq : raw8987step1 = (fun i j => raw8987step0 (permutation3 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8987step0 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem sound45 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node45 = Sparse.eval value45 (momentVector H) := by
  have hc : momentVector H 27 = injectiveMoment H node45 := rfl
  simp [value45, Sparse.eval, hc]

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

theorem sound197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node197 = Sparse.eval value197 (momentVector H) := by
  have hc : momentVector H 23 = injectiveMoment H node197 := rfl
  simp [value197, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node451 node451Labels = Sparse.eval singlePairValue451 (familyPairVector B) := by
  have hp := single_label_three B hB node451
  have hl : node451Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node451 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node451 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 2) = PairSemantics.raw8987 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node451 PairSemantics.raw8987; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical8987 hH).trans (PairSemantics.sound4 hH)
  have hm3 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value45 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 3) = PairSemantics.raw5116 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node451 PairSemantics.raw5116; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5116 hH).trans (PairSemantics.sound45 hH)
  have hm4 : familyPairMoment B (groupedColumns node451 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value197 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node451 (EqualityPatterns.family3.label 4) = PairSemantics.raw3892 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node451 PairSemantics.raw3892; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical3892 hH).trans (PairSemantics.sound197 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue451, PairSemantics.value0, PairSemantics.value4, PairSemantics.value45, PairSemantics.value197, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3740 node3740Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node451 node451Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw500 singletonSmall3740
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3740) = raw500Labels := by decide +kernel
  rw [hl, canonical500 B hB] at h
  have hc0 : mixedMoment B raw500 (Fin.cases (0 : Fin 1) singletonSmall3740) =
      mixedMoment B node451 node451Labels := by
    have ha : raw500 = raw501 := by apply Matrix.ext; unfold raw500 raw501; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3740 = raw501Labels := by decide +kernel
    rw [ha, hj, canonical501 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

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

theorem singleton4241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4241 node4241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node741 node741Labels + mixedMoment B node820 node820Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw957 singletonSmall4241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4241) = raw957Labels := by decide +kernel
  rw [hl, canonical957 B hB] at h
  have hc0 : mixedMoment B raw957 (Fin.cases (0 : Fin 2) singletonSmall4241) =
      mixedMoment B node741 node741Labels := by
    have ha : raw957 = raw958 := by apply Matrix.ext; unfold raw957 raw958; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4241 = raw958Labels := by decide +kernel
    rw [ha, hj, canonical958 B hB]
  have hc1 : mixedMoment B raw957 (Fin.cases (1 : Fin 2) singletonSmall4241) =
      mixedMoment B node820 node820Labels := by
    have ha : raw957 = raw959 := by apply Matrix.ext; unfold raw957 raw959; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4241 = raw959Labels := by decide +kernel
    rw [ha, hj, canonical959 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4243 node4243Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node743 node743Labels + mixedMoment B node844 node844Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw963 singletonSmall4243
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4243) = raw963Labels := by decide +kernel
  rw [hl, canonical963 B hB] at h
  have hc0 : mixedMoment B raw963 (Fin.cases (0 : Fin 2) singletonSmall4243) =
      mixedMoment B node743 node743Labels := by
    have ha : raw963 = raw964 := by apply Matrix.ext; unfold raw963 raw964; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4243 = raw964Labels := by decide +kernel
    rw [ha, hj, canonical964 B hB]
  have hc1 : mixedMoment B raw963 (Fin.cases (1 : Fin 2) singletonSmall4243) =
      mixedMoment B node844 node844Labels := by
    have ha : raw963 = raw965 := by apply Matrix.ext; unfold raw963 raw965; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4243 = raw965Labels := by decide +kernel
    rw [ha, hj, canonical965 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4278 node4278Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node830 node830Labels + mixedMoment B node830 node830Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1008 singletonSmall4278
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4278) = raw1008Labels := by decide +kernel
  rw [hl, canonical1008 B hB] at h
  have hc0 : mixedMoment B raw1008 (Fin.cases (0 : Fin 2) singletonSmall4278) =
      mixedMoment B node830 node830Labels := by
    have ha : raw1008 = raw1009 := by apply Matrix.ext; unfold raw1008 raw1009; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4278 = raw1009Labels := by decide +kernel
    rw [ha, hj, canonical1009 B hB]
  have hc1 : mixedMoment B raw1008 (Fin.cases (1 : Fin 2) singletonSmall4278) =
      mixedMoment B node830 node830Labels := by
    have ha : raw1008 = raw1010 := by apply Matrix.ext; unfold raw1008 raw1010; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4278 = raw1010Labels := by decide +kernel
    rw [ha, hj, canonical1010 B hB]
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

theorem singleton4673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4673 node4673Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1799 node1799Labels + mixedMoment B node1920 node1920Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1548 singletonSmall4673
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4673) = raw1548Labels := by decide +kernel
  rw [hl, canonical1548 B hB] at h
  have hc0 : mixedMoment B raw1548 (Fin.cases (0 : Fin 2) singletonSmall4673) =
      mixedMoment B node1799 node1799Labels := by
    have ha : raw1548 = raw1549 := by apply Matrix.ext; unfold raw1548 raw1549; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4673 = raw1549Labels := by decide +kernel
    rw [ha, hj, canonical1549 B hB]
  have hc1 : mixedMoment B raw1548 (Fin.cases (1 : Fin 2) singletonSmall4673) =
      mixedMoment B node1920 node1920Labels := by
    have ha : raw1548 = raw1550 := by apply Matrix.ext; unfold raw1548 raw1550; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4673 = raw1550Labels := by decide +kernel
    rw [ha, hj, canonical1550 B hB]
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

theorem singleton4691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4691 node4691Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1817 node1817Labels + mixedMoment B node2159 node2159Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1581 singletonSmall4691
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4691) = raw1581Labels := by decide +kernel
  rw [hl, canonical1581 B hB] at h
  have hc0 : mixedMoment B raw1581 (Fin.cases (0 : Fin 2) singletonSmall4691) =
      mixedMoment B node1817 node1817Labels := by
    have ha : raw1581 = raw1582 := by apply Matrix.ext; unfold raw1581 raw1582; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4691 = raw1582Labels := by decide +kernel
    rw [ha, hj, canonical1582 B hB]
  have hc1 : mixedMoment B raw1581 (Fin.cases (1 : Fin 2) singletonSmall4691) =
      mixedMoment B node2159 node2159Labels := by
    have ha : raw1581 = raw1583 := by apply Matrix.ext; unfold raw1581 raw1583; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4691 = raw1583Labels := by decide +kernel
    rw [ha, hj, canonical1583 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4693 node4693Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1819 node1819Labels + mixedMoment B node2169 node2169Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1587 singletonSmall4693
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4693) = raw1587Labels := by decide +kernel
  rw [hl, canonical1587 B hB] at h
  have hc0 : mixedMoment B raw1587 (Fin.cases (0 : Fin 2) singletonSmall4693) =
      mixedMoment B node1819 node1819Labels := by
    have ha : raw1587 = raw1588 := by apply Matrix.ext; unfold raw1587 raw1588; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4693 = raw1588Labels := by decide +kernel
    rw [ha, hj, canonical1588 B hB]
  have hc1 : mixedMoment B raw1587 (Fin.cases (1 : Fin 2) singletonSmall4693) =
      mixedMoment B node2169 node2169Labels := by
    have ha : raw1587 = raw1589 := by apply Matrix.ext; unfold raw1587 raw1589; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4693 = raw1589Labels := by decide +kernel
    rw [ha, hj, canonical1589 B hB]
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

theorem singleton4727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4727 node4727Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1881 node1881Labels + mixedMoment B node1939 node1939Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1638 singletonSmall4727
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4727) = raw1638Labels := by decide +kernel
  rw [hl, canonical1638 B hB] at h
  have hc0 : mixedMoment B raw1638 (Fin.cases (0 : Fin 2) singletonSmall4727) =
      mixedMoment B node1881 node1881Labels := by
    have ha : raw1638 = raw1639 := by apply Matrix.ext; unfold raw1638 raw1639; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4727 = raw1639Labels := by decide +kernel
    rw [ha, hj, canonical1639 B hB]
  have hc1 : mixedMoment B raw1638 (Fin.cases (1 : Fin 2) singletonSmall4727) =
      mixedMoment B node1939 node1939Labels := by
    have ha : raw1638 = raw1640 := by apply Matrix.ext; unfold raw1638 raw1640; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4727 = raw1640Labels := by decide +kernel
    rw [ha, hj, canonical1640 B hB]
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

theorem singleton4749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4749 node4749Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1928 node1928Labels + mixedMoment B node1928 node1928Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1671 singletonSmall4749
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4749) = raw1671Labels := by decide +kernel
  rw [hl, canonical1671 B hB] at h
  have hc0 : mixedMoment B raw1671 (Fin.cases (0 : Fin 2) singletonSmall4749) =
      mixedMoment B node1928 node1928Labels := by
    have ha : raw1671 = raw1672 := by apply Matrix.ext; unfold raw1671 raw1672; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4749 = raw1672Labels := by decide +kernel
    rw [ha, hj, canonical1672 B hB]
  have hc1 : mixedMoment B raw1671 (Fin.cases (1 : Fin 2) singletonSmall4749) =
      mixedMoment B node1928 node1928Labels := by
    have ha : raw1671 = raw1673 := by apply Matrix.ext; unfold raw1671 raw1673; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4749 = raw1673Labels := by decide +kernel
    rw [ha, hj, canonical1673 B hB]
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

theorem singleton4862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4862 node4862Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2103 node2103Labels + mixedMoment B node2103 node2103Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1785 singletonSmall4862
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4862) = raw1785Labels := by decide +kernel
  rw [hl, canonical1785 B hB] at h
  have hc0 : mixedMoment B raw1785 (Fin.cases (0 : Fin 2) singletonSmall4862) =
      mixedMoment B node2103 node2103Labels := by
    have ha : raw1785 = raw1786 := by apply Matrix.ext; unfold raw1785 raw1786; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4862 = raw1786Labels := by decide +kernel
    rw [ha, hj, canonical1786 B hB]
  have hc1 : mixedMoment B raw1785 (Fin.cases (1 : Fin 2) singletonSmall4862) =
      mixedMoment B node2103 node2103Labels := by
    have ha : raw1785 = raw1787 := by apply Matrix.ext; unfold raw1785 raw1787; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4862 = raw1787Labels := by decide +kernel
    rw [ha, hj, canonical1787 B hB]
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

theorem singleton5384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5384 node5384Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3732 node3732Labels + mixedMoment B node3811 node3811Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2439 singletonSmall5384
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5384) = raw2439Labels := by decide +kernel
  rw [hl, canonical2439 B hB] at h
  have hc0 : mixedMoment B raw2439 (Fin.cases (0 : Fin 2) singletonSmall5384) =
      mixedMoment B node3732 node3732Labels := by
    have ha : raw2439 = raw2440 := by apply Matrix.ext; unfold raw2439 raw2440; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5384 = raw2440Labels := by decide +kernel
    rw [ha, hj, canonical2440 B hB]
  have hc1 : mixedMoment B raw2439 (Fin.cases (1 : Fin 2) singletonSmall5384) =
      mixedMoment B node3811 node3811Labels := by
    have ha : raw2439 = raw2441 := by apply Matrix.ext; unfold raw2439 raw2441; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5384 = raw2441Labels := by decide +kernel
    rw [ha, hj, canonical2441 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5389 node5389Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3740 node3740Labels + mixedMoment B node3893 node3893Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2451 singletonSmall5389
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5389) = raw2451Labels := by decide +kernel
  rw [hl, canonical2451 B hB] at h
  have hc0 : mixedMoment B raw2451 (Fin.cases (0 : Fin 2) singletonSmall5389) =
      mixedMoment B node3740 node3740Labels := by
    have ha : raw2451 = raw2452 := by apply Matrix.ext; unfold raw2451 raw2452; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5389 = raw2452Labels := by decide +kernel
    rw [ha, hj, canonical2452 B hB]
  have hc1 : mixedMoment B raw2451 (Fin.cases (1 : Fin 2) singletonSmall5389) =
      mixedMoment B node3893 node3893Labels := by
    have ha : raw2451 = raw2453 := by apply Matrix.ext; unfold raw2451 raw2453; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5389 = raw2453Labels := by decide +kernel
    rw [ha, hj, canonical2453 B hB]
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

theorem singleton5449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5449 node5449Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3886 node3886Labels + mixedMoment B node3886 node3886Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2553 singletonSmall5449
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5449) = raw2553Labels := by decide +kernel
  rw [hl, canonical2553 B hB] at h
  have hc0 : mixedMoment B raw2553 (Fin.cases (0 : Fin 2) singletonSmall5449) =
      mixedMoment B node3886 node3886Labels := by
    have ha : raw2553 = raw2554 := by apply Matrix.ext; unfold raw2553 raw2554; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5449 = raw2554Labels := by decide +kernel
    rw [ha, hj, canonical2554 B hB]
  have hc1 : mixedMoment B raw2553 (Fin.cases (1 : Fin 2) singletonSmall5449) =
      mixedMoment B node3886 node3886Labels := by
    have ha : raw2553 = raw2555 := by apply Matrix.ext; unfold raw2553 raw2555; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5449 = raw2555Labels := by decide +kernel
    rw [ha, hj, canonical2555 B hB]
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

theorem sound738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node738 node738Labels = Sparse.eval nodeValue738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 738) = mixedMoment B node738 node738Labels := rfl
  simpa [nodeValue738, Sparse.eval] using hc.symm

theorem sound741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node741 node741Labels = Sparse.eval nodeValue741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 741) = mixedMoment B node741 node741Labels := rfl
  simpa [nodeValue741, Sparse.eval] using hc.symm

theorem sound743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node743 node743Labels = Sparse.eval nodeValue743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 743) = mixedMoment B node743 node743Labels := rfl
  simpa [nodeValue743, Sparse.eval] using hc.symm

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

theorem sound819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node819 node819Labels = Sparse.eval nodeValue819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 819) = mixedMoment B node819 node819Labels := rfl
  simpa [nodeValue819, Sparse.eval] using hc.symm

theorem sound820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node820 node820Labels = Sparse.eval nodeValue820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 820) = mixedMoment B node820 node820Labels := rfl
  simpa [nodeValue820, Sparse.eval] using hc.symm

theorem sound830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node830 node830Labels = Sparse.eval nodeValue830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 830) = mixedMoment B node830 node830Labels := rfl
  simpa [nodeValue830, Sparse.eval] using hc.symm

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

theorem sound844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node844 node844Labels = Sparse.eval nodeValue844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 844) = mixedMoment B node844 node844Labels := rfl
  simpa [nodeValue844, Sparse.eval] using hc.symm

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

theorem sound1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1799 node1799Labels = Sparse.eval nodeValue1799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1799) = mixedMoment B node1799 node1799Labels := rfl
  simpa [nodeValue1799, Sparse.eval] using hc.symm

theorem sound1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1814 node1814Labels = Sparse.eval nodeValue1814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1814) = mixedMoment B node1814 node1814Labels := rfl
  simpa [nodeValue1814, Sparse.eval] using hc.symm

theorem sound1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1817 node1817Labels = Sparse.eval nodeValue1817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1817) = mixedMoment B node1817 node1817Labels := rfl
  simpa [nodeValue1817, Sparse.eval] using hc.symm

theorem sound1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1819 node1819Labels = Sparse.eval nodeValue1819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1819) = mixedMoment B node1819 node1819Labels := rfl
  simpa [nodeValue1819, Sparse.eval] using hc.symm

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

theorem sound1878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1878 node1878Labels = Sparse.eval nodeValue1878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1878) = mixedMoment B node1878 node1878Labels := rfl
  simpa [nodeValue1878, Sparse.eval] using hc.symm

theorem sound1881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1881 node1881Labels = Sparse.eval nodeValue1881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1881) = mixedMoment B node1881 node1881Labels := rfl
  simpa [nodeValue1881, Sparse.eval] using hc.symm

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

theorem sound1920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1920 node1920Labels = Sparse.eval nodeValue1920 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1920) = mixedMoment B node1920 node1920Labels := rfl
  simpa [nodeValue1920, Sparse.eval] using hc.symm

theorem sound1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1928 node1928Labels = Sparse.eval nodeValue1928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1928) = mixedMoment B node1928 node1928Labels := rfl
  simpa [nodeValue1928, Sparse.eval] using hc.symm

theorem sound1939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1939 node1939Labels = Sparse.eval nodeValue1939 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1939) = mixedMoment B node1939 node1939Labels := rfl
  simpa [nodeValue1939, Sparse.eval] using hc.symm

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

theorem sound2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2101 node2101Labels = Sparse.eval nodeValue2101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2101) = mixedMoment B node2101 node2101Labels := rfl
  simpa [nodeValue2101, Sparse.eval] using hc.symm

theorem sound2103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2103 node2103Labels = Sparse.eval nodeValue2103 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2103) = mixedMoment B node2103 node2103Labels := rfl
  simpa [nodeValue2103, Sparse.eval] using hc.symm

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

theorem sound2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2157 node2157Labels = Sparse.eval nodeValue2157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2157) = mixedMoment B node2157 node2157Labels := rfl
  simpa [nodeValue2157, Sparse.eval] using hc.symm

theorem sound2159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2159 node2159Labels = Sparse.eval nodeValue2159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2159) = mixedMoment B node2159 node2159Labels := rfl
  simpa [nodeValue2159, Sparse.eval] using hc.symm

theorem sound2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2169 node2169Labels = Sparse.eval nodeValue2169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2169) = mixedMoment B node2169 node2169Labels := rfl
  simpa [nodeValue2169, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node451 node451Labels = Sparse.eval nodeValue451 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue451 (familyPairVector B) := singlePair451 B _hB
    _ = _ := by norm_num [singlePairValue451, nodeValue451, Sparse.eval, mixedVector] <;> ring

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

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3740 node3740Labels = Sparse.eval nodeValue3740 (mixedVector B) := by
  have h := singleton3740 B _hB
  rw [sound451 B _hB _hF] at h
  norm_num [nodeValue3740, nodeValue451, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

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

theorem sound3886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3886 node3886Labels = Sparse.eval nodeValue3886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3886) = mixedMoment B node3886 node3886Labels := rfl
  simpa [nodeValue3886, Sparse.eval] using hc.symm

theorem sound3893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3893 node3893Labels = Sparse.eval nodeValue3893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3893) = mixedMoment B node3893 node3893Labels := rfl
  simpa [nodeValue3893, Sparse.eval] using hc.symm

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

theorem sound4238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4238 node4238Labels = Sparse.eval nodeValue4238 (mixedVector B) := by
  have h := singleton4238 B _hB
  rw [sound738 B _hB _hF, sound819 B _hB _hF] at h
  norm_num [nodeValue4238, nodeValue738, nodeValue819, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4241 node4241Labels = Sparse.eval nodeValue4241 (mixedVector B) := by
  have h := singleton4241 B _hB
  rw [sound741 B _hB _hF, sound820 B _hB _hF] at h
  norm_num [nodeValue4241, nodeValue741, nodeValue820, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4243 node4243Labels = Sparse.eval nodeValue4243 (mixedVector B) := by
  have h := singleton4243 B _hB
  rw [sound743 B _hB _hF, sound844 B _hB _hF] at h
  norm_num [nodeValue4243, nodeValue743, nodeValue844, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4278 node4278Labels = Sparse.eval nodeValue4278 (mixedVector B) := by
  have h := singleton4278 B _hB
  rw [sound830 B _hB _hF] at h
  norm_num [nodeValue4278, nodeValue830, Sparse.eval] at h ⊢
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

theorem sound4673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4673 node4673Labels = Sparse.eval nodeValue4673 (mixedVector B) := by
  have h := singleton4673 B _hB
  rw [sound1799 B _hB _hF, sound1920 B _hB _hF] at h
  norm_num [nodeValue4673, nodeValue1799, nodeValue1920, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4688 node4688Labels = Sparse.eval nodeValue4688 (mixedVector B) := by
  have h := singleton4688 B _hB
  rw [sound1814 B _hB _hF, sound2157 B _hB _hF] at h
  norm_num [nodeValue4688, nodeValue1814, nodeValue2157, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4691 node4691Labels = Sparse.eval nodeValue4691 (mixedVector B) := by
  have h := singleton4691 B _hB
  rw [sound1817 B _hB _hF, sound2159 B _hB _hF] at h
  norm_num [nodeValue4691, nodeValue1817, nodeValue2159, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4693 node4693Labels = Sparse.eval nodeValue4693 (mixedVector B) := by
  have h := singleton4693 B _hB
  rw [sound1819 B _hB _hF, sound2169 B _hB _hF] at h
  norm_num [nodeValue4693, nodeValue1819, nodeValue2169, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4724 node4724Labels = Sparse.eval nodeValue4724 (mixedVector B) := by
  have h := singleton4724 B _hB
  rw [sound1878 B _hB _hF, sound1919 B _hB _hF] at h
  norm_num [nodeValue4724, nodeValue1878, nodeValue1919, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4727 node4727Labels = Sparse.eval nodeValue4727 (mixedVector B) := by
  have h := singleton4727 B _hB
  rw [sound1881 B _hB _hF, sound1939 B _hB _hF] at h
  norm_num [nodeValue4727, nodeValue1881, nodeValue1939, Sparse.eval] at h ⊢
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

theorem sound4749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4749 node4749Labels = Sparse.eval nodeValue4749 (mixedVector B) := by
  have h := singleton4749 B _hB
  rw [sound1928 B _hB _hF] at h
  norm_num [nodeValue4749, nodeValue1928, Sparse.eval] at h ⊢
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

theorem sound4860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4860 node4860Labels = Sparse.eval nodeValue4860 (mixedVector B) := by
  have h := singleton4860 B _hB
  rw [sound2101 B _hB _hF] at h
  norm_num [nodeValue4860, nodeValue2101, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4862 node4862Labels = Sparse.eval nodeValue4862 (mixedVector B) := by
  have h := singleton4862 B _hB
  rw [sound2103 B _hB _hF] at h
  norm_num [nodeValue4862, nodeValue2103, Sparse.eval] at h ⊢
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

theorem sound5384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5384 node5384Labels = Sparse.eval nodeValue5384 (mixedVector B) := by
  have h := singleton5384 B _hB
  rw [sound3732 B _hB _hF, sound3811 B _hB _hF] at h
  norm_num [nodeValue5384, nodeValue3732, nodeValue3811, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5389 node5389Labels = Sparse.eval nodeValue5389 (mixedVector B) := by
  have h := singleton5389 B _hB
  rw [sound3740 B _hB _hF, sound3893 B _hB _hF] at h
  norm_num [nodeValue5389, nodeValue3740, nodeValue3893, Sparse.eval] at h ⊢
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

theorem sound5449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5449 node5449Labels = Sparse.eval nodeValue5449 (mixedVector B) := by
  have h := singleton5449 B _hB
  rw [sound3886 B _hB _hF] at h
  norm_num [nodeValue5449, nodeValue3886, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources70
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2256 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 1) (sourceB2256 + difference 1 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 1) (sourceB2256 + difference 1 0) sourceC2256) = raw31009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31009; decide +kernel
    rw [ha]
    exact (canonical31009 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 2) (sourceB2256 + difference 2 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 2) (sourceB2256 + difference 2 0) sourceC2256) = raw31010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31010; decide +kernel
    rw [ha]
    exact (canonical31010 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 3) (sourceB2256 + difference 3 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 3) (sourceB2256 + difference 3 0) sourceC2256) = raw31011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31011; decide +kernel
    rw [ha]
    exact (canonical31011 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 4) (sourceB2256 + difference 4 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 4) (sourceB2256 + difference 4 0) sourceC2256) = raw10769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10769; decide +kernel
    rw [ha]
    exact (canonical10769 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 5) (sourceB2256 + difference 5 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 5) (sourceB2256 + difference 5 0) sourceC2256) = raw19191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw19191; decide +kernel
    rw [ha]
    exact (canonical19191 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 0) (sourceB2256 + difference 0 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4278) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 0) (sourceB2256 + difference 0 1) sourceC2256) = raw10789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10789; decide +kernel
    rw [ha]
    exact (canonical10789 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 2) (sourceB2256 + difference 2 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 2) (sourceB2256 + difference 2 1) sourceC2256) = raw10791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10791; decide +kernel
    rw [ha]
    exact (canonical10791 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 3) (sourceB2256 + difference 3 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 3) (sourceB2256 + difference 3 1) sourceC2256) = raw10792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10792; decide +kernel
    rw [ha]
    exact (canonical10792 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 4) (sourceB2256 + difference 4 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 4) (sourceB2256 + difference 4 1) sourceC2256) = raw31012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31012; decide +kernel
    rw [ha]
    exact (canonical31012 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 5) (sourceB2256 + difference 5 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 5) (sourceB2256 + difference 5 1) sourceC2256) = raw10793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10793; decide +kernel
    rw [ha]
    exact (canonical10793 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 0) (sourceB2256 + difference 0 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 0) (sourceB2256 + difference 0 2) sourceC2256) = raw31013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31013; decide +kernel
    rw [ha]
    exact (canonical31013 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 1) (sourceB2256 + difference 1 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 1) (sourceB2256 + difference 1 2) sourceC2256) = raw31014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31014; decide +kernel
    rw [ha]
    exact (canonical31014 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 3) (sourceB2256 + difference 3 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 3) (sourceB2256 + difference 3 2) sourceC2256) = raw31015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31015; decide +kernel
    rw [ha]
    exact (canonical31015 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 4) (sourceB2256 + difference 4 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 4) (sourceB2256 + difference 4 2) sourceC2256) = raw10780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10780; decide +kernel
    rw [ha]
    exact (canonical10780 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 5) (sourceB2256 + difference 5 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 5) (sourceB2256 + difference 5 2) sourceC2256) = raw31016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31016; decide +kernel
    rw [ha]
    exact (canonical31016 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 0) (sourceB2256 + difference 0 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 0) (sourceB2256 + difference 0 3) sourceC2256) = raw31017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31017; decide +kernel
    rw [ha]
    exact (canonical31017 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 1) (sourceB2256 + difference 1 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 1) (sourceB2256 + difference 1 3) sourceC2256) = raw31018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31018; decide +kernel
    rw [ha]
    exact (canonical31018 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 2) (sourceB2256 + difference 2 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 2) (sourceB2256 + difference 2 3) sourceC2256) = raw31019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31019; decide +kernel
    rw [ha]
    exact (canonical31019 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 4) (sourceB2256 + difference 4 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 4) (sourceB2256 + difference 4 3) sourceC2256) = raw10785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10785; decide +kernel
    rw [ha]
    exact (canonical10785 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 5) (sourceB2256 + difference 5 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 5) (sourceB2256 + difference 5 3) sourceC2256) = raw19188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw19188; decide +kernel
    rw [ha]
    exact (canonical19188 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 0) (sourceB2256 + difference 0 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4241) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 0) (sourceB2256 + difference 0 4) sourceC2256) = raw31020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31020; decide +kernel
    rw [ha]
    exact (canonical31020 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 1) (sourceB2256 + difference 1 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4691) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 1) (sourceB2256 + difference 1 4) sourceC2256) = raw31021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31021; decide +kernel
    rw [ha]
    exact (canonical31021 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 2) (sourceB2256 + difference 2 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4673) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 2) (sourceB2256 + difference 2 4) sourceC2256) = raw31022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31022; decide +kernel
    rw [ha]
    exact (canonical31022 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 3) (sourceB2256 + difference 3 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4673) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 3) (sourceB2256 + difference 3 4) sourceC2256) = raw31023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31023; decide +kernel
    rw [ha]
    exact (canonical31023 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 5) (sourceB2256 + difference 5 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4862) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 5) (sourceB2256 + difference 5 4) sourceC2256) = raw31024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31024; decide +kernel
    rw [ha]
    exact (canonical31024 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 0) (sourceB2256 + difference 0 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4243) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 0) (sourceB2256 + difference 0 5) sourceC2256) = raw31025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31025; decide +kernel
    rw [ha]
    exact (canonical31025 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 1) (sourceB2256 + difference 1 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 1) (sourceB2256 + difference 1 5) sourceC2256) = raw31026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31026; decide +kernel
    rw [ha]
    exact (canonical31026 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 2) (sourceB2256 + difference 2 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 2) (sourceB2256 + difference 2 5) sourceC2256) = raw31027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31027; decide +kernel
    rw [ha]
    exact (canonical31027 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 3) (sourceB2256 + difference 3 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 3) (sourceB2256 + difference 3 5) sourceC2256) = raw31028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31028; decide +kernel
    rw [ha]
    exact (canonical31028 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 4) (sourceB2256 + difference 4 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 4) (sourceB2256 + difference 4 5) sourceC2256) = raw10795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10795; decide +kernel
    rw [ha]
    exact (canonical10795 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2256 sourceB2256 sourceC2256
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2256, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1844 : Integer.Sparse.reindex keyMap MixedData.row1844 = numericRow1844 := by decide +kernel

theorem numericCheck1844 (x : Master → ℝ) : Integer.Sparse.eval numericRow1844 x =
    (25920 : ℝ) * reducedSource1844 x := by
  norm_num [numericRow1844, reducedSource1844, Integer.Sparse.eval, Sparse.eval, nodeValue4238, nodeValue4241, nodeValue4243, nodeValue4278, nodeValue4673, nodeValue4688, nodeValue4691, nodeValue4693, nodeValue4724, nodeValue4727, nodeValue4749, nodeValue4860, nodeValue4862, nodeValue4869, nodeValue4871, nodeValue4874, nodeValue4898, nodeValue5384, nodeValue5389, nodeValue5443, nodeValue5449]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1844 (mixedVector B) = 0 := by
  have h4238 : mixedVector B (Sum.inr 4238) = Sparse.eval nodeValue4238 (mixedVector B) := by
    change mixedMoment B node4238 node4238Labels = _
    exact sound4238 B hB hF
  have h4241 : mixedVector B (Sum.inr 4241) = Sparse.eval nodeValue4241 (mixedVector B) := by
    change mixedMoment B node4241 node4241Labels = _
    exact sound4241 B hB hF
  have h4243 : mixedVector B (Sum.inr 4243) = Sparse.eval nodeValue4243 (mixedVector B) := by
    change mixedMoment B node4243 node4243Labels = _
    exact sound4243 B hB hF
  have h4278 : mixedVector B (Sum.inr 4278) = Sparse.eval nodeValue4278 (mixedVector B) := by
    change mixedMoment B node4278 node4278Labels = _
    exact sound4278 B hB hF
  have h4673 : mixedVector B (Sum.inr 4673) = Sparse.eval nodeValue4673 (mixedVector B) := by
    change mixedMoment B node4673 node4673Labels = _
    exact sound4673 B hB hF
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4691 : mixedVector B (Sum.inr 4691) = Sparse.eval nodeValue4691 (mixedVector B) := by
    change mixedMoment B node4691 node4691Labels = _
    exact sound4691 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4724 : mixedVector B (Sum.inr 4724) = Sparse.eval nodeValue4724 (mixedVector B) := by
    change mixedMoment B node4724 node4724Labels = _
    exact sound4724 B hB hF
  have h4727 : mixedVector B (Sum.inr 4727) = Sparse.eval nodeValue4727 (mixedVector B) := by
    change mixedMoment B node4727 node4727Labels = _
    exact sound4727 B hB hF
  have h4749 : mixedVector B (Sum.inr 4749) = Sparse.eval nodeValue4749 (mixedVector B) := by
    change mixedMoment B node4749 node4749Labels = _
    exact sound4749 B hB hF
  have h4860 : mixedVector B (Sum.inr 4860) = Sparse.eval nodeValue4860 (mixedVector B) := by
    change mixedMoment B node4860 node4860Labels = _
    exact sound4860 B hB hF
  have h4862 : mixedVector B (Sum.inr 4862) = Sparse.eval nodeValue4862 (mixedVector B) := by
    change mixedMoment B node4862 node4862Labels = _
    exact sound4862 B hB hF
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
  have h5384 : mixedVector B (Sum.inr 5384) = Sparse.eval nodeValue5384 (mixedVector B) := by
    change mixedMoment B node5384 node5384Labels = _
    exact sound5384 B hB hF
  have h5389 : mixedVector B (Sum.inr 5389) = Sparse.eval nodeValue5389 (mixedVector B) := by
    change mixedMoment B node5389 node5389Labels = _
    exact sound5389 B hB hF
  have h5443 : mixedVector B (Sum.inr 5443) = Sparse.eval nodeValue5443 (mixedVector B) := by
    change mixedMoment B node5443 node5443Labels = _
    exact sound5443 B hB hF
  have h5449 : mixedVector B (Sum.inr 5449) = Sparse.eval nodeValue5449 (mixedVector B) := by
    change mixedMoment B node5449 node5449Labels = _
    exact sound5449 B hB hF
  simpa only [sourceForm2256, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4238, h4241, h4243, h4278, h4673, h4688, h4691, h4693, h4724, h4727, h4749, h4860, h4862, h4869, h4871, h4874, h4898, h5384, h5389, h5443, h5449, reducedSource1844] using sourceEq2256 B hB

theorem rowSound1844_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1844 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1844, numericCheck1844, reducedZero1844 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e_oai
