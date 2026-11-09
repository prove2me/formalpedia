-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:07:58.343709+00:00
-- url     : https://prove2.me/submissions/d7c41b54-b2f4-483f-bbe4-eb8b000e3c37

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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

theorem canonical1500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1500 raw1500Labels = mixedMoment B node4640 node4640Labels := by
  calc
    mixedMoment B raw1500 raw1500Labels = mixedMoment B raw1500step0 raw1500step0Labels := by
      have ha : raw1500step0 = (fun i j => raw1500 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1500step0 raw1500; decide +kernel
      have hl : raw1500step0Labels = raw1500Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1500 raw1500Labels permutation152 permutation4
    mixedMoment B raw1500step0 raw1500step0Labels = mixedMoment B raw1500step1 raw1500step1Labels := by
      have ha : raw1500step1 = raw1500step0 := by apply Matrix.ext; unfold raw1500step1 raw1500step0; decide +kernel
      have hl : raw1500step0Labels = labelEmbedding7 ∘ raw1500step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1500step0 raw1500step0Labels raw1500step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4640 node4640Labels := by rfl

theorem canonical1501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1501 raw1501Labels = mixedMoment B node1769 node1769Labels := by
  calc
    mixedMoment B raw1501 raw1501Labels = mixedMoment B raw1501step0 raw1501step0Labels := by
      have ha : raw1501step0 = (fun i j => raw1501 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1501step0 raw1501; decide +kernel
      have hl : raw1501step0Labels = raw1501Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1501 raw1501Labels permutation152 permutation4
    _ = mixedMoment B node1769 node1769Labels := by rfl

theorem canonical1502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1502 raw1502Labels = mixedMoment B node1835 node1835Labels := by
  calc
    mixedMoment B raw1502 raw1502Labels = mixedMoment B raw1502step0 raw1502step0Labels := by
      have ha : raw1502step0 = (fun i j => raw1502 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1502step0 raw1502; decide +kernel
      have hl : raw1502step0Labels = raw1502Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1502 raw1502Labels permutation152 permutation6
    mixedMoment B raw1502step0 raw1502step0Labels = mixedMoment B raw1502step1 raw1502step1Labels := by
      have ha : raw1502step1 = -raw1502step0 := by apply Matrix.ext; change ∀ i j, raw1502step1 i j = -(raw1502step0 i j); unfold raw1502step1 raw1502step0; decide +kernel
      have hl : raw1502step1Labels = raw1502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1502step1 raw1502step1Labels = mixedMoment B raw1502step2 raw1502step2Labels := by
      have ha : raw1502step2 = raw1502step1 := by apply Matrix.ext; unfold raw1502step2 raw1502step1; decide +kernel
      have hl : raw1502step1Labels = labelEmbedding1 ∘ raw1502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1502step1 raw1502step1Labels raw1502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1835 node1835Labels := by rfl

theorem canonical1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1506 raw1506Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw1506 raw1506Labels = mixedMoment B raw1506step0 raw1506step0Labels := by
      have ha : raw1506step0 = (fun i j => raw1506 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1506step0 raw1506; decide +kernel
      have hl : raw1506step0Labels = raw1506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1506 raw1506Labels permutation32 permutation4
    mixedMoment B raw1506step0 raw1506step0Labels = mixedMoment B raw1506step1 raw1506step1Labels := by
      have ha : raw1506step1 = raw1506step0 := by apply Matrix.ext; unfold raw1506step1 raw1506step0; decide +kernel
      have hl : raw1506step0Labels = labelEmbedding7 ∘ raw1506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1506step0 raw1506step0Labels raw1506step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

theorem canonical1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1507 raw1507Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw1507 raw1507Labels = mixedMoment B raw1507step0 raw1507step0Labels := by
      have ha : raw1507step0 = (fun i j => raw1507 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1507step0 raw1507; decide +kernel
      have hl : raw1507step0Labels = raw1507Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1507 raw1507Labels permutation32 permutation4
    _ = mixedMoment B node1773 node1773Labels := by rfl

theorem canonical1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1508 raw1508Labels = mixedMoment B node1841 node1841Labels := by
  calc
    mixedMoment B raw1508 raw1508Labels = mixedMoment B raw1508step0 raw1508step0Labels := by
      have ha : raw1508step0 = (fun i j => raw1508 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1508step0 raw1508; decide +kernel
      have hl : raw1508step0Labels = raw1508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1508 raw1508Labels permutation32 permutation6
    mixedMoment B raw1508step0 raw1508step0Labels = mixedMoment B raw1508step1 raw1508step1Labels := by
      have ha : raw1508step1 = -raw1508step0 := by apply Matrix.ext; change ∀ i j, raw1508step1 i j = -(raw1508step0 i j); unfold raw1508step1 raw1508step0; decide +kernel
      have hl : raw1508step1Labels = raw1508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1508step1 raw1508step1Labels = mixedMoment B raw1508step2 raw1508step2Labels := by
      have ha : raw1508step2 = raw1508step1 := by apply Matrix.ext; unfold raw1508step2 raw1508step1; decide +kernel
      have hl : raw1508step1Labels = labelEmbedding1 ∘ raw1508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1508step1 raw1508step1Labels raw1508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1841 node1841Labels := by rfl

theorem canonical1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1521 raw1521Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw1521 raw1521Labels = mixedMoment B raw1521step0 raw1521step0Labels := by
      have ha : raw1521step0 = (fun i j => raw1521 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1521step0 raw1521; decide +kernel
      have hl : raw1521step0Labels = raw1521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1521 raw1521Labels permutation32 permutation4
    mixedMoment B raw1521step0 raw1521step0Labels = mixedMoment B raw1521step1 raw1521step1Labels := by
      have ha : raw1521step1 = raw1521step0 := by apply Matrix.ext; unfold raw1521step1 raw1521step0; decide +kernel
      have hl : raw1521step0Labels = labelEmbedding7 ∘ raw1521step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1521step0 raw1521step0Labels raw1521step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

theorem canonical1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1522 raw1522Labels = mixedMoment B node1781 node1781Labels := by
  calc
    mixedMoment B raw1522 raw1522Labels = mixedMoment B raw1522step0 raw1522step0Labels := by
      have ha : raw1522step0 = (fun i j => raw1522 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1522step0 raw1522; decide +kernel
      have hl : raw1522step0Labels = raw1522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1522 raw1522Labels permutation32 permutation4
    _ = mixedMoment B node1781 node1781Labels := by rfl

theorem canonical1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1523 raw1523Labels = mixedMoment B node1846 node1846Labels := by
  calc
    mixedMoment B raw1523 raw1523Labels = mixedMoment B raw1523step0 raw1523step0Labels := by
      have ha : raw1523step0 = (fun i j => raw1523 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1523step0 raw1523; decide +kernel
      have hl : raw1523step0Labels = raw1523Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1523 raw1523Labels permutation34 permutation6
    mixedMoment B raw1523step0 raw1523step0Labels = mixedMoment B raw1523step1 raw1523step1Labels := by
      have ha : raw1523step1 = -raw1523step0 := by apply Matrix.ext; change ∀ i j, raw1523step1 i j = -(raw1523step0 i j); unfold raw1523step1 raw1523step0; decide +kernel
      have hl : raw1523step1Labels = raw1523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1523step1 raw1523step1Labels = mixedMoment B raw1523step2 raw1523step2Labels := by
      have ha : raw1523step2 = raw1523step1 := by apply Matrix.ext; unfold raw1523step2 raw1523step1; decide +kernel
      have hl : raw1523step1Labels = labelEmbedding1 ∘ raw1523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1523step1 raw1523step1Labels raw1523step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1846 node1846Labels := by rfl

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

theorem canonical1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1596 raw1596Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw1596 raw1596Labels = mixedMoment B raw1596step0 raw1596step0Labels := by
      have ha : raw1596step0 = (fun i j => raw1596 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1596step0 raw1596; decide +kernel
      have hl : raw1596step0Labels = raw1596Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1596 raw1596Labels permutation152 permutation4
    mixedMoment B raw1596step0 raw1596step0Labels = mixedMoment B raw1596step1 raw1596step1Labels := by
      have ha : raw1596step1 = raw1596step0 := by apply Matrix.ext; unfold raw1596step1 raw1596step0; decide +kernel
      have hl : raw1596step0Labels = labelEmbedding7 ∘ raw1596step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1596step0 raw1596step0Labels raw1596step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

theorem canonical1597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1597 raw1597Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw1597 raw1597Labels = mixedMoment B raw1597step0 raw1597step0Labels := by
      have ha : raw1597step0 = (fun i j => raw1597 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1597step0 raw1597; decide +kernel
      have hl : raw1597step0Labels = raw1597Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1597 raw1597Labels permutation152 permutation4
    _ = mixedMoment B node1863 node1863Labels := by rfl

theorem canonical1598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1598 raw1598Labels = mixedMoment B node1883 node1883Labels := by
  calc
    mixedMoment B raw1598 raw1598Labels = mixedMoment B raw1598step0 raw1598step0Labels := by
      have ha : raw1598step0 = (fun i j => raw1598 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1598step0 raw1598; decide +kernel
      have hl : raw1598step0Labels = raw1598Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1598 raw1598Labels permutation152 permutation6
    mixedMoment B raw1598step0 raw1598step0Labels = mixedMoment B raw1598step1 raw1598step1Labels := by
      have ha : raw1598step1 = -raw1598step0 := by apply Matrix.ext; change ∀ i j, raw1598step1 i j = -(raw1598step0 i j); unfold raw1598step1 raw1598step0; decide +kernel
      have hl : raw1598step1Labels = raw1598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1598step1 raw1598step1Labels = mixedMoment B raw1598step2 raw1598step2Labels := by
      have ha : raw1598step2 = raw1598step1 := by apply Matrix.ext; unfold raw1598step2 raw1598step1; decide +kernel
      have hl : raw1598step1Labels = labelEmbedding1 ∘ raw1598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1598step1 raw1598step1Labels raw1598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1883 node1883Labels := by rfl

theorem canonical1608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1608 raw1608Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw1608 raw1608Labels = mixedMoment B raw1608step0 raw1608step0Labels := by
      have ha : raw1608step0 = (fun i j => raw1608 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1608step0 raw1608; decide +kernel
      have hl : raw1608step0Labels = raw1608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1608 raw1608Labels permutation152 permutation4
    mixedMoment B raw1608step0 raw1608step0Labels = mixedMoment B raw1608step1 raw1608step1Labels := by
      have ha : raw1608step1 = raw1608step0 := by apply Matrix.ext; unfold raw1608step1 raw1608step0; decide +kernel
      have hl : raw1608step0Labels = labelEmbedding7 ∘ raw1608step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1608step0 raw1608step0Labels raw1608step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

theorem canonical1609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1609 raw1609Labels = mixedMoment B node1870 node1870Labels := by
  calc
    mixedMoment B raw1609 raw1609Labels = mixedMoment B raw1609step0 raw1609step0Labels := by
      have ha : raw1609step0 = (fun i j => raw1609 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1609step0 raw1609; decide +kernel
      have hl : raw1609step0Labels = raw1609Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1609 raw1609Labels permutation152 permutation4
    _ = mixedMoment B node1870 node1870Labels := by rfl

theorem canonical1610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1610 raw1610Labels = mixedMoment B node1886 node1886Labels := by
  calc
    mixedMoment B raw1610 raw1610Labels = mixedMoment B raw1610step0 raw1610step0Labels := by
      have ha : raw1610step0 = (fun i j => raw1610 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1610step0 raw1610; decide +kernel
      have hl : raw1610step0Labels = raw1610Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1610 raw1610Labels permutation154 permutation6
    mixedMoment B raw1610step0 raw1610step0Labels = mixedMoment B raw1610step1 raw1610step1Labels := by
      have ha : raw1610step1 = -raw1610step0 := by apply Matrix.ext; change ∀ i j, raw1610step1 i j = -(raw1610step0 i j); unfold raw1610step1 raw1610step0; decide +kernel
      have hl : raw1610step1Labels = raw1610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1610step1 raw1610step1Labels = mixedMoment B raw1610step2 raw1610step2Labels := by
      have ha : raw1610step2 = raw1610step1 := by apply Matrix.ext; unfold raw1610step2 raw1610step1; decide +kernel
      have hl : raw1610step1Labels = labelEmbedding1 ∘ raw1610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1610step1 raw1610step1Labels raw1610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1886 node1886Labels := by rfl

theorem canonical1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1647 raw1647Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw1647 raw1647Labels = mixedMoment B raw1647step0 raw1647step0Labels := by
      have ha : raw1647step0 = (fun i j => raw1647 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1647step0 raw1647; decide +kernel
      have hl : raw1647step0Labels = raw1647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1647 raw1647Labels permutation152 permutation4
    mixedMoment B raw1647step0 raw1647step0Labels = mixedMoment B raw1647step1 raw1647step1Labels := by
      have ha : raw1647step1 = raw1647step0 := by apply Matrix.ext; unfold raw1647step1 raw1647step0; decide +kernel
      have hl : raw1647step0Labels = labelEmbedding7 ∘ raw1647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1647step0 raw1647step0Labels raw1647step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

theorem canonical1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1648 raw1648Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw1648 raw1648Labels = mixedMoment B raw1648step0 raw1648step0Labels := by
      have ha : raw1648step0 = (fun i j => raw1648 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1648step0 raw1648; decide +kernel
      have hl : raw1648step0Labels = raw1648Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1648 raw1648Labels permutation152 permutation4
    _ = mixedMoment B node1900 node1900Labels := by rfl

theorem canonical1649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1649 raw1649Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw1649 raw1649Labels = mixedMoment B raw1649step0 raw1649step0Labels := by
      have ha : raw1649step0 = (fun i j => raw1649 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1649step0 raw1649; decide +kernel
      have hl : raw1649step0Labels = raw1649Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1649 raw1649Labels permutation164 permutation6
    mixedMoment B raw1649step0 raw1649step0Labels = mixedMoment B raw1649step1 raw1649step1Labels := by
      have ha : raw1649step1 = -raw1649step0 := by apply Matrix.ext; change ∀ i j, raw1649step1 i j = -(raw1649step0 i j); unfold raw1649step1 raw1649step0; decide +kernel
      have hl : raw1649step1Labels = raw1649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1649step1 raw1649step1Labels = mixedMoment B raw1649step2 raw1649step2Labels := by
      have ha : raw1649step2 = raw1649step1 := by apply Matrix.ext; unfold raw1649step2 raw1649step1; decide +kernel
      have hl : raw1649step1Labels = labelEmbedding1 ∘ raw1649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1649step1 raw1649step1Labels raw1649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1921 node1921Labels := by rfl

theorem canonical1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1650 raw1650Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw1650 raw1650Labels = mixedMoment B raw1650step0 raw1650step0Labels := by
      have ha : raw1650step0 = (fun i j => raw1650 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1650step0 raw1650; decide +kernel
      have hl : raw1650step0Labels = raw1650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1650 raw1650Labels permutation152 permutation4
    mixedMoment B raw1650step0 raw1650step0Labels = mixedMoment B raw1650step1 raw1650step1Labels := by
      have ha : raw1650step1 = raw1650step0 := by apply Matrix.ext; unfold raw1650step1 raw1650step0; decide +kernel
      have hl : raw1650step0Labels = labelEmbedding7 ∘ raw1650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1650step0 raw1650step0Labels raw1650step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

theorem canonical1651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1651 raw1651Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw1651 raw1651Labels = mixedMoment B raw1651step0 raw1651step0Labels := by
      have ha : raw1651step0 = (fun i j => raw1651 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1651step0 raw1651; decide +kernel
      have hl : raw1651step0Labels = raw1651Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1651 raw1651Labels permutation152 permutation4
    _ = mixedMoment B node1901 node1901Labels := by rfl

theorem canonical1652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1652 raw1652Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw1652 raw1652Labels = mixedMoment B raw1652step0 raw1652step0Labels := by
      have ha : raw1652step0 = (fun i j => raw1652 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1652step0 raw1652; decide +kernel
      have hl : raw1652step0Labels = raw1652Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1652 raw1652Labels permutation152 permutation6
    mixedMoment B raw1652step0 raw1652step0Labels = mixedMoment B raw1652step1 raw1652step1Labels := by
      have ha : raw1652step1 = -raw1652step0 := by apply Matrix.ext; change ∀ i j, raw1652step1 i j = -(raw1652step0 i j); unfold raw1652step1 raw1652step0; decide +kernel
      have hl : raw1652step1Labels = raw1652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1652step1 raw1652step1Labels = mixedMoment B raw1652step2 raw1652step2Labels := by
      have ha : raw1652step2 = raw1652step1 := by apply Matrix.ext; unfold raw1652step2 raw1652step1; decide +kernel
      have hl : raw1652step1Labels = labelEmbedding1 ∘ raw1652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1652step1 raw1652step1Labels raw1652step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1941 node1941Labels := by rfl

theorem canonical1662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1662 raw1662Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw1662 raw1662Labels = mixedMoment B raw1662step0 raw1662step0Labels := by
      have ha : raw1662step0 = (fun i j => raw1662 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1662step0 raw1662; decide +kernel
      have hl : raw1662step0Labels = raw1662Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1662 raw1662Labels permutation32 permutation4
    mixedMoment B raw1662step0 raw1662step0Labels = mixedMoment B raw1662step1 raw1662step1Labels := by
      have ha : raw1662step1 = raw1662step0 := by apply Matrix.ext; unfold raw1662step1 raw1662step0; decide +kernel
      have hl : raw1662step0Labels = labelEmbedding7 ∘ raw1662step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1662step0 raw1662step0Labels raw1662step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

theorem canonical1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1663 raw1663Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw1663 raw1663Labels = mixedMoment B raw1663step0 raw1663step0Labels := by
      have ha : raw1663step0 = (fun i j => raw1663 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1663step0 raw1663; decide +kernel
      have hl : raw1663step0Labels = raw1663Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1663 raw1663Labels permutation32 permutation4
    _ = mixedMoment B node1917 node1917Labels := by rfl

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

theorem canonical1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1664 raw1664Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw1664 raw1664Labels = mixedMoment B raw1664step0 raw1664step0Labels := by
      have ha : raw1664step0 = (fun i j => raw1664 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1664step0 raw1664; decide +kernel
      have hl : raw1664step0Labels = raw1664Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1664 raw1664Labels permutation34 permutation6
    mixedMoment B raw1664step0 raw1664step0Labels = mixedMoment B raw1664step1 raw1664step1Labels := by
      have ha : raw1664step1 = -raw1664step0 := by apply Matrix.ext; change ∀ i j, raw1664step1 i j = -(raw1664step0 i j); unfold raw1664step1 raw1664step0; decide +kernel
      have hl : raw1664step1Labels = raw1664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1664step1 raw1664step1Labels = mixedMoment B raw1664step2 raw1664step2Labels := by
      have ha : raw1664step2 = raw1664step1 := by apply Matrix.ext; unfold raw1664step2 raw1664step1; decide +kernel
      have hl : raw1664step1Labels = labelEmbedding1 ∘ raw1664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1664step1 raw1664step1Labels raw1664step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1924 node1924Labels := by rfl

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

theorem canonical1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1674 raw1674Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw1674 raw1674Labels = mixedMoment B raw1674step0 raw1674step0Labels := by
      have ha : raw1674step0 = (fun i j => raw1674 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1674step0 raw1674; decide +kernel
      have hl : raw1674step0Labels = raw1674Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1674 raw1674Labels permutation32 permutation4
    mixedMoment B raw1674step0 raw1674step0Labels = mixedMoment B raw1674step1 raw1674step1Labels := by
      have ha : raw1674step1 = raw1674step0 := by apply Matrix.ext; unfold raw1674step1 raw1674step0; decide +kernel
      have hl : raw1674step0Labels = labelEmbedding7 ∘ raw1674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1674step0 raw1674step0Labels raw1674step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

theorem canonical1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1675 raw1675Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw1675 raw1675Labels = mixedMoment B raw1675step0 raw1675step0Labels := by
      have ha : raw1675step0 = (fun i j => raw1675 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1675step0 raw1675; decide +kernel
      have hl : raw1675step0Labels = raw1675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1675 raw1675Labels permutation32 permutation4
    _ = mixedMoment B node1929 node1929Labels := by rfl

theorem canonical1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1676 raw1676Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw1676 raw1676Labels = mixedMoment B raw1676step0 raw1676step0Labels := by
      have ha : raw1676step0 = (fun i j => raw1676 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1676step0 raw1676; decide +kernel
      have hl : raw1676step0Labels = raw1676Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1676 raw1676Labels permutation35 permutation6
    mixedMoment B raw1676step0 raw1676step0Labels = mixedMoment B raw1676step1 raw1676step1Labels := by
      have ha : raw1676step1 = -raw1676step0 := by apply Matrix.ext; change ∀ i j, raw1676step1 i j = -(raw1676step0 i j); unfold raw1676step1 raw1676step0; decide +kernel
      have hl : raw1676step1Labels = raw1676step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1676step1 raw1676step1Labels = mixedMoment B raw1676step2 raw1676step2Labels := by
      have ha : raw1676step2 = raw1676step1 := by apply Matrix.ext; unfold raw1676step2 raw1676step1; decide +kernel
      have hl : raw1676step1Labels = labelEmbedding1 ∘ raw1676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1676step1 raw1676step1Labels raw1676step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1949 node1949Labels := by rfl

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

theorem canonical2076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2076 raw2076Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw2076 raw2076Labels = mixedMoment B raw2076step0 raw2076step0Labels := by
      have ha : raw2076step0 = (fun i j => raw2076 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2076step0 raw2076; decide +kernel
      have hl : raw2076step0Labels = raw2076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2076 raw2076Labels permutation152 permutation4
    mixedMoment B raw2076step0 raw2076step0Labels = mixedMoment B raw2076step1 raw2076step1Labels := by
      have ha : raw2076step1 = raw2076step0 := by apply Matrix.ext; unfold raw2076step1 raw2076step0; decide +kernel
      have hl : raw2076step0Labels = labelEmbedding7 ∘ raw2076step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2076step0 raw2076step0Labels raw2076step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

theorem canonical2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2077 raw2077Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw2077 raw2077Labels = mixedMoment B raw2077step0 raw2077step0Labels := by
      have ha : raw2077step0 = (fun i j => raw2077 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2077step0 raw2077; decide +kernel
      have hl : raw2077step0Labels = raw2077Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2077 raw2077Labels permutation152 permutation4
    _ = mixedMoment B node2452 node2452Labels := by rfl

theorem canonical2078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2078 raw2078Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw2078 raw2078Labels = mixedMoment B raw2078step0 raw2078step0Labels := by
      have ha : raw2078step0 = (fun i j => raw2078 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2078step0 raw2078; decide +kernel
      have hl : raw2078step0Labels = raw2078Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2078 raw2078Labels permutation152 permutation6
    mixedMoment B raw2078step0 raw2078step0Labels = mixedMoment B raw2078step1 raw2078step1Labels := by
      have ha : raw2078step1 = -raw2078step0 := by apply Matrix.ext; change ∀ i j, raw2078step1 i j = -(raw2078step0 i j); unfold raw2078step1 raw2078step0; decide +kernel
      have hl : raw2078step1Labels = raw2078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2078step1 raw2078step1Labels = mixedMoment B raw2078step2 raw2078step2Labels := by
      have ha : raw2078step2 = raw2078step1 := by apply Matrix.ext; unfold raw2078step2 raw2078step1; decide +kernel
      have hl : raw2078step1Labels = labelEmbedding1 ∘ raw2078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2078step1 raw2078step1Labels raw2078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3433 node3433Labels := by rfl

theorem canonical2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2106 raw2106Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw2106 raw2106Labels = mixedMoment B raw2106step0 raw2106step0Labels := by
      have ha : raw2106step0 = (fun i j => raw2106 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2106step0 raw2106; decide +kernel
      have hl : raw2106step0Labels = raw2106Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2106 raw2106Labels permutation32 permutation4
    mixedMoment B raw2106step0 raw2106step0Labels = mixedMoment B raw2106step1 raw2106step1Labels := by
      have ha : raw2106step1 = raw2106step0 := by apply Matrix.ext; unfold raw2106step1 raw2106step0; decide +kernel
      have hl : raw2106step0Labels = labelEmbedding7 ∘ raw2106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2106step0 raw2106step0Labels raw2106step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2107 raw2107Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw2107 raw2107Labels = mixedMoment B raw2107step0 raw2107step0Labels := by
      have ha : raw2107step0 = (fun i j => raw2107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2107step0 raw2107; decide +kernel
      have hl : raw2107step0Labels = raw2107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2107 raw2107Labels permutation32 permutation4
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2108 raw2108Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw2108 raw2108Labels = mixedMoment B raw2108step0 raw2108step0Labels := by
      have ha : raw2108step0 = (fun i j => raw2108 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2108step0 raw2108; decide +kernel
      have hl : raw2108step0Labels = raw2108Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2108 raw2108Labels permutation34 permutation6
    mixedMoment B raw2108step0 raw2108step0Labels = mixedMoment B raw2108step1 raw2108step1Labels := by
      have ha : raw2108step1 = -raw2108step0 := by apply Matrix.ext; change ∀ i j, raw2108step1 i j = -(raw2108step0 i j); unfold raw2108step1 raw2108step0; decide +kernel
      have hl : raw2108step1Labels = raw2108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2108step1 raw2108step1Labels = mixedMoment B raw2108step2 raw2108step2Labels := by
      have ha : raw2108step2 = raw2108step1 := by apply Matrix.ext; unfold raw2108step2 raw2108step1; decide +kernel
      have hl : raw2108step1Labels = labelEmbedding1 ∘ raw2108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2108step1 raw2108step1Labels raw2108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2109 raw2109Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw2109 raw2109Labels = mixedMoment B raw2109step0 raw2109step0Labels := by
      have ha : raw2109step0 = (fun i j => raw2109 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2109step0 raw2109; decide +kernel
      have hl : raw2109step0Labels = raw2109Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2109 raw2109Labels permutation32 permutation4
    mixedMoment B raw2109step0 raw2109step0Labels = mixedMoment B raw2109step1 raw2109step1Labels := by
      have ha : raw2109step1 = raw2109step0 := by apply Matrix.ext; unfold raw2109step1 raw2109step0; decide +kernel
      have hl : raw2109step0Labels = labelEmbedding7 ∘ raw2109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2109step0 raw2109step0Labels raw2109step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2110 raw2110Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw2110 raw2110Labels = mixedMoment B raw2110step0 raw2110step0Labels := by
      have ha : raw2110step0 = (fun i j => raw2110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2110step0 raw2110; decide +kernel
      have hl : raw2110step0Labels = raw2110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2110 raw2110Labels permutation32 permutation4
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical2111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2111 raw2111Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw2111 raw2111Labels = mixedMoment B raw2111step0 raw2111step0Labels := by
      have ha : raw2111step0 = (fun i j => raw2111 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2111step0 raw2111; decide +kernel
      have hl : raw2111step0Labels = raw2111Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2111 raw2111Labels permutation32 permutation6
    mixedMoment B raw2111step0 raw2111step0Labels = mixedMoment B raw2111step1 raw2111step1Labels := by
      have ha : raw2111step1 = -raw2111step0 := by apply Matrix.ext; change ∀ i j, raw2111step1 i j = -(raw2111step0 i j); unfold raw2111step1 raw2111step0; decide +kernel
      have hl : raw2111step1Labels = raw2111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2111step1 raw2111step1Labels = mixedMoment B raw2111step2 raw2111step2Labels := by
      have ha : raw2111step2 = raw2111step1 := by apply Matrix.ext; unfold raw2111step2 raw2111step1; decide +kernel
      have hl : raw2111step1Labels = labelEmbedding1 ∘ raw2111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2111step1 raw2111step1Labels raw2111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29682 raw29682Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw29682 raw29682Labels = mixedMoment B raw29682step0 raw29682step0Labels := by
      have hz : ∀ j, raw29682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29682step0 = (fun i j => raw29682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29682step0 raw29682; decide +kernel
      have hl : raw29682step0Labels = raw29682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29682 raw29682Labels permutation434 hz
    mixedMoment B raw29682step0 raw29682step0Labels = mixedMoment B raw29682step1 raw29682step1Labels := by
      have ha : raw29682step1 = (fun i j => raw29682step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29682step1 raw29682step0; decide +kernel
      have hl : raw29682step1Labels = raw29682step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29682step0 raw29682step0Labels permutation32 permutation6
    mixedMoment B raw29682step1 raw29682step1Labels = mixedMoment B raw29682step2 raw29682step2Labels := by
      have ha : raw29682step2 = raw29682step1 := by apply Matrix.ext; unfold raw29682step2 raw29682step1; decide +kernel
      have hl : raw29682step1Labels = labelEmbedding9 ∘ raw29682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29682step1 raw29682step1Labels raw29682step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical29683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29683 raw29683Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29683 raw29683Labels = mixedMoment B raw29683step0 raw29683step0Labels := by
      have hz : ∀ j, raw29683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29683step0 = (fun i j => raw29683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29683step0 raw29683; decide +kernel
      have hl : raw29683step0Labels = raw29683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29683 raw29683Labels permutation434 hz
    mixedMoment B raw29683step0 raw29683step0Labels = mixedMoment B raw29683step1 raw29683step1Labels := by
      have ha : raw29683step1 = (fun i j => raw29683step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29683step1 raw29683step0; decide +kernel
      have hl : raw29683step1Labels = raw29683step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29683step0 raw29683step0Labels permutation32 permutation6
    mixedMoment B raw29683step1 raw29683step1Labels = mixedMoment B raw29683step2 raw29683step2Labels := by
      have ha : raw29683step2 = raw29683step1 := by apply Matrix.ext; unfold raw29683step2 raw29683step1; decide +kernel
      have hl : raw29683step1Labels = labelEmbedding9 ∘ raw29683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29683step1 raw29683step1Labels raw29683step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical29690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29690 raw29690Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw29690 raw29690Labels = mixedMoment B raw29690step0 raw29690step0Labels := by
      have hz : ∀ j, raw29690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29690step0 = (fun i j => raw29690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29690step0 raw29690; decide +kernel
      have hl : raw29690step0Labels = raw29690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29690 raw29690Labels permutation434 hz
    mixedMoment B raw29690step0 raw29690step0Labels = mixedMoment B raw29690step1 raw29690step1Labels := by
      have hz : ∀ j, raw29690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29690step1 = (fun i j => raw29690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29690step1 raw29690step0; decide +kernel
      have hl : raw29690step1Labels = raw29690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29690step0 raw29690step0Labels permutation80 hz
    mixedMoment B raw29690step1 raw29690step1Labels = mixedMoment B raw29690step2 raw29690step2Labels := by
      have ha : raw29690step2 = (fun i j => raw29690step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29690step2 raw29690step1; decide +kernel
      have hl : raw29690step2Labels = raw29690step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29690step1 raw29690step1Labels permutation9 permutation6
    mixedMoment B raw29690step2 raw29690step2Labels = mixedMoment B raw29690step3 raw29690step3Labels := by
      have ha : raw29690step3 = raw29690step2 := by apply Matrix.ext; unfold raw29690step3 raw29690step2; decide +kernel
      have hl : raw29690step2Labels = labelEmbedding9 ∘ raw29690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29690step2 raw29690step2Labels raw29690step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical29691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29691 raw29691Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29691 raw29691Labels = mixedMoment B raw29691step0 raw29691step0Labels := by
      have hz : ∀ j, raw29691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29691step0 = (fun i j => raw29691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29691step0 raw29691; decide +kernel
      have hl : raw29691step0Labels = raw29691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29691 raw29691Labels permutation434 hz
    mixedMoment B raw29691step0 raw29691step0Labels = mixedMoment B raw29691step1 raw29691step1Labels := by
      have hz : ∀ j, raw29691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29691step1 = (fun i j => raw29691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29691step1 raw29691step0; decide +kernel
      have hl : raw29691step1Labels = raw29691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29691step0 raw29691step0Labels permutation80 hz
    mixedMoment B raw29691step1 raw29691step1Labels = mixedMoment B raw29691step2 raw29691step2Labels := by
      have ha : raw29691step2 = (fun i j => raw29691step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29691step2 raw29691step1; decide +kernel
      have hl : raw29691step2Labels = raw29691step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29691step1 raw29691step1Labels permutation9 permutation6
    mixedMoment B raw29691step2 raw29691step2Labels = mixedMoment B raw29691step3 raw29691step3Labels := by
      have ha : raw29691step3 = raw29691step2 := by apply Matrix.ext; unfold raw29691step3 raw29691step2; decide +kernel
      have hl : raw29691step2Labels = labelEmbedding9 ∘ raw29691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29691step2 raw29691step2Labels raw29691step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30173 raw30173Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw30173 raw30173Labels = mixedMoment B raw30173step0 raw30173step0Labels := by
      have ha : raw30173step0 = (fun i j => raw30173 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30173step0 raw30173; decide +kernel
      have hl : raw30173step0Labels = raw30173Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30173 raw30173Labels permutation159 permutation6
    mixedMoment B raw30173step0 raw30173step0Labels = mixedMoment B raw30173step1 raw30173step1Labels := by
      have ha : raw30173step1 = raw30173step0 := by apply Matrix.ext; unfold raw30173step1 raw30173step0; decide +kernel
      have hl : raw30173step0Labels = labelEmbedding9 ∘ raw30173step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30173step0 raw30173step0Labels raw30173step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical30174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30174 raw30174Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw30174 raw30174Labels = mixedMoment B raw30174step0 raw30174step0Labels := by
      have ha : raw30174step0 = (fun i j => raw30174 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30174step0 raw30174; decide +kernel
      have hl : raw30174step0Labels = raw30174Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30174 raw30174Labels permutation159 permutation6
    mixedMoment B raw30174step0 raw30174step0Labels = mixedMoment B raw30174step1 raw30174step1Labels := by
      have ha : raw30174step1 = raw30174step0 := by apply Matrix.ext; unfold raw30174step1 raw30174step0; decide +kernel
      have hl : raw30174step0Labels = labelEmbedding9 ∘ raw30174step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30174step0 raw30174step0Labels raw30174step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical237
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30363 raw30363Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw30363 raw30363Labels = mixedMoment B raw30363step0 raw30363step0Labels := by
      have hz : ∀ j, raw30363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30363step0 = (fun i j => raw30363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30363step0 raw30363; decide +kernel
      have hl : raw30363step0Labels = raw30363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30363 raw30363Labels permutation434 hz
    mixedMoment B raw30363step0 raw30363step0Labels = mixedMoment B raw30363step1 raw30363step1Labels := by
      have ha : raw30363step1 = (fun i j => raw30363step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30363step1 raw30363step0; decide +kernel
      have hl : raw30363step1Labels = raw30363step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30363step0 raw30363step0Labels permutation33 permutation6
    mixedMoment B raw30363step1 raw30363step1Labels = mixedMoment B raw30363step2 raw30363step2Labels := by
      have ha : raw30363step2 = raw30363step1 := by apply Matrix.ext; unfold raw30363step2 raw30363step1; decide +kernel
      have hl : raw30363step1Labels = labelEmbedding9 ∘ raw30363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30363step1 raw30363step1Labels raw30363step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical30365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30365 raw30365Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw30365 raw30365Labels = mixedMoment B raw30365step0 raw30365step0Labels := by
      have hz : ∀ j, raw30365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30365step0 = (fun i j => raw30365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30365step0 raw30365; decide +kernel
      have hl : raw30365step0Labels = raw30365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30365 raw30365Labels permutation434 hz
    mixedMoment B raw30365step0 raw30365step0Labels = mixedMoment B raw30365step1 raw30365step1Labels := by
      have ha : raw30365step1 = (fun i j => raw30365step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30365step1 raw30365step0; decide +kernel
      have hl : raw30365step1Labels = raw30365step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30365step0 raw30365step0Labels permutation36 permutation4
    mixedMoment B raw30365step1 raw30365step1Labels = mixedMoment B raw30365step2 raw30365step2Labels := by
      have ha : raw30365step2 = -raw30365step1 := by apply Matrix.ext; change ∀ i j, raw30365step2 i j = -(raw30365step1 i j); unfold raw30365step2 raw30365step1; decide +kernel
      have hl : raw30365step2Labels = raw30365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30365step2 raw30365step2Labels = mixedMoment B raw30365step3 raw30365step3Labels := by
      have ha : raw30365step3 = raw30365step2 := by apply Matrix.ext; unfold raw30365step3 raw30365step2; decide +kernel
      have hl : raw30365step2Labels = labelEmbedding7 ∘ raw30365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30365step2 raw30365step2Labels raw30365step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

theorem canonical30370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30370 raw30370Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw30370 raw30370Labels = mixedMoment B raw30370step0 raw30370step0Labels := by
      have ha : raw30370step0 = (fun i j => raw30370 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30370step0 raw30370; decide +kernel
      have hl : raw30370step0Labels = raw30370Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30370 raw30370Labels permutation153 permutation6
    mixedMoment B raw30370step0 raw30370step0Labels = mixedMoment B raw30370step1 raw30370step1Labels := by
      have ha : raw30370step1 = raw30370step0 := by apply Matrix.ext; unfold raw30370step1 raw30370step0; decide +kernel
      have hl : raw30370step0Labels = labelEmbedding9 ∘ raw30370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30370step0 raw30370step0Labels raw30370step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

theorem canonical30375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30375 raw30375Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw30375 raw30375Labels = mixedMoment B raw30375step0 raw30375step0Labels := by
      have hz : ∀ j, raw30375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30375step0 = (fun i j => raw30375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30375step0 raw30375; decide +kernel
      have hl : raw30375step0Labels = raw30375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30375 raw30375Labels permutation434 hz
    mixedMoment B raw30375step0 raw30375step0Labels = mixedMoment B raw30375step1 raw30375step1Labels := by
      have ha : raw30375step1 = (fun i j => raw30375step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30375step1 raw30375step0; decide +kernel
      have hl : raw30375step1Labels = raw30375step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30375step0 raw30375step0Labels permutation33 permutation6
    mixedMoment B raw30375step1 raw30375step1Labels = mixedMoment B raw30375step2 raw30375step2Labels := by
      have ha : raw30375step2 = raw30375step1 := by apply Matrix.ext; unfold raw30375step2 raw30375step1; decide +kernel
      have hl : raw30375step1Labels = labelEmbedding9 ∘ raw30375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30375step1 raw30375step1Labels raw30375step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

theorem canonical30381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30381 raw30381Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw30381 raw30381Labels = mixedMoment B raw30381step0 raw30381step0Labels := by
      have hz : ∀ j, raw30381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30381step0 = (fun i j => raw30381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30381step0 raw30381; decide +kernel
      have hl : raw30381step0Labels = raw30381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30381 raw30381Labels permutation434 hz
    mixedMoment B raw30381step0 raw30381step0Labels = mixedMoment B raw30381step1 raw30381step1Labels := by
      have ha : raw30381step1 = (fun i j => raw30381step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30381step1 raw30381step0; decide +kernel
      have hl : raw30381step1Labels = raw30381step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30381step0 raw30381step0Labels permutation33 permutation6
    mixedMoment B raw30381step1 raw30381step1Labels = mixedMoment B raw30381step2 raw30381step2Labels := by
      have ha : raw30381step2 = raw30381step1 := by apply Matrix.ext; unfold raw30381step2 raw30381step1; decide +kernel
      have hl : raw30381step1Labels = labelEmbedding9 ∘ raw30381step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30381step1 raw30381step1Labels raw30381step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical238
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30541 raw30541Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw30541 raw30541Labels = mixedMoment B raw30541step0 raw30541step0Labels := by
      have hz : ∀ j, raw30541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30541step0 = (fun i j => raw30541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30541step0 raw30541; decide +kernel
      have hl : raw30541step0Labels = raw30541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30541 raw30541Labels permutation434 hz
    mixedMoment B raw30541step0 raw30541step0Labels = mixedMoment B raw30541step1 raw30541step1Labels := by
      have ha : raw30541step1 = (fun i j => raw30541step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30541step1 raw30541step0; decide +kernel
      have hl : raw30541step1Labels = raw30541step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30541step0 raw30541step0Labels permutation32 permutation6
    mixedMoment B raw30541step1 raw30541step1Labels = mixedMoment B raw30541step2 raw30541step2Labels := by
      have ha : raw30541step2 = raw30541step1 := by apply Matrix.ext; unfold raw30541step2 raw30541step1; decide +kernel
      have hl : raw30541step1Labels = labelEmbedding9 ∘ raw30541step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30541step1 raw30541step1Labels raw30541step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

theorem canonical30545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30545 raw30545Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw30545 raw30545Labels = mixedMoment B raw30545step0 raw30545step0Labels := by
      have ha : raw30545step0 = (fun i j => raw30545 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30545step0 raw30545; decide +kernel
      have hl : raw30545step0Labels = raw30545Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30545 raw30545Labels permutation152 permutation6
    mixedMoment B raw30545step0 raw30545step0Labels = mixedMoment B raw30545step1 raw30545step1Labels := by
      have ha : raw30545step1 = raw30545step0 := by apply Matrix.ext; unfold raw30545step1 raw30545step0; decide +kernel
      have hl : raw30545step0Labels = labelEmbedding9 ∘ raw30545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30545step0 raw30545step0Labels raw30545step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

theorem canonical30547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30547 raw30547Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw30547 raw30547Labels = mixedMoment B raw30547step0 raw30547step0Labels := by
      have hz : ∀ j, raw30547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30547step0 = (fun i j => raw30547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30547step0 raw30547; decide +kernel
      have hl : raw30547step0Labels = raw30547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30547 raw30547Labels permutation434 hz
    mixedMoment B raw30547step0 raw30547step0Labels = mixedMoment B raw30547step1 raw30547step1Labels := by
      have ha : raw30547step1 = (fun i j => raw30547step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30547step1 raw30547step0; decide +kernel
      have hl : raw30547step1Labels = raw30547step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30547step0 raw30547step0Labels permutation33 permutation6
    mixedMoment B raw30547step1 raw30547step1Labels = mixedMoment B raw30547step2 raw30547step2Labels := by
      have ha : raw30547step2 = raw30547step1 := by apply Matrix.ext; unfold raw30547step2 raw30547step1; decide +kernel
      have hl : raw30547step1Labels = labelEmbedding9 ∘ raw30547step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30547step1 raw30547step1Labels raw30547step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical30548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30548 raw30548Labels = mixedMoment B node4745 node4745Labels := by
  calc
    mixedMoment B raw30548 raw30548Labels = mixedMoment B raw30548step0 raw30548step0Labels := by
      have hz : ∀ j, raw30548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30548step0 = (fun i j => raw30548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30548step0 raw30548; decide +kernel
      have hl : raw30548step0Labels = raw30548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30548 raw30548Labels permutation434 hz
    mixedMoment B raw30548step0 raw30548step0Labels = mixedMoment B raw30548step1 raw30548step1Labels := by
      have ha : raw30548step1 = (fun i j => raw30548step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30548step1 raw30548step0; decide +kernel
      have hl : raw30548step1Labels = raw30548step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30548step0 raw30548step0Labels permutation32 permutation6
    mixedMoment B raw30548step1 raw30548step1Labels = mixedMoment B raw30548step2 raw30548step2Labels := by
      have ha : raw30548step2 = raw30548step1 := by apply Matrix.ext; unfold raw30548step2 raw30548step1; decide +kernel
      have hl : raw30548step1Labels = labelEmbedding9 ∘ raw30548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30548step1 raw30548step1Labels raw30548step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4745 node4745Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30699 raw30699Labels = mixedMoment B node4753 node4753Labels := by
  calc
    mixedMoment B raw30699 raw30699Labels = mixedMoment B raw30699step0 raw30699step0Labels := by
      have hz : ∀ j, raw30699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30699step0 = (fun i j => raw30699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30699step0 raw30699; decide +kernel
      have hl : raw30699step0Labels = raw30699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30699 raw30699Labels permutation434 hz
    mixedMoment B raw30699step0 raw30699step0Labels = mixedMoment B raw30699step1 raw30699step1Labels := by
      have hz : ∀ j, raw30699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30699step1 = (fun i j => raw30699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30699step1 raw30699step0; decide +kernel
      have hl : raw30699step1Labels = raw30699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30699step0 raw30699step0Labels permutation80 hz
    mixedMoment B raw30699step1 raw30699step1Labels = mixedMoment B raw30699step2 raw30699step2Labels := by
      have ha : raw30699step2 = (fun i j => raw30699step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30699step2 raw30699step1; decide +kernel
      have hl : raw30699step2Labels = raw30699step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30699step1 raw30699step1Labels permutation9 permutation4
    mixedMoment B raw30699step2 raw30699step2Labels = mixedMoment B raw30699step3 raw30699step3Labels := by
      have ha : raw30699step3 = -raw30699step2 := by apply Matrix.ext; change ∀ i j, raw30699step3 i j = -(raw30699step2 i j); unfold raw30699step3 raw30699step2; decide +kernel
      have hl : raw30699step3Labels = raw30699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30699step3 raw30699step3Labels = mixedMoment B raw30699step4 raw30699step4Labels := by
      have ha : raw30699step4 = raw30699step3 := by apply Matrix.ext; unfold raw30699step4 raw30699step3; decide +kernel
      have hl : raw30699step3Labels = labelEmbedding7 ∘ raw30699step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30699step3 raw30699step3Labels raw30699step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4753 node4753Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30833 raw30833Labels = mixedMoment B node4711 node4711Labels := by
  calc
    mixedMoment B raw30833 raw30833Labels = mixedMoment B raw30833step0 raw30833step0Labels := by
      have ha : raw30833step0 = (fun i j => raw30833 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30833step0 raw30833; decide +kernel
      have hl : raw30833step0Labels = raw30833Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30833 raw30833Labels permutation158 permutation4
    mixedMoment B raw30833step0 raw30833step0Labels = mixedMoment B raw30833step1 raw30833step1Labels := by
      have ha : raw30833step1 = -raw30833step0 := by apply Matrix.ext; change ∀ i j, raw30833step1 i j = -(raw30833step0 i j); unfold raw30833step1 raw30833step0; decide +kernel
      have hl : raw30833step1Labels = raw30833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30833step1 raw30833step1Labels = mixedMoment B raw30833step2 raw30833step2Labels := by
      have ha : raw30833step2 = raw30833step1 := by apply Matrix.ext; unfold raw30833step2 raw30833step1; decide +kernel
      have hl : raw30833step1Labels = labelEmbedding7 ∘ raw30833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30833step1 raw30833step1Labels raw30833step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4711 node4711Labels := by rfl

theorem canonical30836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30836 raw30836Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw30836 raw30836Labels = mixedMoment B raw30836step0 raw30836step0Labels := by
      have hz : ∀ j, raw30836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30836step0 = (fun i j => raw30836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30836step0 raw30836; decide +kernel
      have hl : raw30836step0Labels = raw30836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30836 raw30836Labels permutation434 hz
    mixedMoment B raw30836step0 raw30836step0Labels = mixedMoment B raw30836step1 raw30836step1Labels := by
      have hz : ∀ j, raw30836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30836step1 = (fun i j => raw30836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30836step1 raw30836step0; decide +kernel
      have hl : raw30836step1Labels = raw30836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30836step0 raw30836step0Labels permutation80 hz
    mixedMoment B raw30836step1 raw30836step1Labels = mixedMoment B raw30836step2 raw30836step2Labels := by
      have hz : ∀ i, raw30836step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw30836step2 = (fun i j => raw30836step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw30836step2 raw30836step1; decide +kernel
      have hl : raw30836step2Labels = (fun j => raw30836step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30836step1 raw30836step1Labels permutation2 hz
    mixedMoment B raw30836step2 raw30836step2Labels = mixedMoment B raw30836step3 raw30836step3Labels := by
      have ha : raw30836step3 = -raw30836step2 := by apply Matrix.ext; change ∀ i j, raw30836step3 i j = -(raw30836step2 i j); unfold raw30836step3 raw30836step2; decide +kernel
      have hl : raw30836step3Labels = raw30836step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30836step3 raw30836step3Labels = mixedMoment B raw30836step4 raw30836step4Labels := by
      have ha : raw30836step4 = raw30836step3 := by apply Matrix.ext; unfold raw30836step4 raw30836step3; decide +kernel
      have hl : raw30836step3Labels = labelEmbedding3 ∘ raw30836step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30836step3 raw30836step3Labels raw30836step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4082 node4082Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30922 raw30922Labels = mixedMoment B node4646 node4646Labels := by
  calc
    mixedMoment B raw30922 raw30922Labels = mixedMoment B raw30922step0 raw30922step0Labels := by
      have hz : ∀ j, raw30922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30922step0 = (fun i j => raw30922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30922step0 raw30922; decide +kernel
      have hl : raw30922step0Labels = raw30922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30922 raw30922Labels permutation434 hz
    mixedMoment B raw30922step0 raw30922step0Labels = mixedMoment B raw30922step1 raw30922step1Labels := by
      have ha : raw30922step1 = (fun i j => raw30922step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30922step1 raw30922step0; decide +kernel
      have hl : raw30922step1Labels = raw30922step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30922step0 raw30922step0Labels permutation32 permutation4
    mixedMoment B raw30922step1 raw30922step1Labels = mixedMoment B raw30922step2 raw30922step2Labels := by
      have ha : raw30922step2 = -raw30922step1 := by apply Matrix.ext; change ∀ i j, raw30922step2 i j = -(raw30922step1 i j); unfold raw30922step2 raw30922step1; decide +kernel
      have hl : raw30922step2Labels = raw30922step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30922step2 raw30922step2Labels = mixedMoment B raw30922step3 raw30922step3Labels := by
      have ha : raw30922step3 = raw30922step2 := by apply Matrix.ext; unfold raw30922step3 raw30922step2; decide +kernel
      have hl : raw30922step2Labels = labelEmbedding7 ∘ raw30922step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30922step2 raw30922step2Labels raw30922step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4646 node4646Labels := by rfl

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

theorem canonical31434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31434 raw31434Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw31434 raw31434Labels = mixedMoment B raw31434step0 raw31434step0Labels := by
      have hz : ∀ j, raw31434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31434step0 = (fun i j => raw31434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31434step0 raw31434; decide +kernel
      have hl : raw31434step0Labels = raw31434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31434 raw31434Labels permutation434 hz
    mixedMoment B raw31434step0 raw31434step0Labels = mixedMoment B raw31434step1 raw31434step1Labels := by
      have ha : raw31434step1 = (fun i j => raw31434step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31434step1 raw31434step0; decide +kernel
      have hl : raw31434step1Labels = raw31434step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31434step0 raw31434step0Labels permutation33 permutation4
    mixedMoment B raw31434step1 raw31434step1Labels = mixedMoment B raw31434step2 raw31434step2Labels := by
      have ha : raw31434step2 = -raw31434step1 := by apply Matrix.ext; change ∀ i j, raw31434step2 i j = -(raw31434step1 i j); unfold raw31434step2 raw31434step1; decide +kernel
      have hl : raw31434step2Labels = raw31434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31434step2 raw31434step2Labels = mixedMoment B raw31434step3 raw31434step3Labels := by
      have ha : raw31434step3 = raw31434step2 := by apply Matrix.ext; unfold raw31434step3 raw31434step2; decide +kernel
      have hl : raw31434step2Labels = labelEmbedding7 ∘ raw31434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31434step2 raw31434step2Labels raw31434step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical248
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31867 raw31867Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw31867 raw31867Labels = mixedMoment B raw31867step0 raw31867step0Labels := by
      have hz : ∀ j, raw31867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31867step0 = (fun i j => raw31867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31867step0 raw31867; decide +kernel
      have hl : raw31867step0Labels = raw31867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31867 raw31867Labels permutation434 hz
    mixedMoment B raw31867step0 raw31867step0Labels = mixedMoment B raw31867step1 raw31867step1Labels := by
      have ha : raw31867step1 = (fun i j => raw31867step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31867step1 raw31867step0; decide +kernel
      have hl : raw31867step1Labels = raw31867step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31867step0 raw31867step0Labels permutation36 permutation4
    mixedMoment B raw31867step1 raw31867step1Labels = mixedMoment B raw31867step2 raw31867step2Labels := by
      have ha : raw31867step2 = -raw31867step1 := by apply Matrix.ext; change ∀ i j, raw31867step2 i j = -(raw31867step1 i j); unfold raw31867step2 raw31867step1; decide +kernel
      have hl : raw31867step2Labels = raw31867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31867step2 raw31867step2Labels = mixedMoment B raw31867step3 raw31867step3Labels := by
      have ha : raw31867step3 = raw31867step2 := by apply Matrix.ext; unfold raw31867step3 raw31867step2; decide +kernel
      have hl : raw31867step2Labels = labelEmbedding7 ∘ raw31867step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31867step2 raw31867step2Labels raw31867step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

theorem canonical31868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31868 raw31868Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw31868 raw31868Labels = mixedMoment B raw31868step0 raw31868step0Labels := by
      have hz : ∀ j, raw31868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31868step0 = (fun i j => raw31868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31868step0 raw31868; decide +kernel
      have hl : raw31868step0Labels = raw31868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31868 raw31868Labels permutation434 hz
    mixedMoment B raw31868step0 raw31868step0Labels = mixedMoment B raw31868step1 raw31868step1Labels := by
      have ha : raw31868step1 = (fun i j => raw31868step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31868step1 raw31868step0; decide +kernel
      have hl : raw31868step1Labels = raw31868step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31868step0 raw31868step0Labels permutation36 permutation4
    mixedMoment B raw31868step1 raw31868step1Labels = mixedMoment B raw31868step2 raw31868step2Labels := by
      have ha : raw31868step2 = -raw31868step1 := by apply Matrix.ext; change ∀ i j, raw31868step2 i j = -(raw31868step1 i j); unfold raw31868step2 raw31868step1; decide +kernel
      have hl : raw31868step2Labels = raw31868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31868step2 raw31868step2Labels = mixedMoment B raw31868step3 raw31868step3Labels := by
      have ha : raw31868step3 = raw31868step2 := by apply Matrix.ext; unfold raw31868step3 raw31868step2; decide +kernel
      have hl : raw31868step2Labels = labelEmbedding7 ∘ raw31868step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31868step2 raw31868step2Labels raw31868step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

theorem canonical31869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31869 raw31869Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw31869 raw31869Labels = mixedMoment B raw31869step0 raw31869step0Labels := by
      have ha : raw31869step0 = (fun i j => raw31869 (permutation162 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31869step0 raw31869; decide +kernel
      have hl : raw31869step0Labels = raw31869Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31869 raw31869Labels permutation162 permutation4
    mixedMoment B raw31869step0 raw31869step0Labels = mixedMoment B raw31869step1 raw31869step1Labels := by
      have ha : raw31869step1 = -raw31869step0 := by apply Matrix.ext; change ∀ i j, raw31869step1 i j = -(raw31869step0 i j); unfold raw31869step1 raw31869step0; decide +kernel
      have hl : raw31869step1Labels = raw31869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31869step1 raw31869step1Labels = mixedMoment B raw31869step2 raw31869step2Labels := by
      have ha : raw31869step2 = raw31869step1 := by apply Matrix.ext; unfold raw31869step2 raw31869step1; decide +kernel
      have hl : raw31869step1Labels = labelEmbedding7 ∘ raw31869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31869step1 raw31869step1Labels raw31869step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

theorem canonical31870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31870 raw31870Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw31870 raw31870Labels = mixedMoment B raw31870step0 raw31870step0Labels := by
      have ha : raw31870step0 = (fun i j => raw31870 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31870step0 raw31870; decide +kernel
      have hl : raw31870step0Labels = raw31870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31870 raw31870Labels permutation153 permutation4
    mixedMoment B raw31870step0 raw31870step0Labels = mixedMoment B raw31870step1 raw31870step1Labels := by
      have ha : raw31870step1 = -raw31870step0 := by apply Matrix.ext; change ∀ i j, raw31870step1 i j = -(raw31870step0 i j); unfold raw31870step1 raw31870step0; decide +kernel
      have hl : raw31870step1Labels = raw31870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31870step1 raw31870step1Labels = mixedMoment B raw31870step2 raw31870step2Labels := by
      have ha : raw31870step2 = raw31870step1 := by apply Matrix.ext; unfold raw31870step2 raw31870step1; decide +kernel
      have hl : raw31870step1Labels = labelEmbedding7 ∘ raw31870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31870step1 raw31870step1Labels raw31870step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

theorem canonical31871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31871 raw31871Labels = mixedMoment B node4640 node4640Labels := by
  calc
    mixedMoment B raw31871 raw31871Labels = mixedMoment B raw31871step0 raw31871step0Labels := by
      have ha : raw31871step0 = (fun i j => raw31871 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31871step0 raw31871; decide +kernel
      have hl : raw31871step0Labels = raw31871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31871 raw31871Labels permutation153 permutation4
    mixedMoment B raw31871step0 raw31871step0Labels = mixedMoment B raw31871step1 raw31871step1Labels := by
      have ha : raw31871step1 = -raw31871step0 := by apply Matrix.ext; change ∀ i j, raw31871step1 i j = -(raw31871step0 i j); unfold raw31871step1 raw31871step0; decide +kernel
      have hl : raw31871step1Labels = raw31871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31871step1 raw31871step1Labels = mixedMoment B raw31871step2 raw31871step2Labels := by
      have ha : raw31871step2 = raw31871step1 := by apply Matrix.ext; unfold raw31871step2 raw31871step1; decide +kernel
      have hl : raw31871step1Labels = labelEmbedding7 ∘ raw31871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31871step1 raw31871step1Labels raw31871step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4640 node4640Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31872 raw31872Labels = mixedMoment B node4745 node4745Labels := by
  calc
    mixedMoment B raw31872 raw31872Labels = mixedMoment B raw31872step0 raw31872step0Labels := by
      have hz : ∀ j, raw31872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31872step0 = (fun i j => raw31872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31872step0 raw31872; decide +kernel
      have hl : raw31872step0Labels = raw31872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31872 raw31872Labels permutation346 hz
    mixedMoment B raw31872step0 raw31872step0Labels = mixedMoment B raw31872step1 raw31872step1Labels := by
      have ha : raw31872step1 = (fun i j => raw31872step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31872step1 raw31872step0; decide +kernel
      have hl : raw31872step1Labels = raw31872step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31872step0 raw31872step0Labels permutation33 permutation6
    mixedMoment B raw31872step1 raw31872step1Labels = mixedMoment B raw31872step2 raw31872step2Labels := by
      have ha : raw31872step2 = raw31872step1 := by apply Matrix.ext; unfold raw31872step2 raw31872step1; decide +kernel
      have hl : raw31872step1Labels = labelEmbedding9 ∘ raw31872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31872step1 raw31872step1Labels raw31872step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4745 node4745Labels := by rfl

theorem canonical31873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31873 raw31873Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw31873 raw31873Labels = mixedMoment B raw31873step0 raw31873step0Labels := by
      have hz : ∀ j, raw31873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31873step0 = (fun i j => raw31873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31873step0 raw31873; decide +kernel
      have hl : raw31873step0Labels = raw31873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31873 raw31873Labels permutation434 hz
    mixedMoment B raw31873step0 raw31873step0Labels = mixedMoment B raw31873step1 raw31873step1Labels := by
      have ha : raw31873step1 = (fun i j => raw31873step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31873step1 raw31873step0; decide +kernel
      have hl : raw31873step1Labels = raw31873step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31873step0 raw31873step0Labels permutation33 permutation4
    mixedMoment B raw31873step1 raw31873step1Labels = mixedMoment B raw31873step2 raw31873step2Labels := by
      have ha : raw31873step2 = -raw31873step1 := by apply Matrix.ext; change ∀ i j, raw31873step2 i j = -(raw31873step1 i j); unfold raw31873step2 raw31873step1; decide +kernel
      have hl : raw31873step2Labels = raw31873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31873step2 raw31873step2Labels = mixedMoment B raw31873step3 raw31873step3Labels := by
      have ha : raw31873step3 = raw31873step2 := by apply Matrix.ext; unfold raw31873step3 raw31873step2; decide +kernel
      have hl : raw31873step2Labels = labelEmbedding7 ∘ raw31873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31873step2 raw31873step2Labels raw31873step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

theorem canonical31874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31874 raw31874Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw31874 raw31874Labels = mixedMoment B raw31874step0 raw31874step0Labels := by
      have hz : ∀ j, raw31874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31874step0 = (fun i j => raw31874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31874step0 raw31874; decide +kernel
      have hl : raw31874step0Labels = raw31874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31874 raw31874Labels permutation434 hz
    mixedMoment B raw31874step0 raw31874step0Labels = mixedMoment B raw31874step1 raw31874step1Labels := by
      have ha : raw31874step1 = (fun i j => raw31874step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31874step1 raw31874step0; decide +kernel
      have hl : raw31874step1Labels = raw31874step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31874step0 raw31874step0Labels permutation33 permutation4
    mixedMoment B raw31874step1 raw31874step1Labels = mixedMoment B raw31874step2 raw31874step2Labels := by
      have ha : raw31874step2 = -raw31874step1 := by apply Matrix.ext; change ∀ i j, raw31874step2 i j = -(raw31874step1 i j); unfold raw31874step2 raw31874step1; decide +kernel
      have hl : raw31874step2Labels = raw31874step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31874step2 raw31874step2Labels = mixedMoment B raw31874step3 raw31874step3Labels := by
      have ha : raw31874step3 = raw31874step2 := by apply Matrix.ext; unfold raw31874step3 raw31874step2; decide +kernel
      have hl : raw31874step2Labels = labelEmbedding7 ∘ raw31874step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31874step2 raw31874step2Labels raw31874step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

theorem canonical31875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31875 raw31875Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw31875 raw31875Labels = mixedMoment B raw31875step0 raw31875step0Labels := by
      have ha : raw31875step0 = (fun i j => raw31875 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31875step0 raw31875; decide +kernel
      have hl : raw31875step0Labels = raw31875Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31875 raw31875Labels permutation159 permutation4
    mixedMoment B raw31875step0 raw31875step0Labels = mixedMoment B raw31875step1 raw31875step1Labels := by
      have ha : raw31875step1 = -raw31875step0 := by apply Matrix.ext; change ∀ i j, raw31875step1 i j = -(raw31875step0 i j); unfold raw31875step1 raw31875step0; decide +kernel
      have hl : raw31875step1Labels = raw31875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31875step1 raw31875step1Labels = mixedMoment B raw31875step2 raw31875step2Labels := by
      have ha : raw31875step2 = raw31875step1 := by apply Matrix.ext; unfold raw31875step2 raw31875step1; decide +kernel
      have hl : raw31875step1Labels = labelEmbedding7 ∘ raw31875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31875step1 raw31875step1Labels raw31875step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

theorem canonical31876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31876 raw31876Labels = mixedMoment B node4305 node4305Labels := by
  calc
    mixedMoment B raw31876 raw31876Labels = mixedMoment B raw31876step0 raw31876step0Labels := by
      have hz : ∀ j, raw31876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31876step0 = (fun i j => raw31876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31876step0 raw31876; decide +kernel
      have hl : raw31876step0Labels = raw31876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31876 raw31876Labels permutation434 hz
    mixedMoment B raw31876step0 raw31876step0Labels = mixedMoment B raw31876step1 raw31876step1Labels := by
      have ha : raw31876step1 = (fun i j => raw31876step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31876step1 raw31876step0; decide +kernel
      have hl : raw31876step1Labels = raw31876step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31876step0 raw31876step0Labels permutation32 permutation4
    mixedMoment B raw31876step1 raw31876step1Labels = mixedMoment B raw31876step2 raw31876step2Labels := by
      have ha : raw31876step2 = -raw31876step1 := by apply Matrix.ext; change ∀ i j, raw31876step2 i j = -(raw31876step1 i j); unfold raw31876step2 raw31876step1; decide +kernel
      have hl : raw31876step2Labels = raw31876step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31876step2 raw31876step2Labels = mixedMoment B raw31876step3 raw31876step3Labels := by
      have ha : raw31876step3 = raw31876step2 := by apply Matrix.ext; unfold raw31876step3 raw31876step2; decide +kernel
      have hl : raw31876step2Labels = labelEmbedding7 ∘ raw31876step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31876step2 raw31876step2Labels raw31876step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4305 node4305Labels := by rfl

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

theorem canonical1056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1056 raw1056Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw1056 raw1056Labels = mixedMoment B raw1056step0 raw1056step0Labels := by
      have ha : raw1056step0 = (fun i j => raw1056 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1056step0 raw1056; decide +kernel
      have hl : raw1056step0Labels = raw1056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1056 raw1056Labels permutation152 permutation4
    mixedMoment B raw1056step0 raw1056step0Labels = mixedMoment B raw1056step1 raw1056step1Labels := by
      have ha : raw1056step1 = raw1056step0 := by apply Matrix.ext; unfold raw1056step1 raw1056step0; decide +kernel
      have hl : raw1056step0Labels = labelEmbedding7 ∘ raw1056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1056step0 raw1056step0Labels raw1056step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

theorem canonical1057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1057 raw1057Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw1057 raw1057Labels = mixedMoment B raw1057step0 raw1057step0Labels := by
      have ha : raw1057step0 = (fun i j => raw1057 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1057step0 raw1057; decide +kernel
      have hl : raw1057step0Labels = raw1057Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1057 raw1057Labels permutation152 permutation4
    _ = mixedMoment B node876 node876Labels := by rfl

theorem canonical1058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1058 raw1058Labels = mixedMoment B node1552 node1552Labels := by
  calc
    mixedMoment B raw1058 raw1058Labels = mixedMoment B raw1058step0 raw1058step0Labels := by
      have ha : raw1058step0 = (fun i j => raw1058 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1058step0 raw1058; decide +kernel
      have hl : raw1058step0Labels = raw1058Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1058 raw1058Labels permutation152 permutation6
    mixedMoment B raw1058step0 raw1058step0Labels = mixedMoment B raw1058step1 raw1058step1Labels := by
      have ha : raw1058step1 = -raw1058step0 := by apply Matrix.ext; change ∀ i j, raw1058step1 i j = -(raw1058step0 i j); unfold raw1058step1 raw1058step0; decide +kernel
      have hl : raw1058step1Labels = raw1058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1058step1 raw1058step1Labels = mixedMoment B raw1058step2 raw1058step2Labels := by
      have ha : raw1058step2 = raw1058step1 := by apply Matrix.ext; unfold raw1058step2 raw1058step1; decide +kernel
      have hl : raw1058step1Labels = labelEmbedding1 ∘ raw1058step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1058step1 raw1058step1Labels raw1058step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1552 node1552Labels := by rfl

theorem canonical1065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1065 raw1065Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw1065 raw1065Labels = mixedMoment B raw1065step0 raw1065step0Labels := by
      have ha : raw1065step0 = (fun i j => raw1065 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1065step0 raw1065; decide +kernel
      have hl : raw1065step0Labels = raw1065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1065 raw1065Labels permutation32 permutation4
    mixedMoment B raw1065step0 raw1065step0Labels = mixedMoment B raw1065step1 raw1065step1Labels := by
      have ha : raw1065step1 = raw1065step0 := by apply Matrix.ext; unfold raw1065step1 raw1065step0; decide +kernel
      have hl : raw1065step0Labels = labelEmbedding7 ∘ raw1065step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1065step0 raw1065step0Labels raw1065step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

theorem canonical1066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1066 raw1066Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw1066 raw1066Labels = mixedMoment B raw1066step0 raw1066step0Labels := by
      have ha : raw1066step0 = (fun i j => raw1066 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1066step0 raw1066; decide +kernel
      have hl : raw1066step0Labels = raw1066Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1066 raw1066Labels permutation32 permutation4
    _ = mixedMoment B node881 node881Labels := by rfl

theorem canonical1067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1067 raw1067Labels = mixedMoment B node1559 node1559Labels := by
  calc
    mixedMoment B raw1067 raw1067Labels = mixedMoment B raw1067step0 raw1067step0Labels := by
      have ha : raw1067step0 = (fun i j => raw1067 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1067step0 raw1067; decide +kernel
      have hl : raw1067step0Labels = raw1067Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1067 raw1067Labels permutation32 permutation6
    mixedMoment B raw1067step0 raw1067step0Labels = mixedMoment B raw1067step1 raw1067step1Labels := by
      have ha : raw1067step1 = -raw1067step0 := by apply Matrix.ext; change ∀ i j, raw1067step1 i j = -(raw1067step0 i j); unfold raw1067step1 raw1067step0; decide +kernel
      have hl : raw1067step1Labels = raw1067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1067step1 raw1067step1Labels = mixedMoment B raw1067step2 raw1067step2Labels := by
      have ha : raw1067step2 = raw1067step1 := by apply Matrix.ext; unfold raw1067step2 raw1067step1; decide +kernel
      have hl : raw1067step1Labels = labelEmbedding1 ∘ raw1067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1067step1 raw1067step1Labels raw1067step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1559 node1559Labels := by rfl

theorem canonical1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1080 raw1080Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw1080 raw1080Labels = mixedMoment B raw1080step0 raw1080step0Labels := by
      have ha : raw1080step0 = (fun i j => raw1080 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1080step0 raw1080; decide +kernel
      have hl : raw1080step0Labels = raw1080Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1080 raw1080Labels permutation32 permutation4
    mixedMoment B raw1080step0 raw1080step0Labels = mixedMoment B raw1080step1 raw1080step1Labels := by
      have ha : raw1080step1 = raw1080step0 := by apply Matrix.ext; unfold raw1080step1 raw1080step0; decide +kernel
      have hl : raw1080step0Labels = labelEmbedding7 ∘ raw1080step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1080step0 raw1080step0Labels raw1080step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

theorem canonical1081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1081 raw1081Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw1081 raw1081Labels = mixedMoment B raw1081step0 raw1081step0Labels := by
      have ha : raw1081step0 = (fun i j => raw1081 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1081step0 raw1081; decide +kernel
      have hl : raw1081step0Labels = raw1081Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1081 raw1081Labels permutation32 permutation4
    _ = mixedMoment B node891 node891Labels := by rfl

theorem canonical1082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1082 raw1082Labels = mixedMoment B node1565 node1565Labels := by
  calc
    mixedMoment B raw1082 raw1082Labels = mixedMoment B raw1082step0 raw1082step0Labels := by
      have ha : raw1082step0 = (fun i j => raw1082 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1082step0 raw1082; decide +kernel
      have hl : raw1082step0Labels = raw1082Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1082 raw1082Labels permutation34 permutation6
    mixedMoment B raw1082step0 raw1082step0Labels = mixedMoment B raw1082step1 raw1082step1Labels := by
      have ha : raw1082step1 = -raw1082step0 := by apply Matrix.ext; change ∀ i j, raw1082step1 i j = -(raw1082step0 i j); unfold raw1082step1 raw1082step0; decide +kernel
      have hl : raw1082step1Labels = raw1082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1082step1 raw1082step1Labels = mixedMoment B raw1082step2 raw1082step2Labels := by
      have ha : raw1082step2 = raw1082step1 := by apply Matrix.ext; unfold raw1082step2 raw1082step1; decide +kernel
      have hl : raw1082step1Labels = labelEmbedding1 ∘ raw1082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1082step1 raw1082step1Labels raw1082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1565 node1565Labels := by rfl

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

theorem canonical1230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1230 raw1230Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw1230 raw1230Labels = mixedMoment B raw1230step0 raw1230step0Labels := by
      have ha : raw1230step0 = (fun i j => raw1230 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1230step0 raw1230; decide +kernel
      have hl : raw1230step0Labels = raw1230Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1230 raw1230Labels permutation32 permutation4
    mixedMoment B raw1230step0 raw1230step0Labels = mixedMoment B raw1230step1 raw1230step1Labels := by
      have ha : raw1230step1 = raw1230step0 := by apply Matrix.ext; unfold raw1230step1 raw1230step0; decide +kernel
      have hl : raw1230step0Labels = labelEmbedding7 ∘ raw1230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1230step0 raw1230step0Labels raw1230step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical1231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1231 raw1231Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw1231 raw1231Labels = mixedMoment B raw1231step0 raw1231step0Labels := by
      have ha : raw1231step0 = (fun i j => raw1231 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1231step0 raw1231; decide +kernel
      have hl : raw1231step0Labels = raw1231Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1231 raw1231Labels permutation32 permutation4
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical1232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1232 raw1232Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw1232 raw1232Labels = mixedMoment B raw1232step0 raw1232step0Labels := by
      have ha : raw1232step0 = (fun i j => raw1232 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1232step0 raw1232; decide +kernel
      have hl : raw1232step0Labels = raw1232Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1232 raw1232Labels permutation32 permutation6
    mixedMoment B raw1232step0 raw1232step0Labels = mixedMoment B raw1232step1 raw1232step1Labels := by
      have ha : raw1232step1 = -raw1232step0 := by apply Matrix.ext; change ∀ i j, raw1232step1 i j = -(raw1232step0 i j); unfold raw1232step1 raw1232step0; decide +kernel
      have hl : raw1232step1Labels = raw1232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1232step1 raw1232step1Labels = mixedMoment B raw1232step2 raw1232step2Labels := by
      have ha : raw1232step2 = raw1232step1 := by apply Matrix.ext; unfold raw1232step2 raw1232step1; decide +kernel
      have hl : raw1232step1Labels = labelEmbedding1 ∘ raw1232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1232step1 raw1232step1Labels raw1232step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

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

theorem singleton4298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4298 node4298Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node876 node876Labels + mixedMoment B node1552 node1552Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1056 singletonSmall4298
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4298) = raw1056Labels := by decide +kernel
  rw [hl, canonical1056 B hB] at h
  have hc0 : mixedMoment B raw1056 (Fin.cases (0 : Fin 2) singletonSmall4298) =
      mixedMoment B node876 node876Labels := by
    have ha : raw1056 = raw1057 := by apply Matrix.ext; unfold raw1056 raw1057; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4298 = raw1057Labels := by decide +kernel
    rw [ha, hj, canonical1057 B hB]
  have hc1 : mixedMoment B raw1056 (Fin.cases (1 : Fin 2) singletonSmall4298) =
      mixedMoment B node1552 node1552Labels := by
    have ha : raw1056 = raw1058 := by apply Matrix.ext; unfold raw1056 raw1058; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4298 = raw1058Labels := by decide +kernel
    rw [ha, hj, canonical1058 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4303 node4303Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node881 node881Labels + mixedMoment B node1559 node1559Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1065 singletonSmall4303
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4303) = raw1065Labels := by decide +kernel
  rw [hl, canonical1065 B hB] at h
  have hc0 : mixedMoment B raw1065 (Fin.cases (0 : Fin 2) singletonSmall4303) =
      mixedMoment B node881 node881Labels := by
    have ha : raw1065 = raw1066 := by apply Matrix.ext; unfold raw1065 raw1066; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4303 = raw1066Labels := by decide +kernel
    rw [ha, hj, canonical1066 B hB]
  have hc1 : mixedMoment B raw1065 (Fin.cases (1 : Fin 2) singletonSmall4303) =
      mixedMoment B node1559 node1559Labels := by
    have ha : raw1065 = raw1067 := by apply Matrix.ext; unfold raw1065 raw1067; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4303 = raw1067Labels := by decide +kernel
    rw [ha, hj, canonical1067 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4313 node4313Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node891 node891Labels + mixedMoment B node1565 node1565Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1080 singletonSmall4313
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4313) = raw1080Labels := by decide +kernel
  rw [hl, canonical1080 B hB] at h
  have hc0 : mixedMoment B raw1080 (Fin.cases (0 : Fin 2) singletonSmall4313) =
      mixedMoment B node891 node891Labels := by
    have ha : raw1080 = raw1081 := by apply Matrix.ext; unfold raw1080 raw1081; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4313 = raw1081Labels := by decide +kernel
    rw [ha, hj, canonical1081 B hB]
  have hc1 : mixedMoment B raw1080 (Fin.cases (1 : Fin 2) singletonSmall4313) =
      mixedMoment B node1565 node1565Labels := by
    have ha : raw1080 = raw1082 := by apply Matrix.ext; unfold raw1080 raw1082; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4313 = raw1082Labels := by decide +kernel
    rw [ha, hj, canonical1082 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4419 node4419Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1000 node1000Labels + mixedMoment B node1605 node1605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1230 singletonSmall4419
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4419) = raw1230Labels := by decide +kernel
  rw [hl, canonical1230 B hB] at h
  have hc0 : mixedMoment B raw1230 (Fin.cases (0 : Fin 2) singletonSmall4419) =
      mixedMoment B node1000 node1000Labels := by
    have ha : raw1230 = raw1231 := by apply Matrix.ext; unfold raw1230 raw1231; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4419 = raw1231Labels := by decide +kernel
    rw [ha, hj, canonical1231 B hB]
  have hc1 : mixedMoment B raw1230 (Fin.cases (1 : Fin 2) singletonSmall4419) =
      mixedMoment B node1605 node1605Labels := by
    have ha : raw1230 = raw1232 := by apply Matrix.ext; unfold raw1230 raw1232; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4419 = raw1232Labels := by decide +kernel
    rw [ha, hj, canonical1232 B hB]
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

theorem singleton4640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4640 node4640Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1769 node1769Labels + mixedMoment B node1835 node1835Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1500 singletonSmall4640
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4640) = raw1500Labels := by decide +kernel
  rw [hl, canonical1500 B hB] at h
  have hc0 : mixedMoment B raw1500 (Fin.cases (0 : Fin 2) singletonSmall4640) =
      mixedMoment B node1769 node1769Labels := by
    have ha : raw1500 = raw1501 := by apply Matrix.ext; unfold raw1500 raw1501; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4640 = raw1501Labels := by decide +kernel
    rw [ha, hj, canonical1501 B hB]
  have hc1 : mixedMoment B raw1500 (Fin.cases (1 : Fin 2) singletonSmall4640) =
      mixedMoment B node1835 node1835Labels := by
    have ha : raw1500 = raw1502 := by apply Matrix.ext; unfold raw1500 raw1502; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4640 = raw1502Labels := by decide +kernel
    rw [ha, hj, canonical1502 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4644 node4644Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1773 node1773Labels + mixedMoment B node1841 node1841Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1506 singletonSmall4644
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4644) = raw1506Labels := by decide +kernel
  rw [hl, canonical1506 B hB] at h
  have hc0 : mixedMoment B raw1506 (Fin.cases (0 : Fin 2) singletonSmall4644) =
      mixedMoment B node1773 node1773Labels := by
    have ha : raw1506 = raw1507 := by apply Matrix.ext; unfold raw1506 raw1507; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4644 = raw1507Labels := by decide +kernel
    rw [ha, hj, canonical1507 B hB]
  have hc1 : mixedMoment B raw1506 (Fin.cases (1 : Fin 2) singletonSmall4644) =
      mixedMoment B node1841 node1841Labels := by
    have ha : raw1506 = raw1508 := by apply Matrix.ext; unfold raw1506 raw1508; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4644 = raw1508Labels := by decide +kernel
    rw [ha, hj, canonical1508 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4653 node4653Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1781 node1781Labels + mixedMoment B node1846 node1846Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1521 singletonSmall4653
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4653) = raw1521Labels := by decide +kernel
  rw [hl, canonical1521 B hB] at h
  have hc0 : mixedMoment B raw1521 (Fin.cases (0 : Fin 2) singletonSmall4653) =
      mixedMoment B node1781 node1781Labels := by
    have ha : raw1521 = raw1522 := by apply Matrix.ext; unfold raw1521 raw1522; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4653 = raw1522Labels := by decide +kernel
    rw [ha, hj, canonical1522 B hB]
  have hc1 : mixedMoment B raw1521 (Fin.cases (1 : Fin 2) singletonSmall4653) =
      mixedMoment B node1846 node1846Labels := by
    have ha : raw1521 = raw1523 := by apply Matrix.ext; unfold raw1521 raw1523; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4653 = raw1523Labels := by decide +kernel
    rw [ha, hj, canonical1523 B hB]
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

theorem singleton4709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4709 node4709Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1863 node1863Labels + mixedMoment B node1883 node1883Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1596 singletonSmall4709
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4709) = raw1596Labels := by decide +kernel
  rw [hl, canonical1596 B hB] at h
  have hc0 : mixedMoment B raw1596 (Fin.cases (0 : Fin 2) singletonSmall4709) =
      mixedMoment B node1863 node1863Labels := by
    have ha : raw1596 = raw1597 := by apply Matrix.ext; unfold raw1596 raw1597; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4709 = raw1597Labels := by decide +kernel
    rw [ha, hj, canonical1597 B hB]
  have hc1 : mixedMoment B raw1596 (Fin.cases (1 : Fin 2) singletonSmall4709) =
      mixedMoment B node1883 node1883Labels := by
    have ha : raw1596 = raw1598 := by apply Matrix.ext; unfold raw1596 raw1598; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4709 = raw1598Labels := by decide +kernel
    rw [ha, hj, canonical1598 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4716 node4716Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1870 node1870Labels + mixedMoment B node1886 node1886Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1608 singletonSmall4716
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4716) = raw1608Labels := by decide +kernel
  rw [hl, canonical1608 B hB] at h
  have hc0 : mixedMoment B raw1608 (Fin.cases (0 : Fin 2) singletonSmall4716) =
      mixedMoment B node1870 node1870Labels := by
    have ha : raw1608 = raw1609 := by apply Matrix.ext; unfold raw1608 raw1609; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4716 = raw1609Labels := by decide +kernel
    rw [ha, hj, canonical1609 B hB]
  have hc1 : mixedMoment B raw1608 (Fin.cases (1 : Fin 2) singletonSmall4716) =
      mixedMoment B node1886 node1886Labels := by
    have ha : raw1608 = raw1610 := by apply Matrix.ext; unfold raw1608 raw1610; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4716 = raw1610Labels := by decide +kernel
    rw [ha, hj, canonical1610 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4731 node4731Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1900 node1900Labels + mixedMoment B node1921 node1921Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1647 singletonSmall4731
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4731) = raw1647Labels := by decide +kernel
  rw [hl, canonical1647 B hB] at h
  have hc0 : mixedMoment B raw1647 (Fin.cases (0 : Fin 2) singletonSmall4731) =
      mixedMoment B node1900 node1900Labels := by
    have ha : raw1647 = raw1648 := by apply Matrix.ext; unfold raw1647 raw1648; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4731 = raw1648Labels := by decide +kernel
    rw [ha, hj, canonical1648 B hB]
  have hc1 : mixedMoment B raw1647 (Fin.cases (1 : Fin 2) singletonSmall4731) =
      mixedMoment B node1921 node1921Labels := by
    have ha : raw1647 = raw1649 := by apply Matrix.ext; unfold raw1647 raw1649; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4731 = raw1649Labels := by decide +kernel
    rw [ha, hj, canonical1649 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4732 node4732Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1901 node1901Labels + mixedMoment B node1941 node1941Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1650 singletonSmall4732
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4732) = raw1650Labels := by decide +kernel
  rw [hl, canonical1650 B hB] at h
  have hc0 : mixedMoment B raw1650 (Fin.cases (0 : Fin 2) singletonSmall4732) =
      mixedMoment B node1901 node1901Labels := by
    have ha : raw1650 = raw1651 := by apply Matrix.ext; unfold raw1650 raw1651; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4732 = raw1651Labels := by decide +kernel
    rw [ha, hj, canonical1651 B hB]
  have hc1 : mixedMoment B raw1650 (Fin.cases (1 : Fin 2) singletonSmall4732) =
      mixedMoment B node1941 node1941Labels := by
    have ha : raw1650 = raw1652 := by apply Matrix.ext; unfold raw1650 raw1652; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4732 = raw1652Labels := by decide +kernel
    rw [ha, hj, canonical1652 B hB]
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

theorem singleton4744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4744 node4744Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1917 node1917Labels + mixedMoment B node1924 node1924Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1662 singletonSmall4744
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4744) = raw1662Labels := by decide +kernel
  rw [hl, canonical1662 B hB] at h
  have hc0 : mixedMoment B raw1662 (Fin.cases (0 : Fin 2) singletonSmall4744) =
      mixedMoment B node1917 node1917Labels := by
    have ha : raw1662 = raw1663 := by apply Matrix.ext; unfold raw1662 raw1663; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4744 = raw1663Labels := by decide +kernel
    rw [ha, hj, canonical1663 B hB]
  have hc1 : mixedMoment B raw1662 (Fin.cases (1 : Fin 2) singletonSmall4744) =
      mixedMoment B node1924 node1924Labels := by
    have ha : raw1662 = raw1664 := by apply Matrix.ext; unfold raw1662 raw1664; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4744 = raw1664Labels := by decide +kernel
    rw [ha, hj, canonical1664 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4750 node4750Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1929 node1929Labels + mixedMoment B node1949 node1949Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1674 singletonSmall4750
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4750) = raw1674Labels := by decide +kernel
  rw [hl, canonical1674 B hB] at h
  have hc0 : mixedMoment B raw1674 (Fin.cases (0 : Fin 2) singletonSmall4750) =
      mixedMoment B node1929 node1929Labels := by
    have ha : raw1674 = raw1675 := by apply Matrix.ext; unfold raw1674 raw1675; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4750 = raw1675Labels := by decide +kernel
    rw [ha, hj, canonical1675 B hB]
  have hc1 : mixedMoment B raw1674 (Fin.cases (1 : Fin 2) singletonSmall4750) =
      mixedMoment B node1949 node1949Labels := by
    have ha : raw1674 = raw1676 := by apply Matrix.ext; unfold raw1674 raw1676; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4750 = raw1676Labels := by decide +kernel
    rw [ha, hj, canonical1676 B hB]
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

theorem singleton5050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5050 node5050Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2452 node2452Labels + mixedMoment B node3433 node3433Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2076 singletonSmall5050
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5050) = raw2076Labels := by decide +kernel
  rw [hl, canonical2076 B hB] at h
  have hc0 : mixedMoment B raw2076 (Fin.cases (0 : Fin 2) singletonSmall5050) =
      mixedMoment B node2452 node2452Labels := by
    have ha : raw2076 = raw2077 := by apply Matrix.ext; unfold raw2076 raw2077; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5050 = raw2077Labels := by decide +kernel
    rw [ha, hj, canonical2077 B hB]
  have hc1 : mixedMoment B raw2076 (Fin.cases (1 : Fin 2) singletonSmall5050) =
      mixedMoment B node3433 node3433Labels := by
    have ha : raw2076 = raw2078 := by apply Matrix.ext; unfold raw2076 raw2078; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5050 = raw2078Labels := by decide +kernel
    rw [ha, hj, canonical2078 B hB]
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

theorem singleton5080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5080 node5080Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2488 node2488Labels + mixedMoment B node3478 node3478Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2106 singletonSmall5080
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5080) = raw2106Labels := by decide +kernel
  rw [hl, canonical2106 B hB] at h
  have hc0 : mixedMoment B raw2106 (Fin.cases (0 : Fin 2) singletonSmall5080) =
      mixedMoment B node2488 node2488Labels := by
    have ha : raw2106 = raw2107 := by apply Matrix.ext; unfold raw2106 raw2107; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5080 = raw2107Labels := by decide +kernel
    rw [ha, hj, canonical2107 B hB]
  have hc1 : mixedMoment B raw2106 (Fin.cases (1 : Fin 2) singletonSmall5080) =
      mixedMoment B node3478 node3478Labels := by
    have ha : raw2106 = raw2108 := by apply Matrix.ext; unfold raw2106 raw2108; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5080 = raw2108Labels := by decide +kernel
    rw [ha, hj, canonical2108 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5081 node5081Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2489 node2489Labels + mixedMoment B node3482 node3482Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2109 singletonSmall5081
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5081) = raw2109Labels := by decide +kernel
  rw [hl, canonical2109 B hB] at h
  have hc0 : mixedMoment B raw2109 (Fin.cases (0 : Fin 2) singletonSmall5081) =
      mixedMoment B node2489 node2489Labels := by
    have ha : raw2109 = raw2110 := by apply Matrix.ext; unfold raw2109 raw2110; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5081 = raw2110Labels := by decide +kernel
    rw [ha, hj, canonical2110 B hB]
  have hc1 : mixedMoment B raw2109 (Fin.cases (1 : Fin 2) singletonSmall5081) =
      mixedMoment B node3482 node3482Labels := by
    have ha : raw2109 = raw2111 := by apply Matrix.ext; unfold raw2109 raw2111; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5081 = raw2111Labels := by decide +kernel
    rw [ha, hj, canonical2111 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node876 node876Labels = Sparse.eval nodeValue876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 876) = mixedMoment B node876 node876Labels := rfl
  simpa [nodeValue876, Sparse.eval] using hc.symm

theorem sound881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node881 node881Labels = Sparse.eval nodeValue881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 881) = mixedMoment B node881 node881Labels := rfl
  simpa [nodeValue881, Sparse.eval] using hc.symm

theorem sound891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node891 node891Labels = Sparse.eval nodeValue891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 891) = mixedMoment B node891 node891Labels := rfl
  simpa [nodeValue891, Sparse.eval] using hc.symm

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

theorem sound1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1000 node1000Labels = Sparse.eval nodeValue1000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1000) = mixedMoment B node1000 node1000Labels := rfl
  simpa [nodeValue1000, Sparse.eval] using hc.symm

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

theorem sound1552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1552 node1552Labels = Sparse.eval nodeValue1552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1552) = mixedMoment B node1552 node1552Labels := rfl
  simpa [nodeValue1552, Sparse.eval] using hc.symm

theorem sound1559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1559 node1559Labels = Sparse.eval nodeValue1559 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1559) = mixedMoment B node1559 node1559Labels := rfl
  simpa [nodeValue1559, Sparse.eval] using hc.symm

theorem sound1565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1565 node1565Labels = Sparse.eval nodeValue1565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1565) = mixedMoment B node1565 node1565Labels := rfl
  simpa [nodeValue1565, Sparse.eval] using hc.symm

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

theorem sound1605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1605 node1605Labels = Sparse.eval nodeValue1605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1605) = mixedMoment B node1605 node1605Labels := rfl
  simpa [nodeValue1605, Sparse.eval] using hc.symm

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

theorem sound1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1769 node1769Labels = Sparse.eval nodeValue1769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1769) = mixedMoment B node1769 node1769Labels := rfl
  simpa [nodeValue1769, Sparse.eval] using hc.symm

theorem sound1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1773 node1773Labels = Sparse.eval nodeValue1773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1773) = mixedMoment B node1773 node1773Labels := rfl
  simpa [nodeValue1773, Sparse.eval] using hc.symm

theorem sound1781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1781 node1781Labels = Sparse.eval nodeValue1781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1781) = mixedMoment B node1781 node1781Labels := rfl
  simpa [nodeValue1781, Sparse.eval] using hc.symm

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

theorem sound1835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1835 node1835Labels = Sparse.eval nodeValue1835 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1835) = mixedMoment B node1835 node1835Labels := rfl
  simpa [nodeValue1835, Sparse.eval] using hc.symm

theorem sound1841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1841 node1841Labels = Sparse.eval nodeValue1841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1841) = mixedMoment B node1841 node1841Labels := rfl
  simpa [nodeValue1841, Sparse.eval] using hc.symm

theorem sound1846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1846 node1846Labels = Sparse.eval nodeValue1846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1846) = mixedMoment B node1846 node1846Labels := rfl
  simpa [nodeValue1846, Sparse.eval] using hc.symm

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

theorem sound1863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1863 node1863Labels = Sparse.eval nodeValue1863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1863) = mixedMoment B node1863 node1863Labels := rfl
  simpa [nodeValue1863, Sparse.eval] using hc.symm

theorem sound1870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1870 node1870Labels = Sparse.eval nodeValue1870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1870) = mixedMoment B node1870 node1870Labels := rfl
  simpa [nodeValue1870, Sparse.eval] using hc.symm

theorem sound1883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1883 node1883Labels = Sparse.eval nodeValue1883 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1883) = mixedMoment B node1883 node1883Labels := rfl
  simpa [nodeValue1883, Sparse.eval] using hc.symm

theorem sound1886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1886 node1886Labels = Sparse.eval nodeValue1886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1886) = mixedMoment B node1886 node1886Labels := rfl
  simpa [nodeValue1886, Sparse.eval] using hc.symm

theorem sound1900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1900 node1900Labels = Sparse.eval nodeValue1900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1900) = mixedMoment B node1900 node1900Labels := rfl
  simpa [nodeValue1900, Sparse.eval] using hc.symm

theorem sound1901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1901 node1901Labels = Sparse.eval nodeValue1901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1901) = mixedMoment B node1901 node1901Labels := rfl
  simpa [nodeValue1901, Sparse.eval] using hc.symm

theorem sound1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1917 node1917Labels = Sparse.eval nodeValue1917 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1917) = mixedMoment B node1917 node1917Labels := rfl
  simpa [nodeValue1917, Sparse.eval] using hc.symm

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

theorem sound1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1921 node1921Labels = Sparse.eval nodeValue1921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1921) = mixedMoment B node1921 node1921Labels := rfl
  simpa [nodeValue1921, Sparse.eval] using hc.symm

theorem sound1924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1924 node1924Labels = Sparse.eval nodeValue1924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1924) = mixedMoment B node1924 node1924Labels := rfl
  simpa [nodeValue1924, Sparse.eval] using hc.symm

theorem sound1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1928 node1928Labels = Sparse.eval nodeValue1928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1928) = mixedMoment B node1928 node1928Labels := rfl
  simpa [nodeValue1928, Sparse.eval] using hc.symm

theorem sound1929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1929 node1929Labels = Sparse.eval nodeValue1929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1929) = mixedMoment B node1929 node1929Labels := rfl
  simpa [nodeValue1929, Sparse.eval] using hc.symm

theorem sound1941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1941 node1941Labels = Sparse.eval nodeValue1941 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1941) = mixedMoment B node1941 node1941Labels := rfl
  simpa [nodeValue1941, Sparse.eval] using hc.symm

theorem sound1949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1949 node1949Labels = Sparse.eval nodeValue1949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1949) = mixedMoment B node1949 node1949Labels := rfl
  simpa [nodeValue1949, Sparse.eval] using hc.symm

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

theorem sound1990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1990 node1990Labels = Sparse.eval nodeValue1990 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1990) = mixedMoment B node1990 node1990Labels := rfl
  simpa [nodeValue1990, Sparse.eval] using hc.symm

theorem sound1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1997 node1997Labels = Sparse.eval nodeValue1997 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1997) = mixedMoment B node1997 node1997Labels := rfl
  simpa [nodeValue1997, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

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

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2388 node2388Labels = Sparse.eval nodeValue2388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2388) = mixedMoment B node2388 node2388Labels := rfl
  simpa [nodeValue2388, Sparse.eval] using hc.symm

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

theorem sound2452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2452 node2452Labels = Sparse.eval nodeValue2452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2452) = mixedMoment B node2452 node2452Labels := rfl
  simpa [nodeValue2452, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

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

theorem sound3354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3354 node3354Labels = Sparse.eval nodeValue3354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3354) = mixedMoment B node3354 node3354Labels := rfl
  simpa [nodeValue3354, Sparse.eval] using hc.symm

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

theorem sound3433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3433 node3433Labels = Sparse.eval nodeValue3433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3433) = mixedMoment B node3433 node3433Labels := rfl
  simpa [nodeValue3433, Sparse.eval] using hc.symm

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

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4305 node4305Labels = 0 := by
  exact mixedMoment_order_one B hB node4305 node4305Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4298 node4298Labels = Sparse.eval nodeValue4298 (mixedVector B) := by
  have h := singleton4298 B _hB
  rw [sound876 B _hB _hF, sound1552 B _hB _hF] at h
  norm_num [nodeValue4298, nodeValue876, nodeValue1552, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4303 node4303Labels = Sparse.eval nodeValue4303 (mixedVector B) := by
  have h := singleton4303 B _hB
  rw [sound881 B _hB _hF, sound1559 B _hB _hF] at h
  norm_num [nodeValue4303, nodeValue881, nodeValue1559, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4305 node4305Labels = Sparse.eval nodeValue4305 (mixedVector B) := by
  simpa only [nodeValue4305, Sparse.eval_nil] using zero4305 B _hB _hF

theorem sound4313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4313 node4313Labels = Sparse.eval nodeValue4313 (mixedVector B) := by
  have h := singleton4313 B _hB
  rw [sound891 B _hB _hF, sound1565 B _hB _hF] at h
  norm_num [nodeValue4313, nodeValue891, nodeValue1565, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4419 node4419Labels = Sparse.eval nodeValue4419 (mixedVector B) := by
  have h := singleton4419 B _hB
  rw [sound1000 B _hB _hF, sound1605 B _hB _hF] at h
  norm_num [nodeValue4419, nodeValue1000, nodeValue1605, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4646 node4646Labels = 0 := by
  exact mixedMoment_order_one B hB node4646 node4646Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4640 node4640Labels = Sparse.eval nodeValue4640 (mixedVector B) := by
  have h := singleton4640 B _hB
  rw [sound1769 B _hB _hF, sound1835 B _hB _hF] at h
  norm_num [nodeValue4640, nodeValue1769, nodeValue1835, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4644 node4644Labels = Sparse.eval nodeValue4644 (mixedVector B) := by
  have h := singleton4644 B _hB
  rw [sound1773 B _hB _hF, sound1841 B _hB _hF] at h
  norm_num [nodeValue4644, nodeValue1773, nodeValue1841, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4646 node4646Labels = Sparse.eval nodeValue4646 (mixedVector B) := by
  simpa only [nodeValue4646, Sparse.eval_nil] using zero4646 B _hB _hF

theorem sound4653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4653 node4653Labels = Sparse.eval nodeValue4653 (mixedVector B) := by
  have h := singleton4653 B _hB
  rw [sound1781 B _hB _hF, sound1846 B _hB _hF] at h
  norm_num [nodeValue4653, nodeValue1781, nodeValue1846, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4711 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4711 node4711Labels = 0 := by
  exact mixedMoment_order_one B hB node4711 node4711Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4709 node4709Labels = Sparse.eval nodeValue4709 (mixedVector B) := by
  have h := singleton4709 B _hB
  rw [sound1863 B _hB _hF, sound1883 B _hB _hF] at h
  norm_num [nodeValue4709, nodeValue1863, nodeValue1883, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4711 node4711Labels = Sparse.eval nodeValue4711 (mixedVector B) := by
  simpa only [nodeValue4711, Sparse.eval_nil] using zero4711 B _hB _hF

theorem sound4716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4716 node4716Labels = Sparse.eval nodeValue4716 (mixedVector B) := by
  have h := singleton4716 B _hB
  rw [sound1870 B _hB _hF, sound1886 B _hB _hF] at h
  norm_num [nodeValue4716, nodeValue1870, nodeValue1886, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4731 node4731Labels = Sparse.eval nodeValue4731 (mixedVector B) := by
  have h := singleton4731 B _hB
  rw [sound1900 B _hB _hF, sound1921 B _hB _hF] at h
  norm_num [nodeValue4731, nodeValue1900, nodeValue1921, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4732 node4732Labels = Sparse.eval nodeValue4732 (mixedVector B) := by
  have h := singleton4732 B _hB
  rw [sound1901 B _hB _hF, sound1941 B _hB _hF] at h
  norm_num [nodeValue4732, nodeValue1901, nodeValue1941, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4745 node4745Labels = 0 := by
  exact mixedMoment_order_one B hB node4745 node4745Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4753 node4753Labels = 0 := by
  exact mixedMoment_order_one B hB node4753 node4753Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4744 node4744Labels = Sparse.eval nodeValue4744 (mixedVector B) := by
  have h := singleton4744 B _hB
  rw [sound1917 B _hB _hF, sound1924 B _hB _hF] at h
  norm_num [nodeValue4744, nodeValue1917, nodeValue1924, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4745 node4745Labels = Sparse.eval nodeValue4745 (mixedVector B) := by
  simpa only [nodeValue4745, Sparse.eval_nil] using zero4745 B _hB _hF

theorem sound4749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4749 node4749Labels = Sparse.eval nodeValue4749 (mixedVector B) := by
  have h := singleton4749 B _hB
  rw [sound1928 B _hB _hF] at h
  norm_num [nodeValue4749, nodeValue1928, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4750 node4750Labels = Sparse.eval nodeValue4750 (mixedVector B) := by
  have h := singleton4750 B _hB
  rw [sound1929 B _hB _hF, sound1949 B _hB _hF] at h
  norm_num [nodeValue4750, nodeValue1929, nodeValue1949, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4753 node4753Labels = Sparse.eval nodeValue4753 (mixedVector B) := by
  simpa only [nodeValue4753, Sparse.eval_nil] using zero4753 B _hB _hF

theorem sound4782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4782 node4782Labels = Sparse.eval nodeValue4782 (mixedVector B) := by
  have h := singleton4782 B _hB
  rw [sound1990 B _hB _hF, sound1997 B _hB _hF] at h
  norm_num [nodeValue4782, nodeValue1990, nodeValue1997, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = 0 := by
  exact mixedMoment_order_one B hB node4846 node4846Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = Sparse.eval nodeValue4846 (mixedVector B) := by
  simpa only [nodeValue4846, Sparse.eval_nil] using zero4846 B _hB _hF

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

theorem sound5003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5003 node5003Labels = Sparse.eval nodeValue5003 (mixedVector B) := by
  have h := singleton5003 B _hB
  rw [sound2388 B _hB _hF, sound3354 B _hB _hF] at h
  norm_num [nodeValue5003, nodeValue2388, nodeValue3354, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5050 node5050Labels = Sparse.eval nodeValue5050 (mixedVector B) := by
  have h := singleton5050 B _hB
  rw [sound2452 B _hB _hF, sound3433 B _hB _hF] at h
  norm_num [nodeValue5050, nodeValue2452, nodeValue3433, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = 0 := by
  exact mixedMoment_order_one B hB node5111 node5111Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5080 node5080Labels = Sparse.eval nodeValue5080 (mixedVector B) := by
  have h := singleton5080 B _hB
  rw [sound2488 B _hB _hF, sound3478 B _hB _hF] at h
  norm_num [nodeValue5080, nodeValue2488, nodeValue3478, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5081 node5081Labels = Sparse.eval nodeValue5081 (mixedVector B) := by
  have h := singleton5081 B _hB
  rw [sound2489 B _hB _hF, sound3482 B _hB _hF] at h
  norm_num [nodeValue5081, nodeValue2489, nodeValue3482, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = Sparse.eval nodeValue5111 (mixedVector B) := by
  simpa only [nodeValue5111, Sparse.eval_nil] using zero5111 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources72
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2310 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 1) (sourceB2310 + difference 1 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 1) (sourceB2310 + difference 1 0) sourceC2310) = raw30381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30381; decide +kernel
    rw [ha]
    exact (canonical30381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 2) (sourceB2310 + difference 2 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 2) (sourceB2310 + difference 2 0) sourceC2310) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 3) (sourceB2310 + difference 3 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 3) (sourceB2310 + difference 3 0) sourceC2310) = raw30174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30174; decide +kernel
    rw [ha]
    exact (canonical30174 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 4) (sourceB2310 + difference 4 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 4) (sourceB2310 + difference 4 0) sourceC2310) = raw29683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw29683; decide +kernel
    rw [ha]
    exact (canonical29683 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2310 + difference 0 5) (sourceB2310 + difference 5 0) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2310 + difference 0 5) (sourceB2310 + difference 5 0) sourceC2310) = raw30547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30547; decide +kernel
    rw [ha]
    exact (canonical30547 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 0) (sourceB2310 + difference 0 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 0) (sourceB2310 + difference 0 1) sourceC2310) = raw31434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31434; decide +kernel
    rw [ha]
    exact (canonical31434 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 2) (sourceB2310 + difference 2 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 2) (sourceB2310 + difference 2 1) sourceC2310) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 3) (sourceB2310 + difference 3 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 3) (sourceB2310 + difference 3 1) sourceC2310) = raw30173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30173; decide +kernel
    rw [ha]
    exact (canonical30173 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 4) (sourceB2310 + difference 4 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 4) (sourceB2310 + difference 4 1) sourceC2310) = raw29682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw29682; decide +kernel
    rw [ha]
    exact (canonical29682 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2310 + difference 1 5) (sourceB2310 + difference 5 1) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2310 + difference 1 5) (sourceB2310 + difference 5 1) sourceC2310) = raw30363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30363; decide +kernel
    rw [ha]
    exact (canonical30363 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 0) (sourceB2310 + difference 0 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 0) (sourceB2310 + difference 0 2) sourceC2310) = raw31867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31867; decide +kernel
    rw [ha]
    exact (canonical31867 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 1) (sourceB2310 + difference 1 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4653) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 1) (sourceB2310 + difference 1 2) sourceC2310) = raw31868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31868; decide +kernel
    rw [ha]
    exact (canonical31868 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 3) (sourceB2310 + difference 3 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4716) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 3) (sourceB2310 + difference 3 2) sourceC2310) = raw31869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31869; decide +kernel
    rw [ha]
    exact (canonical31869 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 4) (sourceB2310 + difference 4 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 4) (sourceB2310 + difference 4 2) sourceC2310) = raw30541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30541; decide +kernel
    rw [ha]
    exact (canonical30541 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2310 + difference 2 5) (sourceB2310 + difference 5 2) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2310 + difference 2 5) (sourceB2310 + difference 5 2) sourceC2310) = raw30365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30365; decide +kernel
    rw [ha]
    exact (canonical30365 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 0) (sourceB2310 + difference 0 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4298) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 0) (sourceB2310 + difference 0 3) sourceC2310) = raw31870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31870; decide +kernel
    rw [ha]
    exact (canonical31870 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 1) (sourceB2310 + difference 1 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4640) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 1) (sourceB2310 + difference 1 3) sourceC2310) = raw31871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31871; decide +kernel
    rw [ha]
    exact (canonical31871 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 2) (sourceB2310 + difference 2 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 2) (sourceB2310 + difference 2 3) sourceC2310) = raw31872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31872; decide +kernel
    rw [ha]
    exact (canonical31872 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 4) (sourceB2310 + difference 4 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 4) (sourceB2310 + difference 4 3) sourceC2310) = raw30545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30545; decide +kernel
    rw [ha]
    exact (canonical30545 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2310 + difference 3 5) (sourceB2310 + difference 5 3) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2310 + difference 3 5) (sourceB2310 + difference 5 3) sourceC2310) = raw30370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30370; decide +kernel
    rw [ha]
    exact (canonical30370 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 0) (sourceB2310 + difference 0 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 0) (sourceB2310 + difference 0 4) sourceC2310) = raw31873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31873; decide +kernel
    rw [ha]
    exact (canonical31873 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 1) (sourceB2310 + difference 1 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 1) (sourceB2310 + difference 1 4) sourceC2310) = raw31874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31874; decide +kernel
    rw [ha]
    exact (canonical31874 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 2) (sourceB2310 + difference 2 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4753) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 2) (sourceB2310 + difference 2 4) sourceC2310) = raw30699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30699; decide +kernel
    rw [ha]
    exact (canonical30699 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 3) (sourceB2310 + difference 3 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4709) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 3) (sourceB2310 + difference 3 4) sourceC2310) = raw31875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31875; decide +kernel
    rw [ha]
    exact (canonical31875 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2310 + difference 4 5) (sourceB2310 + difference 5 4) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2310 + difference 4 5) (sourceB2310 + difference 5 4) sourceC2310) = raw30375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30375; decide +kernel
    rw [ha]
    exact (canonical30375 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 0) (sourceB2310 + difference 0 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4305) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 0) (sourceB2310 + difference 0 5) sourceC2310) = raw31876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw31876; decide +kernel
    rw [ha]
    exact (canonical31876 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 1) (sourceB2310 + difference 1 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4646) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 1) (sourceB2310 + difference 1 5) sourceC2310) = raw30922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30922; decide +kernel
    rw [ha]
    exact (canonical30922 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 2) (sourceB2310 + difference 2 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 2) (sourceB2310 + difference 2 5) sourceC2310) = raw30836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30836; decide +kernel
    rw [ha]
    exact (canonical30836 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 3) (sourceB2310 + difference 3 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4711) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 3) (sourceB2310 + difference 3 5) sourceC2310) = raw30833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30833; decide +kernel
    rw [ha]
    exact (canonical30833 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2310 + difference 5 4) (sourceB2310 + difference 4 5) sourceC2310) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2310 + difference 5 4) (sourceB2310 + difference 4 5) sourceC2310) = raw30548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2310 sourceB2310 sourceC2310 difference raw30548; decide +kernel
    rw [ha]
    exact (canonical30548 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2310 sourceB2310 sourceC2310
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2310, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1881 : Integer.Sparse.reindex keyMap MixedData.row1881 = numericRow1881 := by decide +kernel

theorem numericCheck1881 (x : Master → ℝ) : Integer.Sparse.eval numericRow1881 x =
    (4 : ℝ) * reducedSource1881 x := by
  norm_num [numericRow1881, reducedSource1881, Integer.Sparse.eval, Sparse.eval, nodeValue4082, nodeValue4298, nodeValue4303, nodeValue4305, nodeValue4313, nodeValue4419, nodeValue4640, nodeValue4644, nodeValue4646, nodeValue4653, nodeValue4709, nodeValue4711, nodeValue4716, nodeValue4731, nodeValue4732, nodeValue4744, nodeValue4745, nodeValue4749, nodeValue4750, nodeValue4753, nodeValue4782, nodeValue4810, nodeValue4811, nodeValue4846, nodeValue5003, nodeValue5050, nodeValue5080, nodeValue5081, nodeValue5111] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1881 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1881 (mixedVector B) = 0 := by
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4298 : mixedVector B (Sum.inr 4298) = Sparse.eval nodeValue4298 (mixedVector B) := by
    change mixedMoment B node4298 node4298Labels = _
    exact sound4298 B hB hF
  have h4303 : mixedVector B (Sum.inr 4303) = Sparse.eval nodeValue4303 (mixedVector B) := by
    change mixedMoment B node4303 node4303Labels = _
    exact sound4303 B hB hF
  have h4305 : mixedVector B (Sum.inr 4305) = Sparse.eval nodeValue4305 (mixedVector B) := by
    change mixedMoment B node4305 node4305Labels = _
    exact sound4305 B hB hF
  have h4313 : mixedVector B (Sum.inr 4313) = Sparse.eval nodeValue4313 (mixedVector B) := by
    change mixedMoment B node4313 node4313Labels = _
    exact sound4313 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4640 : mixedVector B (Sum.inr 4640) = Sparse.eval nodeValue4640 (mixedVector B) := by
    change mixedMoment B node4640 node4640Labels = _
    exact sound4640 B hB hF
  have h4644 : mixedVector B (Sum.inr 4644) = Sparse.eval nodeValue4644 (mixedVector B) := by
    change mixedMoment B node4644 node4644Labels = _
    exact sound4644 B hB hF
  have h4646 : mixedVector B (Sum.inr 4646) = Sparse.eval nodeValue4646 (mixedVector B) := by
    change mixedMoment B node4646 node4646Labels = _
    exact sound4646 B hB hF
  have h4653 : mixedVector B (Sum.inr 4653) = Sparse.eval nodeValue4653 (mixedVector B) := by
    change mixedMoment B node4653 node4653Labels = _
    exact sound4653 B hB hF
  have h4709 : mixedVector B (Sum.inr 4709) = Sparse.eval nodeValue4709 (mixedVector B) := by
    change mixedMoment B node4709 node4709Labels = _
    exact sound4709 B hB hF
  have h4711 : mixedVector B (Sum.inr 4711) = Sparse.eval nodeValue4711 (mixedVector B) := by
    change mixedMoment B node4711 node4711Labels = _
    exact sound4711 B hB hF
  have h4716 : mixedVector B (Sum.inr 4716) = Sparse.eval nodeValue4716 (mixedVector B) := by
    change mixedMoment B node4716 node4716Labels = _
    exact sound4716 B hB hF
  have h4731 : mixedVector B (Sum.inr 4731) = Sparse.eval nodeValue4731 (mixedVector B) := by
    change mixedMoment B node4731 node4731Labels = _
    exact sound4731 B hB hF
  have h4732 : mixedVector B (Sum.inr 4732) = Sparse.eval nodeValue4732 (mixedVector B) := by
    change mixedMoment B node4732 node4732Labels = _
    exact sound4732 B hB hF
  have h4744 : mixedVector B (Sum.inr 4744) = Sparse.eval nodeValue4744 (mixedVector B) := by
    change mixedMoment B node4744 node4744Labels = _
    exact sound4744 B hB hF
  have h4745 : mixedVector B (Sum.inr 4745) = Sparse.eval nodeValue4745 (mixedVector B) := by
    change mixedMoment B node4745 node4745Labels = _
    exact sound4745 B hB hF
  have h4749 : mixedVector B (Sum.inr 4749) = Sparse.eval nodeValue4749 (mixedVector B) := by
    change mixedMoment B node4749 node4749Labels = _
    exact sound4749 B hB hF
  have h4750 : mixedVector B (Sum.inr 4750) = Sparse.eval nodeValue4750 (mixedVector B) := by
    change mixedMoment B node4750 node4750Labels = _
    exact sound4750 B hB hF
  have h4753 : mixedVector B (Sum.inr 4753) = Sparse.eval nodeValue4753 (mixedVector B) := by
    change mixedMoment B node4753 node4753Labels = _
    exact sound4753 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h5003 : mixedVector B (Sum.inr 5003) = Sparse.eval nodeValue5003 (mixedVector B) := by
    change mixedMoment B node5003 node5003Labels = _
    exact sound5003 B hB hF
  have h5050 : mixedVector B (Sum.inr 5050) = Sparse.eval nodeValue5050 (mixedVector B) := by
    change mixedMoment B node5050 node5050Labels = _
    exact sound5050 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  simpa only [sourceForm2310, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4082, h4298, h4303, h4305, h4313, h4419, h4640, h4644, h4646, h4653, h4709, h4711, h4716, h4731, h4732, h4744, h4745, h4749, h4750, h4753, h4782, h4810, h4811, h4846, h5003, h5050, h5080, h5081, h5111, reducedSource1881] using sourceEq2310 B hB

theorem rowSound1881_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1881 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1881, numericCheck1881, reducedZero1881 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881_e_oai
