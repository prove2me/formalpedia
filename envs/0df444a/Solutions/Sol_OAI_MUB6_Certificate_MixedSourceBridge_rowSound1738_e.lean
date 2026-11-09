-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:38:24.218524+00:00
-- url     : https://prove2.me/submissions/c027f945-5724-4401-bfa7-1560081c287a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E104
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

theorem canonical1356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1356 raw1356Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw1356 raw1356Labels = mixedMoment B raw1356step0 raw1356step0Labels := by
      have ha : raw1356step0 = (fun i j => raw1356 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1356step0 raw1356; decide +kernel
      have hl : raw1356step0Labels = raw1356Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1356 raw1356Labels permutation32 permutation4
    mixedMoment B raw1356step0 raw1356step0Labels = mixedMoment B raw1356step1 raw1356step1Labels := by
      have ha : raw1356step1 = raw1356step0 := by apply Matrix.ext; unfold raw1356step1 raw1356step0; decide +kernel
      have hl : raw1356step0Labels = labelEmbedding7 ∘ raw1356step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1356step0 raw1356step0Labels raw1356step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4538 node4538Labels := by rfl

theorem canonical1357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1357 raw1357Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw1357 raw1357Labels = mixedMoment B raw1357step0 raw1357step0Labels := by
      have ha : raw1357step0 = (fun i j => raw1357 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1357step0 raw1357; decide +kernel
      have hl : raw1357step0Labels = raw1357Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1357 raw1357Labels permutation32 permutation4
    _ = mixedMoment B node1123 node1123Labels := by rfl

theorem canonical1358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1358 raw1358Labels = mixedMoment B node1937 node1937Labels := by
  calc
    mixedMoment B raw1358 raw1358Labels = mixedMoment B raw1358step0 raw1358step0Labels := by
      have ha : raw1358step0 = (fun i j => raw1358 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1358step0 raw1358; decide +kernel
      have hl : raw1358step0Labels = raw1358Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1358 raw1358Labels permutation151 permutation6
    mixedMoment B raw1358step0 raw1358step0Labels = mixedMoment B raw1358step1 raw1358step1Labels := by
      have ha : raw1358step1 = raw1358step0 := by apply Matrix.ext; unfold raw1358step1 raw1358step0; decide +kernel
      have hl : raw1358step0Labels = labelEmbedding1 ∘ raw1358step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1358step0 raw1358step0Labels raw1358step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1937 node1937Labels := by rfl

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

theorem canonical1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1491 raw1491Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw1491 raw1491Labels = mixedMoment B raw1491step0 raw1491step0Labels := by
      have ha : raw1491step0 = (fun i j => raw1491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1491step0 raw1491; decide +kernel
      have hl : raw1491step0Labels = raw1491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1491 raw1491Labels permutation32 permutation4
    mixedMoment B raw1491step0 raw1491step0Labels = mixedMoment B raw1491step1 raw1491step1Labels := by
      have ha : raw1491step1 = raw1491step0 := by apply Matrix.ext; unfold raw1491step1 raw1491step0; decide +kernel
      have hl : raw1491step0Labels = labelEmbedding7 ∘ raw1491step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1491step0 raw1491step0Labels raw1491step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical1492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1492 raw1492Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw1492 raw1492Labels = mixedMoment B raw1492step0 raw1492step0Labels := by
      have ha : raw1492step0 = (fun i j => raw1492 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1492step0 raw1492; decide +kernel
      have hl : raw1492step0Labels = raw1492Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1492 raw1492Labels permutation32 permutation4
    _ = mixedMoment B node1766 node1766Labels := by rfl

theorem canonical1493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1493 raw1493Labels = mixedMoment B node1850 node1850Labels := by
  calc
    mixedMoment B raw1493 raw1493Labels = mixedMoment B raw1493step0 raw1493step0Labels := by
      have ha : raw1493step0 = (fun i j => raw1493 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1493step0 raw1493; decide +kernel
      have hl : raw1493step0Labels = raw1493Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1493 raw1493Labels permutation32 permutation6
    mixedMoment B raw1493step0 raw1493step0Labels = mixedMoment B raw1493step1 raw1493step1Labels := by
      have ha : raw1493step1 = -raw1493step0 := by apply Matrix.ext; change ∀ i j, raw1493step1 i j = -(raw1493step0 i j); unfold raw1493step1 raw1493step0; decide +kernel
      have hl : raw1493step1Labels = raw1493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1493step1 raw1493step1Labels = mixedMoment B raw1493step2 raw1493step2Labels := by
      have ha : raw1493step2 = raw1493step1 := by apply Matrix.ext; unfold raw1493step2 raw1493step1; decide +kernel
      have hl : raw1493step1Labels = labelEmbedding1 ∘ raw1493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1493step1 raw1493step1Labels raw1493step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1850 node1850Labels := by rfl

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

theorem canonical1590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1590 raw1590Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw1590 raw1590Labels = mixedMoment B raw1590step0 raw1590step0Labels := by
      have ha : raw1590step0 = (fun i j => raw1590 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1590step0 raw1590; decide +kernel
      have hl : raw1590step0Labels = raw1590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1590 raw1590Labels permutation152 permutation4
    mixedMoment B raw1590step0 raw1590step0Labels = mixedMoment B raw1590step1 raw1590step1Labels := by
      have ha : raw1590step1 = raw1590step0 := by apply Matrix.ext; unfold raw1590step1 raw1590step0; decide +kernel
      have hl : raw1590step0Labels = labelEmbedding7 ∘ raw1590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1590step0 raw1590step0Labels raw1590step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

theorem canonical1591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1591 raw1591Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw1591 raw1591Labels = mixedMoment B raw1591step0 raw1591step0Labels := by
      have ha : raw1591step0 = (fun i j => raw1591 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1591step0 raw1591; decide +kernel
      have hl : raw1591step0Labels = raw1591Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1591 raw1591Labels permutation152 permutation4
    _ = mixedMoment B node1860 node1860Labels := by rfl

theorem canonical1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1592 raw1592Labels = mixedMoment B node1888 node1888Labels := by
  calc
    mixedMoment B raw1592 raw1592Labels = mixedMoment B raw1592step0 raw1592step0Labels := by
      have ha : raw1592step0 = (fun i j => raw1592 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1592step0 raw1592; decide +kernel
      have hl : raw1592step0Labels = raw1592Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1592 raw1592Labels permutation152 permutation6
    mixedMoment B raw1592step0 raw1592step0Labels = mixedMoment B raw1592step1 raw1592step1Labels := by
      have ha : raw1592step1 = -raw1592step0 := by apply Matrix.ext; change ∀ i j, raw1592step1 i j = -(raw1592step0 i j); unfold raw1592step1 raw1592step0; decide +kernel
      have hl : raw1592step1Labels = raw1592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1592step1 raw1592step1Labels = mixedMoment B raw1592step2 raw1592step2Labels := by
      have ha : raw1592step2 = raw1592step1 := by apply Matrix.ext; unfold raw1592step2 raw1592step1; decide +kernel
      have hl : raw1592step1Labels = labelEmbedding1 ∘ raw1592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1592step1 raw1592step1Labels raw1592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1888 node1888Labels := by rfl

theorem canonical1620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1620 raw1620Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw1620 raw1620Labels = mixedMoment B raw1620step0 raw1620step0Labels := by
      have ha : raw1620step0 = (fun i j => raw1620 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1620step0 raw1620; decide +kernel
      have hl : raw1620step0Labels = raw1620Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1620 raw1620Labels permutation152 permutation4
    mixedMoment B raw1620step0 raw1620step0Labels = mixedMoment B raw1620step1 raw1620step1Labels := by
      have ha : raw1620step1 = raw1620step0 := by apply Matrix.ext; unfold raw1620step1 raw1620step0; decide +kernel
      have hl : raw1620step0Labels = labelEmbedding7 ∘ raw1620step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1620step0 raw1620step0Labels raw1620step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

theorem canonical1621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1621 raw1621Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw1621 raw1621Labels = mixedMoment B raw1621step0 raw1621step0Labels := by
      have ha : raw1621step0 = (fun i j => raw1621 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1621step0 raw1621; decide +kernel
      have hl : raw1621step0Labels = raw1621Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1621 raw1621Labels permutation152 permutation4
    _ = mixedMoment B node1875 node1875Labels := by rfl

theorem canonical1622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1622 raw1622Labels = mixedMoment B node1905 node1905Labels := by
  calc
    mixedMoment B raw1622 raw1622Labels = mixedMoment B raw1622step0 raw1622step0Labels := by
      have ha : raw1622step0 = (fun i j => raw1622 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1622step0 raw1622; decide +kernel
      have hl : raw1622step0Labels = raw1622Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1622 raw1622Labels permutation158 permutation6
    mixedMoment B raw1622step0 raw1622step0Labels = mixedMoment B raw1622step1 raw1622step1Labels := by
      have ha : raw1622step1 = -raw1622step0 := by apply Matrix.ext; change ∀ i j, raw1622step1 i j = -(raw1622step0 i j); unfold raw1622step1 raw1622step0; decide +kernel
      have hl : raw1622step1Labels = raw1622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1622step1 raw1622step1Labels = mixedMoment B raw1622step2 raw1622step2Labels := by
      have ha : raw1622step2 = raw1622step1 := by apply Matrix.ext; unfold raw1622step2 raw1622step1; decide +kernel
      have hl : raw1622step1Labels = labelEmbedding1 ∘ raw1622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1622step1 raw1622step1Labels raw1622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1905 node1905Labels := by rfl

theorem canonical1635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1635 raw1635Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw1635 raw1635Labels = mixedMoment B raw1635step0 raw1635step0Labels := by
      have ha : raw1635step0 = (fun i j => raw1635 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1635step0 raw1635; decide +kernel
      have hl : raw1635step0Labels = raw1635Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1635 raw1635Labels permutation32 permutation4
    mixedMoment B raw1635step0 raw1635step0Labels = mixedMoment B raw1635step1 raw1635step1Labels := by
      have ha : raw1635step1 = raw1635step0 := by apply Matrix.ext; unfold raw1635step1 raw1635step0; decide +kernel
      have hl : raw1635step0Labels = labelEmbedding7 ∘ raw1635step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1635step0 raw1635step0Labels raw1635step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

theorem canonical1636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1636 raw1636Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw1636 raw1636Labels = mixedMoment B raw1636step0 raw1636step0Labels := by
      have ha : raw1636step0 = (fun i j => raw1636 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1636step0 raw1636; decide +kernel
      have hl : raw1636step0Labels = raw1636Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1636 raw1636Labels permutation32 permutation4
    _ = mixedMoment B node1880 node1880Labels := by rfl

theorem canonical1637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1637 raw1637Labels = mixedMoment B node1938 node1938Labels := by
  calc
    mixedMoment B raw1637 raw1637Labels = mixedMoment B raw1637step0 raw1637step0Labels := by
      have ha : raw1637step0 = (fun i j => raw1637 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1637step0 raw1637; decide +kernel
      have hl : raw1637step0Labels = raw1637Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1637 raw1637Labels permutation32 permutation6
    mixedMoment B raw1637step0 raw1637step0Labels = mixedMoment B raw1637step1 raw1637step1Labels := by
      have ha : raw1637step1 = -raw1637step0 := by apply Matrix.ext; change ∀ i j, raw1637step1 i j = -(raw1637step0 i j); unfold raw1637step1 raw1637step0; decide +kernel
      have hl : raw1637step1Labels = raw1637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1637step1 raw1637step1Labels = mixedMoment B raw1637step2 raw1637step2Labels := by
      have ha : raw1637step2 = raw1637step1 := by apply Matrix.ext; unfold raw1637step2 raw1637step1; decide +kernel
      have hl : raw1637step1Labels = labelEmbedding1 ∘ raw1637step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1637step1 raw1637step1Labels raw1637step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1938 node1938Labels := by rfl

theorem canonical1641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1641 raw1641Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw1641 raw1641Labels = mixedMoment B raw1641step0 raw1641step0Labels := by
      have ha : raw1641step0 = (fun i j => raw1641 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1641step0 raw1641; decide +kernel
      have hl : raw1641step0Labels = raw1641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1641 raw1641Labels permutation152 permutation4
    mixedMoment B raw1641step0 raw1641step0Labels = mixedMoment B raw1641step1 raw1641step1Labels := by
      have ha : raw1641step1 = raw1641step0 := by apply Matrix.ext; unfold raw1641step1 raw1641step0; decide +kernel
      have hl : raw1641step0Labels = labelEmbedding7 ∘ raw1641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1641step0 raw1641step0Labels raw1641step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

theorem canonical1642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1642 raw1642Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw1642 raw1642Labels = mixedMoment B raw1642step0 raw1642step0Labels := by
      have ha : raw1642step0 = (fun i j => raw1642 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1642step0 raw1642; decide +kernel
      have hl : raw1642step0Labels = raw1642Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1642 raw1642Labels permutation152 permutation4
    _ = mixedMoment B node1897 node1897Labels := by rfl

theorem canonical1643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1643 raw1643Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw1643 raw1643Labels = mixedMoment B raw1643step0 raw1643step0Labels := by
      have ha : raw1643step0 = (fun i j => raw1643 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1643step0 raw1643; decide +kernel
      have hl : raw1643step0Labels = raw1643Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1643 raw1643Labels permutation164 permutation6
    mixedMoment B raw1643step0 raw1643step0Labels = mixedMoment B raw1643step1 raw1643step1Labels := by
      have ha : raw1643step1 = -raw1643step0 := by apply Matrix.ext; change ∀ i j, raw1643step1 i j = -(raw1643step0 i j); unfold raw1643step1 raw1643step0; decide +kernel
      have hl : raw1643step1Labels = raw1643step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1643step1 raw1643step1Labels = mixedMoment B raw1643step2 raw1643step2Labels := by
      have ha : raw1643step2 = raw1643step1 := by apply Matrix.ext; unfold raw1643step2 raw1643step1; decide +kernel
      have hl : raw1643step1Labels = labelEmbedding1 ∘ raw1643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1643step1 raw1643step1Labels raw1643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1907 node1907Labels := by rfl

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

theorem canonical1755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1755 raw1755Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw1755 raw1755Labels = mixedMoment B raw1755step0 raw1755step0Labels := by
      have ha : raw1755step0 = (fun i j => raw1755 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1755step0 raw1755; decide +kernel
      have hl : raw1755step0Labels = raw1755Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1755 raw1755Labels permutation32 permutation4
    mixedMoment B raw1755step0 raw1755step0Labels = mixedMoment B raw1755step1 raw1755step1Labels := by
      have ha : raw1755step1 = raw1755step0 := by apply Matrix.ext; unfold raw1755step1 raw1755step0; decide +kernel
      have hl : raw1755step0Labels = labelEmbedding7 ∘ raw1755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1755step0 raw1755step0Labels raw1755step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

theorem canonical1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1756 raw1756Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw1756 raw1756Labels = mixedMoment B raw1756step0 raw1756step0Labels := by
      have ha : raw1756step0 = (fun i j => raw1756 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1756step0 raw1756; decide +kernel
      have hl : raw1756step0Labels = raw1756Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1756 raw1756Labels permutation32 permutation4
    _ = mixedMoment B node2047 node2047Labels := by rfl

theorem canonical1757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1757 raw1757Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw1757 raw1757Labels = mixedMoment B raw1757step0 raw1757step0Labels := by
      have ha : raw1757step0 = (fun i j => raw1757 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1757step0 raw1757; decide +kernel
      have hl : raw1757step0Labels = raw1757Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1757 raw1757Labels permutation38 permutation6
    mixedMoment B raw1757step0 raw1757step0Labels = mixedMoment B raw1757step1 raw1757step1Labels := by
      have ha : raw1757step1 = -raw1757step0 := by apply Matrix.ext; change ∀ i j, raw1757step1 i j = -(raw1757step0 i j); unfold raw1757step1 raw1757step0; decide +kernel
      have hl : raw1757step1Labels = raw1757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1757step1 raw1757step1Labels = mixedMoment B raw1757step2 raw1757step2Labels := by
      have ha : raw1757step2 = raw1757step1 := by apply Matrix.ext; unfold raw1757step2 raw1757step1; decide +kernel
      have hl : raw1757step1Labels = labelEmbedding1 ∘ raw1757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1757step1 raw1757step1Labels raw1757step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

theorem canonical1764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1764 raw1764Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw1764 raw1764Labels = mixedMoment B raw1764step0 raw1764step0Labels := by
      have ha : raw1764step0 = (fun i j => raw1764 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1764step0 raw1764; decide +kernel
      have hl : raw1764step0Labels = raw1764Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1764 raw1764Labels permutation32 permutation4
    mixedMoment B raw1764step0 raw1764step0Labels = mixedMoment B raw1764step1 raw1764step1Labels := by
      have ha : raw1764step1 = raw1764step0 := by apply Matrix.ext; unfold raw1764step1 raw1764step0; decide +kernel
      have hl : raw1764step0Labels = labelEmbedding7 ∘ raw1764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1764step0 raw1764step0Labels raw1764step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical1765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1765 raw1765Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw1765 raw1765Labels = mixedMoment B raw1765step0 raw1765step0Labels := by
      have ha : raw1765step0 = (fun i j => raw1765 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1765step0 raw1765; decide +kernel
      have hl : raw1765step0Labels = raw1765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1765 raw1765Labels permutation32 permutation4
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1766 raw1766Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw1766 raw1766Labels = mixedMoment B raw1766step0 raw1766step0Labels := by
      have ha : raw1766step0 = (fun i j => raw1766 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1766step0 raw1766; decide +kernel
      have hl : raw1766step0Labels = raw1766Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1766 raw1766Labels permutation32 permutation6
    mixedMoment B raw1766step0 raw1766step0Labels = mixedMoment B raw1766step1 raw1766step1Labels := by
      have ha : raw1766step1 = -raw1766step0 := by apply Matrix.ext; change ∀ i j, raw1766step1 i j = -(raw1766step0 i j); unfold raw1766step1 raw1766step0; decide +kernel
      have hl : raw1766step1Labels = raw1766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1766step1 raw1766step1Labels = mixedMoment B raw1766step2 raw1766step2Labels := by
      have ha : raw1766step2 = raw1766step1 := by apply Matrix.ext; unfold raw1766step2 raw1766step1; decide +kernel
      have hl : raw1766step1Labels = labelEmbedding1 ∘ raw1766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1766step1 raw1766step1Labels raw1766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

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

theorem canonical2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2022 raw2022Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw2022 raw2022Labels = mixedMoment B raw2022step0 raw2022step0Labels := by
      have ha : raw2022step0 = (fun i j => raw2022 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2022step0 raw2022; decide +kernel
      have hl : raw2022step0Labels = raw2022Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2022 raw2022Labels permutation32 permutation4
    mixedMoment B raw2022step0 raw2022step0Labels = mixedMoment B raw2022step1 raw2022step1Labels := by
      have ha : raw2022step1 = raw2022step0 := by apply Matrix.ext; unfold raw2022step1 raw2022step0; decide +kernel
      have hl : raw2022step0Labels = labelEmbedding7 ∘ raw2022step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2022step0 raw2022step0Labels raw2022step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

theorem canonical2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2023 raw2023Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw2023 raw2023Labels = mixedMoment B raw2023step0 raw2023step0Labels := by
      have ha : raw2023step0 = (fun i j => raw2023 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2023step0 raw2023; decide +kernel
      have hl : raw2023step0Labels = raw2023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2023 raw2023Labels permutation32 permutation4
    _ = mixedMoment B node2399 node2399Labels := by rfl

theorem canonical2024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2024 raw2024Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw2024 raw2024Labels = mixedMoment B raw2024step0 raw2024step0Labels := by
      have ha : raw2024step0 = (fun i j => raw2024 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2024step0 raw2024; decide +kernel
      have hl : raw2024step0Labels = raw2024Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2024 raw2024Labels permutation151 permutation6
    mixedMoment B raw2024step0 raw2024step0Labels = mixedMoment B raw2024step1 raw2024step1Labels := by
      have ha : raw2024step1 = raw2024step0 := by apply Matrix.ext; unfold raw2024step1 raw2024step0; decide +kernel
      have hl : raw2024step0Labels = labelEmbedding1 ∘ raw2024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2024step0 raw2024step0Labels raw2024step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2467 node2467Labels := by rfl

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

theorem canonical2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2079 raw2079Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw2079 raw2079Labels = mixedMoment B raw2079step0 raw2079step0Labels := by
      have ha : raw2079step0 = (fun i j => raw2079 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2079step0 raw2079; decide +kernel
      have hl : raw2079step0Labels = raw2079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2079 raw2079Labels permutation152 permutation4
    mixedMoment B raw2079step0 raw2079step0Labels = mixedMoment B raw2079step1 raw2079step1Labels := by
      have ha : raw2079step1 = raw2079step0 := by apply Matrix.ext; unfold raw2079step1 raw2079step0; decide +kernel
      have hl : raw2079step0Labels = labelEmbedding7 ∘ raw2079step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2079step0 raw2079step0Labels raw2079step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

theorem canonical2080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2080 raw2080Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw2080 raw2080Labels = mixedMoment B raw2080step0 raw2080step0Labels := by
      have ha : raw2080step0 = (fun i j => raw2080 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2080step0 raw2080; decide +kernel
      have hl : raw2080step0Labels = raw2080Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2080 raw2080Labels permutation152 permutation4
    _ = mixedMoment B node2458 node2458Labels := by rfl

theorem canonical2081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2081 raw2081Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw2081 raw2081Labels = mixedMoment B raw2081step0 raw2081step0Labels := by
      have ha : raw2081step0 = (fun i j => raw2081 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2081step0 raw2081; decide +kernel
      have hl : raw2081step0Labels = raw2081Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2081 raw2081Labels permutation688 permutation6
    mixedMoment B raw2081step0 raw2081step0Labels = mixedMoment B raw2081step1 raw2081step1Labels := by
      have ha : raw2081step1 = raw2081step0 := by apply Matrix.ext; unfold raw2081step1 raw2081step0; decide +kernel
      have hl : raw2081step0Labels = labelEmbedding1 ∘ raw2081step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2081step0 raw2081step0Labels raw2081step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2458 node2458Labels := by rfl

theorem canonical2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2115 raw2115Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw2115 raw2115Labels = mixedMoment B raw2115step0 raw2115step0Labels := by
      have ha : raw2115step0 = (fun i j => raw2115 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2115step0 raw2115; decide +kernel
      have hl : raw2115step0Labels = raw2115Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2115 raw2115Labels permutation32 permutation4
    mixedMoment B raw2115step0 raw2115step0Labels = mixedMoment B raw2115step1 raw2115step1Labels := by
      have ha : raw2115step1 = raw2115step0 := by apply Matrix.ext; unfold raw2115step1 raw2115step0; decide +kernel
      have hl : raw2115step0Labels = labelEmbedding7 ∘ raw2115step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2115step0 raw2115step0Labels raw2115step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

theorem canonical2116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2116 raw2116Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw2116 raw2116Labels = mixedMoment B raw2116step0 raw2116step0Labels := by
      have ha : raw2116step0 = (fun i j => raw2116 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2116step0 raw2116; decide +kernel
      have hl : raw2116step0Labels = raw2116Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2116 raw2116Labels permutation32 permutation4
    _ = mixedMoment B node2504 node2504Labels := by rfl

theorem canonical2117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2117 raw2117Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw2117 raw2117Labels = mixedMoment B raw2117step0 raw2117step0Labels := by
      have ha : raw2117step0 = (fun i j => raw2117 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2117step0 raw2117; decide +kernel
      have hl : raw2117step0Labels = raw2117Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2117 raw2117Labels permutation151 permutation6
    mixedMoment B raw2117step0 raw2117step0Labels = mixedMoment B raw2117step1 raw2117step1Labels := by
      have ha : raw2117step1 = raw2117step0 := by apply Matrix.ext; unfold raw2117step1 raw2117step0; decide +kernel
      have hl : raw2117step0Labels = labelEmbedding1 ∘ raw2117step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2117step0 raw2117step0Labels raw2117step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2504 node2504Labels := by rfl

theorem canonical2124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2124 raw2124Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw2124 raw2124Labels = mixedMoment B raw2124step0 raw2124step0Labels := by
      have ha : raw2124step0 = (fun i j => raw2124 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2124step0 raw2124; decide +kernel
      have hl : raw2124step0Labels = raw2124Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2124 raw2124Labels permutation32 permutation4
    mixedMoment B raw2124step0 raw2124step0Labels = mixedMoment B raw2124step1 raw2124step1Labels := by
      have ha : raw2124step1 = raw2124step0 := by apply Matrix.ext; unfold raw2124step1 raw2124step0; decide +kernel
      have hl : raw2124step0Labels = labelEmbedding7 ∘ raw2124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2124step0 raw2124step0Labels raw2124step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical2125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2125 raw2125Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw2125 raw2125Labels = mixedMoment B raw2125step0 raw2125step0Labels := by
      have ha : raw2125step0 = (fun i j => raw2125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2125step0 raw2125; decide +kernel
      have hl : raw2125step0Labels = raw2125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2125 raw2125Labels permutation32 permutation4
    _ = mixedMoment B node2509 node2509Labels := by rfl

theorem canonical2126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2126 raw2126Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw2126 raw2126Labels = mixedMoment B raw2126step0 raw2126step0Labels := by
      have ha : raw2126step0 = (fun i j => raw2126 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2126step0 raw2126; decide +kernel
      have hl : raw2126step0Labels = raw2126Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2126 raw2126Labels permutation145 permutation6
    mixedMoment B raw2126step0 raw2126step0Labels = mixedMoment B raw2126step1 raw2126step1Labels := by
      have ha : raw2126step1 = raw2126step0 := by apply Matrix.ext; unfold raw2126step1 raw2126step0; decide +kernel
      have hl : raw2126step0Labels = labelEmbedding1 ∘ raw2126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2126step0 raw2126step0Labels raw2126step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29146 raw29146Labels = mixedMoment B node4745 node4745Labels := by
  calc
    mixedMoment B raw29146 raw29146Labels = mixedMoment B raw29146step0 raw29146step0Labels := by
      have hz : ∀ j, raw29146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29146step0 = (fun i j => raw29146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29146step0 raw29146; decide +kernel
      have hl : raw29146step0Labels = raw29146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29146 raw29146Labels permutation346 hz
    mixedMoment B raw29146step0 raw29146step0Labels = mixedMoment B raw29146step1 raw29146step1Labels := by
      have ha : raw29146step1 = (fun i j => raw29146step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29146step1 raw29146step0; decide +kernel
      have hl : raw29146step1Labels = raw29146step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29146step0 raw29146step0Labels permutation151 permutation2
    mixedMoment B raw29146step1 raw29146step1Labels = mixedMoment B raw29146step2 raw29146step2Labels := by
      have ha : raw29146step2 = -raw29146step1 := by apply Matrix.ext; change ∀ i j, raw29146step2 i j = -(raw29146step1 i j); unfold raw29146step2 raw29146step1; decide +kernel
      have hl : raw29146step2Labels = raw29146step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4745 node4745Labels := by rfl

theorem canonical29147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29147 raw29147Labels = mixedMoment B node4736 node4736Labels := by
  calc
    mixedMoment B raw29147 raw29147Labels = mixedMoment B raw29147step0 raw29147step0Labels := by
      have ha : raw29147step0 = (fun i j => raw29147 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29147step0 raw29147; decide +kernel
      have hl : raw29147step0Labels = raw29147Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29147 raw29147Labels permutation688 permutation2
    mixedMoment B raw29147step0 raw29147step0Labels = mixedMoment B raw29147step1 raw29147step1Labels := by
      have ha : raw29147step1 = -raw29147step0 := by apply Matrix.ext; change ∀ i j, raw29147step1 i j = -(raw29147step0 i j); unfold raw29147step1 raw29147step0; decide +kernel
      have hl : raw29147step1Labels = raw29147step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4736 node4736Labels := by rfl

theorem canonical29148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29148 raw29148Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw29148 raw29148Labels = mixedMoment B raw29148step0 raw29148step0Labels := by
      have hz : ∀ j, raw29148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29148step0 = (fun i j => raw29148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29148step0 raw29148; decide +kernel
      have hl : raw29148step0Labels = raw29148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29148 raw29148Labels permutation346 hz
    mixedMoment B raw29148step0 raw29148step0Labels = mixedMoment B raw29148step1 raw29148step1Labels := by
      have hz : ∀ i, raw29148step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw29148step1 = (fun i j => raw29148step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw29148step1 raw29148step0; decide +kernel
      have hl : raw29148step1Labels = (fun j => raw29148step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29148step0 raw29148step0Labels permutation4 hz
    mixedMoment B raw29148step1 raw29148step1Labels = mixedMoment B raw29148step2 raw29148step2Labels := by
      have ha : raw29148step2 = (fun i j => raw29148step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29148step2 raw29148step1; decide +kernel
      have hl : raw29148step2Labels = raw29148step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29148step1 raw29148step1Labels permutation149 permutation0
    mixedMoment B raw29148step2 raw29148step2Labels = mixedMoment B raw29148step3 raw29148step3Labels := by
      have ha : raw29148step3 = -raw29148step2 := by apply Matrix.ext; change ∀ i j, raw29148step3 i j = -(raw29148step2 i j); unfold raw29148step3 raw29148step2; decide +kernel
      have hl : raw29148step3Labels = raw29148step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29148step3 raw29148step3Labels = mixedMoment B raw29148step4 raw29148step4Labels := by
      have ha : raw29148step4 = raw29148step3 := by apply Matrix.ext; unfold raw29148step4 raw29148step3; decide +kernel
      have hl : raw29148step3Labels = labelEmbedding2 ∘ raw29148step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29148step3 raw29148step3Labels raw29148step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical29149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29149 raw29149Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw29149 raw29149Labels = mixedMoment B raw29149step0 raw29149step0Labels := by
      have hz : ∀ j, raw29149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29149step0 = (fun i j => raw29149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29149step0 raw29149; decide +kernel
      have hl : raw29149step0Labels = raw29149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29149 raw29149Labels permutation346 hz
    mixedMoment B raw29149step0 raw29149step0Labels = mixedMoment B raw29149step1 raw29149step1Labels := by
      have ha : raw29149step1 = (fun i j => raw29149step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29149step1 raw29149step0; decide +kernel
      have hl : raw29149step1Labels = raw29149step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29149step0 raw29149step0Labels permutation151 permutation7
    mixedMoment B raw29149step1 raw29149step1Labels = mixedMoment B raw29149step2 raw29149step2Labels := by
      have ha : raw29149step2 = raw29149step1 := by apply Matrix.ext; unfold raw29149step2 raw29149step1; decide +kernel
      have hl : raw29149step1Labels = labelEmbedding10 ∘ raw29149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29149step1 raw29149step1Labels raw29149step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical29150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29150 raw29150Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw29150 raw29150Labels = mixedMoment B raw29150step0 raw29150step0Labels := by
      have hz : ∀ j, raw29150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29150step0 = (fun i j => raw29150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29150step0 raw29150; decide +kernel
      have hl : raw29150step0Labels = raw29150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29150 raw29150Labels permutation346 hz
    mixedMoment B raw29150step0 raw29150step0Labels = mixedMoment B raw29150step1 raw29150step1Labels := by
      have ha : raw29150step1 = (fun i j => raw29150step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29150step1 raw29150step0; decide +kernel
      have hl : raw29150step1Labels = raw29150step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29150step0 raw29150step0Labels permutation151 permutation7
    mixedMoment B raw29150step1 raw29150step1Labels = mixedMoment B raw29150step2 raw29150step2Labels := by
      have ha : raw29150step2 = raw29150step1 := by apply Matrix.ext; unfold raw29150step2 raw29150step1; decide +kernel
      have hl : raw29150step1Labels = labelEmbedding10 ∘ raw29150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29150step1 raw29150step1Labels raw29150step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical29151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29151 raw29151Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw29151 raw29151Labels = mixedMoment B raw29151step0 raw29151step0Labels := by
      have hz : ∀ j, raw29151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29151step0 = (fun i j => raw29151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29151step0 raw29151; decide +kernel
      have hl : raw29151step0Labels = raw29151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29151 raw29151Labels permutation346 hz
    _ = mixedMoment B node4583 node4583Labels := by rfl

theorem canonical29152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29152 raw29152Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw29152 raw29152Labels = mixedMoment B raw29152step0 raw29152step0Labels := by
      have ha : raw29152step0 = (fun i j => raw29152 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29152step0 raw29152; decide +kernel
      have hl : raw29152step0Labels = raw29152Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29152 raw29152Labels permutation676 permutation2
    mixedMoment B raw29152step0 raw29152step0Labels = mixedMoment B raw29152step1 raw29152step1Labels := by
      have ha : raw29152step1 = -raw29152step0 := by apply Matrix.ext; change ∀ i j, raw29152step1 i j = -(raw29152step0 i j); unfold raw29152step1 raw29152step0; decide +kernel
      have hl : raw29152step1Labels = raw29152step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4728 node4728Labels := by rfl

theorem canonical29153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29153 raw29153Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw29153 raw29153Labels = mixedMoment B raw29153step0 raw29153step0Labels := by
      have hz : ∀ j, raw29153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29153step0 = (fun i j => raw29153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29153step0 raw29153; decide +kernel
      have hl : raw29153step0Labels = raw29153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29153 raw29153Labels permutation346 hz
    mixedMoment B raw29153step0 raw29153step0Labels = mixedMoment B raw29153step1 raw29153step1Labels := by
      have ha : raw29153step1 = (fun i j => raw29153step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29153step1 raw29153step0; decide +kernel
      have hl : raw29153step1Labels = raw29153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29153step0 raw29153step0Labels permutation149 permutation2
    mixedMoment B raw29153step1 raw29153step1Labels = mixedMoment B raw29153step2 raw29153step2Labels := by
      have ha : raw29153step2 = -raw29153step1 := by apply Matrix.ext; change ∀ i j, raw29153step2 i j = -(raw29153step1 i j); unfold raw29153step2 raw29153step1; decide +kernel
      have hl : raw29153step2Labels = raw29153step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4741 node4741Labels := by rfl

theorem canonical29154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29154 raw29154Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw29154 raw29154Labels = mixedMoment B raw29154step0 raw29154step0Labels := by
      have hz : ∀ j, raw29154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29154step0 = (fun i j => raw29154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29154step0 raw29154; decide +kernel
      have hl : raw29154step0Labels = raw29154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29154 raw29154Labels permutation346 hz
    mixedMoment B raw29154step0 raw29154step0Labels = mixedMoment B raw29154step1 raw29154step1Labels := by
      have ha : raw29154step1 = (fun i j => raw29154step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29154step1 raw29154step0; decide +kernel
      have hl : raw29154step1Labels = raw29154step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29154step0 raw29154step0Labels permutation149 permutation7
    mixedMoment B raw29154step1 raw29154step1Labels = mixedMoment B raw29154step2 raw29154step2Labels := by
      have ha : raw29154step2 = raw29154step1 := by apply Matrix.ext; unfold raw29154step2 raw29154step1; decide +kernel
      have hl : raw29154step1Labels = labelEmbedding10 ∘ raw29154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29154step1 raw29154step1Labels raw29154step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical29155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29155 raw29155Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw29155 raw29155Labels = mixedMoment B raw29155step0 raw29155step0Labels := by
      have hz : ∀ j, raw29155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29155step0 = (fun i j => raw29155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29155step0 raw29155; decide +kernel
      have hl : raw29155step0Labels = raw29155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29155 raw29155Labels permutation346 hz
    mixedMoment B raw29155step0 raw29155step0Labels = mixedMoment B raw29155step1 raw29155step1Labels := by
      have ha : raw29155step1 = (fun i j => raw29155step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29155step1 raw29155step0; decide +kernel
      have hl : raw29155step1Labels = raw29155step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29155step0 raw29155step0Labels permutation149 permutation7
    mixedMoment B raw29155step1 raw29155step1Labels = mixedMoment B raw29155step2 raw29155step2Labels := by
      have ha : raw29155step2 = raw29155step1 := by apply Matrix.ext; unfold raw29155step2 raw29155step1; decide +kernel
      have hl : raw29155step1Labels = labelEmbedding10 ∘ raw29155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29155step1 raw29155step1Labels raw29155step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical29156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29156 raw29156Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw29156 raw29156Labels = mixedMoment B raw29156step0 raw29156step0Labels := by
      have ha : raw29156step0 = (fun i j => raw29156 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29156step0 raw29156; decide +kernel
      have hl : raw29156step0Labels = raw29156Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29156 raw29156Labels permutation158 permutation2
    _ = mixedMoment B node4521 node4521Labels := by rfl

theorem canonical29157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29157 raw29157Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw29157 raw29157Labels = mixedMoment B raw29157step0 raw29157step0Labels := by
      have ha : raw29157step0 = (fun i j => raw29157 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29157step0 raw29157; decide +kernel
      have hl : raw29157step0Labels = raw29157Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29157 raw29157Labels permutation682 permutation2
    mixedMoment B raw29157step0 raw29157step0Labels = mixedMoment B raw29157step1 raw29157step1Labels := by
      have ha : raw29157step1 = -raw29157step0 := by apply Matrix.ext; change ∀ i j, raw29157step1 i j = -(raw29157step0 i j); unfold raw29157step1 raw29157step0; decide +kernel
      have hl : raw29157step1Labels = raw29157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4706 node4706Labels := by rfl

theorem canonical29158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29158 raw29158Labels = mixedMoment B node4712 node4712Labels := by
  calc
    mixedMoment B raw29158 raw29158Labels = mixedMoment B raw29158step0 raw29158step0Labels := by
      have ha : raw29158step0 = (fun i j => raw29158 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29158step0 raw29158; decide +kernel
      have hl : raw29158step0Labels = raw29158Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29158 raw29158Labels permutation680 permutation2
    mixedMoment B raw29158step0 raw29158step0Labels = mixedMoment B raw29158step1 raw29158step1Labels := by
      have ha : raw29158step1 = -raw29158step0 := by apply Matrix.ext; change ∀ i j, raw29158step1 i j = -(raw29158step0 i j); unfold raw29158step1 raw29158step0; decide +kernel
      have hl : raw29158step1Labels = raw29158step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4712 node4712Labels := by rfl

theorem canonical29159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29159 raw29159Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw29159 raw29159Labels = mixedMoment B raw29159step0 raw29159step0Labels := by
      have ha : raw29159step0 = (fun i j => raw29159 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29159step0 raw29159; decide +kernel
      have hl : raw29159step0Labels = raw29159Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29159 raw29159Labels permutation646 permutation2
    mixedMoment B raw29159step0 raw29159step0Labels = mixedMoment B raw29159step1 raw29159step1Labels := by
      have ha : raw29159step1 = -raw29159step0 := by apply Matrix.ext; change ∀ i j, raw29159step1 i j = -(raw29159step0 i j); unfold raw29159step1 raw29159step0; decide +kernel
      have hl : raw29159step1Labels = raw29159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4779 node4779Labels := by rfl

theorem canonical29160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29160 raw29160Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw29160 raw29160Labels = mixedMoment B raw29160step0 raw29160step0Labels := by
      have ha : raw29160step0 = (fun i j => raw29160 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29160step0 raw29160; decide +kernel
      have hl : raw29160step0Labels = raw29160Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29160 raw29160Labels permutation158 permutation2
    _ = mixedMoment B node5055 node5055Labels := by rfl

theorem canonical29161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29161 raw29161Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw29161 raw29161Labels = mixedMoment B raw29161step0 raw29161step0Labels := by
      have hz : ∀ j, raw29161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29161step0 = (fun i j => raw29161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29161step0 raw29161; decide +kernel
      have hl : raw29161step0Labels = raw29161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29161 raw29161Labels permutation346 hz
    _ = mixedMoment B node4538 node4538Labels := by rfl

theorem canonical29162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29162 raw29162Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw29162 raw29162Labels = mixedMoment B raw29162step0 raw29162step0Labels := by
      have hz : ∀ j, raw29162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29162step0 = (fun i j => raw29162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29162step0 raw29162; decide +kernel
      have hl : raw29162step0Labels = raw29162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29162 raw29162Labels permutation346 hz
    mixedMoment B raw29162step0 raw29162step0Labels = mixedMoment B raw29162step1 raw29162step1Labels := by
      have ha : raw29162step1 = (fun i j => raw29162step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29162step1 raw29162step0; decide +kernel
      have hl : raw29162step1Labels = raw29162step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29162step0 raw29162step0Labels permutation151 permutation2
    mixedMoment B raw29162step1 raw29162step1Labels = mixedMoment B raw29162step2 raw29162step2Labels := by
      have ha : raw29162step2 = -raw29162step1 := by apply Matrix.ext; change ∀ i j, raw29162step2 i j = -(raw29162step1 i j); unfold raw29162step2 raw29162step1; decide +kernel
      have hl : raw29162step2Labels = raw29162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4726 node4726Labels := by rfl

theorem canonical29163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29163 raw29163Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw29163 raw29163Labels = mixedMoment B raw29163step0 raw29163step0Labels := by
      have ha : raw29163step0 = (fun i j => raw29163 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29163step0 raw29163; decide +kernel
      have hl : raw29163step0Labels = raw29163Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29163 raw29163Labels permutation688 permutation2
    mixedMoment B raw29163step0 raw29163step0Labels = mixedMoment B raw29163step1 raw29163step1Labels := by
      have ha : raw29163step1 = -raw29163step0 := by apply Matrix.ext; change ∀ i j, raw29163step1 i j = -(raw29163step0 i j); unfold raw29163step1 raw29163step0; decide +kernel
      have hl : raw29163step1Labels = raw29163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4721 node4721Labels := by rfl

theorem canonical29164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29164 raw29164Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw29164 raw29164Labels = mixedMoment B raw29164step0 raw29164step0Labels := by
      have hz : ∀ j, raw29164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29164step0 = (fun i j => raw29164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29164step0 raw29164; decide +kernel
      have hl : raw29164step0Labels = raw29164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29164 raw29164Labels permutation346 hz
    mixedMoment B raw29164step0 raw29164step0Labels = mixedMoment B raw29164step1 raw29164step1Labels := by
      have ha : raw29164step1 = (fun i j => raw29164step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29164step1 raw29164step0; decide +kernel
      have hl : raw29164step1Labels = raw29164step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29164step0 raw29164step0Labels permutation151 permutation7
    mixedMoment B raw29164step1 raw29164step1Labels = mixedMoment B raw29164step2 raw29164step2Labels := by
      have ha : raw29164step2 = raw29164step1 := by apply Matrix.ext; unfold raw29164step2 raw29164step1; decide +kernel
      have hl : raw29164step1Labels = labelEmbedding10 ∘ raw29164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29164step1 raw29164step1Labels raw29164step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

theorem canonical29165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29165 raw29165Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw29165 raw29165Labels = mixedMoment B raw29165step0 raw29165step0Labels := by
      have hz : ∀ j, raw29165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29165step0 = (fun i j => raw29165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29165step0 raw29165; decide +kernel
      have hl : raw29165step0Labels = raw29165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29165 raw29165Labels permutation346 hz
    _ = mixedMoment B node5094 node5094Labels := by rfl

theorem canonical29166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29166 raw29166Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw29166 raw29166Labels = mixedMoment B raw29166step0 raw29166step0Labels := by
      have hz : ∀ j, raw29166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29166step0 = (fun i j => raw29166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29166step0 raw29166; decide +kernel
      have hl : raw29166step0Labels = raw29166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29166 raw29166Labels permutation346 hz
    _ = mixedMoment B node4525 node4525Labels := by rfl

theorem canonical29167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29167 raw29167Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw29167 raw29167Labels = mixedMoment B raw29167step0 raw29167step0Labels := by
      have hz : ∀ j, raw29167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29167step0 = (fun i j => raw29167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29167step0 raw29167; decide +kernel
      have hl : raw29167step0Labels = raw29167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29167 raw29167Labels permutation346 hz
    mixedMoment B raw29167step0 raw29167step0Labels = mixedMoment B raw29167step1 raw29167step1Labels := by
      have ha : raw29167step1 = (fun i j => raw29167step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29167step1 raw29167step0; decide +kernel
      have hl : raw29167step1Labels = raw29167step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29167step0 raw29167step0Labels permutation151 permutation2
    mixedMoment B raw29167step1 raw29167step1Labels = mixedMoment B raw29167step2 raw29167step2Labels := by
      have ha : raw29167step2 = -raw29167step1 := by apply Matrix.ext; change ∀ i j, raw29167step2 i j = -(raw29167step1 i j); unfold raw29167step2 raw29167step1; decide +kernel
      have hl : raw29167step2Labels = raw29167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical29168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29168 raw29168Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw29168 raw29168Labels = mixedMoment B raw29168step0 raw29168step0Labels := by
      have ha : raw29168step0 = (fun i j => raw29168 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29168step0 raw29168; decide +kernel
      have hl : raw29168step0Labels = raw29168Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29168 raw29168Labels permutation688 permutation2
    mixedMoment B raw29168step0 raw29168step0Labels = mixedMoment B raw29168step1 raw29168step1Labels := by
      have ha : raw29168step1 = -raw29168step0 := by apply Matrix.ext; change ∀ i j, raw29168step1 i j = -(raw29168step0 i j); unfold raw29168step1 raw29168step0; decide +kernel
      have hl : raw29168step1Labels = raw29168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4631 node4631Labels := by rfl

theorem canonical29169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29169 raw29169Labels = mixedMoment B node4649 node4649Labels := by
  calc
    mixedMoment B raw29169 raw29169Labels = mixedMoment B raw29169step0 raw29169step0Labels := by
      have hz : ∀ j, raw29169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29169step0 = (fun i j => raw29169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29169step0 raw29169; decide +kernel
      have hl : raw29169step0Labels = raw29169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29169 raw29169Labels permutation346 hz
    mixedMoment B raw29169step0 raw29169step0Labels = mixedMoment B raw29169step1 raw29169step1Labels := by
      have ha : raw29169step1 = (fun i j => raw29169step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29169step1 raw29169step0; decide +kernel
      have hl : raw29169step1Labels = raw29169step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29169step0 raw29169step0Labels permutation149 permutation2
    mixedMoment B raw29169step1 raw29169step1Labels = mixedMoment B raw29169step2 raw29169step2Labels := by
      have ha : raw29169step2 = -raw29169step1 := by apply Matrix.ext; change ∀ i j, raw29169step2 i j = -(raw29169step1 i j); unfold raw29169step2 raw29169step1; decide +kernel
      have hl : raw29169step2Labels = raw29169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4649 node4649Labels := by rfl

theorem canonical29170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29170 raw29170Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw29170 raw29170Labels = mixedMoment B raw29170step0 raw29170step0Labels := by
      have hz : ∀ j, raw29170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29170step0 = (fun i j => raw29170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29170step0 raw29170; decide +kernel
      have hl : raw29170step0Labels = raw29170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29170 raw29170Labels permutation346 hz
    mixedMoment B raw29170step0 raw29170step0Labels = mixedMoment B raw29170step1 raw29170step1Labels := by
      have ha : raw29170step1 = (fun i j => raw29170step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29170step1 raw29170step0; decide +kernel
      have hl : raw29170step1Labels = raw29170step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29170step0 raw29170step0Labels permutation151 permutation7
    mixedMoment B raw29170step1 raw29170step1Labels = mixedMoment B raw29170step2 raw29170step2Labels := by
      have ha : raw29170step2 = raw29170step1 := by apply Matrix.ext; unfold raw29170step2 raw29170step1; decide +kernel
      have hl : raw29170step1Labels = labelEmbedding10 ∘ raw29170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29170step1 raw29170step1Labels raw29170step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

theorem canonical29171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29171 raw29171Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw29171 raw29171Labels = mixedMoment B raw29171step0 raw29171step0Labels := by
      have hz : ∀ j, raw29171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29171step0 = (fun i j => raw29171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29171step0 raw29171; decide +kernel
      have hl : raw29171step0Labels = raw29171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29171 raw29171Labels permutation346 hz
    mixedMoment B raw29171step0 raw29171step0Labels = mixedMoment B raw29171step1 raw29171step1Labels := by
      have ha : raw29171step1 = (fun i j => raw29171step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29171step1 raw29171step0; decide +kernel
      have hl : raw29171step1Labels = raw29171step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29171step0 raw29171step0Labels permutation151 permutation2
    mixedMoment B raw29171step1 raw29171step1Labels = mixedMoment B raw29171step2 raw29171step2Labels := by
      have ha : raw29171step2 = -raw29171step1 := by apply Matrix.ext; change ∀ i j, raw29171step2 i j = -(raw29171step1 i j); unfold raw29171step2 raw29171step1; decide +kernel
      have hl : raw29171step2Labels = raw29171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4293 node4293Labels := by rfl

theorem canonical29172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29172 raw29172Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw29172 raw29172Labels = mixedMoment B raw29172step0 raw29172step0Labels := by
      have hz : ∀ j, raw29172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29172step0 = (fun i j => raw29172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29172step0 raw29172; decide +kernel
      have hl : raw29172step0Labels = raw29172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29172 raw29172Labels permutation346 hz
    mixedMoment B raw29172step0 raw29172step0Labels = mixedMoment B raw29172step1 raw29172step1Labels := by
      have ha : raw29172step1 = (fun i j => raw29172step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29172step1 raw29172step0; decide +kernel
      have hl : raw29172step1Labels = raw29172step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29172step0 raw29172step0Labels permutation151 permutation2
    mixedMoment B raw29172step1 raw29172step1Labels = mixedMoment B raw29172step2 raw29172step2Labels := by
      have ha : raw29172step2 = -raw29172step1 := by apply Matrix.ext; change ∀ i j, raw29172step2 i j = -(raw29172step1 i j); unfold raw29172step2 raw29172step1; decide +kernel
      have hl : raw29172step2Labels = raw29172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical29173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29173 raw29173Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw29173 raw29173Labels = mixedMoment B raw29173step0 raw29173step0Labels := by
      have ha : raw29173step0 = (fun i j => raw29173 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29173step0 raw29173; decide +kernel
      have hl : raw29173step0Labels = raw29173Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29173 raw29173Labels permutation688 permutation2
    mixedMoment B raw29173step0 raw29173step0Labels = mixedMoment B raw29173step1 raw29173step1Labels := by
      have ha : raw29173step1 = -raw29173step0 := by apply Matrix.ext; change ∀ i j, raw29173step1 i j = -(raw29173step0 i j); unfold raw29173step1 raw29173step0; decide +kernel
      have hl : raw29173step1Labels = raw29173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4287 node4287Labels := by rfl

theorem canonical29174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29174 raw29174Labels = mixedMoment B node4308 node4308Labels := by
  calc
    mixedMoment B raw29174 raw29174Labels = mixedMoment B raw29174step0 raw29174step0Labels := by
      have hz : ∀ j, raw29174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29174step0 = (fun i j => raw29174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29174step0 raw29174; decide +kernel
      have hl : raw29174step0Labels = raw29174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29174 raw29174Labels permutation346 hz
    mixedMoment B raw29174step0 raw29174step0Labels = mixedMoment B raw29174step1 raw29174step1Labels := by
      have ha : raw29174step1 = (fun i j => raw29174step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29174step1 raw29174step0; decide +kernel
      have hl : raw29174step1Labels = raw29174step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29174step0 raw29174step0Labels permutation149 permutation2
    mixedMoment B raw29174step1 raw29174step1Labels = mixedMoment B raw29174step2 raw29174step2Labels := by
      have ha : raw29174step2 = -raw29174step1 := by apply Matrix.ext; change ∀ i j, raw29174step2 i j = -(raw29174step1 i j); unfold raw29174step2 raw29174step1; decide +kernel
      have hl : raw29174step2Labels = raw29174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4308 node4308Labels := by rfl

theorem canonical29175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29175 raw29175Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw29175 raw29175Labels = mixedMoment B raw29175step0 raw29175step0Labels := by
      have hz : ∀ j, raw29175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29175step0 = (fun i j => raw29175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29175step0 raw29175; decide +kernel
      have hl : raw29175step0Labels = raw29175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29175 raw29175Labels permutation346 hz
    mixedMoment B raw29175step0 raw29175step0Labels = mixedMoment B raw29175step1 raw29175step1Labels := by
      have ha : raw29175step1 = (fun i j => raw29175step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29175step1 raw29175step0; decide +kernel
      have hl : raw29175step1Labels = raw29175step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29175step0 raw29175step0Labels permutation151 permutation2
    mixedMoment B raw29175step1 raw29175step1Labels = mixedMoment B raw29175step2 raw29175step2Labels := by
      have ha : raw29175step2 = -raw29175step1 := by apply Matrix.ext; change ∀ i j, raw29175step2 i j = -(raw29175step1 i j); unfold raw29175step2 raw29175step1; decide +kernel
      have hl : raw29175step2Labels = raw29175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4401 node4401Labels := by rfl

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

theorem canonical1023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1023 raw1023Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw1023 raw1023Labels = mixedMoment B raw1023step0 raw1023step0Labels := by
      have ha : raw1023step0 = (fun i j => raw1023 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1023step0 raw1023; decide +kernel
      have hl : raw1023step0Labels = raw1023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1023 raw1023Labels permutation152 permutation4
    mixedMoment B raw1023step0 raw1023step0Labels = mixedMoment B raw1023step1 raw1023step1Labels := by
      have ha : raw1023step1 = raw1023step0 := by apply Matrix.ext; unfold raw1023step1 raw1023step0; decide +kernel
      have hl : raw1023step0Labels = labelEmbedding7 ∘ raw1023step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1023step0 raw1023step0Labels raw1023step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

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

theorem canonical1024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1024 raw1024Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw1024 raw1024Labels = mixedMoment B raw1024step0 raw1024step0Labels := by
      have ha : raw1024step0 = (fun i j => raw1024 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1024step0 raw1024; decide +kernel
      have hl : raw1024step0Labels = raw1024Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1024 raw1024Labels permutation152 permutation4
    _ = mixedMoment B node865 node865Labels := by rfl

theorem canonical1025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1025 raw1025Labels = mixedMoment B node1553 node1553Labels := by
  calc
    mixedMoment B raw1025 raw1025Labels = mixedMoment B raw1025step0 raw1025step0Labels := by
      have ha : raw1025step0 = (fun i j => raw1025 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1025step0 raw1025; decide +kernel
      have hl : raw1025step0Labels = raw1025Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1025 raw1025Labels permutation158 permutation6
    mixedMoment B raw1025step0 raw1025step0Labels = mixedMoment B raw1025step1 raw1025step1Labels := by
      have ha : raw1025step1 = -raw1025step0 := by apply Matrix.ext; change ∀ i j, raw1025step1 i j = -(raw1025step0 i j); unfold raw1025step1 raw1025step0; decide +kernel
      have hl : raw1025step1Labels = raw1025step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1025step1 raw1025step1Labels = mixedMoment B raw1025step2 raw1025step2Labels := by
      have ha : raw1025step2 = raw1025step1 := by apply Matrix.ext; unfold raw1025step2 raw1025step1; decide +kernel
      have hl : raw1025step1Labels = labelEmbedding1 ∘ raw1025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1025step1 raw1025step1Labels raw1025step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1553 node1553Labels := by rfl

theorem canonical1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1041 raw1041Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw1041 raw1041Labels = mixedMoment B raw1041step0 raw1041step0Labels := by
      have ha : raw1041step0 = (fun i j => raw1041 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1041step0 raw1041; decide +kernel
      have hl : raw1041step0Labels = raw1041Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1041 raw1041Labels permutation32 permutation4
    mixedMoment B raw1041step0 raw1041step0Labels = mixedMoment B raw1041step1 raw1041step1Labels := by
      have ha : raw1041step1 = raw1041step0 := by apply Matrix.ext; unfold raw1041step1 raw1041step0; decide +kernel
      have hl : raw1041step0Labels = labelEmbedding7 ∘ raw1041step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1041step0 raw1041step0Labels raw1041step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

theorem canonical1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1042 raw1042Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw1042 raw1042Labels = mixedMoment B raw1042step0 raw1042step0Labels := by
      have ha : raw1042step0 = (fun i j => raw1042 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1042step0 raw1042; decide +kernel
      have hl : raw1042step0Labels = raw1042Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1042 raw1042Labels permutation32 permutation4
    _ = mixedMoment B node871 node871Labels := by rfl

theorem canonical1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1043 raw1043Labels = mixedMoment B node1568 node1568Labels := by
  calc
    mixedMoment B raw1043 raw1043Labels = mixedMoment B raw1043step0 raw1043step0Labels := by
      have ha : raw1043step0 = (fun i j => raw1043 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1043step0 raw1043; decide +kernel
      have hl : raw1043step0Labels = raw1043Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1043 raw1043Labels permutation32 permutation6
    mixedMoment B raw1043step0 raw1043step0Labels = mixedMoment B raw1043step1 raw1043step1Labels := by
      have ha : raw1043step1 = -raw1043step0 := by apply Matrix.ext; change ∀ i j, raw1043step1 i j = -(raw1043step0 i j); unfold raw1043step1 raw1043step0; decide +kernel
      have hl : raw1043step1Labels = raw1043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1043step1 raw1043step1Labels = mixedMoment B raw1043step2 raw1043step2Labels := by
      have ha : raw1043step2 = raw1043step1 := by apply Matrix.ext; unfold raw1043step2 raw1043step1; decide +kernel
      have hl : raw1043step1Labels = labelEmbedding1 ∘ raw1043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1043step1 raw1043step1Labels raw1043step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1568 node1568Labels := by rfl

theorem canonical1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1047 raw1047Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw1047 raw1047Labels = mixedMoment B raw1047step0 raw1047step0Labels := by
      have ha : raw1047step0 = (fun i j => raw1047 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1047step0 raw1047; decide +kernel
      have hl : raw1047step0Labels = raw1047Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1047 raw1047Labels permutation32 permutation4
    mixedMoment B raw1047step0 raw1047step0Labels = mixedMoment B raw1047step1 raw1047step1Labels := by
      have ha : raw1047step1 = raw1047step0 := by apply Matrix.ext; unfold raw1047step1 raw1047step0; decide +kernel
      have hl : raw1047step0Labels = labelEmbedding7 ∘ raw1047step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1047step0 raw1047step0Labels raw1047step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical1048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1048 raw1048Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw1048 raw1048Labels = mixedMoment B raw1048step0 raw1048step0Labels := by
      have ha : raw1048step0 = (fun i j => raw1048 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1048step0 raw1048; decide +kernel
      have hl : raw1048step0Labels = raw1048Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1048 raw1048Labels permutation32 permutation4
    _ = mixedMoment B node873 node873Labels := by rfl

theorem canonical1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1049 raw1049Labels = mixedMoment B node1569 node1569Labels := by
  calc
    mixedMoment B raw1049 raw1049Labels = mixedMoment B raw1049step0 raw1049step0Labels := by
      have ha : raw1049step0 = (fun i j => raw1049 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1049step0 raw1049; decide +kernel
      have hl : raw1049step0Labels = raw1049Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1049 raw1049Labels permutation32 permutation6
    mixedMoment B raw1049step0 raw1049step0Labels = mixedMoment B raw1049step1 raw1049step1Labels := by
      have ha : raw1049step1 = -raw1049step0 := by apply Matrix.ext; change ∀ i j, raw1049step1 i j = -(raw1049step0 i j); unfold raw1049step1 raw1049step0; decide +kernel
      have hl : raw1049step1Labels = raw1049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1049step1 raw1049step1Labels = mixedMoment B raw1049step2 raw1049step2Labels := by
      have ha : raw1049step2 = raw1049step1 := by apply Matrix.ext; unfold raw1049step2 raw1049step1; decide +kernel
      have hl : raw1049step1Labels = labelEmbedding1 ∘ raw1049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1049step1 raw1049step1Labels raw1049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1569 node1569Labels := by rfl

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

theorem canonical1215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1215 raw1215Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw1215 raw1215Labels = mixedMoment B raw1215step0 raw1215step0Labels := by
      have ha : raw1215step0 = (fun i j => raw1215 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1215step0 raw1215; decide +kernel
      have hl : raw1215step0Labels = raw1215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1215 raw1215Labels permutation32 permutation4
    mixedMoment B raw1215step0 raw1215step0Labels = mixedMoment B raw1215step1 raw1215step1Labels := by
      have ha : raw1215step1 = raw1215step0 := by apply Matrix.ext; unfold raw1215step1 raw1215step0; decide +kernel
      have hl : raw1215step0Labels = labelEmbedding7 ∘ raw1215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1215step0 raw1215step0Labels raw1215step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

theorem canonical1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1216 raw1216Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw1216 raw1216Labels = mixedMoment B raw1216step0 raw1216step0Labels := by
      have ha : raw1216step0 = (fun i j => raw1216 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1216step0 raw1216; decide +kernel
      have hl : raw1216step0Labels = raw1216Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1216 raw1216Labels permutation32 permutation4
    _ = mixedMoment B node982 node982Labels := by rfl

theorem canonical1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1217 raw1217Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw1217 raw1217Labels = mixedMoment B raw1217step0 raw1217step0Labels := by
      have ha : raw1217step0 = (fun i j => raw1217 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1217step0 raw1217; decide +kernel
      have hl : raw1217step0Labels = raw1217Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1217 raw1217Labels permutation32 permutation6
    mixedMoment B raw1217step0 raw1217step0Labels = mixedMoment B raw1217step1 raw1217step1Labels := by
      have ha : raw1217step1 = -raw1217step0 := by apply Matrix.ext; change ∀ i j, raw1217step1 i j = -(raw1217step0 i j); unfold raw1217step1 raw1217step0; decide +kernel
      have hl : raw1217step1Labels = raw1217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1217step1 raw1217step1Labels = mixedMoment B raw1217step2 raw1217step2Labels := by
      have ha : raw1217step2 = raw1217step1 := by apply Matrix.ext; unfold raw1217step2 raw1217step1; decide +kernel
      have hl : raw1217step1Labels = labelEmbedding1 ∘ raw1217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1217step1 raw1217step1Labels raw1217step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1617 node1617Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4287 node4287Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node865 node865Labels + mixedMoment B node1553 node1553Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1023 singletonSmall4287
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4287) = raw1023Labels := by decide +kernel
  rw [hl, canonical1023 B hB] at h
  have hc0 : mixedMoment B raw1023 (Fin.cases (0 : Fin 2) singletonSmall4287) =
      mixedMoment B node865 node865Labels := by
    have ha : raw1023 = raw1024 := by apply Matrix.ext; unfold raw1023 raw1024; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4287 = raw1024Labels := by decide +kernel
    rw [ha, hj, canonical1024 B hB]
  have hc1 : mixedMoment B raw1023 (Fin.cases (1 : Fin 2) singletonSmall4287) =
      mixedMoment B node1553 node1553Labels := by
    have ha : raw1023 = raw1025 := by apply Matrix.ext; unfold raw1023 raw1025; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4287 = raw1025Labels := by decide +kernel
    rw [ha, hj, canonical1025 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4293 node4293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node871 node871Labels + mixedMoment B node1568 node1568Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1041 singletonSmall4293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4293) = raw1041Labels := by decide +kernel
  rw [hl, canonical1041 B hB] at h
  have hc0 : mixedMoment B raw1041 (Fin.cases (0 : Fin 2) singletonSmall4293) =
      mixedMoment B node871 node871Labels := by
    have ha : raw1041 = raw1042 := by apply Matrix.ext; unfold raw1041 raw1042; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4293 = raw1042Labels := by decide +kernel
    rw [ha, hj, canonical1042 B hB]
  have hc1 : mixedMoment B raw1041 (Fin.cases (1 : Fin 2) singletonSmall4293) =
      mixedMoment B node1568 node1568Labels := by
    have ha : raw1041 = raw1043 := by apply Matrix.ext; unfold raw1041 raw1043; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4293 = raw1043Labels := by decide +kernel
    rw [ha, hj, canonical1043 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4295 node4295Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node873 node873Labels + mixedMoment B node1569 node1569Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1047 singletonSmall4295
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4295) = raw1047Labels := by decide +kernel
  rw [hl, canonical1047 B hB] at h
  have hc0 : mixedMoment B raw1047 (Fin.cases (0 : Fin 2) singletonSmall4295) =
      mixedMoment B node873 node873Labels := by
    have ha : raw1047 = raw1048 := by apply Matrix.ext; unfold raw1047 raw1048; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4295 = raw1048Labels := by decide +kernel
    rw [ha, hj, canonical1048 B hB]
  have hc1 : mixedMoment B raw1047 (Fin.cases (1 : Fin 2) singletonSmall4295) =
      mixedMoment B node1569 node1569Labels := by
    have ha : raw1047 = raw1049 := by apply Matrix.ext; unfold raw1047 raw1049; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4295 = raw1049Labels := by decide +kernel
    rw [ha, hj, canonical1049 B hB]
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

theorem singleton4401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4401 node4401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node982 node982Labels + mixedMoment B node1617 node1617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1215 singletonSmall4401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4401) = raw1215Labels := by decide +kernel
  rw [hl, canonical1215 B hB] at h
  have hc0 : mixedMoment B raw1215 (Fin.cases (0 : Fin 2) singletonSmall4401) =
      mixedMoment B node982 node982Labels := by
    have ha : raw1215 = raw1216 := by apply Matrix.ext; unfold raw1215 raw1216; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4401 = raw1216Labels := by decide +kernel
    rw [ha, hj, canonical1216 B hB]
  have hc1 : mixedMoment B raw1215 (Fin.cases (1 : Fin 2) singletonSmall4401) =
      mixedMoment B node1617 node1617Labels := by
    have ha : raw1215 = raw1217 := by apply Matrix.ext; unfold raw1215 raw1217; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4401 = raw1217Labels := by decide +kernel
    rw [ha, hj, canonical1217 B hB]
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

theorem singleton4538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4538 node4538Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1123 node1123Labels + mixedMoment B node1937 node1937Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1356 singletonSmall4538
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4538) = raw1356Labels := by decide +kernel
  rw [hl, canonical1356 B hB] at h
  have hc0 : mixedMoment B raw1356 (Fin.cases (0 : Fin 2) singletonSmall4538) =
      mixedMoment B node1123 node1123Labels := by
    have ha : raw1356 = raw1357 := by apply Matrix.ext; unfold raw1356 raw1357; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4538 = raw1357Labels := by decide +kernel
    rw [ha, hj, canonical1357 B hB]
  have hc1 : mixedMoment B raw1356 (Fin.cases (1 : Fin 2) singletonSmall4538) =
      mixedMoment B node1937 node1937Labels := by
    have ha : raw1356 = raw1358 := by apply Matrix.ext; unfold raw1356 raw1358; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4538 = raw1358Labels := by decide +kernel
    rw [ha, hj, canonical1358 B hB]
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

theorem singleton4637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4637 node4637Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1766 node1766Labels + mixedMoment B node1850 node1850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1491 singletonSmall4637
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4637) = raw1491Labels := by decide +kernel
  rw [hl, canonical1491 B hB] at h
  have hc0 : mixedMoment B raw1491 (Fin.cases (0 : Fin 2) singletonSmall4637) =
      mixedMoment B node1766 node1766Labels := by
    have ha : raw1491 = raw1492 := by apply Matrix.ext; unfold raw1491 raw1492; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4637 = raw1492Labels := by decide +kernel
    rw [ha, hj, canonical1492 B hB]
  have hc1 : mixedMoment B raw1491 (Fin.cases (1 : Fin 2) singletonSmall4637) =
      mixedMoment B node1850 node1850Labels := by
    have ha : raw1491 = raw1493 := by apply Matrix.ext; unfold raw1491 raw1493; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4637 = raw1493Labels := by decide +kernel
    rw [ha, hj, canonical1493 B hB]
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

theorem singleton4706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4706 node4706Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1860 node1860Labels + mixedMoment B node1888 node1888Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1590 singletonSmall4706
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4706) = raw1590Labels := by decide +kernel
  rw [hl, canonical1590 B hB] at h
  have hc0 : mixedMoment B raw1590 (Fin.cases (0 : Fin 2) singletonSmall4706) =
      mixedMoment B node1860 node1860Labels := by
    have ha : raw1590 = raw1591 := by apply Matrix.ext; unfold raw1590 raw1591; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4706 = raw1591Labels := by decide +kernel
    rw [ha, hj, canonical1591 B hB]
  have hc1 : mixedMoment B raw1590 (Fin.cases (1 : Fin 2) singletonSmall4706) =
      mixedMoment B node1888 node1888Labels := by
    have ha : raw1590 = raw1592 := by apply Matrix.ext; unfold raw1590 raw1592; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4706 = raw1592Labels := by decide +kernel
    rw [ha, hj, canonical1592 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4721 node4721Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1875 node1875Labels + mixedMoment B node1905 node1905Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1620 singletonSmall4721
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4721) = raw1620Labels := by decide +kernel
  rw [hl, canonical1620 B hB] at h
  have hc0 : mixedMoment B raw1620 (Fin.cases (0 : Fin 2) singletonSmall4721) =
      mixedMoment B node1875 node1875Labels := by
    have ha : raw1620 = raw1621 := by apply Matrix.ext; unfold raw1620 raw1621; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4721 = raw1621Labels := by decide +kernel
    rw [ha, hj, canonical1621 B hB]
  have hc1 : mixedMoment B raw1620 (Fin.cases (1 : Fin 2) singletonSmall4721) =
      mixedMoment B node1905 node1905Labels := by
    have ha : raw1620 = raw1622 := by apply Matrix.ext; unfold raw1620 raw1622; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4721 = raw1622Labels := by decide +kernel
    rw [ha, hj, canonical1622 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4726 node4726Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1880 node1880Labels + mixedMoment B node1938 node1938Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1635 singletonSmall4726
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4726) = raw1635Labels := by decide +kernel
  rw [hl, canonical1635 B hB] at h
  have hc0 : mixedMoment B raw1635 (Fin.cases (0 : Fin 2) singletonSmall4726) =
      mixedMoment B node1880 node1880Labels := by
    have ha : raw1635 = raw1636 := by apply Matrix.ext; unfold raw1635 raw1636; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4726 = raw1636Labels := by decide +kernel
    rw [ha, hj, canonical1636 B hB]
  have hc1 : mixedMoment B raw1635 (Fin.cases (1 : Fin 2) singletonSmall4726) =
      mixedMoment B node1938 node1938Labels := by
    have ha : raw1635 = raw1637 := by apply Matrix.ext; unfold raw1635 raw1637; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4726 = raw1637Labels := by decide +kernel
    rw [ha, hj, canonical1637 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4728 node4728Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1897 node1897Labels + mixedMoment B node1907 node1907Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1641 singletonSmall4728
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4728) = raw1641Labels := by decide +kernel
  rw [hl, canonical1641 B hB] at h
  have hc0 : mixedMoment B raw1641 (Fin.cases (0 : Fin 2) singletonSmall4728) =
      mixedMoment B node1897 node1897Labels := by
    have ha : raw1641 = raw1642 := by apply Matrix.ext; unfold raw1641 raw1642; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4728 = raw1642Labels := by decide +kernel
    rw [ha, hj, canonical1642 B hB]
  have hc1 : mixedMoment B raw1641 (Fin.cases (1 : Fin 2) singletonSmall4728) =
      mixedMoment B node1907 node1907Labels := by
    have ha : raw1641 = raw1643 := by apply Matrix.ext; unfold raw1641 raw1643; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4728 = raw1643Labels := by decide +kernel
    rw [ha, hj, canonical1643 B hB]
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

theorem singleton4827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4827 node4827Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2047 node2047Labels + mixedMoment B node2079 node2079Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1755 singletonSmall4827
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4827) = raw1755Labels := by decide +kernel
  rw [hl, canonical1755 B hB] at h
  have hc0 : mixedMoment B raw1755 (Fin.cases (0 : Fin 2) singletonSmall4827) =
      mixedMoment B node2047 node2047Labels := by
    have ha : raw1755 = raw1756 := by apply Matrix.ext; unfold raw1755 raw1756; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4827 = raw1756Labels := by decide +kernel
    rw [ha, hj, canonical1756 B hB]
  have hc1 : mixedMoment B raw1755 (Fin.cases (1 : Fin 2) singletonSmall4827) =
      mixedMoment B node2079 node2079Labels := by
    have ha : raw1755 = raw1757 := by apply Matrix.ext; unfold raw1755 raw1757; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4827 = raw1757Labels := by decide +kernel
    rw [ha, hj, canonical1757 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4832 node4832Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2052 node2052Labels + mixedMoment B node2193 node2193Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1764 singletonSmall4832
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4832) = raw1764Labels := by decide +kernel
  rw [hl, canonical1764 B hB] at h
  have hc0 : mixedMoment B raw1764 (Fin.cases (0 : Fin 2) singletonSmall4832) =
      mixedMoment B node2052 node2052Labels := by
    have ha : raw1764 = raw1765 := by apply Matrix.ext; unfold raw1764 raw1765; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4832 = raw1765Labels := by decide +kernel
    rw [ha, hj, canonical1765 B hB]
  have hc1 : mixedMoment B raw1764 (Fin.cases (1 : Fin 2) singletonSmall4832) =
      mixedMoment B node2193 node2193Labels := by
    have ha : raw1764 = raw1766 := by apply Matrix.ext; unfold raw1764 raw1766; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4832 = raw1766Labels := by decide +kernel
    rw [ha, hj, canonical1766 B hB]
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

theorem singleton5014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5014 node5014Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2399 node2399Labels + mixedMoment B node2467 node2467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2022 singletonSmall5014
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5014) = raw2022Labels := by decide +kernel
  rw [hl, canonical2022 B hB] at h
  have hc0 : mixedMoment B raw2022 (Fin.cases (0 : Fin 2) singletonSmall5014) =
      mixedMoment B node2399 node2399Labels := by
    have ha : raw2022 = raw2023 := by apply Matrix.ext; unfold raw2022 raw2023; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5014 = raw2023Labels := by decide +kernel
    rw [ha, hj, canonical2023 B hB]
  have hc1 : mixedMoment B raw2022 (Fin.cases (1 : Fin 2) singletonSmall5014) =
      mixedMoment B node2467 node2467Labels := by
    have ha : raw2022 = raw2024 := by apply Matrix.ext; unfold raw2022 raw2024; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5014 = raw2024Labels := by decide +kernel
    rw [ha, hj, canonical2024 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5055 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5055 node5055Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2458 node2458Labels + mixedMoment B node2458 node2458Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2079 singletonSmall5055
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5055) = raw2079Labels := by decide +kernel
  rw [hl, canonical2079 B hB] at h
  have hc0 : mixedMoment B raw2079 (Fin.cases (0 : Fin 2) singletonSmall5055) =
      mixedMoment B node2458 node2458Labels := by
    have ha : raw2079 = raw2080 := by apply Matrix.ext; unfold raw2079 raw2080; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5055 = raw2080Labels := by decide +kernel
    rw [ha, hj, canonical2080 B hB]
  have hc1 : mixedMoment B raw2079 (Fin.cases (1 : Fin 2) singletonSmall5055) =
      mixedMoment B node2458 node2458Labels := by
    have ha : raw2079 = raw2081 := by apply Matrix.ext; unfold raw2079 raw2081; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5055 = raw2081Labels := by decide +kernel
    rw [ha, hj, canonical2081 B hB]
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

theorem singleton5094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5094 node5094Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2504 node2504Labels + mixedMoment B node2504 node2504Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2115 singletonSmall5094
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5094) = raw2115Labels := by decide +kernel
  rw [hl, canonical2115 B hB] at h
  have hc0 : mixedMoment B raw2115 (Fin.cases (0 : Fin 2) singletonSmall5094) =
      mixedMoment B node2504 node2504Labels := by
    have ha : raw2115 = raw2116 := by apply Matrix.ext; unfold raw2115 raw2116; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5094 = raw2116Labels := by decide +kernel
    rw [ha, hj, canonical2116 B hB]
  have hc1 : mixedMoment B raw2115 (Fin.cases (1 : Fin 2) singletonSmall5094) =
      mixedMoment B node2504 node2504Labels := by
    have ha : raw2115 = raw2117 := by apply Matrix.ext; unfold raw2115 raw2117; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5094 = raw2117Labels := by decide +kernel
    rw [ha, hj, canonical2117 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5099 node5099Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2509 node2509Labels + mixedMoment B node2704 node2704Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2124 singletonSmall5099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5099) = raw2124Labels := by decide +kernel
  rw [hl, canonical2124 B hB] at h
  have hc0 : mixedMoment B raw2124 (Fin.cases (0 : Fin 2) singletonSmall5099) =
      mixedMoment B node2509 node2509Labels := by
    have ha : raw2124 = raw2125 := by apply Matrix.ext; unfold raw2124 raw2125; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5099 = raw2125Labels := by decide +kernel
    rw [ha, hj, canonical2125 B hB]
  have hc1 : mixedMoment B raw2124 (Fin.cases (1 : Fin 2) singletonSmall5099) =
      mixedMoment B node2704 node2704Labels := by
    have ha : raw2124 = raw2126 := by apply Matrix.ext; unfold raw2124 raw2126; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5099 = raw2126Labels := by decide +kernel
    rw [ha, hj, canonical2126 B hB]
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

theorem sound865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node865 node865Labels = Sparse.eval nodeValue865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 865) = mixedMoment B node865 node865Labels := rfl
  simpa [nodeValue865, Sparse.eval] using hc.symm

theorem sound871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node871 node871Labels = Sparse.eval nodeValue871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 871) = mixedMoment B node871 node871Labels := rfl
  simpa [nodeValue871, Sparse.eval] using hc.symm

theorem sound873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node873 node873Labels = Sparse.eval nodeValue873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 873) = mixedMoment B node873 node873Labels := rfl
  simpa [nodeValue873, Sparse.eval] using hc.symm

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

theorem sound982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node982 node982Labels = Sparse.eval nodeValue982 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 982) = mixedMoment B node982 node982Labels := rfl
  simpa [nodeValue982, Sparse.eval] using hc.symm

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

theorem sound1123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1123 node1123Labels = Sparse.eval nodeValue1123 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1123) = mixedMoment B node1123 node1123Labels := rfl
  simpa [nodeValue1123, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1553 node1553Labels = Sparse.eval nodeValue1553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1553) = mixedMoment B node1553 node1553Labels := rfl
  simpa [nodeValue1553, Sparse.eval] using hc.symm

theorem sound1568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1568 node1568Labels = Sparse.eval nodeValue1568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1568) = mixedMoment B node1568 node1568Labels := rfl
  simpa [nodeValue1568, Sparse.eval] using hc.symm

theorem sound1569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1569 node1569Labels = Sparse.eval nodeValue1569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1569) = mixedMoment B node1569 node1569Labels := rfl
  simpa [nodeValue1569, Sparse.eval] using hc.symm

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

theorem sound1617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1617 node1617Labels = Sparse.eval nodeValue1617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1617) = mixedMoment B node1617 node1617Labels := rfl
  simpa [nodeValue1617, Sparse.eval] using hc.symm

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

theorem sound1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1766 node1766Labels = Sparse.eval nodeValue1766 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1766) = mixedMoment B node1766 node1766Labels := rfl
  simpa [nodeValue1766, Sparse.eval] using hc.symm

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

theorem sound1849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1849 node1849Labels = Sparse.eval nodeValue1849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1849) = mixedMoment B node1849 node1849Labels := rfl
  simpa [nodeValue1849, Sparse.eval] using hc.symm

theorem sound1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1850 node1850Labels = Sparse.eval nodeValue1850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1850) = mixedMoment B node1850 node1850Labels := rfl
  simpa [nodeValue1850, Sparse.eval] using hc.symm

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

theorem sound1860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1860 node1860Labels = Sparse.eval nodeValue1860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1860) = mixedMoment B node1860 node1860Labels := rfl
  simpa [nodeValue1860, Sparse.eval] using hc.symm

theorem sound1875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1875 node1875Labels = Sparse.eval nodeValue1875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1875) = mixedMoment B node1875 node1875Labels := rfl
  simpa [nodeValue1875, Sparse.eval] using hc.symm

theorem sound1880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1880 node1880Labels = Sparse.eval nodeValue1880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1880) = mixedMoment B node1880 node1880Labels := rfl
  simpa [nodeValue1880, Sparse.eval] using hc.symm

theorem sound1887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1887 node1887Labels = Sparse.eval nodeValue1887 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1887) = mixedMoment B node1887 node1887Labels := rfl
  simpa [nodeValue1887, Sparse.eval] using hc.symm

theorem sound1888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1888 node1888Labels = Sparse.eval nodeValue1888 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1888) = mixedMoment B node1888 node1888Labels := rfl
  simpa [nodeValue1888, Sparse.eval] using hc.symm

theorem sound1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1897 node1897Labels = Sparse.eval nodeValue1897 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1897) = mixedMoment B node1897 node1897Labels := rfl
  simpa [nodeValue1897, Sparse.eval] using hc.symm

theorem sound1905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1905 node1905Labels = Sparse.eval nodeValue1905 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1905) = mixedMoment B node1905 node1905Labels := rfl
  simpa [nodeValue1905, Sparse.eval] using hc.symm

theorem sound1907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1907 node1907Labels = Sparse.eval nodeValue1907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1907) = mixedMoment B node1907 node1907Labels := rfl
  simpa [nodeValue1907, Sparse.eval] using hc.symm

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

theorem sound1937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1937 node1937Labels = Sparse.eval nodeValue1937 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1937) = mixedMoment B node1937 node1937Labels := rfl
  simpa [nodeValue1937, Sparse.eval] using hc.symm

theorem sound1938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1938 node1938Labels = Sparse.eval nodeValue1938 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1938) = mixedMoment B node1938 node1938Labels := rfl
  simpa [nodeValue1938, Sparse.eval] using hc.symm

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

theorem sound1987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1987 node1987Labels = Sparse.eval nodeValue1987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1987) = mixedMoment B node1987 node1987Labels := rfl
  simpa [nodeValue1987, Sparse.eval] using hc.symm

theorem sound1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1996 node1996Labels = Sparse.eval nodeValue1996 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1996) = mixedMoment B node1996 node1996Labels := rfl
  simpa [nodeValue1996, Sparse.eval] using hc.symm

theorem sound2047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2047 node2047Labels = Sparse.eval nodeValue2047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2047) = mixedMoment B node2047 node2047Labels := rfl
  simpa [nodeValue2047, Sparse.eval] using hc.symm

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

theorem sound2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2052 node2052Labels = Sparse.eval nodeValue2052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2052) = mixedMoment B node2052 node2052Labels := rfl
  simpa [nodeValue2052, Sparse.eval] using hc.symm

theorem sound2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2079 node2079Labels = Sparse.eval nodeValue2079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2079) = mixedMoment B node2079 node2079Labels := rfl
  simpa [nodeValue2079, Sparse.eval] using hc.symm

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

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

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

theorem sound2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2399 node2399Labels = Sparse.eval nodeValue2399 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2399) = mixedMoment B node2399 node2399Labels := rfl
  simpa [nodeValue2399, Sparse.eval] using hc.symm

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

theorem sound2458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2458 node2458Labels = Sparse.eval nodeValue2458 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2458) = mixedMoment B node2458 node2458Labels := rfl
  simpa [nodeValue2458, Sparse.eval] using hc.symm

theorem sound2467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2467 node2467Labels = Sparse.eval nodeValue2467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2467) = mixedMoment B node2467 node2467Labels := rfl
  simpa [nodeValue2467, Sparse.eval] using hc.symm

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

theorem sound2504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2504 node2504Labels = Sparse.eval nodeValue2504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2504) = mixedMoment B node2504 node2504Labels := rfl
  simpa [nodeValue2504, Sparse.eval] using hc.symm

theorem sound2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2509 node2509Labels = Sparse.eval nodeValue2509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2509) = mixedMoment B node2509 node2509Labels := rfl
  simpa [nodeValue2509, Sparse.eval] using hc.symm

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

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

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

theorem sound4287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4287 node4287Labels = Sparse.eval nodeValue4287 (mixedVector B) := by
  have h := singleton4287 B _hB
  rw [sound865 B _hB _hF, sound1553 B _hB _hF] at h
  norm_num [nodeValue4287, nodeValue865, nodeValue1553, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero4308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4308 node4308Labels = 0 := by
  exact mixedMoment_order_one B hB node4308 node4308Labels 1
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

theorem sound4293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4293 node4293Labels = Sparse.eval nodeValue4293 (mixedVector B) := by
  have h := singleton4293 B _hB
  rw [sound871 B _hB _hF, sound1568 B _hB _hF] at h
  norm_num [nodeValue4293, nodeValue871, nodeValue1568, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4295 node4295Labels = Sparse.eval nodeValue4295 (mixedVector B) := by
  have h := singleton4295 B _hB
  rw [sound873 B _hB _hF, sound1569 B _hB _hF] at h
  norm_num [nodeValue4295, nodeValue873, nodeValue1569, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4308 node4308Labels = Sparse.eval nodeValue4308 (mixedVector B) := by
  simpa only [nodeValue4308, Sparse.eval_nil] using zero4308 B _hB _hF

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

theorem sound4401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4401 node4401Labels = Sparse.eval nodeValue4401 (mixedVector B) := by
  have h := singleton4401 B _hB
  rw [sound982 B _hB _hF, sound1617 B _hB _hF] at h
  norm_num [nodeValue4401, nodeValue982, nodeValue1617, Sparse.eval] at h ⊢
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

theorem sound4538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4538 node4538Labels = Sparse.eval nodeValue4538 (mixedVector B) := by
  have h := singleton4538 B _hB
  rw [sound1123 B _hB _hF, sound1937 B _hB _hF] at h
  norm_num [nodeValue4538, nodeValue1123, nodeValue1937, Sparse.eval] at h ⊢
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

theorem zero4649 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4649 node4649Labels = 0 := by
  exact mixedMoment_order_one B hB node4649 node4649Labels 1
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

theorem sound4631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4631 node4631Labels = Sparse.eval nodeValue4631 (mixedVector B) := by
  have h := singleton4631 B _hB
  rw [sound1760 B _hB _hF, sound1836 B _hB _hF] at h
  norm_num [nodeValue4631, nodeValue1760, nodeValue1836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4637 node4637Labels = Sparse.eval nodeValue4637 (mixedVector B) := by
  have h := singleton4637 B _hB
  rw [sound1766 B _hB _hF, sound1850 B _hB _hF] at h
  norm_num [nodeValue4637, nodeValue1766, nodeValue1850, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4649 node4649Labels = Sparse.eval nodeValue4649 (mixedVector B) := by
  simpa only [nodeValue4649, Sparse.eval_nil] using zero4649 B _hB _hF

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

theorem zero4712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4712 node4712Labels = 0 := by
  exact mixedMoment_order_one B hB node4712 node4712Labels 1
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

theorem sound4706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4706 node4706Labels = Sparse.eval nodeValue4706 (mixedVector B) := by
  have h := singleton4706 B _hB
  rw [sound1860 B _hB _hF, sound1888 B _hB _hF] at h
  norm_num [nodeValue4706, nodeValue1860, nodeValue1888, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4712 node4712Labels = Sparse.eval nodeValue4712 (mixedVector B) := by
  simpa only [nodeValue4712, Sparse.eval_nil] using zero4712 B _hB _hF

theorem sound4721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4721 node4721Labels = Sparse.eval nodeValue4721 (mixedVector B) := by
  have h := singleton4721 B _hB
  rw [sound1875 B _hB _hF, sound1905 B _hB _hF] at h
  norm_num [nodeValue4721, nodeValue1875, nodeValue1905, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4726 node4726Labels = Sparse.eval nodeValue4726 (mixedVector B) := by
  have h := singleton4726 B _hB
  rw [sound1880 B _hB _hF, sound1938 B _hB _hF] at h
  norm_num [nodeValue4726, nodeValue1880, nodeValue1938, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4728 node4728Labels = Sparse.eval nodeValue4728 (mixedVector B) := by
  have h := singleton4728 B _hB
  rw [sound1897 B _hB _hF, sound1907 B _hB _hF] at h
  norm_num [nodeValue4728, nodeValue1897, nodeValue1907, Sparse.eval] at h ⊢
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

theorem zero4736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4736 node4736Labels = 0 := by
  exact mixedMoment_order_one B hB node4736 node4736Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4741 node4741Labels = 0 := by
  exact mixedMoment_order_one B hB node4741 node4741Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4745 node4745Labels = 0 := by
  exact mixedMoment_order_one B hB node4745 node4745Labels 1
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

theorem sound4736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4736 node4736Labels = Sparse.eval nodeValue4736 (mixedVector B) := by
  simpa only [nodeValue4736, Sparse.eval_nil] using zero4736 B _hB _hF

theorem sound4741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4741 node4741Labels = Sparse.eval nodeValue4741 (mixedVector B) := by
  simpa only [nodeValue4741, Sparse.eval_nil] using zero4741 B _hB _hF

theorem sound4745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4745 node4745Labels = Sparse.eval nodeValue4745 (mixedVector B) := by
  simpa only [nodeValue4745, Sparse.eval_nil] using zero4745 B _hB _hF

theorem sound4779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4779 node4779Labels = Sparse.eval nodeValue4779 (mixedVector B) := by
  have h := singleton4779 B _hB
  rw [sound1987 B _hB _hF, sound1996 B _hB _hF] at h
  norm_num [nodeValue4779, nodeValue1987, nodeValue1996, Sparse.eval] at h ⊢
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

theorem zero4834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = 0 := by
  exact mixedMoment_order_one B hB node4834 node4834Labels 1
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

theorem sound4827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4827 node4827Labels = Sparse.eval nodeValue4827 (mixedVector B) := by
  have h := singleton4827 B _hB
  rw [sound2047 B _hB _hF, sound2079 B _hB _hF] at h
  norm_num [nodeValue4827, nodeValue2047, nodeValue2079, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4832 node4832Labels = Sparse.eval nodeValue4832 (mixedVector B) := by
  have h := singleton4832 B _hB
  rw [sound2052 B _hB _hF, sound2193 B _hB _hF] at h
  norm_num [nodeValue4832, nodeValue2052, nodeValue2193, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

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

theorem sound5014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5014 node5014Labels = Sparse.eval nodeValue5014 (mixedVector B) := by
  have h := singleton5014 B _hB
  rw [sound2399 B _hB _hF, sound2467 B _hB _hF] at h
  norm_num [nodeValue5014, nodeValue2399, nodeValue2467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5055 node5055Labels = Sparse.eval nodeValue5055 (mixedVector B) := by
  have h := singleton5055 B _hB
  rw [sound2458 B _hB _hF] at h
  norm_num [nodeValue5055, nodeValue2458, Sparse.eval] at h ⊢
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

theorem zero5101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = 0 := by
  exact mixedMoment_order_one B hB node5101 node5101Labels 1
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

theorem sound5094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5094 node5094Labels = Sparse.eval nodeValue5094 (mixedVector B) := by
  have h := singleton5094 B _hB
  rw [sound2504 B _hB _hF] at h
  norm_num [nodeValue5094, nodeValue2504, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5099 node5099Labels = Sparse.eval nodeValue5099 (mixedVector B) := by
  have h := singleton5099 B _hB
  rw [sound2509 B _hB _hF, sound2704 B _hB _hF] at h
  norm_num [nodeValue5099, nodeValue2509, nodeValue2704, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = Sparse.eval nodeValue5101 (mixedVector B) := by
  simpa only [nodeValue5101, Sparse.eval_nil] using zero5101 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources64
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2079 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2079 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 1) (sourceB2079 + difference 1 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 1) (sourceB2079 + difference 1 0) sourceC2079) = raw29146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29146; decide +kernel
    rw [ha]
    exact (canonical29146 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 2) (sourceB2079 + difference 2 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 2) (sourceB2079 + difference 2 0) sourceC2079) = raw29147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29147; decide +kernel
    rw [ha]
    exact (canonical29147 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 3) (sourceB2079 + difference 3 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 3) (sourceB2079 + difference 3 0) sourceC2079) = raw29148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29148; decide +kernel
    rw [ha]
    exact (canonical29148 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 4) (sourceB2079 + difference 4 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 4) (sourceB2079 + difference 4 0) sourceC2079) = raw29149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29149; decide +kernel
    rw [ha]
    exact (canonical29149 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2079 + difference 0 5) (sourceB2079 + difference 5 0) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2079 + difference 0 5) (sourceB2079 + difference 5 0) sourceC2079) = raw29150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29150; decide +kernel
    rw [ha]
    exact (canonical29150 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 0) (sourceB2079 + difference 0 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 0) (sourceB2079 + difference 0 1) sourceC2079) = raw29151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29151; decide +kernel
    rw [ha]
    exact (canonical29151 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 2) (sourceB2079 + difference 2 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 2) (sourceB2079 + difference 2 1) sourceC2079) = raw29152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29152; decide +kernel
    rw [ha]
    exact (canonical29152 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 3) (sourceB2079 + difference 3 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 3) (sourceB2079 + difference 3 1) sourceC2079) = raw29153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29153; decide +kernel
    rw [ha]
    exact (canonical29153 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 4) (sourceB2079 + difference 4 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 4) (sourceB2079 + difference 4 1) sourceC2079) = raw29154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29154; decide +kernel
    rw [ha]
    exact (canonical29154 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2079 + difference 1 5) (sourceB2079 + difference 5 1) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2079 + difference 1 5) (sourceB2079 + difference 5 1) sourceC2079) = raw29155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29155; decide +kernel
    rw [ha]
    exact (canonical29155 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 0) (sourceB2079 + difference 0 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 0) (sourceB2079 + difference 0 2) sourceC2079) = raw29156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29156; decide +kernel
    rw [ha]
    exact (canonical29156 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 1) (sourceB2079 + difference 1 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 1) (sourceB2079 + difference 1 2) sourceC2079) = raw29157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29157; decide +kernel
    rw [ha]
    exact (canonical29157 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 3) (sourceB2079 + difference 3 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4712) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 3) (sourceB2079 + difference 3 2) sourceC2079) = raw29158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29158; decide +kernel
    rw [ha]
    exact (canonical29158 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 4) (sourceB2079 + difference 4 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 4) (sourceB2079 + difference 4 2) sourceC2079) = raw29159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29159; decide +kernel
    rw [ha]
    exact (canonical29159 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2079 + difference 2 5) (sourceB2079 + difference 5 2) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA2079 + difference 2 5) (sourceB2079 + difference 5 2) sourceC2079) = raw29160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29160; decide +kernel
    rw [ha]
    exact (canonical29160 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 0) (sourceB2079 + difference 0 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 0) (sourceB2079 + difference 0 3) sourceC2079) = raw29161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29161; decide +kernel
    rw [ha]
    exact (canonical29161 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 1) (sourceB2079 + difference 1 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 1) (sourceB2079 + difference 1 3) sourceC2079) = raw29162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29162; decide +kernel
    rw [ha]
    exact (canonical29162 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 2) (sourceB2079 + difference 2 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4721) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 2) (sourceB2079 + difference 2 3) sourceC2079) = raw29163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29163; decide +kernel
    rw [ha]
    exact (canonical29163 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 4) (sourceB2079 + difference 4 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 4) (sourceB2079 + difference 4 3) sourceC2079) = raw29164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29164; decide +kernel
    rw [ha]
    exact (canonical29164 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2079 + difference 3 5) (sourceB2079 + difference 5 3) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA2079 + difference 3 5) (sourceB2079 + difference 5 3) sourceC2079) = raw29165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29165; decide +kernel
    rw [ha]
    exact (canonical29165 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 0) (sourceB2079 + difference 0 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 0) (sourceB2079 + difference 0 4) sourceC2079) = raw29166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29166; decide +kernel
    rw [ha]
    exact (canonical29166 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 1) (sourceB2079 + difference 1 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 1) (sourceB2079 + difference 1 4) sourceC2079) = raw29167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29167; decide +kernel
    rw [ha]
    exact (canonical29167 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 2) (sourceB2079 + difference 2 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 2) (sourceB2079 + difference 2 4) sourceC2079) = raw29168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29168; decide +kernel
    rw [ha]
    exact (canonical29168 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 3) (sourceB2079 + difference 3 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4649) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 3) (sourceB2079 + difference 3 4) sourceC2079) = raw29169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29169; decide +kernel
    rw [ha]
    exact (canonical29169 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2079 + difference 4 5) (sourceB2079 + difference 5 4) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2079 + difference 4 5) (sourceB2079 + difference 5 4) sourceC2079) = raw29170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29170; decide +kernel
    rw [ha]
    exact (canonical29170 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 0) (sourceB2079 + difference 0 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 0) (sourceB2079 + difference 0 5) sourceC2079) = raw29171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29171; decide +kernel
    rw [ha]
    exact (canonical29171 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 1) (sourceB2079 + difference 1 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 1) (sourceB2079 + difference 1 5) sourceC2079) = raw29172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29172; decide +kernel
    rw [ha]
    exact (canonical29172 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 2) (sourceB2079 + difference 2 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 2) (sourceB2079 + difference 2 5) sourceC2079) = raw29173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29173; decide +kernel
    rw [ha]
    exact (canonical29173 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 3) (sourceB2079 + difference 3 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4308) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 3) (sourceB2079 + difference 3 5) sourceC2079) = raw29174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29174; decide +kernel
    rw [ha]
    exact (canonical29174 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2079 + difference 5 4) (sourceB2079 + difference 4 5) sourceC2079) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA2079 + difference 5 4) (sourceB2079 + difference 4 5) sourceC2079) = raw29175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2079 sourceB2079 sourceC2079 difference raw29175; decide +kernel
    rw [ha]
    exact (canonical29175 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2079 sourceB2079 sourceC2079
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2079, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1738 : Integer.Sparse.reindex keyMap MixedData.row1738 = numericRow1738 := by decide +kernel

theorem numericCheck1738 (x : Master → ℝ) : Integer.Sparse.eval numericRow1738 x =
    (4 : ℝ) * reducedSource1738 x := by
  norm_num [numericRow1738, reducedSource1738, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4287, nodeValue4293, nodeValue4295, nodeValue4308, nodeValue4401, nodeValue4521, nodeValue4525, nodeValue4538, nodeValue4583, nodeValue4631, nodeValue4637, nodeValue4649, nodeValue4706, nodeValue4712, nodeValue4721, nodeValue4726, nodeValue4728, nodeValue4736, nodeValue4741, nodeValue4745, nodeValue4779, nodeValue4827, nodeValue4832, nodeValue4834, nodeValue5014, nodeValue5055, nodeValue5094, nodeValue5099, nodeValue5101] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1738 (mixedVector B) = 0 := by
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4287 : mixedVector B (Sum.inr 4287) = Sparse.eval nodeValue4287 (mixedVector B) := by
    change mixedMoment B node4287 node4287Labels = _
    exact sound4287 B hB hF
  have h4293 : mixedVector B (Sum.inr 4293) = Sparse.eval nodeValue4293 (mixedVector B) := by
    change mixedMoment B node4293 node4293Labels = _
    exact sound4293 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4308 : mixedVector B (Sum.inr 4308) = Sparse.eval nodeValue4308 (mixedVector B) := by
    change mixedMoment B node4308 node4308Labels = _
    exact sound4308 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4521 : mixedVector B (Sum.inr 4521) = Sparse.eval nodeValue4521 (mixedVector B) := by
    change mixedMoment B node4521 node4521Labels = _
    exact sound4521 B hB hF
  have h4525 : mixedVector B (Sum.inr 4525) = Sparse.eval nodeValue4525 (mixedVector B) := by
    change mixedMoment B node4525 node4525Labels = _
    exact sound4525 B hB hF
  have h4538 : mixedVector B (Sum.inr 4538) = Sparse.eval nodeValue4538 (mixedVector B) := by
    change mixedMoment B node4538 node4538Labels = _
    exact sound4538 B hB hF
  have h4583 : mixedVector B (Sum.inr 4583) = Sparse.eval nodeValue4583 (mixedVector B) := by
    change mixedMoment B node4583 node4583Labels = _
    exact sound4583 B hB hF
  have h4631 : mixedVector B (Sum.inr 4631) = Sparse.eval nodeValue4631 (mixedVector B) := by
    change mixedMoment B node4631 node4631Labels = _
    exact sound4631 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4649 : mixedVector B (Sum.inr 4649) = Sparse.eval nodeValue4649 (mixedVector B) := by
    change mixedMoment B node4649 node4649Labels = _
    exact sound4649 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4712 : mixedVector B (Sum.inr 4712) = Sparse.eval nodeValue4712 (mixedVector B) := by
    change mixedMoment B node4712 node4712Labels = _
    exact sound4712 B hB hF
  have h4721 : mixedVector B (Sum.inr 4721) = Sparse.eval nodeValue4721 (mixedVector B) := by
    change mixedMoment B node4721 node4721Labels = _
    exact sound4721 B hB hF
  have h4726 : mixedVector B (Sum.inr 4726) = Sparse.eval nodeValue4726 (mixedVector B) := by
    change mixedMoment B node4726 node4726Labels = _
    exact sound4726 B hB hF
  have h4728 : mixedVector B (Sum.inr 4728) = Sparse.eval nodeValue4728 (mixedVector B) := by
    change mixedMoment B node4728 node4728Labels = _
    exact sound4728 B hB hF
  have h4736 : mixedVector B (Sum.inr 4736) = Sparse.eval nodeValue4736 (mixedVector B) := by
    change mixedMoment B node4736 node4736Labels = _
    exact sound4736 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4745 : mixedVector B (Sum.inr 4745) = Sparse.eval nodeValue4745 (mixedVector B) := by
    change mixedMoment B node4745 node4745Labels = _
    exact sound4745 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4827 : mixedVector B (Sum.inr 4827) = Sparse.eval nodeValue4827 (mixedVector B) := by
    change mixedMoment B node4827 node4827Labels = _
    exact sound4827 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h5014 : mixedVector B (Sum.inr 5014) = Sparse.eval nodeValue5014 (mixedVector B) := by
    change mixedMoment B node5014 node5014Labels = _
    exact sound5014 B hB hF
  have h5055 : mixedVector B (Sum.inr 5055) = Sparse.eval nodeValue5055 (mixedVector B) := by
    change mixedMoment B node5055 node5055Labels = _
    exact sound5055 B hB hF
  have h5094 : mixedVector B (Sum.inr 5094) = Sparse.eval nodeValue5094 (mixedVector B) := by
    change mixedMoment B node5094 node5094Labels = _
    exact sound5094 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  simpa only [sourceForm2079, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4080, h4287, h4293, h4295, h4308, h4401, h4521, h4525, h4538, h4583, h4631, h4637, h4649, h4706, h4712, h4721, h4726, h4728, h4736, h4741, h4745, h4779, h4827, h4832, h4834, h5014, h5055, h5094, h5099, h5101, reducedSource1738] using sourceEq2079 B hB

theorem rowSound1738_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1738 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1738, numericCheck1738, reducedZero1738 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1738_e_oai
