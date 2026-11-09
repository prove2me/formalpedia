-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:29:41.39634+00:00
-- url     : https://prove2.me/submissions/497c22a4-ad8b-4c49-869c-2ebc662c80a6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27263 raw27263Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27263 raw27263Labels = mixedMoment B raw27263step0 raw27263step0Labels := by
      have ha : raw27263step0 = (fun i j => raw27263 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27263step0 raw27263; decide +kernel
      have hl : raw27263step0Labels = raw27263Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27263 raw27263Labels permutation246 permutation7
    mixedMoment B raw27263step0 raw27263step0Labels = mixedMoment B raw27263step1 raw27263step1Labels := by
      have ha : raw27263step1 = -raw27263step0 := by apply Matrix.ext; change ∀ i j, raw27263step1 i j = -(raw27263step0 i j); unfold raw27263step1 raw27263step0; decide +kernel
      have hl : raw27263step1Labels = raw27263step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27263step1 raw27263step1Labels = mixedMoment B raw27263step2 raw27263step2Labels := by
      have ha : raw27263step2 = raw27263step1 := by apply Matrix.ext; unfold raw27263step2 raw27263step1; decide +kernel
      have hl : raw27263step1Labels = labelEmbedding10 ∘ raw27263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27263step1 raw27263step1Labels raw27263step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27264 raw27264Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27264 raw27264Labels = mixedMoment B raw27264step0 raw27264step0Labels := by
      have ha : raw27264step0 = (fun i j => raw27264 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27264step0 raw27264; decide +kernel
      have hl : raw27264step0Labels = raw27264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27264 raw27264Labels permutation246 permutation7
    mixedMoment B raw27264step0 raw27264step0Labels = mixedMoment B raw27264step1 raw27264step1Labels := by
      have ha : raw27264step1 = -raw27264step0 := by apply Matrix.ext; change ∀ i j, raw27264step1 i j = -(raw27264step0 i j); unfold raw27264step1 raw27264step0; decide +kernel
      have hl : raw27264step1Labels = raw27264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27264step1 raw27264step1Labels = mixedMoment B raw27264step2 raw27264step2Labels := by
      have ha : raw27264step2 = raw27264step1 := by apply Matrix.ext; unfold raw27264step2 raw27264step1; decide +kernel
      have hl : raw27264step1Labels = labelEmbedding10 ∘ raw27264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27264step1 raw27264step1Labels raw27264step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical27265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27265 raw27265Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27265 raw27265Labels = mixedMoment B raw27265step0 raw27265step0Labels := by
      have ha : raw27265step0 = (fun i j => raw27265 (permutation248 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27265step0 raw27265; decide +kernel
      have hl : raw27265step0Labels = raw27265Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27265 raw27265Labels permutation248 permutation7
    mixedMoment B raw27265step0 raw27265step0Labels = mixedMoment B raw27265step1 raw27265step1Labels := by
      have ha : raw27265step1 = -raw27265step0 := by apply Matrix.ext; change ∀ i j, raw27265step1 i j = -(raw27265step0 i j); unfold raw27265step1 raw27265step0; decide +kernel
      have hl : raw27265step1Labels = raw27265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27265step1 raw27265step1Labels = mixedMoment B raw27265step2 raw27265step2Labels := by
      have ha : raw27265step2 = raw27265step1 := by apply Matrix.ext; unfold raw27265step2 raw27265step1; decide +kernel
      have hl : raw27265step1Labels = labelEmbedding10 ∘ raw27265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27265step1 raw27265step1Labels raw27265step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical27266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27266 raw27266Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27266 raw27266Labels = mixedMoment B raw27266step0 raw27266step0Labels := by
      have ha : raw27266step0 = (fun i j => raw27266 (permutation250 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27266step0 raw27266; decide +kernel
      have hl : raw27266step0Labels = raw27266Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27266 raw27266Labels permutation250 permutation7
    mixedMoment B raw27266step0 raw27266step0Labels = mixedMoment B raw27266step1 raw27266step1Labels := by
      have ha : raw27266step1 = -raw27266step0 := by apply Matrix.ext; change ∀ i j, raw27266step1 i j = -(raw27266step0 i j); unfold raw27266step1 raw27266step0; decide +kernel
      have hl : raw27266step1Labels = raw27266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27266step1 raw27266step1Labels = mixedMoment B raw27266step2 raw27266step2Labels := by
      have ha : raw27266step2 = raw27266step1 := by apply Matrix.ext; unfold raw27266step2 raw27266step1; decide +kernel
      have hl : raw27266step1Labels = labelEmbedding10 ∘ raw27266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27266step1 raw27266step1Labels raw27266step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical27267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27267 raw27267Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw27267 raw27267Labels = mixedMoment B raw27267step0 raw27267step0Labels := by
      have hz : ∀ j, raw27267 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27267step0 = (fun i j => raw27267 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27267step0 raw27267; decide +kernel
      have hl : raw27267step0Labels = raw27267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27267 raw27267Labels permutation590 hz
    mixedMoment B raw27267step0 raw27267step0Labels = mixedMoment B raw27267step1 raw27267step1Labels := by
      have ha : raw27267step1 = (fun i j => raw27267step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27267step1 raw27267step0; decide +kernel
      have hl : raw27267step1Labels = raw27267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27267step0 raw27267step0Labels permutation32 permutation7
    mixedMoment B raw27267step1 raw27267step1Labels = mixedMoment B raw27267step2 raw27267step2Labels := by
      have ha : raw27267step2 = -raw27267step1 := by apply Matrix.ext; change ∀ i j, raw27267step2 i j = -(raw27267step1 i j); unfold raw27267step2 raw27267step1; decide +kernel
      have hl : raw27267step2Labels = raw27267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27267step2 raw27267step2Labels = mixedMoment B raw27267step3 raw27267step3Labels := by
      have ha : raw27267step3 = raw27267step2 := by apply Matrix.ext; unfold raw27267step3 raw27267step2; decide +kernel
      have hl : raw27267step2Labels = labelEmbedding10 ∘ raw27267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27267step2 raw27267step2Labels raw27267step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical27268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27268 raw27268Labels = mixedMoment B node4117 node4117Labels := by
  calc
    mixedMoment B raw27268 raw27268Labels = mixedMoment B raw27268step0 raw27268step0Labels := by
      have ha : raw27268step0 = (fun i j => raw27268 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27268step0 raw27268; decide +kernel
      have hl : raw27268step0Labels = raw27268Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27268 raw27268Labels permutation246 permutation2
    _ = mixedMoment B node4117 node4117Labels := by rfl

theorem canonical27269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27269 raw27269Labels = mixedMoment B node4263 node4263Labels := by
  calc
    mixedMoment B raw27269 raw27269Labels = mixedMoment B raw27269step0 raw27269step0Labels := by
      have ha : raw27269step0 = (fun i j => raw27269 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27269step0 raw27269; decide +kernel
      have hl : raw27269step0Labels = raw27269Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27269 raw27269Labels permutation194 permutation2
    _ = mixedMoment B node4263 node4263Labels := by rfl

theorem canonical27270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27270 raw27270Labels = mixedMoment B node4263 node4263Labels := by
  calc
    mixedMoment B raw27270 raw27270Labels = mixedMoment B raw27270step0 raw27270step0Labels := by
      have ha : raw27270step0 = (fun i j => raw27270 (permutation218 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27270step0 raw27270; decide +kernel
      have hl : raw27270step0Labels = raw27270Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27270 raw27270Labels permutation218 permutation2
    _ = mixedMoment B node4263 node4263Labels := by rfl

theorem canonical27271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27271 raw27271Labels = mixedMoment B node4263 node4263Labels := by
  calc
    mixedMoment B raw27271 raw27271Labels = mixedMoment B raw27271step0 raw27271step0Labels := by
      have ha : raw27271step0 = (fun i j => raw27271 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27271step0 raw27271; decide +kernel
      have hl : raw27271step0Labels = raw27271Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27271 raw27271Labels permutation240 permutation2
    _ = mixedMoment B node4263 node4263Labels := by rfl

theorem canonical27272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27272 raw27272Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27272 raw27272Labels = mixedMoment B raw27272step0 raw27272step0Labels := by
      have hz : ∀ j, raw27272 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27272step0 = (fun i j => raw27272 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27272step0 raw27272; decide +kernel
      have hl : raw27272step0Labels = raw27272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27272 raw27272Labels permutation590 hz
    mixedMoment B raw27272step0 raw27272step0Labels = mixedMoment B raw27272step1 raw27272step1Labels := by
      have hz : ∀ i, raw27272step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw27272step1 = (fun i j => raw27272step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw27272step1 raw27272step0; decide +kernel
      have hl : raw27272step1Labels = (fun j => raw27272step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27272step0 raw27272step0Labels permutation4 hz
    mixedMoment B raw27272step1 raw27272step1Labels = mixedMoment B raw27272step2 raw27272step2Labels := by
      have ha : raw27272step2 = raw27272step1 := by apply Matrix.ext; unfold raw27272step2 raw27272step1; decide +kernel
      have hl : raw27272step1Labels = labelEmbedding2 ∘ raw27272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27272step1 raw27272step1Labels raw27272step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4068 node4068Labels := by rfl

theorem canonical27273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27273 raw27273Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw27273 raw27273Labels = mixedMoment B raw27273step0 raw27273step0Labels := by
      have ha : raw27273step0 = (fun i j => raw27273 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27273step0 raw27273; decide +kernel
      have hl : raw27273step0Labels = raw27273Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27273 raw27273Labels permutation173 permutation2
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical27274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27274 raw27274Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw27274 raw27274Labels = mixedMoment B raw27274step0 raw27274step0Labels := by
      have ha : raw27274step0 = (fun i j => raw27274 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27274step0 raw27274; decide +kernel
      have hl : raw27274step0Labels = raw27274Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27274 raw27274Labels permutation173 permutation2
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical27275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27275 raw27275Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27275 raw27275Labels = mixedMoment B raw27275step0 raw27275step0Labels := by
      have ha : raw27275step0 = (fun i j => raw27275 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27275step0 raw27275; decide +kernel
      have hl : raw27275step0Labels = raw27275Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27275 raw27275Labels permutation163 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical27276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27276 raw27276Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27276 raw27276Labels = mixedMoment B raw27276step0 raw27276step0Labels := by
      have ha : raw27276step0 = (fun i j => raw27276 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27276step0 raw27276; decide +kernel
      have hl : raw27276step0Labels = raw27276Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27276 raw27276Labels permutation169 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical27277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27277 raw27277Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw27277 raw27277Labels = mixedMoment B raw27277step0 raw27277step0Labels := by
      have hz : ∀ j, raw27277 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27277step0 = (fun i j => raw27277 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27277step0 raw27277; decide +kernel
      have hl : raw27277step0Labels = raw27277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27277 raw27277Labels permutation590 hz
    mixedMoment B raw27277step0 raw27277step0Labels = mixedMoment B raw27277step1 raw27277step1Labels := by
      have ha : raw27277step1 = (fun i j => raw27277step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27277step1 raw27277step0; decide +kernel
      have hl : raw27277step1Labels = raw27277step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27277step0 raw27277step0Labels permutation35 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

theorem canonical27278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27278 raw27278Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw27278 raw27278Labels = mixedMoment B raw27278step0 raw27278step0Labels := by
      have ha : raw27278step0 = (fun i j => raw27278 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27278step0 raw27278; decide +kernel
      have hl : raw27278step0Labels = raw27278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27278 raw27278Labels permutation171 permutation2
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical27279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27279 raw27279Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw27279 raw27279Labels = mixedMoment B raw27279step0 raw27279step0Labels := by
      have ha : raw27279step0 = (fun i j => raw27279 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27279step0 raw27279; decide +kernel
      have hl : raw27279step0Labels = raw27279Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27279 raw27279Labels permutation171 permutation2
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical27280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27280 raw27280Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27280 raw27280Labels = mixedMoment B raw27280step0 raw27280step0Labels := by
      have ha : raw27280step0 = (fun i j => raw27280 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27280step0 raw27280; decide +kernel
      have hl : raw27280step0Labels = raw27280Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27280 raw27280Labels permutation157 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical27281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27281 raw27281Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27281 raw27281Labels = mixedMoment B raw27281step0 raw27281step0Labels := by
      have ha : raw27281step0 = (fun i j => raw27281 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27281step0 raw27281; decide +kernel
      have hl : raw27281step0Labels = raw27281Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27281 raw27281Labels permutation168 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical27282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27282 raw27282Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw27282 raw27282Labels = mixedMoment B raw27282step0 raw27282step0Labels := by
      have hz : ∀ j, raw27282 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27282step0 = (fun i j => raw27282 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27282step0 raw27282; decide +kernel
      have hl : raw27282step0Labels = raw27282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27282 raw27282Labels permutation590 hz
    mixedMoment B raw27282step0 raw27282step0Labels = mixedMoment B raw27282step1 raw27282step1Labels := by
      have ha : raw27282step1 = (fun i j => raw27282step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27282step1 raw27282step0; decide +kernel
      have hl : raw27282step1Labels = raw27282step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27282step0 raw27282step0Labels permutation33 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

theorem canonical27283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27283 raw27283Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw27283 raw27283Labels = mixedMoment B raw27283step0 raw27283step0Labels := by
      have ha : raw27283step0 = (fun i j => raw27283 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27283step0 raw27283; decide +kernel
      have hl : raw27283step0Labels = raw27283Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27283 raw27283Labels permutation170 permutation2
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical27284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27284 raw27284Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw27284 raw27284Labels = mixedMoment B raw27284step0 raw27284step0Labels := by
      have ha : raw27284step0 = (fun i j => raw27284 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27284step0 raw27284; decide +kernel
      have hl : raw27284step0Labels = raw27284Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27284 raw27284Labels permutation170 permutation2
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical27285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27285 raw27285Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27285 raw27285Labels = mixedMoment B raw27285step0 raw27285step0Labels := by
      have ha : raw27285step0 = (fun i j => raw27285 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27285step0 raw27285; decide +kernel
      have hl : raw27285step0Labels = raw27285Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27285 raw27285Labels permutation156 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical27286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27286 raw27286Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27286 raw27286Labels = mixedMoment B raw27286step0 raw27286step0Labels := by
      have ha : raw27286step0 = (fun i j => raw27286 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27286step0 raw27286; decide +kernel
      have hl : raw27286step0Labels = raw27286Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27286 raw27286Labels permutation162 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical27287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27287 raw27287Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw27287 raw27287Labels = mixedMoment B raw27287step0 raw27287step0Labels := by
      have hz : ∀ j, raw27287 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27287step0 = (fun i j => raw27287 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27287step0 raw27287; decide +kernel
      have hl : raw27287step0Labels = raw27287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27287 raw27287Labels permutation590 hz
    _ = mixedMoment B node4267 node4267Labels := by rfl

theorem canonical27288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27288 raw27288Labels = mixedMoment B node4104 node4104Labels := by
  calc
    _ = mixedMoment B node4104 node4104Labels := by rfl

theorem canonical27289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27289 raw27289Labels = mixedMoment B node4236 node4236Labels := by
  calc
    _ = mixedMoment B node4236 node4236Labels := by rfl

theorem canonical27290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27290 raw27290Labels = mixedMoment B node4252 node4252Labels := by
  calc
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical27291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27291 raw27291Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw27291 raw27291Labels = mixedMoment B raw27291step0 raw27291step0Labels := by
      have ha : raw27291step0 = (fun i j => raw27291 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27291step0 raw27291; decide +kernel
      have hl : raw27291step0Labels = raw27291Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27291 raw27291Labels permutation158 permutation2
    _ = mixedMoment B node4252 node4252Labels := by rfl

theorem canonical27292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27292 raw27292Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw27292 raw27292Labels = mixedMoment B raw27292step0 raw27292step0Labels := by
      have ha : raw27292step0 = (fun i j => raw27292 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27292step0 raw27292; decide +kernel
      have hl : raw27292step0Labels = raw27292Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27292 raw27292Labels permutation164 permutation2
    _ = mixedMoment B node4252 node4252Labels := by rfl

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

theorem canonical672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw672 raw672Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw672 raw672Labels = mixedMoment B raw672step0 raw672step0Labels := by
      have ha : raw672step0 = (fun i j => raw672 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw672step0 raw672; decide +kernel
      have hl : raw672step0Labels = raw672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw672 raw672Labels permutation152 permutation4
    mixedMoment B raw672step0 raw672step0Labels = mixedMoment B raw672step1 raw672step1Labels := by
      have ha : raw672step1 = raw672step0 := by apply Matrix.ext; unfold raw672step1 raw672step0; decide +kernel
      have hl : raw672step0Labels = labelEmbedding7 ∘ raw672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw672step0 raw672step0Labels raw672step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw673 raw673Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw673 raw673Labels = mixedMoment B raw673step0 raw673step0Labels := by
      have ha : raw673step0 = (fun i j => raw673 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw673step0 raw673; decide +kernel
      have hl : raw673step0Labels = raw673Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw673 raw673Labels permutation152 permutation4
    _ = mixedMoment B node537 node537Labels := by rfl

theorem canonical674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw674 raw674Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw674 raw674Labels = mixedMoment B raw674step0 raw674step0Labels := by
      have ha : raw674step0 = (fun i j => raw674 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw674step0 raw674; decide +kernel
      have hl : raw674step0Labels = raw674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw674 raw674Labels permutation176 permutation6
    mixedMoment B raw674step0 raw674step0Labels = mixedMoment B raw674step1 raw674step1Labels := by
      have ha : raw674step1 = -raw674step0 := by apply Matrix.ext; change ∀ i j, raw674step1 i j = -(raw674step0 i j); unfold raw674step1 raw674step0; decide +kernel
      have hl : raw674step1Labels = raw674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw674step1 raw674step1Labels = mixedMoment B raw674step2 raw674step2Labels := by
      have ha : raw674step2 = raw674step1 := by apply Matrix.ext; unfold raw674step2 raw674step1; decide +kernel
      have hl : raw674step1Labels = labelEmbedding1 ∘ raw674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw674step1 raw674step1Labels raw674step2Labels labelEmbedding1 hl
    _ = mixedMoment B node662 node662Labels := by rfl

theorem canonical684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw684 raw684Labels = mixedMoment B node4104 node4104Labels := by
  calc
    mixedMoment B raw684 raw684Labels = mixedMoment B raw684step0 raw684step0Labels := by
      have ha : raw684step0 = (fun i j => raw684 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw684step0 raw684; decide +kernel
      have hl : raw684step0Labels = raw684Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw684 raw684Labels permutation152 permutation4
    mixedMoment B raw684step0 raw684step0Labels = mixedMoment B raw684step1 raw684step1Labels := by
      have ha : raw684step1 = raw684step0 := by apply Matrix.ext; unfold raw684step1 raw684step0; decide +kernel
      have hl : raw684step0Labels = labelEmbedding7 ∘ raw684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw684step0 raw684step0Labels raw684step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4104 node4104Labels := by rfl

theorem canonical685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw685 raw685Labels = mixedMoment B node541 node541Labels := by
  calc
    mixedMoment B raw685 raw685Labels = mixedMoment B raw685step0 raw685step0Labels := by
      have ha : raw685step0 = (fun i j => raw685 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw685step0 raw685; decide +kernel
      have hl : raw685step0Labels = raw685Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw685 raw685Labels permutation152 permutation4
    _ = mixedMoment B node541 node541Labels := by rfl

theorem canonical686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw686 raw686Labels = mixedMoment B node674 node674Labels := by
  calc
    mixedMoment B raw686 raw686Labels = mixedMoment B raw686step0 raw686step0Labels := by
      have ha : raw686step0 = (fun i j => raw686 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw686step0 raw686; decide +kernel
      have hl : raw686step0Labels = raw686Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw686 raw686Labels permutation246 permutation6
    mixedMoment B raw686step0 raw686step0Labels = mixedMoment B raw686step1 raw686step1Labels := by
      have ha : raw686step1 = -raw686step0 := by apply Matrix.ext; change ∀ i j, raw686step1 i j = -(raw686step0 i j); unfold raw686step1 raw686step0; decide +kernel
      have hl : raw686step1Labels = raw686step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw686step1 raw686step1Labels = mixedMoment B raw686step2 raw686step2Labels := by
      have ha : raw686step2 = raw686step1 := by apply Matrix.ext; unfold raw686step2 raw686step1; decide +kernel
      have hl : raw686step1Labels = labelEmbedding1 ∘ raw686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw686step1 raw686step1Labels raw686step2Labels labelEmbedding1 hl
    _ = mixedMoment B node674 node674Labels := by rfl

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

theorem canonical930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw930 raw930Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw930 raw930Labels = mixedMoment B raw930step0 raw930step0Labels := by
      have ha : raw930step0 = (fun i j => raw930 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw930step0 raw930; decide +kernel
      have hl : raw930step0Labels = raw930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw930 raw930Labels permutation152 permutation4
    mixedMoment B raw930step0 raw930step0Labels = mixedMoment B raw930step1 raw930step1Labels := by
      have ha : raw930step1 = raw930step0 := by apply Matrix.ext; unfold raw930step1 raw930step0; decide +kernel
      have hl : raw930step0Labels = labelEmbedding7 ∘ raw930step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw930step0 raw930step0Labels raw930step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4232 node4232Labels := by rfl

theorem canonical931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw931 raw931Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw931 raw931Labels = mixedMoment B raw931step0 raw931step0Labels := by
      have ha : raw931step0 = (fun i j => raw931 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw931step0 raw931; decide +kernel
      have hl : raw931step0Labels = raw931Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw931 raw931Labels permutation152 permutation4
    _ = mixedMoment B node732 node732Labels := by rfl

theorem canonical932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw932 raw932Labels = mixedMoment B node798 node798Labels := by
  calc
    mixedMoment B raw932 raw932Labels = mixedMoment B raw932step0 raw932step0Labels := by
      have ha : raw932step0 = (fun i j => raw932 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw932step0 raw932; decide +kernel
      have hl : raw932step0Labels = raw932Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw932 raw932Labels permutation176 permutation6
    mixedMoment B raw932step0 raw932step0Labels = mixedMoment B raw932step1 raw932step1Labels := by
      have ha : raw932step1 = -raw932step0 := by apply Matrix.ext; change ∀ i j, raw932step1 i j = -(raw932step0 i j); unfold raw932step1 raw932step0; decide +kernel
      have hl : raw932step1Labels = raw932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw932step1 raw932step1Labels = mixedMoment B raw932step2 raw932step2Labels := by
      have ha : raw932step2 = raw932step1 := by apply Matrix.ext; unfold raw932step2 raw932step1; decide +kernel
      have hl : raw932step1Labels = labelEmbedding1 ∘ raw932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw932step1 raw932step1Labels raw932step2Labels labelEmbedding1 hl
    _ = mixedMoment B node798 node798Labels := by rfl

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

theorem canonical969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw969 raw969Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw969 raw969Labels = mixedMoment B raw969step0 raw969step0Labels := by
      have ha : raw969step0 = (fun i j => raw969 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw969step0 raw969; decide +kernel
      have hl : raw969step0Labels = raw969Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw969 raw969Labels permutation152 permutation4
    mixedMoment B raw969step0 raw969step0Labels = mixedMoment B raw969step1 raw969step1Labels := by
      have ha : raw969step1 = raw969step0 := by apply Matrix.ext; unfold raw969step1 raw969step0; decide +kernel
      have hl : raw969step0Labels = labelEmbedding7 ∘ raw969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw969step0 raw969step0Labels raw969step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw970 raw970Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw970 raw970Labels = mixedMoment B raw970step0 raw970step0Labels := by
      have ha : raw970step0 = (fun i j => raw970 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw970step0 raw970; decide +kernel
      have hl : raw970step0Labels = raw970Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw970 raw970Labels permutation152 permutation4
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw971 raw971Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw971 raw971Labels = mixedMoment B raw971step0 raw971step0Labels := by
      have ha : raw971step0 = (fun i j => raw971 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw971step0 raw971; decide +kernel
      have hl : raw971step0Labels = raw971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw971 raw971Labels permutation200 permutation6
    mixedMoment B raw971step0 raw971step0Labels = mixedMoment B raw971step1 raw971step1Labels := by
      have ha : raw971step1 = -raw971step0 := by apply Matrix.ext; change ∀ i j, raw971step1 i j = -(raw971step0 i j); unfold raw971step1 raw971step0; decide +kernel
      have hl : raw971step1Labels = raw971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw971step1 raw971step1Labels = mixedMoment B raw971step2 raw971step2Labels := by
      have ha : raw971step2 = raw971step1 := by apply Matrix.ext; unfold raw971step2 raw971step1; decide +kernel
      have hl : raw971step1Labels = labelEmbedding1 ∘ raw971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw971step1 raw971step1Labels raw971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1245 raw1245Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw1245 raw1245Labels = mixedMoment B raw1245step0 raw1245step0Labels := by
      have ha : raw1245step0 = (fun i j => raw1245 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1245step0 raw1245; decide +kernel
      have hl : raw1245step0Labels = raw1245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1245 raw1245Labels permutation152 permutation4
    mixedMoment B raw1245step0 raw1245step0Labels = mixedMoment B raw1245step1 raw1245step1Labels := by
      have ha : raw1245step1 = raw1245step0 := by apply Matrix.ext; unfold raw1245step1 raw1245step0; decide +kernel
      have hl : raw1245step0Labels = labelEmbedding7 ∘ raw1245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1245step0 raw1245step0Labels raw1245step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1246 raw1246Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw1246 raw1246Labels = mixedMoment B raw1246step0 raw1246step0Labels := by
      have ha : raw1246step0 = (fun i j => raw1246 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1246step0 raw1246; decide +kernel
      have hl : raw1246step0Labels = raw1246Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1246 raw1246Labels permutation152 permutation4
    _ = mixedMoment B node1034 node1034Labels := by rfl

theorem canonical1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1247 raw1247Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw1247 raw1247Labels = mixedMoment B raw1247step0 raw1247step0Labels := by
      have ha : raw1247step0 = (fun i j => raw1247 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1247step0 raw1247; decide +kernel
      have hl : raw1247step0Labels = raw1247Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1247 raw1247Labels permutation176 permutation6
    mixedMoment B raw1247step0 raw1247step0Labels = mixedMoment B raw1247step1 raw1247step1Labels := by
      have ha : raw1247step1 = -raw1247step0 := by apply Matrix.ext; change ∀ i j, raw1247step1 i j = -(raw1247step0 i j); unfold raw1247step1 raw1247step0; decide +kernel
      have hl : raw1247step1Labels = raw1247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1247step1 raw1247step1Labels = mixedMoment B raw1247step2 raw1247step2Labels := by
      have ha : raw1247step2 = raw1247step1 := by apply Matrix.ext; unfold raw1247step2 raw1247step1; decide +kernel
      have hl : raw1247step1Labels = labelEmbedding1 ∘ raw1247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1247step1 raw1247step1Labels raw1247step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1644 node1644Labels := by rfl

theorem canonical1254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1254 raw1254Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw1254 raw1254Labels = mixedMoment B raw1254step0 raw1254step0Labels := by
      have ha : raw1254step0 = (fun i j => raw1254 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1254step0 raw1254; decide +kernel
      have hl : raw1254step0Labels = raw1254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1254 raw1254Labels permutation152 permutation4
    mixedMoment B raw1254step0 raw1254step0Labels = mixedMoment B raw1254step1 raw1254step1Labels := by
      have ha : raw1254step1 = raw1254step0 := by apply Matrix.ext; unfold raw1254step1 raw1254step0; decide +kernel
      have hl : raw1254step0Labels = labelEmbedding7 ∘ raw1254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1254step0 raw1254step0Labels raw1254step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical1255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1255 raw1255Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw1255 raw1255Labels = mixedMoment B raw1255step0 raw1255step0Labels := by
      have ha : raw1255step0 = (fun i j => raw1255 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1255step0 raw1255; decide +kernel
      have hl : raw1255step0Labels = raw1255Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1255 raw1255Labels permutation152 permutation4
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical1256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1256 raw1256Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw1256 raw1256Labels = mixedMoment B raw1256step0 raw1256step0Labels := by
      have ha : raw1256step0 = (fun i j => raw1256 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1256step0 raw1256; decide +kernel
      have hl : raw1256step0Labels = raw1256Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1256 raw1256Labels permutation182 permutation6
    mixedMoment B raw1256step0 raw1256step0Labels = mixedMoment B raw1256step1 raw1256step1Labels := by
      have ha : raw1256step1 = -raw1256step0 := by apply Matrix.ext; change ∀ i j, raw1256step1 i j = -(raw1256step0 i j); unfold raw1256step1 raw1256step0; decide +kernel
      have hl : raw1256step1Labels = raw1256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1256step1 raw1256step1Labels = mixedMoment B raw1256step2 raw1256step2Labels := by
      have ha : raw1256step2 = raw1256step1 := by apply Matrix.ext; unfold raw1256step2 raw1256step1; decide +kernel
      have hl : raw1256step1Labels = labelEmbedding1 ∘ raw1256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1256step1 raw1256step1Labels raw1256step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4100 node4100Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node537 node537Labels + mixedMoment B node662 node662Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw672 singletonSmall4100
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4100) = raw672Labels := by decide +kernel
  rw [hl, canonical672 B hB] at h
  have hc0 : mixedMoment B raw672 (Fin.cases (0 : Fin 2) singletonSmall4100) =
      mixedMoment B node537 node537Labels := by
    have ha : raw672 = raw673 := by apply Matrix.ext; unfold raw672 raw673; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4100 = raw673Labels := by decide +kernel
    rw [ha, hj, canonical673 B hB]
  have hc1 : mixedMoment B raw672 (Fin.cases (1 : Fin 2) singletonSmall4100) =
      mixedMoment B node662 node662Labels := by
    have ha : raw672 = raw674 := by apply Matrix.ext; unfold raw672 raw674; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4100 = raw674Labels := by decide +kernel
    rw [ha, hj, canonical674 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4104 node4104Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node541 node541Labels + mixedMoment B node674 node674Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw684 singletonSmall4104
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4104) = raw684Labels := by decide +kernel
  rw [hl, canonical684 B hB] at h
  have hc0 : mixedMoment B raw684 (Fin.cases (0 : Fin 2) singletonSmall4104) =
      mixedMoment B node541 node541Labels := by
    have ha : raw684 = raw685 := by apply Matrix.ext; unfold raw684 raw685; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4104 = raw685Labels := by decide +kernel
    rw [ha, hj, canonical685 B hB]
  have hc1 : mixedMoment B raw684 (Fin.cases (1 : Fin 2) singletonSmall4104) =
      mixedMoment B node674 node674Labels := by
    have ha : raw684 = raw686 := by apply Matrix.ext; unfold raw684 raw686; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4104 = raw686Labels := by decide +kernel
    rw [ha, hj, canonical686 B hB]
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

theorem singleton4232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4232 node4232Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node732 node732Labels + mixedMoment B node798 node798Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw930 singletonSmall4232
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4232) = raw930Labels := by decide +kernel
  rw [hl, canonical930 B hB] at h
  have hc0 : mixedMoment B raw930 (Fin.cases (0 : Fin 2) singletonSmall4232) =
      mixedMoment B node732 node732Labels := by
    have ha : raw930 = raw931 := by apply Matrix.ext; unfold raw930 raw931; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4232 = raw931Labels := by decide +kernel
    rw [ha, hj, canonical931 B hB]
  have hc1 : mixedMoment B raw930 (Fin.cases (1 : Fin 2) singletonSmall4232) =
      mixedMoment B node798 node798Labels := by
    have ha : raw930 = raw932 := by apply Matrix.ext; unfold raw930 raw932; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4232 = raw932Labels := by decide +kernel
    rw [ha, hj, canonical932 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4249 node4249Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node783 node783Labels + mixedMoment B node803 node803Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw969 singletonSmall4249
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4249) = raw969Labels := by decide +kernel
  rw [hl, canonical969 B hB] at h
  have hc0 : mixedMoment B raw969 (Fin.cases (0 : Fin 2) singletonSmall4249) =
      mixedMoment B node783 node783Labels := by
    have ha : raw969 = raw970 := by apply Matrix.ext; unfold raw969 raw970; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4249 = raw970Labels := by decide +kernel
    rw [ha, hj, canonical970 B hB]
  have hc1 : mixedMoment B raw969 (Fin.cases (1 : Fin 2) singletonSmall4249) =
      mixedMoment B node803 node803Labels := by
    have ha : raw969 = raw971 := by apply Matrix.ext; unfold raw969 raw971; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4249 = raw971Labels := by decide +kernel
    rw [ha, hj, canonical971 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4451 node4451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1034 node1034Labels + mixedMoment B node1644 node1644Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1245 singletonSmall4451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4451) = raw1245Labels := by decide +kernel
  rw [hl, canonical1245 B hB] at h
  have hc0 : mixedMoment B raw1245 (Fin.cases (0 : Fin 2) singletonSmall4451) =
      mixedMoment B node1034 node1034Labels := by
    have ha : raw1245 = raw1246 := by apply Matrix.ext; unfold raw1245 raw1246; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4451 = raw1246Labels := by decide +kernel
    rw [ha, hj, canonical1246 B hB]
  have hc1 : mixedMoment B raw1245 (Fin.cases (1 : Fin 2) singletonSmall4451) =
      mixedMoment B node1644 node1644Labels := by
    have ha : raw1245 = raw1247 := by apply Matrix.ext; unfold raw1245 raw1247; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4451 = raw1247Labels := by decide +kernel
    rw [ha, hj, canonical1247 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4456 node4456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1039 node1039Labels + mixedMoment B node1706 node1706Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1254 singletonSmall4456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4456) = raw1254Labels := by decide +kernel
  rw [hl, canonical1254 B hB] at h
  have hc0 : mixedMoment B raw1254 (Fin.cases (0 : Fin 2) singletonSmall4456) =
      mixedMoment B node1039 node1039Labels := by
    have ha : raw1254 = raw1255 := by apply Matrix.ext; unfold raw1254 raw1255; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4456 = raw1255Labels := by decide +kernel
    rw [ha, hj, canonical1255 B hB]
  have hc1 : mixedMoment B raw1254 (Fin.cases (1 : Fin 2) singletonSmall4456) =
      mixedMoment B node1706 node1706Labels := by
    have ha : raw1254 = raw1256 := by apply Matrix.ext; unfold raw1254 raw1256; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4456 = raw1256Labels := by decide +kernel
    rw [ha, hj, canonical1256 B hB]
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

theorem sound662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node662 node662Labels = Sparse.eval nodeValue662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 662) = mixedMoment B node662 node662Labels := rfl
  simpa [nodeValue662, Sparse.eval] using hc.symm

theorem sound674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node674 node674Labels = Sparse.eval nodeValue674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 674) = mixedMoment B node674 node674Labels := rfl
  simpa [nodeValue674, Sparse.eval] using hc.symm

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

theorem sound732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node732 node732Labels = Sparse.eval nodeValue732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 732) = mixedMoment B node732 node732Labels := rfl
  simpa [nodeValue732, Sparse.eval] using hc.symm

theorem sound736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node736 node736Labels = Sparse.eval nodeValue736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 736) = mixedMoment B node736 node736Labels := rfl
  simpa [nodeValue736, Sparse.eval] using hc.symm

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

theorem sound783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node783 node783Labels = Sparse.eval nodeValue783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 783) = mixedMoment B node783 node783Labels := rfl
  simpa [nodeValue783, Sparse.eval] using hc.symm

theorem sound786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node786 node786Labels = Sparse.eval nodeValue786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 786) = mixedMoment B node786 node786Labels := rfl
  simpa [nodeValue786, Sparse.eval] using hc.symm

theorem sound798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node798 node798Labels = Sparse.eval nodeValue798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 798) = mixedMoment B node798 node798Labels := rfl
  simpa [nodeValue798, Sparse.eval] using hc.symm

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

theorem sound818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node818 node818Labels = Sparse.eval nodeValue818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 818) = mixedMoment B node818 node818Labels := rfl
  simpa [nodeValue818, Sparse.eval] using hc.symm

theorem sound822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node822 node822Labels = Sparse.eval nodeValue822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 822) = mixedMoment B node822 node822Labels := rfl
  simpa [nodeValue822, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1034 node1034Labels = Sparse.eval nodeValue1034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1034) = mixedMoment B node1034 node1034Labels := rfl
  simpa [nodeValue1034, Sparse.eval] using hc.symm

theorem sound1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1039 node1039Labels = Sparse.eval nodeValue1039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1039) = mixedMoment B node1039 node1039Labels := rfl
  simpa [nodeValue1039, Sparse.eval] using hc.symm

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

theorem sound1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1644 node1644Labels = Sparse.eval nodeValue1644 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1644) = mixedMoment B node1644 node1644Labels := rfl
  simpa [nodeValue1644, Sparse.eval] using hc.symm

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

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

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

theorem sound537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node537 node537Labels = Sparse.eval nodeValue537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 537) = mixedMoment B node537 node537Labels := rfl
  simpa [nodeValue537, Sparse.eval] using hc.symm

theorem sound541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node541 node541Labels = Sparse.eval nodeValue541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 541) = mixedMoment B node541 node541Labels := rfl
  simpa [nodeValue541, Sparse.eval] using hc.symm

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

theorem sound4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4068 node4068Labels = Sparse.eval nodeValue4068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4068) = mixedMoment B node4068 node4068Labels := rfl
  simpa [nodeValue4068, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4117 node4117Labels = 0 := by
  exact mixedMoment_order_one B hB node4117 node4117Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4100 node4100Labels = Sparse.eval nodeValue4100 (mixedVector B) := by
  have h := singleton4100 B _hB
  rw [sound537 B _hB _hF, sound662 B _hB _hF] at h
  norm_num [nodeValue4100, nodeValue537, nodeValue662, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4104 node4104Labels = Sparse.eval nodeValue4104 (mixedVector B) := by
  have h := singleton4104 B _hB
  rw [sound541 B _hB _hF, sound674 B _hB _hF] at h
  norm_num [nodeValue4104, nodeValue541, nodeValue674, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4117 node4117Labels = Sparse.eval nodeValue4117 (mixedVector B) := by
  simpa only [nodeValue4117, Sparse.eval_nil] using zero4117 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4263 node4263Labels = 0 := by
  exact mixedMoment_order_one B hB node4263 node4263Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4267 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4267 node4267Labels = 0 := by
  exact mixedMoment_order_one B hB node4267 node4267Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4232 node4232Labels = Sparse.eval nodeValue4232 (mixedVector B) := by
  have h := singleton4232 B _hB
  rw [sound732 B _hB _hF, sound798 B _hB _hF] at h
  norm_num [nodeValue4232, nodeValue732, nodeValue798, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4236 node4236Labels = Sparse.eval nodeValue4236 (mixedVector B) := by
  have h := singleton4236 B _hB
  rw [sound736 B _hB _hF, sound818 B _hB _hF] at h
  norm_num [nodeValue4236, nodeValue736, nodeValue818, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4249 node4249Labels = Sparse.eval nodeValue4249 (mixedVector B) := by
  have h := singleton4249 B _hB
  rw [sound783 B _hB _hF, sound803 B _hB _hF] at h
  norm_num [nodeValue4249, nodeValue783, nodeValue803, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4252 node4252Labels = Sparse.eval nodeValue4252 (mixedVector B) := by
  have h := singleton4252 B _hB
  rw [sound786 B _hB _hF, sound822 B _hB _hF] at h
  norm_num [nodeValue4252, nodeValue786, nodeValue822, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4263 node4263Labels = Sparse.eval nodeValue4263 (mixedVector B) := by
  simpa only [nodeValue4263, Sparse.eval_nil] using zero4263 B _hB _hF

theorem sound4267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4267 node4267Labels = Sparse.eval nodeValue4267 (mixedVector B) := by
  simpa only [nodeValue4267, Sparse.eval_nil] using zero4267 B _hB _hF

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

theorem sound4451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4451 node4451Labels = Sparse.eval nodeValue4451 (mixedVector B) := by
  have h := singleton4451 B _hB
  rw [sound1034 B _hB _hF, sound1644 B _hB _hF] at h
  norm_num [nodeValue4451, nodeValue1034, nodeValue1644, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4456 node4456Labels = Sparse.eval nodeValue4456 (mixedVector B) := by
  have h := singleton4456 B _hB
  rw [sound1039 B _hB _hF, sound1706 B _hB _hF] at h
  norm_num [nodeValue4456, nodeValue1039, nodeValue1706, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = 0 := by
  exact mixedMoment_order_one B hB node4497 node4497Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = Sparse.eval nodeValue4497 (mixedVector B) := by
  simpa only [nodeValue4497, Sparse.eval_nil] using zero4497 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources59
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1889 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 1) (sourceB1889 + difference 1 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 1) (sourceB1889 + difference 1 0) sourceC1889) = raw27263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27263; decide +kernel
    rw [ha]
    exact (canonical27263 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 2) (sourceB1889 + difference 2 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 2) (sourceB1889 + difference 2 0) sourceC1889) = raw27264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27264; decide +kernel
    rw [ha]
    exact (canonical27264 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 3) (sourceB1889 + difference 3 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 3) (sourceB1889 + difference 3 0) sourceC1889) = raw27265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27265; decide +kernel
    rw [ha]
    exact (canonical27265 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 4) (sourceB1889 + difference 4 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 4) (sourceB1889 + difference 4 0) sourceC1889) = raw27266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27266; decide +kernel
    rw [ha]
    exact (canonical27266 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 5) (sourceB1889 + difference 5 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 5) (sourceB1889 + difference 5 0) sourceC1889) = raw27267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27267; decide +kernel
    rw [ha]
    exact (canonical27267 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 0) (sourceB1889 + difference 0 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4117) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 0) (sourceB1889 + difference 0 1) sourceC1889) = raw27268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27268; decide +kernel
    rw [ha]
    exact (canonical27268 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 2) (sourceB1889 + difference 2 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 2) (sourceB1889 + difference 2 1) sourceC1889) = raw27269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27269; decide +kernel
    rw [ha]
    exact (canonical27269 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 3) (sourceB1889 + difference 3 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 3) (sourceB1889 + difference 3 1) sourceC1889) = raw27270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27270; decide +kernel
    rw [ha]
    exact (canonical27270 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 4) (sourceB1889 + difference 4 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 4) (sourceB1889 + difference 4 1) sourceC1889) = raw27271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27271; decide +kernel
    rw [ha]
    exact (canonical27271 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 5) (sourceB1889 + difference 5 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 5) (sourceB1889 + difference 5 1) sourceC1889) = raw27272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27272; decide +kernel
    rw [ha]
    exact (canonical27272 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 0) (sourceB1889 + difference 0 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 0) (sourceB1889 + difference 0 2) sourceC1889) = raw27273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27273; decide +kernel
    rw [ha]
    exact (canonical27273 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 1) (sourceB1889 + difference 1 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 1) (sourceB1889 + difference 1 2) sourceC1889) = raw27274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27274; decide +kernel
    rw [ha]
    exact (canonical27274 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 3) (sourceB1889 + difference 3 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 3) (sourceB1889 + difference 3 2) sourceC1889) = raw27275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27275; decide +kernel
    rw [ha]
    exact (canonical27275 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 4) (sourceB1889 + difference 4 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 4) (sourceB1889 + difference 4 2) sourceC1889) = raw27276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27276; decide +kernel
    rw [ha]
    exact (canonical27276 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 5) (sourceB1889 + difference 5 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 5) (sourceB1889 + difference 5 2) sourceC1889) = raw27277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27277; decide +kernel
    rw [ha]
    exact (canonical27277 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 0) (sourceB1889 + difference 0 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 0) (sourceB1889 + difference 0 3) sourceC1889) = raw27278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27278; decide +kernel
    rw [ha]
    exact (canonical27278 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 1) (sourceB1889 + difference 1 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 1) (sourceB1889 + difference 1 3) sourceC1889) = raw27279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27279; decide +kernel
    rw [ha]
    exact (canonical27279 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 2) (sourceB1889 + difference 2 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 2) (sourceB1889 + difference 2 3) sourceC1889) = raw27280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27280; decide +kernel
    rw [ha]
    exact (canonical27280 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 4) (sourceB1889 + difference 4 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 4) (sourceB1889 + difference 4 3) sourceC1889) = raw27281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27281; decide +kernel
    rw [ha]
    exact (canonical27281 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 5) (sourceB1889 + difference 5 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 5) (sourceB1889 + difference 5 3) sourceC1889) = raw27282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27282; decide +kernel
    rw [ha]
    exact (canonical27282 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 0) (sourceB1889 + difference 0 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 0) (sourceB1889 + difference 0 4) sourceC1889) = raw27283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27283; decide +kernel
    rw [ha]
    exact (canonical27283 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 1) (sourceB1889 + difference 1 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 1) (sourceB1889 + difference 1 4) sourceC1889) = raw27284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27284; decide +kernel
    rw [ha]
    exact (canonical27284 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 2) (sourceB1889 + difference 2 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 2) (sourceB1889 + difference 2 4) sourceC1889) = raw27285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27285; decide +kernel
    rw [ha]
    exact (canonical27285 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 3) (sourceB1889 + difference 3 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 3) (sourceB1889 + difference 3 4) sourceC1889) = raw27286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27286; decide +kernel
    rw [ha]
    exact (canonical27286 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 5) (sourceB1889 + difference 5 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 5) (sourceB1889 + difference 5 4) sourceC1889) = raw27287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27287; decide +kernel
    rw [ha]
    exact (canonical27287 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 0) (sourceB1889 + difference 0 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4104) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 0) (sourceB1889 + difference 0 5) sourceC1889) = raw27288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27288; decide +kernel
    rw [ha]
    exact (canonical27288 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 1) (sourceB1889 + difference 1 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4236) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 1) (sourceB1889 + difference 1 5) sourceC1889) = raw27289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27289; decide +kernel
    rw [ha]
    exact (canonical27289 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 2) (sourceB1889 + difference 2 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 2) (sourceB1889 + difference 2 5) sourceC1889) = raw27290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27290; decide +kernel
    rw [ha]
    exact (canonical27290 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 3) (sourceB1889 + difference 3 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 3) (sourceB1889 + difference 3 5) sourceC1889) = raw27291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27291; decide +kernel
    rw [ha]
    exact (canonical27291 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 4) (sourceB1889 + difference 4 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 4) (sourceB1889 + difference 4 5) sourceC1889) = raw27292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27292; decide +kernel
    rw [ha]
    exact (canonical27292 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1889 sourceB1889 sourceC1889
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1889, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1599 : Integer.Sparse.reindex keyMap MixedData.row1599 = numericRow1599 := by decide +kernel

theorem numericCheck1599 (x : Master → ℝ) : Integer.Sparse.eval numericRow1599 x =
    (4 : ℝ) * reducedSource1599 x := by
  norm_num [numericRow1599, reducedSource1599, Integer.Sparse.eval, Sparse.eval, nodeValue4068, nodeValue4100, nodeValue4104, nodeValue4117, nodeValue4232, nodeValue4236, nodeValue4249, nodeValue4252, nodeValue4263, nodeValue4267, nodeValue4451, nodeValue4456, nodeValue4497]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1599 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1599 (mixedVector B) = 0 := by
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  have h4100 : mixedVector B (Sum.inr 4100) = Sparse.eval nodeValue4100 (mixedVector B) := by
    change mixedMoment B node4100 node4100Labels = _
    exact sound4100 B hB hF
  have h4104 : mixedVector B (Sum.inr 4104) = Sparse.eval nodeValue4104 (mixedVector B) := by
    change mixedMoment B node4104 node4104Labels = _
    exact sound4104 B hB hF
  have h4117 : mixedVector B (Sum.inr 4117) = Sparse.eval nodeValue4117 (mixedVector B) := by
    change mixedMoment B node4117 node4117Labels = _
    exact sound4117 B hB hF
  have h4232 : mixedVector B (Sum.inr 4232) = Sparse.eval nodeValue4232 (mixedVector B) := by
    change mixedMoment B node4232 node4232Labels = _
    exact sound4232 B hB hF
  have h4236 : mixedVector B (Sum.inr 4236) = Sparse.eval nodeValue4236 (mixedVector B) := by
    change mixedMoment B node4236 node4236Labels = _
    exact sound4236 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4252 : mixedVector B (Sum.inr 4252) = Sparse.eval nodeValue4252 (mixedVector B) := by
    change mixedMoment B node4252 node4252Labels = _
    exact sound4252 B hB hF
  have h4263 : mixedVector B (Sum.inr 4263) = Sparse.eval nodeValue4263 (mixedVector B) := by
    change mixedMoment B node4263 node4263Labels = _
    exact sound4263 B hB hF
  have h4267 : mixedVector B (Sum.inr 4267) = Sparse.eval nodeValue4267 (mixedVector B) := by
    change mixedMoment B node4267 node4267Labels = _
    exact sound4267 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  simpa only [sourceForm1889, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4068, h4100, h4104, h4117, h4232, h4236, h4249, h4252, h4263, h4267, h4451, h4456, h4497, reducedSource1599] using sourceEq1889 B hB

theorem rowSound1599_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1599 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1599, numericCheck1599, reducedZero1599 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e_oai
