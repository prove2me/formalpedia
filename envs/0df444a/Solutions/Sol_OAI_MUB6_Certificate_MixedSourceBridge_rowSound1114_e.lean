-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:19:54.881846+00:00
-- url     : https://prove2.me/submissions/0fb6f41b-afe9-4b0d-8f57-e9096dc94166

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E119
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1371 raw1371Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw1371 raw1371Labels = mixedMoment B raw1371step0 raw1371step0Labels := by
      have ha : raw1371step0 = (fun i j => raw1371 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1371step0 raw1371; decide +kernel
      have hl : raw1371step0Labels = raw1371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1371 raw1371Labels permutation32 permutation4
    mixedMoment B raw1371step0 raw1371step0Labels = mixedMoment B raw1371step1 raw1371step1Labels := by
      have ha : raw1371step1 = raw1371step0 := by apply Matrix.ext; unfold raw1371step1 raw1371step0; decide +kernel
      have hl : raw1371step0Labels = labelEmbedding7 ∘ raw1371step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1371step0 raw1371step0Labels raw1371step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1372 raw1372Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw1372 raw1372Labels = mixedMoment B raw1372step0 raw1372step0Labels := by
      have ha : raw1372step0 = (fun i j => raw1372 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1372step0 raw1372; decide +kernel
      have hl : raw1372step0Labels = raw1372Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1372 raw1372Labels permutation32 permutation4
    _ = mixedMoment B node1131 node1131Labels := by rfl

theorem canonical1373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1373 raw1373Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw1373 raw1373Labels = mixedMoment B raw1373step0 raw1373step0Labels := by
      have ha : raw1373step0 = (fun i j => raw1373 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1373step0 raw1373; decide +kernel
      have hl : raw1373step0Labels = raw1373Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1373 raw1373Labels permutation32 permutation6
    mixedMoment B raw1373step0 raw1373step0Labels = mixedMoment B raw1373step1 raw1373step1Labels := by
      have ha : raw1373step1 = -raw1373step0 := by apply Matrix.ext; change ∀ i j, raw1373step1 i j = -(raw1373step0 i j); unfold raw1373step1 raw1373step0; decide +kernel
      have hl : raw1373step1Labels = raw1373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1373step1 raw1373step1Labels = mixedMoment B raw1373step2 raw1373step2Labels := by
      have ha : raw1373step2 = raw1373step1 := by apply Matrix.ext; unfold raw1373step2 raw1373step1; decide +kernel
      have hl : raw1373step1Labels = labelEmbedding1 ∘ raw1373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1373step1 raw1373step1Labels raw1373step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

theorem canonical1389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1389 raw1389Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw1389 raw1389Labels = mixedMoment B raw1389step0 raw1389step0Labels := by
      have ha : raw1389step0 = (fun i j => raw1389 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1389step0 raw1389; decide +kernel
      have hl : raw1389step0Labels = raw1389Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1389 raw1389Labels permutation8 permutation4
    mixedMoment B raw1389step0 raw1389step0Labels = mixedMoment B raw1389step1 raw1389step1Labels := by
      have ha : raw1389step1 = raw1389step0 := by apply Matrix.ext; unfold raw1389step1 raw1389step0; decide +kernel
      have hl : raw1389step0Labels = labelEmbedding7 ∘ raw1389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1389step0 raw1389step0Labels raw1389step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

theorem canonical1390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1390 raw1390Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw1390 raw1390Labels = mixedMoment B raw1390step0 raw1390step0Labels := by
      have ha : raw1390step0 = (fun i j => raw1390 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1390step0 raw1390; decide +kernel
      have hl : raw1390step0Labels = raw1390Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1390 raw1390Labels permutation8 permutation4
    _ = mixedMoment B node1140 node1140Labels := by rfl

theorem canonical1391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1391 raw1391Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw1391 raw1391Labels = mixedMoment B raw1391step0 raw1391step0Labels := by
      have ha : raw1391step0 = (fun i j => raw1391 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1391step0 raw1391; decide +kernel
      have hl : raw1391step0Labels = raw1391Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1391 raw1391Labels permutation31 permutation6
    mixedMoment B raw1391step0 raw1391step0Labels = mixedMoment B raw1391step1 raw1391step1Labels := by
      have ha : raw1391step1 = raw1391step0 := by apply Matrix.ext; unfold raw1391step1 raw1391step0; decide +kernel
      have hl : raw1391step0Labels = labelEmbedding1 ∘ raw1391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1391step0 raw1391step0Labels raw1391step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3275 node3275Labels := by rfl

theorem canonical1395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1395 raw1395Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw1395 raw1395Labels = mixedMoment B raw1395step0 raw1395step0Labels := by
      have ha : raw1395step0 = (fun i j => raw1395 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1395step0 raw1395; decide +kernel
      have hl : raw1395step0Labels = raw1395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1395 raw1395Labels permutation8 permutation4
    mixedMoment B raw1395step0 raw1395step0Labels = mixedMoment B raw1395step1 raw1395step1Labels := by
      have ha : raw1395step1 = raw1395step0 := by apply Matrix.ext; unfold raw1395step1 raw1395step0; decide +kernel
      have hl : raw1395step0Labels = labelEmbedding7 ∘ raw1395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1395step0 raw1395step0Labels raw1395step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical1396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1396 raw1396Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw1396 raw1396Labels = mixedMoment B raw1396step0 raw1396step0Labels := by
      have ha : raw1396step0 = (fun i j => raw1396 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1396step0 raw1396; decide +kernel
      have hl : raw1396step0Labels = raw1396Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1396 raw1396Labels permutation8 permutation4
    _ = mixedMoment B node1144 node1144Labels := by rfl

theorem canonical1397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1397 raw1397Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw1397 raw1397Labels = mixedMoment B raw1397step0 raw1397step0Labels := by
      have ha : raw1397step0 = (fun i j => raw1397 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1397step0 raw1397; decide +kernel
      have hl : raw1397step0Labels = raw1397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1397 raw1397Labels permutation8 permutation6
    mixedMoment B raw1397step0 raw1397step0Labels = mixedMoment B raw1397step1 raw1397step1Labels := by
      have ha : raw1397step1 = -raw1397step0 := by apply Matrix.ext; change ∀ i j, raw1397step1 i j = -(raw1397step0 i j); unfold raw1397step1 raw1397step0; decide +kernel
      have hl : raw1397step1Labels = raw1397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1397step1 raw1397step1Labels = mixedMoment B raw1397step2 raw1397step2Labels := by
      have ha : raw1397step2 = raw1397step1 := by apply Matrix.ext; unfold raw1397step2 raw1397step1; decide +kernel
      have hl : raw1397step1Labels = labelEmbedding1 ∘ raw1397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1397step1 raw1397step1Labels raw1397step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

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

theorem canonical1443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1443 raw1443Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw1443 raw1443Labels = mixedMoment B raw1443step0 raw1443step0Labels := by
      have ha : raw1443step0 = (fun i j => raw1443 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1443step0 raw1443; decide +kernel
      have hl : raw1443step0Labels = raw1443Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1443 raw1443Labels permutation8 permutation4
    mixedMoment B raw1443step0 raw1443step0Labels = mixedMoment B raw1443step1 raw1443step1Labels := by
      have ha : raw1443step1 = raw1443step0 := by apply Matrix.ext; unfold raw1443step1 raw1443step0; decide +kernel
      have hl : raw1443step0Labels = labelEmbedding7 ∘ raw1443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1443step0 raw1443step0Labels raw1443step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

theorem canonical1444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1444 raw1444Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw1444 raw1444Labels = mixedMoment B raw1444step0 raw1444step0Labels := by
      have ha : raw1444step0 = (fun i j => raw1444 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1444step0 raw1444; decide +kernel
      have hl : raw1444step0Labels = raw1444Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1444 raw1444Labels permutation8 permutation4
    _ = mixedMoment B node1294 node1294Labels := by rfl

theorem canonical1445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1445 raw1445Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw1445 raw1445Labels = mixedMoment B raw1445step0 raw1445step0Labels := by
      have ha : raw1445step0 = (fun i j => raw1445 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1445step0 raw1445; decide +kernel
      have hl : raw1445step0Labels = raw1445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1445 raw1445Labels permutation8 permutation6
    mixedMoment B raw1445step0 raw1445step0Labels = mixedMoment B raw1445step1 raw1445step1Labels := by
      have ha : raw1445step1 = -raw1445step0 := by apply Matrix.ext; change ∀ i j, raw1445step1 i j = -(raw1445step0 i j); unfold raw1445step1 raw1445step0; decide +kernel
      have hl : raw1445step1Labels = raw1445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1445step1 raw1445step1Labels = mixedMoment B raw1445step2 raw1445step2Labels := by
      have ha : raw1445step2 = raw1445step1 := by apply Matrix.ext; unfold raw1445step2 raw1445step1; decide +kernel
      have hl : raw1445step1Labels = labelEmbedding1 ∘ raw1445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1445step1 raw1445step1Labels raw1445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18318 raw18318Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw18318 raw18318Labels = mixedMoment B raw18318step0 raw18318step0Labels := by
      have hz : ∀ j, raw18318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18318step0 = (fun i j => raw18318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18318step0 raw18318; decide +kernel
      have hl : raw18318step0Labels = raw18318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18318 raw18318Labels permutation346 hz
    mixedMoment B raw18318step0 raw18318step0Labels = mixedMoment B raw18318step1 raw18318step1Labels := by
      have hz : ∀ j, raw18318step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18318step1 = (fun i j => raw18318step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18318step1 raw18318step0; decide +kernel
      have hl : raw18318step1Labels = raw18318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18318step0 raw18318step0Labels permutation56 hz
    _ = mixedMoment B node5274 node5274Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20651 raw20651Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw20651 raw20651Labels = mixedMoment B raw20651step0 raw20651step0Labels := by
      have hz : ∀ j, raw20651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20651step0 = (fun i j => raw20651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20651step0 raw20651; decide +kernel
      have hl : raw20651step0Labels = raw20651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20651 raw20651Labels permutation346 hz
    mixedMoment B raw20651step0 raw20651step0Labels = mixedMoment B raw20651step1 raw20651step1Labels := by
      have ha : raw20651step1 = (fun i j => raw20651step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20651step1 raw20651step0; decide +kernel
      have hl : raw20651step1Labels = raw20651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20651step0 raw20651step0Labels permutation40 permutation3
    mixedMoment B raw20651step1 raw20651step1Labels = mixedMoment B raw20651step2 raw20651step2Labels := by
      have ha : raw20651step2 = raw20651step1 := by apply Matrix.ext; unfold raw20651step2 raw20651step1; decide +kernel
      have hl : raw20651step1Labels = labelEmbedding6 ∘ raw20651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20651step1 raw20651step1Labels raw20651step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4153 node4153Labels := by rfl

theorem canonical20652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20652 raw20652Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw20652 raw20652Labels = mixedMoment B raw20652step0 raw20652step0Labels := by
      have ha : raw20652step0 = (fun i j => raw20652 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20652step0 raw20652; decide +kernel
      have hl : raw20652step0Labels = raw20652Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20652 raw20652Labels permutation184 permutation3
    mixedMoment B raw20652step0 raw20652step0Labels = mixedMoment B raw20652step1 raw20652step1Labels := by
      have ha : raw20652step1 = raw20652step0 := by apply Matrix.ext; unfold raw20652step1 raw20652step0; decide +kernel
      have hl : raw20652step0Labels = labelEmbedding6 ∘ raw20652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20652step0 raw20652step0Labels raw20652step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4528 node4528Labels := by rfl

theorem canonical20653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20653 raw20653Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20653 raw20653Labels = mixedMoment B raw20653step0 raw20653step0Labels := by
      have hz : ∀ j, raw20653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20653step0 = (fun i j => raw20653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20653step0 raw20653; decide +kernel
      have hl : raw20653step0Labels = raw20653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20653 raw20653Labels permutation346 hz
    mixedMoment B raw20653step0 raw20653step0Labels = mixedMoment B raw20653step1 raw20653step1Labels := by
      have ha : raw20653step1 = (fun i j => raw20653step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20653step1 raw20653step0; decide +kernel
      have hl : raw20653step1Labels = raw20653step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20653step0 raw20653step0Labels permutation38 permutation2
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20654 raw20654Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20654 raw20654Labels = mixedMoment B raw20654step0 raw20654step0Labels := by
      have hz : ∀ j, raw20654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20654step0 = (fun i j => raw20654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20654step0 raw20654; decide +kernel
      have hl : raw20654step0Labels = raw20654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20654 raw20654Labels permutation346 hz
    mixedMoment B raw20654step0 raw20654step0Labels = mixedMoment B raw20654step1 raw20654step1Labels := by
      have ha : raw20654step1 = (fun i j => raw20654step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20654step1 raw20654step0; decide +kernel
      have hl : raw20654step1Labels = raw20654step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20654step0 raw20654step0Labels permutation40 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical20655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20655 raw20655Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw20655 raw20655Labels = mixedMoment B raw20655step0 raw20655step0Labels := by
      have hz : ∀ j, raw20655 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20655step0 = (fun i j => raw20655 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20655step0 raw20655; decide +kernel
      have hl : raw20655step0Labels = raw20655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20655 raw20655Labels permutation265 hz
    mixedMoment B raw20655step0 raw20655step0Labels = mixedMoment B raw20655step1 raw20655step1Labels := by
      have ha : raw20655step1 = (fun i j => raw20655step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20655step1 raw20655step0; decide +kernel
      have hl : raw20655step1Labels = raw20655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20655step0 raw20655step0Labels permutation40 permutation3
    mixedMoment B raw20655step1 raw20655step1Labels = mixedMoment B raw20655step2 raw20655step2Labels := by
      have ha : raw20655step2 = raw20655step1 := by apply Matrix.ext; unfold raw20655step2 raw20655step1; decide +kernel
      have hl : raw20655step1Labels = labelEmbedding6 ∘ raw20655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20655step1 raw20655step1Labels raw20655step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4153 node4153Labels := by rfl

theorem canonical20656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20656 raw20656Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw20656 raw20656Labels = mixedMoment B raw20656step0 raw20656step0Labels := by
      have ha : raw20656step0 = (fun i j => raw20656 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20656step0 raw20656; decide +kernel
      have hl : raw20656step0Labels = raw20656Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20656 raw20656Labels permutation160 permutation3
    mixedMoment B raw20656step0 raw20656step0Labels = mixedMoment B raw20656step1 raw20656step1Labels := by
      have ha : raw20656step1 = raw20656step0 := by apply Matrix.ext; unfold raw20656step1 raw20656step0; decide +kernel
      have hl : raw20656step0Labels = labelEmbedding6 ∘ raw20656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20656step0 raw20656step0Labels raw20656step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4528 node4528Labels := by rfl

theorem canonical20657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20657 raw20657Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20657 raw20657Labels = mixedMoment B raw20657step0 raw20657step0Labels := by
      have hz : ∀ j, raw20657 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20657step0 = (fun i j => raw20657 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20657step0 raw20657; decide +kernel
      have hl : raw20657step0Labels = raw20657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20657 raw20657Labels permutation265 hz
    mixedMoment B raw20657step0 raw20657step0Labels = mixedMoment B raw20657step1 raw20657step1Labels := by
      have ha : raw20657step1 = (fun i j => raw20657step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20657step1 raw20657step0; decide +kernel
      have hl : raw20657step1Labels = raw20657step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20657step0 raw20657step0Labels permutation38 permutation2
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20658 raw20658Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20658 raw20658Labels = mixedMoment B raw20658step0 raw20658step0Labels := by
      have hz : ∀ j, raw20658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20658step0 = (fun i j => raw20658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20658step0 raw20658; decide +kernel
      have hl : raw20658step0Labels = raw20658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20658 raw20658Labels permutation265 hz
    mixedMoment B raw20658step0 raw20658step0Labels = mixedMoment B raw20658step1 raw20658step1Labels := by
      have ha : raw20658step1 = (fun i j => raw20658step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20658step1 raw20658step0; decide +kernel
      have hl : raw20658step1Labels = raw20658step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20658step0 raw20658step0Labels permutation40 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

theorem canonical20659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20659 raw20659Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw20659 raw20659Labels = mixedMoment B raw20659step0 raw20659step0Labels := by
      have hz : ∀ j, raw20659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20659step0 = (fun i j => raw20659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20659step0 raw20659; decide +kernel
      have hl : raw20659step0Labels = raw20659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20659 raw20659Labels permutation346 hz
    mixedMoment B raw20659step0 raw20659step0Labels = mixedMoment B raw20659step1 raw20659step1Labels := by
      have hz : ∀ j, raw20659step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20659step1 = (fun i j => raw20659step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20659step1 raw20659step0; decide +kernel
      have hl : raw20659step1Labels = raw20659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20659step0 raw20659step0Labels permutation56 hz
    mixedMoment B raw20659step1 raw20659step1Labels = mixedMoment B raw20659step2 raw20659step2Labels := by
      have ha : raw20659step2 = (fun i j => raw20659step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20659step2 raw20659step1; decide +kernel
      have hl : raw20659step2Labels = raw20659step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20659step1 raw20659step1Labels permutation10 permutation3
    mixedMoment B raw20659step2 raw20659step2Labels = mixedMoment B raw20659step3 raw20659step3Labels := by
      have ha : raw20659step3 = raw20659step2 := by apply Matrix.ext; unfold raw20659step3 raw20659step2; decide +kernel
      have hl : raw20659step2Labels = labelEmbedding6 ∘ raw20659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20659step2 raw20659step2Labels raw20659step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4178 node4178Labels := by rfl

theorem canonical20660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20660 raw20660Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw20660 raw20660Labels = mixedMoment B raw20660step0 raw20660step0Labels := by
      have hz : ∀ j, raw20660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20660step0 = (fun i j => raw20660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20660step0 raw20660; decide +kernel
      have hl : raw20660step0Labels = raw20660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20660 raw20660Labels permutation346 hz
    mixedMoment B raw20660step0 raw20660step0Labels = mixedMoment B raw20660step1 raw20660step1Labels := by
      have ha : raw20660step1 = (fun i j => raw20660step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20660step1 raw20660step0; decide +kernel
      have hl : raw20660step1Labels = raw20660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20660step0 raw20660step0Labels permutation34 permutation3
    mixedMoment B raw20660step1 raw20660step1Labels = mixedMoment B raw20660step2 raw20660step2Labels := by
      have ha : raw20660step2 = raw20660step1 := by apply Matrix.ext; unfold raw20660step2 raw20660step1; decide +kernel
      have hl : raw20660step1Labels = labelEmbedding6 ∘ raw20660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20660step1 raw20660step1Labels raw20660step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

theorem canonical20661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20661 raw20661Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw20661 raw20661Labels = mixedMoment B raw20661step0 raw20661step0Labels := by
      have hz : ∀ j, raw20661 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20661step0 = (fun i j => raw20661 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20661step0 raw20661; decide +kernel
      have hl : raw20661step0Labels = raw20661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20661 raw20661Labels permutation265 hz
    mixedMoment B raw20661step0 raw20661step0Labels = mixedMoment B raw20661step1 raw20661step1Labels := by
      have ha : raw20661step1 = (fun i j => raw20661step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20661step1 raw20661step0; decide +kernel
      have hl : raw20661step1Labels = raw20661step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20661step0 raw20661step0Labels permutation34 permutation3
    mixedMoment B raw20661step1 raw20661step1Labels = mixedMoment B raw20661step2 raw20661step2Labels := by
      have ha : raw20661step2 = raw20661step1 := by apply Matrix.ext; unfold raw20661step2 raw20661step1; decide +kernel
      have hl : raw20661step1Labels = labelEmbedding6 ∘ raw20661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20661step1 raw20661step1Labels raw20661step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

theorem canonical20662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20662 raw20662Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw20662 raw20662Labels = mixedMoment B raw20662step0 raw20662step0Labels := by
      have hz : ∀ j, raw20662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20662step0 = (fun i j => raw20662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20662step0 raw20662; decide +kernel
      have hl : raw20662step0Labels = raw20662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20662 raw20662Labels permutation346 hz
    mixedMoment B raw20662step0 raw20662step0Labels = mixedMoment B raw20662step1 raw20662step1Labels := by
      have hz : ∀ j, raw20662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20662step1 = (fun i j => raw20662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20662step1 raw20662step0; decide +kernel
      have hl : raw20662step1Labels = raw20662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20662step0 raw20662step0Labels permutation56 hz
    mixedMoment B raw20662step1 raw20662step1Labels = mixedMoment B raw20662step2 raw20662step2Labels := by
      have ha : raw20662step2 = (fun i j => raw20662step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20662step2 raw20662step1; decide +kernel
      have hl : raw20662step2Labels = raw20662step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20662step1 raw20662step1Labels permutation10 permutation3
    mixedMoment B raw20662step2 raw20662step2Labels = mixedMoment B raw20662step3 raw20662step3Labels := by
      have ha : raw20662step3 = raw20662step2 := by apply Matrix.ext; unfold raw20662step3 raw20662step2; decide +kernel
      have hl : raw20662step2Labels = labelEmbedding6 ∘ raw20662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20662step2 raw20662step2Labels raw20662step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

theorem canonical20663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20663 raw20663Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw20663 raw20663Labels = mixedMoment B raw20663step0 raw20663step0Labels := by
      have hz : ∀ j, raw20663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20663step0 = (fun i j => raw20663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20663step0 raw20663; decide +kernel
      have hl : raw20663step0Labels = raw20663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20663 raw20663Labels permutation346 hz
    mixedMoment B raw20663step0 raw20663step0Labels = mixedMoment B raw20663step1 raw20663step1Labels := by
      have hz : ∀ j, raw20663step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20663step1 = (fun i j => raw20663step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20663step1 raw20663step0; decide +kernel
      have hl : raw20663step1Labels = raw20663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20663step0 raw20663step0Labels permutation56 hz
    mixedMoment B raw20663step1 raw20663step1Labels = mixedMoment B raw20663step2 raw20663step2Labels := by
      have ha : raw20663step2 = (fun i j => raw20663step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20663step2 raw20663step1; decide +kernel
      have hl : raw20663step2Labels = raw20663step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20663step1 raw20663step1Labels permutation8 permutation3
    mixedMoment B raw20663step2 raw20663step2Labels = mixedMoment B raw20663step3 raw20663step3Labels := by
      have ha : raw20663step3 = raw20663step2 := by apply Matrix.ext; unfold raw20663step3 raw20663step2; decide +kernel
      have hl : raw20663step2Labels = labelEmbedding6 ∘ raw20663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20663step2 raw20663step2Labels raw20663step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4161 node4161Labels := by rfl

theorem canonical20664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20664 raw20664Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw20664 raw20664Labels = mixedMoment B raw20664step0 raw20664step0Labels := by
      have hz : ∀ j, raw20664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20664step0 = (fun i j => raw20664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20664step0 raw20664; decide +kernel
      have hl : raw20664step0Labels = raw20664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20664 raw20664Labels permutation346 hz
    mixedMoment B raw20664step0 raw20664step0Labels = mixedMoment B raw20664step1 raw20664step1Labels := by
      have ha : raw20664step1 = (fun i j => raw20664step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20664step1 raw20664step0; decide +kernel
      have hl : raw20664step1Labels = raw20664step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20664step0 raw20664step0Labels permutation32 permutation3
    mixedMoment B raw20664step1 raw20664step1Labels = mixedMoment B raw20664step2 raw20664step2Labels := by
      have ha : raw20664step2 = raw20664step1 := by apply Matrix.ext; unfold raw20664step2 raw20664step1; decide +kernel
      have hl : raw20664step1Labels = labelEmbedding6 ∘ raw20664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20664step1 raw20664step1Labels raw20664step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical20665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20665 raw20665Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw20665 raw20665Labels = mixedMoment B raw20665step0 raw20665step0Labels := by
      have hz : ∀ j, raw20665 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20665step0 = (fun i j => raw20665 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20665step0 raw20665; decide +kernel
      have hl : raw20665step0Labels = raw20665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20665 raw20665Labels permutation265 hz
    mixedMoment B raw20665step0 raw20665step0Labels = mixedMoment B raw20665step1 raw20665step1Labels := by
      have ha : raw20665step1 = (fun i j => raw20665step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20665step1 raw20665step0; decide +kernel
      have hl : raw20665step1Labels = raw20665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20665step0 raw20665step0Labels permutation32 permutation3
    mixedMoment B raw20665step1 raw20665step1Labels = mixedMoment B raw20665step2 raw20665step2Labels := by
      have ha : raw20665step2 = raw20665step1 := by apply Matrix.ext; unfold raw20665step2 raw20665step1; decide +kernel
      have hl : raw20665step1Labels = labelEmbedding6 ∘ raw20665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20665step1 raw20665step1Labels raw20665step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical20666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20666 raw20666Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw20666 raw20666Labels = mixedMoment B raw20666step0 raw20666step0Labels := by
      have hz : ∀ j, raw20666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20666step0 = (fun i j => raw20666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20666step0 raw20666; decide +kernel
      have hl : raw20666step0Labels = raw20666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20666 raw20666Labels permutation346 hz
    mixedMoment B raw20666step0 raw20666step0Labels = mixedMoment B raw20666step1 raw20666step1Labels := by
      have hz : ∀ j, raw20666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20666step1 = (fun i j => raw20666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20666step1 raw20666step0; decide +kernel
      have hl : raw20666step1Labels = raw20666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20666step0 raw20666step0Labels permutation56 hz
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical20667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20667 raw20667Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw20667 raw20667Labels = mixedMoment B raw20667step0 raw20667step0Labels := by
      have hz : ∀ j, raw20667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20667step0 = (fun i j => raw20667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20667step0 raw20667; decide +kernel
      have hl : raw20667step0Labels = raw20667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20667 raw20667Labels permutation346 hz
    mixedMoment B raw20667step0 raw20667step0Labels = mixedMoment B raw20667step1 raw20667step1Labels := by
      have hz : ∀ j, raw20667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20667step1 = (fun i j => raw20667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20667step1 raw20667step0; decide +kernel
      have hl : raw20667step1Labels = raw20667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20667step0 raw20667step0Labels permutation56 hz
    mixedMoment B raw20667step1 raw20667step1Labels = mixedMoment B raw20667step2 raw20667step2Labels := by
      have ha : raw20667step2 = (fun i j => raw20667step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20667step2 raw20667step1; decide +kernel
      have hl : raw20667step2Labels = raw20667step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20667step1 raw20667step1Labels permutation8 permutation3
    mixedMoment B raw20667step2 raw20667step2Labels = mixedMoment B raw20667step3 raw20667step3Labels := by
      have ha : raw20667step3 = raw20667step2 := by apply Matrix.ext; unfold raw20667step3 raw20667step2; decide +kernel
      have hl : raw20667step2Labels = labelEmbedding6 ∘ raw20667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20667step2 raw20667step2Labels raw20667step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4156 node4156Labels := by rfl

theorem canonical20668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20668 raw20668Labels = mixedMoment B node4531 node4531Labels := by
  calc
    mixedMoment B raw20668 raw20668Labels = mixedMoment B raw20668step0 raw20668step0Labels := by
      have hz : ∀ j, raw20668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20668step0 = (fun i j => raw20668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20668step0 raw20668; decide +kernel
      have hl : raw20668step0Labels = raw20668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20668 raw20668Labels permutation346 hz
    mixedMoment B raw20668step0 raw20668step0Labels = mixedMoment B raw20668step1 raw20668step1Labels := by
      have ha : raw20668step1 = (fun i j => raw20668step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20668step1 raw20668step0; decide +kernel
      have hl : raw20668step1Labels = raw20668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20668step0 raw20668step0Labels permutation151 permutation2
    mixedMoment B raw20668step1 raw20668step1Labels = mixedMoment B raw20668step2 raw20668step2Labels := by
      have ha : raw20668step2 = -raw20668step1 := by apply Matrix.ext; change ∀ i j, raw20668step2 i j = -(raw20668step1 i j); unfold raw20668step2 raw20668step1; decide +kernel
      have hl : raw20668step2Labels = raw20668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4531 node4531Labels := by rfl

theorem canonical20669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20669 raw20669Labels = mixedMoment B node4531 node4531Labels := by
  calc
    mixedMoment B raw20669 raw20669Labels = mixedMoment B raw20669step0 raw20669step0Labels := by
      have hz : ∀ j, raw20669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20669step0 = (fun i j => raw20669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20669step0 raw20669; decide +kernel
      have hl : raw20669step0Labels = raw20669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20669 raw20669Labels permutation265 hz
    mixedMoment B raw20669step0 raw20669step0Labels = mixedMoment B raw20669step1 raw20669step1Labels := by
      have ha : raw20669step1 = (fun i j => raw20669step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20669step1 raw20669step0; decide +kernel
      have hl : raw20669step1Labels = raw20669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20669step0 raw20669step0Labels permutation151 permutation2
    mixedMoment B raw20669step1 raw20669step1Labels = mixedMoment B raw20669step2 raw20669step2Labels := by
      have ha : raw20669step2 = -raw20669step1 := by apply Matrix.ext; change ∀ i j, raw20669step2 i j = -(raw20669step1 i j); unfold raw20669step2 raw20669step1; decide +kernel
      have hl : raw20669step2Labels = raw20669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4531 node4531Labels := by rfl

theorem canonical20670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20670 raw20670Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw20670 raw20670Labels = mixedMoment B raw20670step0 raw20670step0Labels := by
      have hz : ∀ j, raw20670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20670step0 = (fun i j => raw20670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20670step0 raw20670; decide +kernel
      have hl : raw20670step0Labels = raw20670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20670 raw20670Labels permutation346 hz
    mixedMoment B raw20670step0 raw20670step0Labels = mixedMoment B raw20670step1 raw20670step1Labels := by
      have hz : ∀ j, raw20670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20670step1 = (fun i j => raw20670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20670step1 raw20670step0; decide +kernel
      have hl : raw20670step1Labels = raw20670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20670step0 raw20670step0Labels permutation56 hz
    _ = mixedMoment B node4555 node4555Labels := by rfl

theorem canonical20671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20671 raw20671Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw20671 raw20671Labels = mixedMoment B raw20671step0 raw20671step0Labels := by
      have hz : ∀ j, raw20671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20671step0 = (fun i j => raw20671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20671step0 raw20671; decide +kernel
      have hl : raw20671step0Labels = raw20671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20671 raw20671Labels permutation346 hz
    mixedMoment B raw20671step0 raw20671step0Labels = mixedMoment B raw20671step1 raw20671step1Labels := by
      have hz : ∀ j, raw20671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20671step1 = (fun i j => raw20671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20671step1 raw20671step0; decide +kernel
      have hl : raw20671step1Labels = raw20671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20671step0 raw20671step0Labels permutation56 hz
    _ = mixedMoment B node4594 node4594Labels := by rfl

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

theorem canonical2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2277 raw2277Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw2277 raw2277Labels = mixedMoment B raw2277step0 raw2277step0Labels := by
      have ha : raw2277step0 = (fun i j => raw2277 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2277step0 raw2277; decide +kernel
      have hl : raw2277step0Labels = raw2277Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2277 raw2277Labels permutation8 permutation4
    mixedMoment B raw2277step0 raw2277step0Labels = mixedMoment B raw2277step1 raw2277step1Labels := by
      have ha : raw2277step1 = raw2277step0 := by apply Matrix.ext; unfold raw2277step1 raw2277step0; decide +kernel
      have hl : raw2277step0Labels = labelEmbedding7 ∘ raw2277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2277step0 raw2277step0Labels raw2277step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2278 raw2278Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw2278 raw2278Labels = mixedMoment B raw2278step0 raw2278step0Labels := by
      have ha : raw2278step0 = (fun i j => raw2278 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2278step0 raw2278; decide +kernel
      have hl : raw2278step0Labels = raw2278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2278 raw2278Labels permutation8 permutation4
    _ = mixedMoment B node2726 node2726Labels := by rfl

theorem canonical2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2279 raw2279Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw2279 raw2279Labels = mixedMoment B raw2279step0 raw2279step0Labels := by
      have ha : raw2279step0 = (fun i j => raw2279 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2279step0 raw2279; decide +kernel
      have hl : raw2279step0Labels = raw2279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2279 raw2279Labels permutation31 permutation6
    mixedMoment B raw2279step0 raw2279step0Labels = mixedMoment B raw2279step1 raw2279step1Labels := by
      have ha : raw2279step1 = raw2279step0 := by apply Matrix.ext; unfold raw2279step1 raw2279step0; decide +kernel
      have hl : raw2279step0Labels = labelEmbedding1 ∘ raw2279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2279step0 raw2279step0Labels raw2279step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10544 raw10544Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw10544 raw10544Labels = mixedMoment B raw10544step0 raw10544step0Labels := by
      have hz : ∀ j, raw10544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10544step0 = (fun i j => raw10544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10544step0 raw10544; decide +kernel
      have hl : raw10544step0Labels = raw10544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10544 raw10544Labels permutation346 hz
    mixedMoment B raw10544step0 raw10544step0Labels = mixedMoment B raw10544step1 raw10544step1Labels := by
      have ha : raw10544step1 = (fun i j => raw10544step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10544step1 raw10544step0; decide +kernel
      have hl : raw10544step1Labels = raw10544step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10544step0 raw10544step0Labels permutation38 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical10549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10549 raw10549Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw10549 raw10549Labels = mixedMoment B raw10549step0 raw10549step0Labels := by
      have hz : ∀ j, raw10549 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10549step0 = (fun i j => raw10549 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10549step0 raw10549; decide +kernel
      have hl : raw10549step0Labels = raw10549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10549 raw10549Labels permutation265 hz
    mixedMoment B raw10549step0 raw10549step0Labels = mixedMoment B raw10549step1 raw10549step1Labels := by
      have ha : raw10549step1 = (fun i j => raw10549step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10549step1 raw10549step0; decide +kernel
      have hl : raw10549step1Labels = raw10549step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10549step0 raw10549step0Labels permutation38 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical10554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10554 raw10554Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw10554 raw10554Labels = mixedMoment B raw10554step0 raw10554step0Labels := by
      have hz : ∀ j, raw10554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10554step0 = (fun i j => raw10554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10554step0 raw10554; decide +kernel
      have hl : raw10554step0Labels = raw10554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10554 raw10554Labels permutation346 hz
    mixedMoment B raw10554step0 raw10554step0Labels = mixedMoment B raw10554step1 raw10554step1Labels := by
      have hz : ∀ j, raw10554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10554step1 = (fun i j => raw10554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10554step1 raw10554step0; decide +kernel
      have hl : raw10554step1Labels = raw10554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10554step0 raw10554step0Labels permutation56 hz
    _ = mixedMoment B node4619 node4619Labels := by rfl

theorem canonical10559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10559 raw10559Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw10559 raw10559Labels = mixedMoment B raw10559step0 raw10559step0Labels := by
      have hz : ∀ j, raw10559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10559step0 = (fun i j => raw10559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10559step0 raw10559; decide +kernel
      have hl : raw10559step0Labels = raw10559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10559 raw10559Labels permutation346 hz
    mixedMoment B raw10559step0 raw10559step0Labels = mixedMoment B raw10559step1 raw10559step1Labels := by
      have hz : ∀ j, raw10559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10559step1 = (fun i j => raw10559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10559step1 raw10559step0; decide +kernel
      have hl : raw10559step1Labels = raw10559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10559step0 raw10559step0Labels permutation56 hz
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical10565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10565 raw10565Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw10565 raw10565Labels = mixedMoment B raw10565step0 raw10565step0Labels := by
      have hz : ∀ j, raw10565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10565step0 = (fun i j => raw10565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10565step0 raw10565; decide +kernel
      have hl : raw10565step0Labels = raw10565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10565 raw10565Labels permutation346 hz
    mixedMoment B raw10565step0 raw10565step0Labels = mixedMoment B raw10565step1 raw10565step1Labels := by
      have ha : raw10565step1 = (fun i j => raw10565step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10565step1 raw10565step0; decide +kernel
      have hl : raw10565step1Labels = raw10565step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10565step0 raw10565step0Labels permutation151 permutation2
    mixedMoment B raw10565step1 raw10565step1Labels = mixedMoment B raw10565step2 raw10565step2Labels := by
      have ha : raw10565step2 = -raw10565step1 := by apply Matrix.ext; change ∀ i j, raw10565step2 i j = -(raw10565step1 i j); unfold raw10565step2 raw10565step1; decide +kernel
      have hl : raw10565step2Labels = raw10565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical10566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10566 raw10566Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw10566 raw10566Labels = mixedMoment B raw10566step0 raw10566step0Labels := by
      have hz : ∀ j, raw10566 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10566step0 = (fun i j => raw10566 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10566step0 raw10566; decide +kernel
      have hl : raw10566step0Labels = raw10566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10566 raw10566Labels permutation265 hz
    mixedMoment B raw10566step0 raw10566step0Labels = mixedMoment B raw10566step1 raw10566step1Labels := by
      have ha : raw10566step1 = (fun i j => raw10566step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10566step1 raw10566step0; decide +kernel
      have hl : raw10566step1Labels = raw10566step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10566step0 raw10566step0Labels permutation151 permutation2
    mixedMoment B raw10566step1 raw10566step1Labels = mixedMoment B raw10566step2 raw10566step2Labels := by
      have ha : raw10566step2 = -raw10566step1 := by apply Matrix.ext; change ∀ i j, raw10566step2 i j = -(raw10566step1 i j); unfold raw10566step2 raw10566step1; decide +kernel
      have hl : raw10566step2Labels = raw10566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical10567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10567 raw10567Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw10567 raw10567Labels = mixedMoment B raw10567step0 raw10567step0Labels := by
      have hz : ∀ j, raw10567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10567step0 = (fun i j => raw10567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10567step0 raw10567; decide +kernel
      have hl : raw10567step0Labels = raw10567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10567 raw10567Labels permutation346 hz
    mixedMoment B raw10567step0 raw10567step0Labels = mixedMoment B raw10567step1 raw10567step1Labels := by
      have hz : ∀ j, raw10567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10567step1 = (fun i j => raw10567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10567step1 raw10567step0; decide +kernel
      have hl : raw10567step1Labels = raw10567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10567step0 raw10567step0Labels permutation56 hz
    _ = mixedMoment B node5107 node5107Labels := by rfl

theorem canonical10568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10568 raw10568Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw10568 raw10568Labels = mixedMoment B raw10568step0 raw10568step0Labels := by
      have hz : ∀ j, raw10568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10568step0 = (fun i j => raw10568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10568step0 raw10568; decide +kernel
      have hl : raw10568step0Labels = raw10568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10568 raw10568Labels permutation346 hz
    mixedMoment B raw10568step0 raw10568step0Labels = mixedMoment B raw10568step1 raw10568step1Labels := by
      have hz : ∀ j, raw10568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10568step1 = (fun i j => raw10568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10568step1 raw10568step0; decide +kernel
      have hl : raw10568step1Labels = raw10568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10568step0 raw10568step0Labels permutation56 hz
    _ = mixedMoment B node5261 node5261Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4546 node4546Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1131 node1131Labels + mixedMoment B node3264 node3264Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1371 singletonSmall4546
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4546) = raw1371Labels := by decide +kernel
  rw [hl, canonical1371 B hB] at h
  have hc0 : mixedMoment B raw1371 (Fin.cases (0 : Fin 2) singletonSmall4546) =
      mixedMoment B node1131 node1131Labels := by
    have ha : raw1371 = raw1372 := by apply Matrix.ext; unfold raw1371 raw1372; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4546 = raw1372Labels := by decide +kernel
    rw [ha, hj, canonical1372 B hB]
  have hc1 : mixedMoment B raw1371 (Fin.cases (1 : Fin 2) singletonSmall4546) =
      mixedMoment B node3264 node3264Labels := by
    have ha : raw1371 = raw1373 := by apply Matrix.ext; unfold raw1371 raw1373; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4546 = raw1373Labels := by decide +kernel
    rw [ha, hj, canonical1373 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4555 node4555Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1140 node1140Labels + mixedMoment B node3275 node3275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1389 singletonSmall4555
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4555) = raw1389Labels := by decide +kernel
  rw [hl, canonical1389 B hB] at h
  have hc0 : mixedMoment B raw1389 (Fin.cases (0 : Fin 2) singletonSmall4555) =
      mixedMoment B node1140 node1140Labels := by
    have ha : raw1389 = raw1390 := by apply Matrix.ext; unfold raw1389 raw1390; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4555 = raw1390Labels := by decide +kernel
    rw [ha, hj, canonical1390 B hB]
  have hc1 : mixedMoment B raw1389 (Fin.cases (1 : Fin 2) singletonSmall4555) =
      mixedMoment B node3275 node3275Labels := by
    have ha : raw1389 = raw1391 := by apply Matrix.ext; unfold raw1389 raw1391; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4555 = raw1391Labels := by decide +kernel
    rw [ha, hj, canonical1391 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4558 node4558Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1144 node1144Labels + mixedMoment B node3276 node3276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1395 singletonSmall4558
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4558) = raw1395Labels := by decide +kernel
  rw [hl, canonical1395 B hB] at h
  have hc0 : mixedMoment B raw1395 (Fin.cases (0 : Fin 2) singletonSmall4558) =
      mixedMoment B node1144 node1144Labels := by
    have ha : raw1395 = raw1396 := by apply Matrix.ext; unfold raw1395 raw1396; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4558 = raw1396Labels := by decide +kernel
    rw [ha, hj, canonical1396 B hB]
  have hc1 : mixedMoment B raw1395 (Fin.cases (1 : Fin 2) singletonSmall4558) =
      mixedMoment B node3276 node3276Labels := by
    have ha : raw1395 = raw1397 := by apply Matrix.ext; unfold raw1395 raw1397; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4558 = raw1397Labels := by decide +kernel
    rw [ha, hj, canonical1397 B hB]
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

theorem singleton4619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4619 node4619Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1294 node1294Labels + mixedMoment B node3305 node3305Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1443 singletonSmall4619
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4619) = raw1443Labels := by decide +kernel
  rw [hl, canonical1443 B hB] at h
  have hc0 : mixedMoment B raw1443 (Fin.cases (0 : Fin 2) singletonSmall4619) =
      mixedMoment B node1294 node1294Labels := by
    have ha : raw1443 = raw1444 := by apply Matrix.ext; unfold raw1443 raw1444; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4619 = raw1444Labels := by decide +kernel
    rw [ha, hj, canonical1444 B hB]
  have hc1 : mixedMoment B raw1443 (Fin.cases (1 : Fin 2) singletonSmall4619) =
      mixedMoment B node3305 node3305Labels := by
    have ha : raw1443 = raw1445 := by apply Matrix.ext; unfold raw1443 raw1445; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4619 = raw1445Labels := by decide +kernel
    rw [ha, hj, canonical1445 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5261 node5261Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2726 node2726Labels + mixedMoment B node3545 node3545Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2277 singletonSmall5261
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5261) = raw2277Labels := by decide +kernel
  rw [hl, canonical2277 B hB] at h
  have hc0 : mixedMoment B raw2277 (Fin.cases (0 : Fin 2) singletonSmall5261) =
      mixedMoment B node2726 node2726Labels := by
    have ha : raw2277 = raw2278 := by apply Matrix.ext; unfold raw2277 raw2278; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5261 = raw2278Labels := by decide +kernel
    rw [ha, hj, canonical2278 B hB]
  have hc1 : mixedMoment B raw2277 (Fin.cases (1 : Fin 2) singletonSmall5261) =
      mixedMoment B node3545 node3545Labels := by
    have ha : raw2277 = raw2279 := by apply Matrix.ext; unfold raw2277 raw2279; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5261 = raw2279Labels := by decide +kernel
    rw [ha, hj, canonical2279 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1131 node1131Labels = Sparse.eval nodeValue1131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1131) = mixedMoment B node1131 node1131Labels := rfl
  simpa [nodeValue1131, Sparse.eval] using hc.symm

theorem sound1140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1140 node1140Labels = Sparse.eval nodeValue1140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1140) = mixedMoment B node1140 node1140Labels := rfl
  simpa [nodeValue1140, Sparse.eval] using hc.symm

theorem sound1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1144 node1144Labels = Sparse.eval nodeValue1144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1144) = mixedMoment B node1144 node1144Labels := rfl
  simpa [nodeValue1144, Sparse.eval] using hc.symm

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

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2726 node2726Labels = Sparse.eval nodeValue2726 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2726) = mixedMoment B node2726 node2726Labels := rfl
  simpa [nodeValue2726, Sparse.eval] using hc.symm

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

theorem sound3264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3264 node3264Labels = Sparse.eval nodeValue3264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3264) = mixedMoment B node3264 node3264Labels := rfl
  simpa [nodeValue3264, Sparse.eval] using hc.symm

theorem sound3275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3275 node3275Labels = Sparse.eval nodeValue3275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3275) = mixedMoment B node3275 node3275Labels := rfl
  simpa [nodeValue3275, Sparse.eval] using hc.symm

theorem sound3276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3276 node3276Labels = Sparse.eval nodeValue3276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3276) = mixedMoment B node3276 node3276Labels := rfl
  simpa [nodeValue3276, Sparse.eval] using hc.symm

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

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

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

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

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

theorem sound4153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4153 node4153Labels = Sparse.eval nodeValue4153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4153) = mixedMoment B node4153 node4153Labels := rfl
  simpa [nodeValue4153, Sparse.eval] using hc.symm

theorem sound4156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4156 node4156Labels = Sparse.eval nodeValue4156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4156) = mixedMoment B node4156 node4156Labels := rfl
  simpa [nodeValue4156, Sparse.eval] using hc.symm

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

theorem sound4161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4161 node4161Labels = Sparse.eval nodeValue4161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4161) = mixedMoment B node4161 node4161Labels := rfl
  simpa [nodeValue4161, Sparse.eval] using hc.symm

theorem sound4178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4178 node4178Labels = Sparse.eval nodeValue4178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4178) = mixedMoment B node4178 node4178Labels := rfl
  simpa [nodeValue4178, Sparse.eval] using hc.symm

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

theorem sound4528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4528 node4528Labels = Sparse.eval nodeValue4528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4528) = mixedMoment B node4528 node4528Labels := rfl
  simpa [nodeValue4528, Sparse.eval] using hc.symm

theorem sound4531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4531 node4531Labels = Sparse.eval nodeValue4531 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4531) = mixedMoment B node4531 node4531Labels := rfl
  simpa [nodeValue4531, Sparse.eval] using hc.symm

theorem sound4535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4535 node4535Labels = Sparse.eval nodeValue4535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4535) = mixedMoment B node4535 node4535Labels := rfl
  simpa [nodeValue4535, Sparse.eval] using hc.symm

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

theorem sound4546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4546 node4546Labels = Sparse.eval nodeValue4546 (mixedVector B) := by
  have h := singleton4546 B _hB
  rw [sound1131 B _hB _hF, sound3264 B _hB _hF] at h
  norm_num [nodeValue4546, nodeValue1131, nodeValue3264, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4547 node4547Labels = Sparse.eval nodeValue4547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4547) = mixedMoment B node4547 node4547Labels := rfl
  simpa [nodeValue4547, Sparse.eval] using hc.symm

theorem sound4555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4555 node4555Labels = Sparse.eval nodeValue4555 (mixedVector B) := by
  have h := singleton4555 B _hB
  rw [sound1140 B _hB _hF, sound3275 B _hB _hF] at h
  norm_num [nodeValue4555, nodeValue1140, nodeValue3275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4558 node4558Labels = Sparse.eval nodeValue4558 (mixedVector B) := by
  have h := singleton4558 B _hB
  rw [sound1144 B _hB _hF, sound3276 B _hB _hF] at h
  norm_num [nodeValue4558, nodeValue1144, nodeValue3276, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4591 node4591Labels = Sparse.eval nodeValue4591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4591) = mixedMoment B node4591 node4591Labels := rfl
  simpa [nodeValue4591, Sparse.eval] using hc.symm

theorem sound4594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4594 node4594Labels = Sparse.eval nodeValue4594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4594) = mixedMoment B node4594 node4594Labels := rfl
  simpa [nodeValue4594, Sparse.eval] using hc.symm

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
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

theorem sound4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4609 node4609Labels = Sparse.eval nodeValue4609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4609) = mixedMoment B node4609 node4609Labels := rfl
  simpa [nodeValue4609, Sparse.eval] using hc.symm

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4619 node4619Labels = Sparse.eval nodeValue4619 (mixedVector B) := by
  have h := singleton4619 B _hB
  rw [sound1294 B _hB _hF, sound3305 B _hB _hF] at h
  norm_num [nodeValue4619, nodeValue1294, nodeValue3305, Sparse.eval] at h ⊢
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

theorem zero5107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = 0 := by
  exact mixedMoment_order_one B hB node5107 node5107Labels 1
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

theorem sound5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5075 node5075Labels = Sparse.eval nodeValue5075 (mixedVector B) := by
  have h := singleton5075 B _hB
  rw [sound2482 B _hB _hF, sound3468 B _hB _hF] at h
  norm_num [nodeValue5075, nodeValue2482, nodeValue3468, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = Sparse.eval nodeValue5107 (mixedVector B) := by
  simpa only [nodeValue5107, Sparse.eval_nil] using zero5107 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = 0 := by
  exact mixedMoment_order_one B hB node5274 node5274Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5261 node5261Labels = Sparse.eval nodeValue5261 (mixedVector B) := by
  have h := singleton5261 B _hB
  rw [sound2726 B _hB _hF, sound3545 B _hB _hF] at h
  norm_num [nodeValue5261, nodeValue2726, nodeValue3545, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

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

theorem sourceEq1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1285 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 1) (sourceB1285 + difference 1 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 1) (sourceB1285 + difference 1 0) sourceC1285) = raw10565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10565; decide +kernel
    rw [ha]
    exact (canonical10565 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 2) (sourceB1285 + difference 2 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 2) (sourceB1285 + difference 2 0) sourceC1285) = raw10566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10566; decide +kernel
    rw [ha]
    exact (canonical10566 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 3) (sourceB1285 + difference 3 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 3) (sourceB1285 + difference 3 0) sourceC1285) = raw10567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10567; decide +kernel
    rw [ha]
    exact (canonical10567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 4) (sourceB1285 + difference 4 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 4) (sourceB1285 + difference 4 0) sourceC1285) = raw10568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10568; decide +kernel
    rw [ha]
    exact (canonical10568 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1285 + difference 0 5) (sourceB1285 + difference 5 0) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA1285 + difference 0 5) (sourceB1285 + difference 5 0) sourceC1285) = raw18318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw18318; decide +kernel
    rw [ha]
    exact (canonical18318 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 0) (sourceB1285 + difference 0 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 0) (sourceB1285 + difference 0 1) sourceC1285) = raw20651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20651; decide +kernel
    rw [ha]
    exact (canonical20651 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 2) (sourceB1285 + difference 2 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 2) (sourceB1285 + difference 2 1) sourceC1285) = raw20652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20652; decide +kernel
    rw [ha]
    exact (canonical20652 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 3) (sourceB1285 + difference 3 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 3) (sourceB1285 + difference 3 1) sourceC1285) = raw20653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20653; decide +kernel
    rw [ha]
    exact (canonical20653 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 4) (sourceB1285 + difference 4 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 4) (sourceB1285 + difference 4 1) sourceC1285) = raw20654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20654; decide +kernel
    rw [ha]
    exact (canonical20654 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1285 + difference 1 5) (sourceB1285 + difference 5 1) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1285 + difference 1 5) (sourceB1285 + difference 5 1) sourceC1285) = raw10544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10544; decide +kernel
    rw [ha]
    exact (canonical10544 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 0) (sourceB1285 + difference 0 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 0) (sourceB1285 + difference 0 2) sourceC1285) = raw20655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20655; decide +kernel
    rw [ha]
    exact (canonical20655 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 1) (sourceB1285 + difference 1 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 1) (sourceB1285 + difference 1 2) sourceC1285) = raw20656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20656; decide +kernel
    rw [ha]
    exact (canonical20656 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 3) (sourceB1285 + difference 3 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 3) (sourceB1285 + difference 3 2) sourceC1285) = raw20657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20657; decide +kernel
    rw [ha]
    exact (canonical20657 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 4) (sourceB1285 + difference 4 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 4) (sourceB1285 + difference 4 2) sourceC1285) = raw20658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20658; decide +kernel
    rw [ha]
    exact (canonical20658 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1285 + difference 2 5) (sourceB1285 + difference 5 2) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1285 + difference 2 5) (sourceB1285 + difference 5 2) sourceC1285) = raw10549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10549; decide +kernel
    rw [ha]
    exact (canonical10549 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 0) (sourceB1285 + difference 0 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 0) (sourceB1285 + difference 0 3) sourceC1285) = raw20659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20659; decide +kernel
    rw [ha]
    exact (canonical20659 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 1) (sourceB1285 + difference 1 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 1) (sourceB1285 + difference 1 3) sourceC1285) = raw20660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20660; decide +kernel
    rw [ha]
    exact (canonical20660 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 2) (sourceB1285 + difference 2 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 2) (sourceB1285 + difference 2 3) sourceC1285) = raw20661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20661; decide +kernel
    rw [ha]
    exact (canonical20661 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 4) (sourceB1285 + difference 4 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 4) (sourceB1285 + difference 4 3) sourceC1285) = raw20662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20662; decide +kernel
    rw [ha]
    exact (canonical20662 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1285 + difference 3 5) (sourceB1285 + difference 5 3) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1285 + difference 3 5) (sourceB1285 + difference 5 3) sourceC1285) = raw10554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10554; decide +kernel
    rw [ha]
    exact (canonical10554 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 0) (sourceB1285 + difference 0 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 0) (sourceB1285 + difference 0 4) sourceC1285) = raw20663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20663; decide +kernel
    rw [ha]
    exact (canonical20663 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 1) (sourceB1285 + difference 1 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 1) (sourceB1285 + difference 1 4) sourceC1285) = raw20664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20664; decide +kernel
    rw [ha]
    exact (canonical20664 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 2) (sourceB1285 + difference 2 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 2) (sourceB1285 + difference 2 4) sourceC1285) = raw20665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20665; decide +kernel
    rw [ha]
    exact (canonical20665 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 3) (sourceB1285 + difference 3 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 3) (sourceB1285 + difference 3 4) sourceC1285) = raw20666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20666; decide +kernel
    rw [ha]
    exact (canonical20666 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1285 + difference 4 5) (sourceB1285 + difference 5 4) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1285 + difference 4 5) (sourceB1285 + difference 5 4) sourceC1285) = raw10559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw10559; decide +kernel
    rw [ha]
    exact (canonical10559 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 0) (sourceB1285 + difference 0 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 0) (sourceB1285 + difference 0 5) sourceC1285) = raw20667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20667; decide +kernel
    rw [ha]
    exact (canonical20667 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 1) (sourceB1285 + difference 1 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4531) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 1) (sourceB1285 + difference 1 5) sourceC1285) = raw20668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20668; decide +kernel
    rw [ha]
    exact (canonical20668 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 2) (sourceB1285 + difference 2 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4531) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 2) (sourceB1285 + difference 2 5) sourceC1285) = raw20669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20669; decide +kernel
    rw [ha]
    exact (canonical20669 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 3) (sourceB1285 + difference 3 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 3) (sourceB1285 + difference 3 5) sourceC1285) = raw20670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20670; decide +kernel
    rw [ha]
    exact (canonical20670 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1285 + difference 5 4) (sourceB1285 + difference 4 5) sourceC1285) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1285 + difference 5 4) (sourceB1285 + difference 4 5) sourceC1285) = raw20671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1285 sourceB1285 sourceC1285 difference raw20671; decide +kernel
    rw [ha]
    exact (canonical20671 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1285 sourceB1285 sourceC1285
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1285, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1114 : Integer.Sparse.reindex keyMap MixedData.row1114 = numericRow1114 := by decide +kernel

theorem numericCheck1114 (x : Master → ℝ) : Integer.Sparse.eval numericRow1114 x =
    (4 : ℝ) * reducedSource1114 x := by
  norm_num [numericRow1114, reducedSource1114, Integer.Sparse.eval, Sparse.eval, nodeValue4153, nodeValue4156, nodeValue4161, nodeValue4178, nodeValue4528, nodeValue4531, nodeValue4535, nodeValue4546, nodeValue4547, nodeValue4555, nodeValue4558, nodeValue4591, nodeValue4594, nodeValue4602, nodeValue4609, nodeValue4612, nodeValue4619, nodeValue5075, nodeValue5107, nodeValue5261, nodeValue5274]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1114 (mixedVector B) = 0 := by
  have h4153 : mixedVector B (Sum.inr 4153) = Sparse.eval nodeValue4153 (mixedVector B) := by
    change mixedMoment B node4153 node4153Labels = _
    exact sound4153 B hB hF
  have h4156 : mixedVector B (Sum.inr 4156) = Sparse.eval nodeValue4156 (mixedVector B) := by
    change mixedMoment B node4156 node4156Labels = _
    exact sound4156 B hB hF
  have h4161 : mixedVector B (Sum.inr 4161) = Sparse.eval nodeValue4161 (mixedVector B) := by
    change mixedMoment B node4161 node4161Labels = _
    exact sound4161 B hB hF
  have h4178 : mixedVector B (Sum.inr 4178) = Sparse.eval nodeValue4178 (mixedVector B) := by
    change mixedMoment B node4178 node4178Labels = _
    exact sound4178 B hB hF
  have h4528 : mixedVector B (Sum.inr 4528) = Sparse.eval nodeValue4528 (mixedVector B) := by
    change mixedMoment B node4528 node4528Labels = _
    exact sound4528 B hB hF
  have h4531 : mixedVector B (Sum.inr 4531) = Sparse.eval nodeValue4531 (mixedVector B) := by
    change mixedMoment B node4531 node4531Labels = _
    exact sound4531 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4547 : mixedVector B (Sum.inr 4547) = Sparse.eval nodeValue4547 (mixedVector B) := by
    change mixedMoment B node4547 node4547Labels = _
    exact sound4547 B hB hF
  have h4555 : mixedVector B (Sum.inr 4555) = Sparse.eval nodeValue4555 (mixedVector B) := by
    change mixedMoment B node4555 node4555Labels = _
    exact sound4555 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4594 : mixedVector B (Sum.inr 4594) = Sparse.eval nodeValue4594 (mixedVector B) := by
    change mixedMoment B node4594 node4594Labels = _
    exact sound4594 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  simpa only [sourceForm1285, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4153, h4156, h4161, h4178, h4528, h4531, h4535, h4546, h4547, h4555, h4558, h4591, h4594, h4602, h4609, h4612, h4619, h5075, h5107, h5261, h5274, reducedSource1114] using sourceEq1285 B hB

theorem rowSound1114_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1114 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1114, numericCheck1114, reducedZero1114 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e_oai
