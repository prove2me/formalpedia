-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:07:52.562945+00:00
-- url     : https://prove2.me/submissions/a232f9c6-fcb0-4416-bcc0-120a1c350a16

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1560 raw1560Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw1560 raw1560Labels = mixedMoment B raw1560step0 raw1560step0Labels := by
      have ha : raw1560step0 = (fun i j => raw1560 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1560step0 raw1560; decide +kernel
      have hl : raw1560step0Labels = raw1560Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1560 raw1560Labels permutation152 permutation4
    mixedMoment B raw1560step0 raw1560step0Labels = mixedMoment B raw1560step1 raw1560step1Labels := by
      have ha : raw1560step1 = raw1560step0 := by apply Matrix.ext; unfold raw1560step1 raw1560step0; decide +kernel
      have hl : raw1560step0Labels = labelEmbedding7 ∘ raw1560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1560step0 raw1560step0Labels raw1560step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical1561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1561 raw1561Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw1561 raw1561Labels = mixedMoment B raw1561step0 raw1561step0Labels := by
      have ha : raw1561step0 = (fun i j => raw1561 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1561step0 raw1561; decide +kernel
      have hl : raw1561step0Labels = raw1561Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1561 raw1561Labels permutation152 permutation4
    _ = mixedMoment B node1805 node1805Labels := by rfl

theorem canonical1562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1562 raw1562Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw1562 raw1562Labels = mixedMoment B raw1562step0 raw1562step0Labels := by
      have ha : raw1562step0 = (fun i j => raw1562 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1562step0 raw1562; decide +kernel
      have hl : raw1562step0Labels = raw1562Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1562 raw1562Labels permutation152 permutation6
    mixedMoment B raw1562step0 raw1562step0Labels = mixedMoment B raw1562step1 raw1562step1Labels := by
      have ha : raw1562step1 = -raw1562step0 := by apply Matrix.ext; change ∀ i j, raw1562step1 i j = -(raw1562step0 i j); unfold raw1562step1 raw1562step0; decide +kernel
      have hl : raw1562step1Labels = raw1562step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1562step1 raw1562step1Labels = mixedMoment B raw1562step2 raw1562step2Labels := by
      have ha : raw1562step2 = raw1562step1 := by apply Matrix.ext; unfold raw1562step2 raw1562step1; decide +kernel
      have hl : raw1562step1Labels = labelEmbedding1 ∘ raw1562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1562step1 raw1562step1Labels raw1562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

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

theorem canonical2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2253 raw2253Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw2253 raw2253Labels = mixedMoment B raw2253step0 raw2253step0Labels := by
      have ha : raw2253step0 = (fun i j => raw2253 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2253step0 raw2253; decide +kernel
      have hl : raw2253step0Labels = raw2253Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2253 raw2253Labels permutation32 permutation4
    mixedMoment B raw2253step0 raw2253step0Labels = mixedMoment B raw2253step1 raw2253step1Labels := by
      have ha : raw2253step1 = raw2253step0 := by apply Matrix.ext; unfold raw2253step1 raw2253step0; decide +kernel
      have hl : raw2253step0Labels = labelEmbedding7 ∘ raw2253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2253step0 raw2253step0Labels raw2253step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2254 raw2254Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw2254 raw2254Labels = mixedMoment B raw2254step0 raw2254step0Labels := by
      have ha : raw2254step0 = (fun i j => raw2254 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2254step0 raw2254; decide +kernel
      have hl : raw2254step0Labels = raw2254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2254 raw2254Labels permutation32 permutation4
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical2255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2255 raw2255Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw2255 raw2255Labels = mixedMoment B raw2255step0 raw2255step0Labels := by
      have ha : raw2255step0 = (fun i j => raw2255 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2255step0 raw2255; decide +kernel
      have hl : raw2255step0Labels = raw2255Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2255 raw2255Labels permutation32 permutation6
    mixedMoment B raw2255step0 raw2255step0Labels = mixedMoment B raw2255step1 raw2255step1Labels := by
      have ha : raw2255step1 = -raw2255step0 := by apply Matrix.ext; change ∀ i j, raw2255step1 i j = -(raw2255step0 i j); unfold raw2255step1 raw2255step0; decide +kernel
      have hl : raw2255step1Labels = raw2255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2255step1 raw2255step1Labels = mixedMoment B raw2255step2 raw2255step2Labels := by
      have ha : raw2255step2 = raw2255step1 := by apply Matrix.ext; unfold raw2255step2 raw2255step1; decide +kernel
      have hl : raw2255step1Labels = labelEmbedding1 ∘ raw2255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2255step1 raw2255step1Labels raw2255step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3394 node3394Labels := by rfl

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

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

theorem canonical2310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2310 raw2310Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2310 raw2310Labels = mixedMoment B raw2310step0 raw2310step0Labels := by
      have ha : raw2310step0 = (fun i j => raw2310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2310step0 raw2310; decide +kernel
      have hl : raw2310step0Labels = raw2310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2310 raw2310Labels permutation32 permutation5
    mixedMoment B raw2310step0 raw2310step0Labels = mixedMoment B raw2310step1 raw2310step1Labels := by
      have ha : raw2310step1 = raw2310step0 := by apply Matrix.ext; unfold raw2310step1 raw2310step0; decide +kernel
      have hl : raw2310step0Labels = labelEmbedding8 ∘ raw2310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2310step0 raw2310step0Labels raw2310step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical2311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2311 raw2311Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw2311 raw2311Labels = mixedMoment B raw2311step0 raw2311step0Labels := by
      have ha : raw2311step0 = (fun i j => raw2311 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2311step0 raw2311; decide +kernel
      have hl : raw2311step0Labels = raw2311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2311 raw2311Labels permutation32 permutation4
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical2312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2312 raw2312Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw2312 raw2312Labels = mixedMoment B raw2312step0 raw2312step0Labels := by
      have ha : raw2312step0 = (fun i j => raw2312 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2312step0 raw2312; decide +kernel
      have hl : raw2312step0Labels = raw2312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2312 raw2312Labels permutation41 permutation3
    mixedMoment B raw2312step0 raw2312step0Labels = mixedMoment B raw2312step1 raw2312step1Labels := by
      have ha : raw2312step1 = -raw2312step0 := by apply Matrix.ext; change ∀ i j, raw2312step1 i j = -(raw2312step0 i j); unfold raw2312step1 raw2312step0; decide +kernel
      have hl : raw2312step1Labels = raw2312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2312step1 raw2312step1Labels = mixedMoment B raw2312step2 raw2312step2Labels := by
      have ha : raw2312step2 = raw2312step1 := by apply Matrix.ext; unfold raw2312step2 raw2312step1; decide +kernel
      have hl : raw2312step1Labels = labelEmbedding1 ∘ raw2312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2312step1 raw2312step1Labels raw2312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical290
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37126 raw37126Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw37126 raw37126Labels = mixedMoment B raw37126step0 raw37126step0Labels := by
      have ha : raw37126step0 = (fun i j => raw37126 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37126step0 raw37126; decide +kernel
      have hl : raw37126step0Labels = raw37126Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37126 raw37126Labels permutation283 permutation2
    _ = mixedMoment B node4833 node4833Labels := by rfl

theorem canonical37127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37127 raw37127Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw37127 raw37127Labels = mixedMoment B raw37127step0 raw37127step0Labels := by
      have ha : raw37127step0 = (fun i j => raw37127 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37127step0 raw37127; decide +kernel
      have hl : raw37127step0Labels = raw37127Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37127 raw37127Labels permutation283 permutation7
    mixedMoment B raw37127step0 raw37127step0Labels = mixedMoment B raw37127step1 raw37127step1Labels := by
      have ha : raw37127step1 = -raw37127step0 := by apply Matrix.ext; change ∀ i j, raw37127step1 i j = -(raw37127step0 i j); unfold raw37127step1 raw37127step0; decide +kernel
      have hl : raw37127step1Labels = raw37127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37127step1 raw37127step1Labels = mixedMoment B raw37127step2 raw37127step2Labels := by
      have ha : raw37127step2 = raw37127step1 := by apply Matrix.ext; unfold raw37127step2 raw37127step1; decide +kernel
      have hl : raw37127step1Labels = labelEmbedding10 ∘ raw37127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37127step1 raw37127step1Labels raw37127step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical37128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37128 raw37128Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw37128 raw37128Labels = mixedMoment B raw37128step0 raw37128step0Labels := by
      have ha : raw37128step0 = (fun i j => raw37128 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37128step0 raw37128; decide +kernel
      have hl : raw37128step0Labels = raw37128Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37128 raw37128Labels permutation285 permutation7
    mixedMoment B raw37128step0 raw37128step0Labels = mixedMoment B raw37128step1 raw37128step1Labels := by
      have ha : raw37128step1 = -raw37128step0 := by apply Matrix.ext; change ∀ i j, raw37128step1 i j = -(raw37128step0 i j); unfold raw37128step1 raw37128step0; decide +kernel
      have hl : raw37128step1Labels = raw37128step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37128step1 raw37128step1Labels = mixedMoment B raw37128step2 raw37128step2Labels := by
      have ha : raw37128step2 = raw37128step1 := by apply Matrix.ext; unfold raw37128step2 raw37128step1; decide +kernel
      have hl : raw37128step1Labels = labelEmbedding10 ∘ raw37128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37128step1 raw37128step1Labels raw37128step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical37129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37129 raw37129Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw37129 raw37129Labels = mixedMoment B raw37129step0 raw37129step0Labels := by
      have ha : raw37129step0 = (fun i j => raw37129 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37129step0 raw37129; decide +kernel
      have hl : raw37129step0Labels = raw37129Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37129 raw37129Labels permutation287 permutation7
    mixedMoment B raw37129step0 raw37129step0Labels = mixedMoment B raw37129step1 raw37129step1Labels := by
      have ha : raw37129step1 = -raw37129step0 := by apply Matrix.ext; change ∀ i j, raw37129step1 i j = -(raw37129step0 i j); unfold raw37129step1 raw37129step0; decide +kernel
      have hl : raw37129step1Labels = raw37129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37129step1 raw37129step1Labels = mixedMoment B raw37129step2 raw37129step2Labels := by
      have ha : raw37129step2 = raw37129step1 := by apply Matrix.ext; unfold raw37129step2 raw37129step1; decide +kernel
      have hl : raw37129step1Labels = labelEmbedding10 ∘ raw37129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37129step1 raw37129step1Labels raw37129step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical37130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37130 raw37130Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw37130 raw37130Labels = mixedMoment B raw37130step0 raw37130step0Labels := by
      have hz : ∀ j, raw37130 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37130step0 = (fun i j => raw37130 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37130step0 raw37130; decide +kernel
      have hl : raw37130step0Labels = raw37130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37130 raw37130Labels permutation590 hz
    mixedMoment B raw37130step0 raw37130step0Labels = mixedMoment B raw37130step1 raw37130step1Labels := by
      have ha : raw37130step1 = (fun i j => raw37130step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37130step1 raw37130step0; decide +kernel
      have hl : raw37130step1Labels = raw37130step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37130step0 raw37130step0Labels permutation56 permutation7
    mixedMoment B raw37130step1 raw37130step1Labels = mixedMoment B raw37130step2 raw37130step2Labels := by
      have ha : raw37130step2 = -raw37130step1 := by apply Matrix.ext; change ∀ i j, raw37130step2 i j = -(raw37130step1 i j); unfold raw37130step2 raw37130step1; decide +kernel
      have hl : raw37130step2Labels = raw37130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37130step2 raw37130step2Labels = mixedMoment B raw37130step3 raw37130step3Labels := by
      have ha : raw37130step3 = raw37130step2 := by apply Matrix.ext; unfold raw37130step3 raw37130step2; decide +kernel
      have hl : raw37130step2Labels = labelEmbedding10 ∘ raw37130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37130step2 raw37130step2Labels raw37130step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical37131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37131 raw37131Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw37131 raw37131Labels = mixedMoment B raw37131step0 raw37131step0Labels := by
      have ha : raw37131step0 = (fun i j => raw37131 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37131step0 raw37131; decide +kernel
      have hl : raw37131step0Labels = raw37131Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37131 raw37131Labels permutation152 permutation3
    mixedMoment B raw37131step0 raw37131step0Labels = mixedMoment B raw37131step1 raw37131step1Labels := by
      have ha : raw37131step1 = raw37131step0 := by apply Matrix.ext; unfold raw37131step1 raw37131step0; decide +kernel
      have hl : raw37131step0Labels = labelEmbedding6 ∘ raw37131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37131step0 raw37131step0Labels raw37131step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

theorem canonical37132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37132 raw37132Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw37132 raw37132Labels = mixedMoment B raw37132step0 raw37132step0Labels := by
      have ha : raw37132step0 = (fun i j => raw37132 (permutation336 i) (permutation6 j)) := by apply Matrix.ext; unfold raw37132step0 raw37132; decide +kernel
      have hl : raw37132step0Labels = raw37132Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37132 raw37132Labels permutation336 permutation6
    mixedMoment B raw37132step0 raw37132step0Labels = mixedMoment B raw37132step1 raw37132step1Labels := by
      have ha : raw37132step1 = -raw37132step0 := by apply Matrix.ext; change ∀ i j, raw37132step1 i j = -(raw37132step0 i j); unfold raw37132step1 raw37132step0; decide +kernel
      have hl : raw37132step1Labels = raw37132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37132step1 raw37132step1Labels = mixedMoment B raw37132step2 raw37132step2Labels := by
      have ha : raw37132step2 = raw37132step1 := by apply Matrix.ext; unfold raw37132step2 raw37132step1; decide +kernel
      have hl : raw37132step1Labels = labelEmbedding9 ∘ raw37132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37132step1 raw37132step1Labels raw37132step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical37133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37133 raw37133Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw37133 raw37133Labels = mixedMoment B raw37133step0 raw37133step0Labels := by
      have ha : raw37133step0 = (fun i j => raw37133 (permutation334 i) (permutation6 j)) := by apply Matrix.ext; unfold raw37133step0 raw37133; decide +kernel
      have hl : raw37133step0Labels = raw37133Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37133 raw37133Labels permutation334 permutation6
    mixedMoment B raw37133step0 raw37133step0Labels = mixedMoment B raw37133step1 raw37133step1Labels := by
      have ha : raw37133step1 = -raw37133step0 := by apply Matrix.ext; change ∀ i j, raw37133step1 i j = -(raw37133step0 i j); unfold raw37133step1 raw37133step0; decide +kernel
      have hl : raw37133step1Labels = raw37133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37133step1 raw37133step1Labels = mixedMoment B raw37133step2 raw37133step2Labels := by
      have ha : raw37133step2 = raw37133step1 := by apply Matrix.ext; unfold raw37133step2 raw37133step1; decide +kernel
      have hl : raw37133step1Labels = labelEmbedding9 ∘ raw37133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37133step1 raw37133step1Labels raw37133step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical37134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37134 raw37134Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw37134 raw37134Labels = mixedMoment B raw37134step0 raw37134step0Labels := by
      have ha : raw37134step0 = (fun i j => raw37134 (permutation333 i) (permutation6 j)) := by apply Matrix.ext; unfold raw37134step0 raw37134; decide +kernel
      have hl : raw37134step0Labels = raw37134Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37134 raw37134Labels permutation333 permutation6
    mixedMoment B raw37134step0 raw37134step0Labels = mixedMoment B raw37134step1 raw37134step1Labels := by
      have ha : raw37134step1 = -raw37134step0 := by apply Matrix.ext; change ∀ i j, raw37134step1 i j = -(raw37134step0 i j); unfold raw37134step1 raw37134step0; decide +kernel
      have hl : raw37134step1Labels = raw37134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37134step1 raw37134step1Labels = mixedMoment B raw37134step2 raw37134step2Labels := by
      have ha : raw37134step2 = raw37134step1 := by apply Matrix.ext; unfold raw37134step2 raw37134step1; decide +kernel
      have hl : raw37134step1Labels = labelEmbedding9 ∘ raw37134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37134step1 raw37134step1Labels raw37134step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical37135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37135 raw37135Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw37135 raw37135Labels = mixedMoment B raw37135step0 raw37135step0Labels := by
      have hz : ∀ j, raw37135 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37135step0 = (fun i j => raw37135 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37135step0 raw37135; decide +kernel
      have hl : raw37135step0Labels = raw37135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37135 raw37135Labels permutation590 hz
    mixedMoment B raw37135step0 raw37135step0Labels = mixedMoment B raw37135step1 raw37135step1Labels := by
      have ha : raw37135step1 = (fun i j => raw37135step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw37135step1 raw37135step0; decide +kernel
      have hl : raw37135step1Labels = raw37135step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37135step0 raw37135step0Labels permutation56 permutation6
    mixedMoment B raw37135step1 raw37135step1Labels = mixedMoment B raw37135step2 raw37135step2Labels := by
      have ha : raw37135step2 = -raw37135step1 := by apply Matrix.ext; change ∀ i j, raw37135step2 i j = -(raw37135step1 i j); unfold raw37135step2 raw37135step1; decide +kernel
      have hl : raw37135step2Labels = raw37135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37135step2 raw37135step2Labels = mixedMoment B raw37135step3 raw37135step3Labels := by
      have ha : raw37135step3 = raw37135step2 := by apply Matrix.ext; unfold raw37135step3 raw37135step2; decide +kernel
      have hl : raw37135step2Labels = labelEmbedding9 ∘ raw37135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37135step2 raw37135step2Labels raw37135step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical37136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37136 raw37136Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw37136 raw37136Labels = mixedMoment B raw37136step0 raw37136step0Labels := by
      have ha : raw37136step0 = (fun i j => raw37136 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37136step0 raw37136; decide +kernel
      have hl : raw37136step0Labels = raw37136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37136 raw37136Labels permutation161 permutation3
    mixedMoment B raw37136step0 raw37136step0Labels = mixedMoment B raw37136step1 raw37136step1Labels := by
      have ha : raw37136step1 = raw37136step0 := by apply Matrix.ext; unfold raw37136step1 raw37136step0; decide +kernel
      have hl : raw37136step0Labels = labelEmbedding6 ∘ raw37136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37136step0 raw37136step0Labels raw37136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

theorem canonical37137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37137 raw37137Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw37137 raw37137Labels = mixedMoment B raw37137step0 raw37137step0Labels := by
      have ha : raw37137step0 = (fun i j => raw37137 (permutation286 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37137step0 raw37137; decide +kernel
      have hl : raw37137step0Labels = raw37137Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37137 raw37137Labels permutation286 permutation2
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical37138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37138 raw37138Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37138 raw37138Labels = mixedMoment B raw37138step0 raw37138step0Labels := by
      have ha : raw37138step0 = (fun i j => raw37138 (permutation286 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37138step0 raw37138; decide +kernel
      have hl : raw37138step0Labels = raw37138Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37138 raw37138Labels permutation286 permutation7
    mixedMoment B raw37138step0 raw37138step0Labels = mixedMoment B raw37138step1 raw37138step1Labels := by
      have ha : raw37138step1 = -raw37138step0 := by apply Matrix.ext; change ∀ i j, raw37138step1 i j = -(raw37138step0 i j); unfold raw37138step1 raw37138step0; decide +kernel
      have hl : raw37138step1Labels = raw37138step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37138step1 raw37138step1Labels = mixedMoment B raw37138step2 raw37138step2Labels := by
      have ha : raw37138step2 = raw37138step1 := by apply Matrix.ext; unfold raw37138step2 raw37138step1; decide +kernel
      have hl : raw37138step1Labels = labelEmbedding10 ∘ raw37138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37138step1 raw37138step1Labels raw37138step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical37139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37139 raw37139Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37139 raw37139Labels = mixedMoment B raw37139step0 raw37139step0Labels := by
      have ha : raw37139step0 = (fun i j => raw37139 (permutation288 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37139step0 raw37139; decide +kernel
      have hl : raw37139step0Labels = raw37139Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37139 raw37139Labels permutation288 permutation7
    mixedMoment B raw37139step0 raw37139step0Labels = mixedMoment B raw37139step1 raw37139step1Labels := by
      have ha : raw37139step1 = -raw37139step0 := by apply Matrix.ext; change ∀ i j, raw37139step1 i j = -(raw37139step0 i j); unfold raw37139step1 raw37139step0; decide +kernel
      have hl : raw37139step1Labels = raw37139step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37139step1 raw37139step1Labels = mixedMoment B raw37139step2 raw37139step2Labels := by
      have ha : raw37139step2 = raw37139step1 := by apply Matrix.ext; unfold raw37139step2 raw37139step1; decide +kernel
      have hl : raw37139step1Labels = labelEmbedding10 ∘ raw37139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37139step1 raw37139step1Labels raw37139step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical37140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37140 raw37140Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw37140 raw37140Labels = mixedMoment B raw37140step0 raw37140step0Labels := by
      have hz : ∀ j, raw37140 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37140step0 = (fun i j => raw37140 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37140step0 raw37140; decide +kernel
      have hl : raw37140step0Labels = raw37140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37140 raw37140Labels permutation590 hz
    mixedMoment B raw37140step0 raw37140step0Labels = mixedMoment B raw37140step1 raw37140step1Labels := by
      have ha : raw37140step1 = (fun i j => raw37140step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37140step1 raw37140step0; decide +kernel
      have hl : raw37140step1Labels = raw37140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37140step0 raw37140step0Labels permutation59 permutation7
    mixedMoment B raw37140step1 raw37140step1Labels = mixedMoment B raw37140step2 raw37140step2Labels := by
      have ha : raw37140step2 = -raw37140step1 := by apply Matrix.ext; change ∀ i j, raw37140step2 i j = -(raw37140step1 i j); unfold raw37140step2 raw37140step1; decide +kernel
      have hl : raw37140step2Labels = raw37140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37140step2 raw37140step2Labels = mixedMoment B raw37140step3 raw37140step3Labels := by
      have ha : raw37140step3 = raw37140step2 := by apply Matrix.ext; unfold raw37140step3 raw37140step2; decide +kernel
      have hl : raw37140step2Labels = labelEmbedding10 ∘ raw37140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37140step2 raw37140step2Labels raw37140step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical37141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37141 raw37141Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw37141 raw37141Labels = mixedMoment B raw37141step0 raw37141step0Labels := by
      have ha : raw37141step0 = (fun i j => raw37141 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37141step0 raw37141; decide +kernel
      have hl : raw37141step0Labels = raw37141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37141 raw37141Labels permutation155 permutation3
    mixedMoment B raw37141step0 raw37141step0Labels = mixedMoment B raw37141step1 raw37141step1Labels := by
      have ha : raw37141step1 = raw37141step0 := by apply Matrix.ext; unfold raw37141step1 raw37141step0; decide +kernel
      have hl : raw37141step0Labels = labelEmbedding6 ∘ raw37141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37141step0 raw37141step0Labels raw37141step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

theorem canonical37142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37142 raw37142Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw37142 raw37142Labels = mixedMoment B raw37142step0 raw37142step0Labels := by
      have ha : raw37142step0 = (fun i j => raw37142 (permutation284 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37142step0 raw37142; decide +kernel
      have hl : raw37142step0Labels = raw37142Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37142 raw37142Labels permutation284 permutation2
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical37143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37143 raw37143Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37143 raw37143Labels = mixedMoment B raw37143step0 raw37143step0Labels := by
      have ha : raw37143step0 = (fun i j => raw37143 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37143step0 raw37143; decide +kernel
      have hl : raw37143step0Labels = raw37143Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37143 raw37143Labels permutation284 permutation7
    mixedMoment B raw37143step0 raw37143step0Labels = mixedMoment B raw37143step1 raw37143step1Labels := by
      have ha : raw37143step1 = -raw37143step0 := by apply Matrix.ext; change ∀ i j, raw37143step1 i j = -(raw37143step0 i j); unfold raw37143step1 raw37143step0; decide +kernel
      have hl : raw37143step1Labels = raw37143step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37143step1 raw37143step1Labels = mixedMoment B raw37143step2 raw37143step2Labels := by
      have ha : raw37143step2 = raw37143step1 := by apply Matrix.ext; unfold raw37143step2 raw37143step1; decide +kernel
      have hl : raw37143step1Labels = labelEmbedding10 ∘ raw37143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37143step1 raw37143step1Labels raw37143step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical37144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37144 raw37144Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37144 raw37144Labels = mixedMoment B raw37144step0 raw37144step0Labels := by
      have ha : raw37144step0 = (fun i j => raw37144 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37144step0 raw37144; decide +kernel
      have hl : raw37144step0Labels = raw37144Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37144 raw37144Labels permutation287 permutation7
    mixedMoment B raw37144step0 raw37144step0Labels = mixedMoment B raw37144step1 raw37144step1Labels := by
      have ha : raw37144step1 = -raw37144step0 := by apply Matrix.ext; change ∀ i j, raw37144step1 i j = -(raw37144step0 i j); unfold raw37144step1 raw37144step0; decide +kernel
      have hl : raw37144step1Labels = raw37144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37144step1 raw37144step1Labels = mixedMoment B raw37144step2 raw37144step2Labels := by
      have ha : raw37144step2 = raw37144step1 := by apply Matrix.ext; unfold raw37144step2 raw37144step1; decide +kernel
      have hl : raw37144step1Labels = labelEmbedding10 ∘ raw37144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37144step1 raw37144step1Labels raw37144step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical37145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37145 raw37145Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw37145 raw37145Labels = mixedMoment B raw37145step0 raw37145step0Labels := by
      have hz : ∀ j, raw37145 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37145step0 = (fun i j => raw37145 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37145step0 raw37145; decide +kernel
      have hl : raw37145step0Labels = raw37145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37145 raw37145Labels permutation590 hz
    mixedMoment B raw37145step0 raw37145step0Labels = mixedMoment B raw37145step1 raw37145step1Labels := by
      have ha : raw37145step1 = (fun i j => raw37145step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37145step1 raw37145step0; decide +kernel
      have hl : raw37145step1Labels = raw37145step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37145step0 raw37145step0Labels permutation57 permutation7
    mixedMoment B raw37145step1 raw37145step1Labels = mixedMoment B raw37145step2 raw37145step2Labels := by
      have ha : raw37145step2 = -raw37145step1 := by apply Matrix.ext; change ∀ i j, raw37145step2 i j = -(raw37145step1 i j); unfold raw37145step2 raw37145step1; decide +kernel
      have hl : raw37145step2Labels = raw37145step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37145step2 raw37145step2Labels = mixedMoment B raw37145step3 raw37145step3Labels := by
      have ha : raw37145step3 = raw37145step2 := by apply Matrix.ext; unfold raw37145step3 raw37145step2; decide +kernel
      have hl : raw37145step2Labels = labelEmbedding10 ∘ raw37145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37145step2 raw37145step2Labels raw37145step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical37146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37146 raw37146Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw37146 raw37146Labels = mixedMoment B raw37146step0 raw37146step0Labels := by
      have ha : raw37146step0 = (fun i j => raw37146 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37146step0 raw37146; decide +kernel
      have hl : raw37146step0Labels = raw37146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37146 raw37146Labels permutation153 permutation3
    mixedMoment B raw37146step0 raw37146step0Labels = mixedMoment B raw37146step1 raw37146step1Labels := by
      have ha : raw37146step1 = raw37146step0 := by apply Matrix.ext; unfold raw37146step1 raw37146step0; decide +kernel
      have hl : raw37146step0Labels = labelEmbedding6 ∘ raw37146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37146step0 raw37146step0Labels raw37146step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

theorem canonical37147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37147 raw37147Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw37147 raw37147Labels = mixedMoment B raw37147step0 raw37147step0Labels := by
      have ha : raw37147step0 = (fun i j => raw37147 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37147step0 raw37147; decide +kernel
      have hl : raw37147step0Labels = raw37147Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37147 raw37147Labels permutation283 permutation2
    _ = mixedMoment B node4679 node4679Labels := by rfl

theorem canonical37148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37148 raw37148Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37148 raw37148Labels = mixedMoment B raw37148step0 raw37148step0Labels := by
      have ha : raw37148step0 = (fun i j => raw37148 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37148step0 raw37148; decide +kernel
      have hl : raw37148step0Labels = raw37148Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37148 raw37148Labels permutation283 permutation7
    mixedMoment B raw37148step0 raw37148step0Labels = mixedMoment B raw37148step1 raw37148step1Labels := by
      have ha : raw37148step1 = -raw37148step0 := by apply Matrix.ext; change ∀ i j, raw37148step1 i j = -(raw37148step0 i j); unfold raw37148step1 raw37148step0; decide +kernel
      have hl : raw37148step1Labels = raw37148step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37148step1 raw37148step1Labels = mixedMoment B raw37148step2 raw37148step2Labels := by
      have ha : raw37148step2 = raw37148step1 := by apply Matrix.ext; unfold raw37148step2 raw37148step1; decide +kernel
      have hl : raw37148step1Labels = labelEmbedding10 ∘ raw37148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37148step1 raw37148step1Labels raw37148step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical37149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37149 raw37149Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37149 raw37149Labels = mixedMoment B raw37149step0 raw37149step0Labels := by
      have ha : raw37149step0 = (fun i j => raw37149 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37149step0 raw37149; decide +kernel
      have hl : raw37149step0Labels = raw37149Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37149 raw37149Labels permutation285 permutation7
    mixedMoment B raw37149step0 raw37149step0Labels = mixedMoment B raw37149step1 raw37149step1Labels := by
      have ha : raw37149step1 = -raw37149step0 := by apply Matrix.ext; change ∀ i j, raw37149step1 i j = -(raw37149step0 i j); unfold raw37149step1 raw37149step0; decide +kernel
      have hl : raw37149step1Labels = raw37149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37149step1 raw37149step1Labels = mixedMoment B raw37149step2 raw37149step2Labels := by
      have ha : raw37149step2 = raw37149step1 := by apply Matrix.ext; unfold raw37149step2 raw37149step1; decide +kernel
      have hl : raw37149step1Labels = labelEmbedding10 ∘ raw37149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37149step1 raw37149step1Labels raw37149step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical37150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37150 raw37150Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw37150 raw37150Labels = mixedMoment B raw37150step0 raw37150step0Labels := by
      have hz : ∀ j, raw37150 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37150step0 = (fun i j => raw37150 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37150step0 raw37150; decide +kernel
      have hl : raw37150step0Labels = raw37150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37150 raw37150Labels permutation590 hz
    mixedMoment B raw37150step0 raw37150step0Labels = mixedMoment B raw37150step1 raw37150step1Labels := by
      have ha : raw37150step1 = (fun i j => raw37150step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37150step1 raw37150step0; decide +kernel
      have hl : raw37150step1Labels = raw37150step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37150step0 raw37150step0Labels permutation56 permutation7
    mixedMoment B raw37150step1 raw37150step1Labels = mixedMoment B raw37150step2 raw37150step2Labels := by
      have ha : raw37150step2 = -raw37150step1 := by apply Matrix.ext; change ∀ i j, raw37150step2 i j = -(raw37150step1 i j); unfold raw37150step2 raw37150step1; decide +kernel
      have hl : raw37150step2Labels = raw37150step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37150step2 raw37150step2Labels = mixedMoment B raw37150step3 raw37150step3Labels := by
      have ha : raw37150step3 = raw37150step2 := by apply Matrix.ext; unfold raw37150step3 raw37150step2; decide +kernel
      have hl : raw37150step2Labels = labelEmbedding10 ∘ raw37150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37150step2 raw37150step2Labels raw37150step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical37151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37151 raw37151Labels = mixedMoment B node4695 node4695Labels := by
  calc
    mixedMoment B raw37151 raw37151Labels = mixedMoment B raw37151step0 raw37151step0Labels := by
      have ha : raw37151step0 = (fun i j => raw37151 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37151step0 raw37151; decide +kernel
      have hl : raw37151step0Labels = raw37151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37151 raw37151Labels permutation152 permutation3
    mixedMoment B raw37151step0 raw37151step0Labels = mixedMoment B raw37151step1 raw37151step1Labels := by
      have ha : raw37151step1 = raw37151step0 := by apply Matrix.ext; unfold raw37151step1 raw37151step0; decide +kernel
      have hl : raw37151step0Labels = labelEmbedding6 ∘ raw37151step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37151step0 raw37151step0Labels raw37151step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4695 node4695Labels := by rfl

theorem canonical37152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37152 raw37152Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw37152 raw37152Labels = mixedMoment B raw37152step0 raw37152step0Labels := by
      have ha : raw37152step0 = (fun i j => raw37152 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37152step0 raw37152; decide +kernel
      have hl : raw37152step0Labels = raw37152Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37152 raw37152Labels permutation265 permutation2
    _ = mixedMoment B node4685 node4685Labels := by rfl

theorem canonical37153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37153 raw37153Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw37153 raw37153Labels = mixedMoment B raw37153step0 raw37153step0Labels := by
      have ha : raw37153step0 = (fun i j => raw37153 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37153step0 raw37153; decide +kernel
      have hl : raw37153step0Labels = raw37153Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37153 raw37153Labels permutation283 permutation7
    mixedMoment B raw37153step0 raw37153step0Labels = mixedMoment B raw37153step1 raw37153step1Labels := by
      have ha : raw37153step1 = -raw37153step0 := by apply Matrix.ext; change ∀ i j, raw37153step1 i j = -(raw37153step0 i j); unfold raw37153step1 raw37153step0; decide +kernel
      have hl : raw37153step1Labels = raw37153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37153step1 raw37153step1Labels = mixedMoment B raw37153step2 raw37153step2Labels := by
      have ha : raw37153step2 = raw37153step1 := by apply Matrix.ext; unfold raw37153step2 raw37153step1; decide +kernel
      have hl : raw37153step1Labels = labelEmbedding10 ∘ raw37153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37153step1 raw37153step1Labels raw37153step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical37154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37154 raw37154Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw37154 raw37154Labels = mixedMoment B raw37154step0 raw37154step0Labels := by
      have ha : raw37154step0 = (fun i j => raw37154 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37154step0 raw37154; decide +kernel
      have hl : raw37154step0Labels = raw37154Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37154 raw37154Labels permutation285 permutation7
    mixedMoment B raw37154step0 raw37154step0Labels = mixedMoment B raw37154step1 raw37154step1Labels := by
      have ha : raw37154step1 = -raw37154step0 := by apply Matrix.ext; change ∀ i j, raw37154step1 i j = -(raw37154step0 i j); unfold raw37154step1 raw37154step0; decide +kernel
      have hl : raw37154step1Labels = raw37154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37154step1 raw37154step1Labels = mixedMoment B raw37154step2 raw37154step2Labels := by
      have ha : raw37154step2 = raw37154step1 := by apply Matrix.ext; unfold raw37154step2 raw37154step1; decide +kernel
      have hl : raw37154step1Labels = labelEmbedding10 ∘ raw37154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37154step1 raw37154step1Labels raw37154step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical37155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37155 raw37155Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw37155 raw37155Labels = mixedMoment B raw37155step0 raw37155step0Labels := by
      have ha : raw37155step0 = (fun i j => raw37155 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37155step0 raw37155; decide +kernel
      have hl : raw37155step0Labels = raw37155Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37155 raw37155Labels permutation287 permutation7
    mixedMoment B raw37155step0 raw37155step0Labels = mixedMoment B raw37155step1 raw37155step1Labels := by
      have ha : raw37155step1 = -raw37155step0 := by apply Matrix.ext; change ∀ i j, raw37155step1 i j = -(raw37155step0 i j); unfold raw37155step1 raw37155step0; decide +kernel
      have hl : raw37155step1Labels = raw37155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37155step1 raw37155step1Labels = mixedMoment B raw37155step2 raw37155step2Labels := by
      have ha : raw37155step2 = raw37155step1 := by apply Matrix.ext; unfold raw37155step2 raw37155step1; decide +kernel
      have hl : raw37155step1Labels = labelEmbedding10 ∘ raw37155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37155step1 raw37155step1Labels raw37155step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4679 node4679Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1805 node1805Labels + mixedMoment B node2150 node2150Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1560 singletonSmall4679
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4679) = raw1560Labels := by decide +kernel
  rw [hl, canonical1560 B hB] at h
  have hc0 : mixedMoment B raw1560 (Fin.cases (0 : Fin 2) singletonSmall4679) =
      mixedMoment B node1805 node1805Labels := by
    have ha : raw1560 = raw1561 := by apply Matrix.ext; unfold raw1560 raw1561; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4679 = raw1561Labels := by decide +kernel
    rw [ha, hj, canonical1561 B hB]
  have hc1 : mixedMoment B raw1560 (Fin.cases (1 : Fin 2) singletonSmall4679) =
      mixedMoment B node2150 node2150Labels := by
    have ha : raw1560 = raw1562 := by apply Matrix.ext; unfold raw1560 raw1562; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4679 = raw1562Labels := by decide +kernel
    rw [ha, hj, canonical1562 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5237 node5237Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2684 node2684Labels + mixedMoment B node3394 node3394Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2253 singletonSmall5237
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5237) = raw2253Labels := by decide +kernel
  rw [hl, canonical2253 B hB] at h
  have hc0 : mixedMoment B raw2253 (Fin.cases (0 : Fin 2) singletonSmall5237) =
      mixedMoment B node2684 node2684Labels := by
    have ha : raw2253 = raw2254 := by apply Matrix.ext; unfold raw2253 raw2254; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5237 = raw2254Labels := by decide +kernel
    rw [ha, hj, canonical2254 B hB]
  have hc1 : mixedMoment B raw2253 (Fin.cases (1 : Fin 2) singletonSmall5237) =
      mixedMoment B node3394 node3394Labels := by
    have ha : raw2253 = raw2255 := by apply Matrix.ext; unfold raw2253 raw2255; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5237 = raw2255Labels := by decide +kernel
    rw [ha, hj, canonical2255 B hB]
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

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5301 node5301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3053 node3053Labels + mixedMoment B node3619 node3619Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2310 singletonSmall5301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5301) = raw2310Labels := by decide +kernel
  rw [hl, canonical2310 B hB] at h
  have hc0 : mixedMoment B raw2310 (Fin.cases (0 : Fin 2) singletonSmall5301) =
      mixedMoment B node3053 node3053Labels := by
    have ha : raw2310 = raw2311 := by apply Matrix.ext; unfold raw2310 raw2311; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5301 = raw2311Labels := by decide +kernel
    rw [ha, hj, canonical2311 B hB]
  have hc1 : mixedMoment B raw2310 (Fin.cases (1 : Fin 2) singletonSmall5301) =
      mixedMoment B node3619 node3619Labels := by
    have ha : raw2310 = raw2312 := by apply Matrix.ext; unfold raw2310 raw2312; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5301 = raw2312Labels := by decide +kernel
    rw [ha, hj, canonical2312 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1805 node1805Labels = Sparse.eval nodeValue1805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1805) = mixedMoment B node1805 node1805Labels := rfl
  simpa [nodeValue1805, Sparse.eval] using hc.symm

theorem sound1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1811 node1811Labels = Sparse.eval nodeValue1811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1811) = mixedMoment B node1811 node1811Labels := rfl
  simpa [nodeValue1811, Sparse.eval] using hc.symm

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

theorem sound2150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2150 node2150Labels = Sparse.eval nodeValue2150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2150) = mixedMoment B node2150 node2150Labels := rfl
  simpa [nodeValue2150, Sparse.eval] using hc.symm

theorem sound2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2156 node2156Labels = Sparse.eval nodeValue2156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2156) = mixedMoment B node2156 node2156Labels := rfl
  simpa [nodeValue2156, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

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

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3394 node3394Labels = Sparse.eval nodeValue3394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3394) = mixedMoment B node3394 node3394Labels := rfl
  simpa [nodeValue3394, Sparse.eval] using hc.symm

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

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

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

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

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

theorem sound4679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4679 node4679Labels = Sparse.eval nodeValue4679 (mixedVector B) := by
  have h := singleton4679 B _hB
  rw [sound1805 B _hB _hF, sound2150 B _hB _hF] at h
  norm_num [nodeValue4679, nodeValue1805, nodeValue2150, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4685 node4685Labels = Sparse.eval nodeValue4685 (mixedVector B) := by
  have h := singleton4685 B _hB
  rw [sound1811 B _hB _hF, sound2156 B _hB _hF] at h
  norm_num [nodeValue4685, nodeValue1811, nodeValue2156, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4695 node4695Labels = Sparse.eval nodeValue4695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4695) = mixedMoment B node4695 node4695Labels := rfl
  simpa [nodeValue4695, Sparse.eval] using hc.symm

theorem sound4696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4696 node4696Labels = Sparse.eval nodeValue4696 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4696) = mixedMoment B node4696 node4696Labels := rfl
  simpa [nodeValue4696, Sparse.eval] using hc.symm

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

theorem zero4833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4833 node4833Labels = 0 := by
  exact mixedMoment_order_one B hB node4833 node4833Labels 1
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

theorem sound4833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4833 node4833Labels = Sparse.eval nodeValue4833 (mixedVector B) := by
  simpa only [nodeValue4833, Sparse.eval_nil] using zero4833 B _hB _hF

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

theorem sound4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4878 node4878Labels = Sparse.eval nodeValue4878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4878) = mixedMoment B node4878 node4878Labels := rfl
  simpa [nodeValue4878, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5226 node5226Labels = Sparse.eval nodeValue5226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5226) = mixedMoment B node5226 node5226Labels := rfl
  simpa [nodeValue5226, Sparse.eval] using hc.symm

theorem sound5231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5231 node5231Labels = Sparse.eval nodeValue5231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5231) = mixedMoment B node5231 node5231Labels := rfl
  simpa [nodeValue5231, Sparse.eval] using hc.symm

theorem sound5237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5237 node5237Labels = Sparse.eval nodeValue5237 (mixedVector B) := by
  have h := singleton5237 B _hB
  rw [sound2684 B _hB _hF, sound3394 B _hB _hF] at h
  norm_num [nodeValue5237, nodeValue2684, nodeValue3394, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero5273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = 0 := by
  exact mixedMoment_order_one B hB node5273 node5273Labels 1
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

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = Sparse.eval nodeValue5273 (mixedVector B) := by
  simpa only [nodeValue5273, Sparse.eval_nil] using zero5273 B _hB _hF

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources82
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2644 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 1) (sourceB2644 + difference 1 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 1) (sourceB2644 + difference 1 0) sourceC2644) = raw37126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37126; decide +kernel
    rw [ha]
    exact (canonical37126 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 2) (sourceB2644 + difference 2 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 2) (sourceB2644 + difference 2 0) sourceC2644) = raw37127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37127; decide +kernel
    rw [ha]
    exact (canonical37127 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 3) (sourceB2644 + difference 3 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 3) (sourceB2644 + difference 3 0) sourceC2644) = raw37128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37128; decide +kernel
    rw [ha]
    exact (canonical37128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 4) (sourceB2644 + difference 4 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 4) (sourceB2644 + difference 4 0) sourceC2644) = raw37129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37129; decide +kernel
    rw [ha]
    exact (canonical37129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2644 + difference 0 5) (sourceB2644 + difference 5 0) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA2644 + difference 0 5) (sourceB2644 + difference 5 0) sourceC2644) = raw37130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37130; decide +kernel
    rw [ha]
    exact (canonical37130 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 0) (sourceB2644 + difference 0 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 0) (sourceB2644 + difference 0 1) sourceC2644) = raw37131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37131; decide +kernel
    rw [ha]
    exact (canonical37131 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 2) (sourceB2644 + difference 2 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 2) (sourceB2644 + difference 2 1) sourceC2644) = raw37132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37132; decide +kernel
    rw [ha]
    exact (canonical37132 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 3) (sourceB2644 + difference 3 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 3) (sourceB2644 + difference 3 1) sourceC2644) = raw37133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37133; decide +kernel
    rw [ha]
    exact (canonical37133 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 4) (sourceB2644 + difference 4 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 4) (sourceB2644 + difference 4 1) sourceC2644) = raw37134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37134; decide +kernel
    rw [ha]
    exact (canonical37134 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2644 + difference 1 5) (sourceB2644 + difference 5 1) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA2644 + difference 1 5) (sourceB2644 + difference 5 1) sourceC2644) = raw37135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37135; decide +kernel
    rw [ha]
    exact (canonical37135 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 0) (sourceB2644 + difference 0 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4696) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 0) (sourceB2644 + difference 0 2) sourceC2644) = raw37136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37136; decide +kernel
    rw [ha]
    exact (canonical37136 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 1) (sourceB2644 + difference 1 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 1) (sourceB2644 + difference 1 2) sourceC2644) = raw37137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37137; decide +kernel
    rw [ha]
    exact (canonical37137 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 3) (sourceB2644 + difference 3 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 3) (sourceB2644 + difference 3 2) sourceC2644) = raw37138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37138; decide +kernel
    rw [ha]
    exact (canonical37138 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 4) (sourceB2644 + difference 4 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 4) (sourceB2644 + difference 4 2) sourceC2644) = raw37139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37139; decide +kernel
    rw [ha]
    exact (canonical37139 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2644 + difference 2 5) (sourceB2644 + difference 5 2) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2644 + difference 2 5) (sourceB2644 + difference 5 2) sourceC2644) = raw37140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37140; decide +kernel
    rw [ha]
    exact (canonical37140 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 0) (sourceB2644 + difference 0 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4696) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 0) (sourceB2644 + difference 0 3) sourceC2644) = raw37141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37141; decide +kernel
    rw [ha]
    exact (canonical37141 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 1) (sourceB2644 + difference 1 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 1) (sourceB2644 + difference 1 3) sourceC2644) = raw37142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37142; decide +kernel
    rw [ha]
    exact (canonical37142 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 2) (sourceB2644 + difference 2 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 2) (sourceB2644 + difference 2 3) sourceC2644) = raw37143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37143; decide +kernel
    rw [ha]
    exact (canonical37143 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 4) (sourceB2644 + difference 4 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 4) (sourceB2644 + difference 4 3) sourceC2644) = raw37144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37144; decide +kernel
    rw [ha]
    exact (canonical37144 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2644 + difference 3 5) (sourceB2644 + difference 5 3) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2644 + difference 3 5) (sourceB2644 + difference 5 3) sourceC2644) = raw37145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37145; decide +kernel
    rw [ha]
    exact (canonical37145 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 0) (sourceB2644 + difference 0 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4696) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 0) (sourceB2644 + difference 0 4) sourceC2644) = raw37146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37146; decide +kernel
    rw [ha]
    exact (canonical37146 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 1) (sourceB2644 + difference 1 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 1) (sourceB2644 + difference 1 4) sourceC2644) = raw37147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37147; decide +kernel
    rw [ha]
    exact (canonical37147 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 2) (sourceB2644 + difference 2 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 2) (sourceB2644 + difference 2 4) sourceC2644) = raw37148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37148; decide +kernel
    rw [ha]
    exact (canonical37148 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 3) (sourceB2644 + difference 3 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 3) (sourceB2644 + difference 3 4) sourceC2644) = raw37149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37149; decide +kernel
    rw [ha]
    exact (canonical37149 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2644 + difference 4 5) (sourceB2644 + difference 5 4) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2644 + difference 4 5) (sourceB2644 + difference 5 4) sourceC2644) = raw37150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37150; decide +kernel
    rw [ha]
    exact (canonical37150 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 0) (sourceB2644 + difference 0 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4695) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 0) (sourceB2644 + difference 0 5) sourceC2644) = raw37151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37151; decide +kernel
    rw [ha]
    exact (canonical37151 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 1) (sourceB2644 + difference 1 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 1) (sourceB2644 + difference 1 5) sourceC2644) = raw37152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37152; decide +kernel
    rw [ha]
    exact (canonical37152 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 2) (sourceB2644 + difference 2 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 2) (sourceB2644 + difference 2 5) sourceC2644) = raw37153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37153; decide +kernel
    rw [ha]
    exact (canonical37153 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 3) (sourceB2644 + difference 3 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 3) (sourceB2644 + difference 3 5) sourceC2644) = raw37154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37154; decide +kernel
    rw [ha]
    exact (canonical37154 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2644 + difference 5 4) (sourceB2644 + difference 4 5) sourceC2644) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2644 + difference 5 4) (sourceB2644 + difference 4 5) sourceC2644) = raw37155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2644 sourceB2644 sourceC2644 difference raw37155; decide +kernel
    rw [ha]
    exact (canonical37155 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2644 sourceB2644 sourceC2644
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2644, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2103 : Integer.Sparse.reindex keyMap MixedData.row2103 = numericRow2103 := by decide +kernel

theorem numericCheck2103 (x : Master → ℝ) : Integer.Sparse.eval numericRow2103 x =
    (4 : ℝ) * reducedSource2103 x := by
  norm_num [numericRow2103, reducedSource2103, Integer.Sparse.eval, Sparse.eval, nodeValue4679, nodeValue4685, nodeValue4695, nodeValue4696, nodeValue4833, nodeValue4878, nodeValue5226, nodeValue5231, nodeValue5237, nodeValue5257, nodeValue5265, nodeValue5273, nodeValue5301] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2103 (mixedVector B) = 0 := by
  have h4679 : mixedVector B (Sum.inr 4679) = Sparse.eval nodeValue4679 (mixedVector B) := by
    change mixedMoment B node4679 node4679Labels = _
    exact sound4679 B hB hF
  have h4685 : mixedVector B (Sum.inr 4685) = Sparse.eval nodeValue4685 (mixedVector B) := by
    change mixedMoment B node4685 node4685Labels = _
    exact sound4685 B hB hF
  have h4695 : mixedVector B (Sum.inr 4695) = Sparse.eval nodeValue4695 (mixedVector B) := by
    change mixedMoment B node4695 node4695Labels = _
    exact sound4695 B hB hF
  have h4696 : mixedVector B (Sum.inr 4696) = Sparse.eval nodeValue4696 (mixedVector B) := by
    change mixedMoment B node4696 node4696Labels = _
    exact sound4696 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4878 : mixedVector B (Sum.inr 4878) = Sparse.eval nodeValue4878 (mixedVector B) := by
    change mixedMoment B node4878 node4878Labels = _
    exact sound4878 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5237 : mixedVector B (Sum.inr 5237) = Sparse.eval nodeValue5237 (mixedVector B) := by
    change mixedMoment B node5237 node5237Labels = _
    exact sound5237 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  simpa only [sourceForm2644, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4679, h4685, h4695, h4696, h4833, h4878, h5226, h5231, h5237, h5257, h5265, h5273, h5301, reducedSource2103] using sourceEq2644 B hB

theorem rowSound2103_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2103 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2103, numericCheck2103, reducedZero2103 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e_oai
