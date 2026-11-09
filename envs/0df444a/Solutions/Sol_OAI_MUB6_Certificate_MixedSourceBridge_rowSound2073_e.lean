-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:58:50.583937+00:00
-- url     : https://prove2.me/submissions/334089fb-4c32-4d9f-a440-cb8ff0c2d794

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E109
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

theorem canonical1554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1554 raw1554Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw1554 raw1554Labels = mixedMoment B raw1554step0 raw1554step0Labels := by
      have ha : raw1554step0 = (fun i j => raw1554 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1554step0 raw1554; decide +kernel
      have hl : raw1554step0Labels = raw1554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1554 raw1554Labels permutation152 permutation4
    mixedMoment B raw1554step0 raw1554step0Labels = mixedMoment B raw1554step1 raw1554step1Labels := by
      have ha : raw1554step1 = raw1554step0 := by apply Matrix.ext; unfold raw1554step1 raw1554step0; decide +kernel
      have hl : raw1554step0Labels = labelEmbedding7 ∘ raw1554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1554step0 raw1554step0Labels raw1554step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

theorem canonical1555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1555 raw1555Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw1555 raw1555Labels = mixedMoment B raw1555step0 raw1555step0Labels := by
      have ha : raw1555step0 = (fun i j => raw1555 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1555step0 raw1555; decide +kernel
      have hl : raw1555step0Labels = raw1555Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1555 raw1555Labels permutation152 permutation4
    _ = mixedMoment B node1802 node1802Labels := by rfl

theorem canonical1556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1556 raw1556Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw1556 raw1556Labels = mixedMoment B raw1556step0 raw1556step0Labels := by
      have ha : raw1556step0 = (fun i j => raw1556 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1556step0 raw1556; decide +kernel
      have hl : raw1556step0Labels = raw1556Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1556 raw1556Labels permutation152 permutation6
    mixedMoment B raw1556step0 raw1556step0Labels = mixedMoment B raw1556step1 raw1556step1Labels := by
      have ha : raw1556step1 = -raw1556step0 := by apply Matrix.ext; change ∀ i j, raw1556step1 i j = -(raw1556step0 i j); unfold raw1556step1 raw1556step0; decide +kernel
      have hl : raw1556step1Labels = raw1556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1556step1 raw1556step1Labels = mixedMoment B raw1556step2 raw1556step2Labels := by
      have ha : raw1556step2 = raw1556step1 := by apply Matrix.ext; unfold raw1556step2 raw1556step1; decide +kernel
      have hl : raw1556step1Labels = labelEmbedding1 ∘ raw1556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1556step1 raw1556step1Labels raw1556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

theorem canonical1563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1563 raw1563Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw1563 raw1563Labels = mixedMoment B raw1563step0 raw1563step0Labels := by
      have ha : raw1563step0 = (fun i j => raw1563 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1563step0 raw1563; decide +kernel
      have hl : raw1563step0Labels = raw1563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1563 raw1563Labels permutation32 permutation4
    mixedMoment B raw1563step0 raw1563step0Labels = mixedMoment B raw1563step1 raw1563step1Labels := by
      have ha : raw1563step1 = raw1563step0 := by apply Matrix.ext; unfold raw1563step1 raw1563step0; decide +kernel
      have hl : raw1563step0Labels = labelEmbedding7 ∘ raw1563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1563step0 raw1563step0Labels raw1563step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical1564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1564 raw1564Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw1564 raw1564Labels = mixedMoment B raw1564step0 raw1564step0Labels := by
      have ha : raw1564step0 = (fun i j => raw1564 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1564step0 raw1564; decide +kernel
      have hl : raw1564step0Labels = raw1564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1564 raw1564Labels permutation32 permutation4
    _ = mixedMoment B node1807 node1807Labels := by rfl

theorem canonical1565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1565 raw1565Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw1565 raw1565Labels = mixedMoment B raw1565step0 raw1565step0Labels := by
      have ha : raw1565step0 = (fun i j => raw1565 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1565step0 raw1565; decide +kernel
      have hl : raw1565step0Labels = raw1565Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1565 raw1565Labels permutation32 permutation6
    mixedMoment B raw1565step0 raw1565step0Labels = mixedMoment B raw1565step1 raw1565step1Labels := by
      have ha : raw1565step1 = -raw1565step0 := by apply Matrix.ext; change ∀ i j, raw1565step1 i j = -(raw1565step0 i j); unfold raw1565step1 raw1565step0; decide +kernel
      have hl : raw1565step1Labels = raw1565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1565step1 raw1565step1Labels = mixedMoment B raw1565step2 raw1565step2Labels := by
      have ha : raw1565step2 = raw1565step1 := by apply Matrix.ext; unfold raw1565step2 raw1565step1; decide +kernel
      have hl : raw1565step1Labels = labelEmbedding1 ∘ raw1565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1565step1 raw1565step1Labels raw1565step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical1566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1566 raw1566Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw1566 raw1566Labels = mixedMoment B raw1566step0 raw1566step0Labels := by
      have ha : raw1566step0 = (fun i j => raw1566 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1566step0 raw1566; decide +kernel
      have hl : raw1566step0Labels = raw1566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1566 raw1566Labels permutation32 permutation4
    mixedMoment B raw1566step0 raw1566step0Labels = mixedMoment B raw1566step1 raw1566step1Labels := by
      have ha : raw1566step1 = raw1566step0 := by apply Matrix.ext; unfold raw1566step1 raw1566step0; decide +kernel
      have hl : raw1566step0Labels = labelEmbedding7 ∘ raw1566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1566step0 raw1566step0Labels raw1566step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical1567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1567 raw1567Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw1567 raw1567Labels = mixedMoment B raw1567step0 raw1567step0Labels := by
      have ha : raw1567step0 = (fun i j => raw1567 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1567step0 raw1567; decide +kernel
      have hl : raw1567step0Labels = raw1567Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1567 raw1567Labels permutation32 permutation4
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical1568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1568 raw1568Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw1568 raw1568Labels = mixedMoment B raw1568step0 raw1568step0Labels := by
      have ha : raw1568step0 = (fun i j => raw1568 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1568step0 raw1568; decide +kernel
      have hl : raw1568step0Labels = raw1568Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1568 raw1568Labels permutation32 permutation6
    mixedMoment B raw1568step0 raw1568step0Labels = mixedMoment B raw1568step1 raw1568step1Labels := by
      have ha : raw1568step1 = -raw1568step0 := by apply Matrix.ext; change ∀ i j, raw1568step1 i j = -(raw1568step0 i j); unfold raw1568step1 raw1568step0; decide +kernel
      have hl : raw1568step1Labels = raw1568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1568step1 raw1568step1Labels = mixedMoment B raw1568step2 raw1568step2Labels := by
      have ha : raw1568step2 = raw1568step1 := by apply Matrix.ext; unfold raw1568step2 raw1568step1; decide +kernel
      have hl : raw1568step1Labels = labelEmbedding1 ∘ raw1568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1568step1 raw1568step1Labels raw1568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

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

theorem canonical2136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2136 raw2136Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw2136 raw2136Labels = mixedMoment B raw2136step0 raw2136step0Labels := by
      have ha : raw2136step0 = (fun i j => raw2136 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2136step0 raw2136; decide +kernel
      have hl : raw2136step0Labels = raw2136Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2136 raw2136Labels permutation8 permutation4
    mixedMoment B raw2136step0 raw2136step0Labels = mixedMoment B raw2136step1 raw2136step1Labels := by
      have ha : raw2136step1 = raw2136step0 := by apply Matrix.ext; unfold raw2136step1 raw2136step0; decide +kernel
      have hl : raw2136step0Labels = labelEmbedding7 ∘ raw2136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2136step0 raw2136step0Labels raw2136step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

theorem canonical2137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2137 raw2137Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw2137 raw2137Labels = mixedMoment B raw2137step0 raw2137step0Labels := by
      have ha : raw2137step0 = (fun i j => raw2137 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2137step0 raw2137; decide +kernel
      have hl : raw2137step0Labels = raw2137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2137 raw2137Labels permutation8 permutation4
    _ = mixedMoment B node2522 node2522Labels := by rfl

theorem canonical2138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2138 raw2138Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw2138 raw2138Labels = mixedMoment B raw2138step0 raw2138step0Labels := by
      have ha : raw2138step0 = (fun i j => raw2138 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2138step0 raw2138; decide +kernel
      have hl : raw2138step0Labels = raw2138Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2138 raw2138Labels permutation31 permutation6
    mixedMoment B raw2138step0 raw2138step0Labels = mixedMoment B raw2138step1 raw2138step1Labels := by
      have ha : raw2138step1 = raw2138step0 := by apply Matrix.ext; unfold raw2138step1 raw2138step0; decide +kernel
      have hl : raw2138step0Labels = labelEmbedding1 ∘ raw2138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2138step0 raw2138step0Labels raw2138step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

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

theorem canonical2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2250 raw2250Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw2250 raw2250Labels = mixedMoment B raw2250step0 raw2250step0Labels := by
      have ha : raw2250step0 = (fun i j => raw2250 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2250step0 raw2250; decide +kernel
      have hl : raw2250step0Labels = raw2250Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2250 raw2250Labels permutation32 permutation4
    mixedMoment B raw2250step0 raw2250step0Labels = mixedMoment B raw2250step1 raw2250step1Labels := by
      have ha : raw2250step1 = raw2250step0 := by apply Matrix.ext; unfold raw2250step1 raw2250step0; decide +kernel
      have hl : raw2250step0Labels = labelEmbedding7 ∘ raw2250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2250step0 raw2250step0Labels raw2250step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2251 raw2251Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw2251 raw2251Labels = mixedMoment B raw2251step0 raw2251step0Labels := by
      have ha : raw2251step0 = (fun i j => raw2251 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2251step0 raw2251; decide +kernel
      have hl : raw2251step0Labels = raw2251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2251 raw2251Labels permutation32 permutation4
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2252 raw2252Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw2252 raw2252Labels = mixedMoment B raw2252step0 raw2252step0Labels := by
      have ha : raw2252step0 = (fun i j => raw2252 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2252step0 raw2252; decide +kernel
      have hl : raw2252step0Labels = raw2252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2252 raw2252Labels permutation32 permutation6
    mixedMoment B raw2252step0 raw2252step0Labels = mixedMoment B raw2252step1 raw2252step1Labels := by
      have ha : raw2252step1 = -raw2252step0 := by apply Matrix.ext; change ∀ i j, raw2252step1 i j = -(raw2252step0 i j); unfold raw2252step1 raw2252step0; decide +kernel
      have hl : raw2252step1Labels = raw2252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2252step1 raw2252step1Labels = mixedMoment B raw2252step2 raw2252step2Labels := by
      have ha : raw2252step2 = raw2252step1 := by apply Matrix.ext; unfold raw2252step2 raw2252step1; decide +kernel
      have hl : raw2252step1Labels = labelEmbedding1 ∘ raw2252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2252step1 raw2252step1Labels raw2252step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2256 raw2256Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw2256 raw2256Labels = mixedMoment B raw2256step0 raw2256step0Labels := by
      have ha : raw2256step0 = (fun i j => raw2256 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2256step0 raw2256; decide +kernel
      have hl : raw2256step0Labels = raw2256Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2256 raw2256Labels permutation8 permutation4
    mixedMoment B raw2256step0 raw2256step0Labels = mixedMoment B raw2256step1 raw2256step1Labels := by
      have ha : raw2256step1 = raw2256step0 := by apply Matrix.ext; unfold raw2256step1 raw2256step0; decide +kernel
      have hl : raw2256step0Labels = labelEmbedding7 ∘ raw2256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2256step0 raw2256step0Labels raw2256step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2257 raw2257Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw2257 raw2257Labels = mixedMoment B raw2257step0 raw2257step0Labels := by
      have ha : raw2257step0 = (fun i j => raw2257 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2257step0 raw2257; decide +kernel
      have hl : raw2257step0Labels = raw2257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2257 raw2257Labels permutation8 permutation4
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2258 raw2258Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw2258 raw2258Labels = mixedMoment B raw2258step0 raw2258step0Labels := by
      have ha : raw2258step0 = (fun i j => raw2258 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2258step0 raw2258; decide +kernel
      have hl : raw2258step0Labels = raw2258Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2258 raw2258Labels permutation8 permutation6
    mixedMoment B raw2258step0 raw2258step0Labels = mixedMoment B raw2258step1 raw2258step1Labels := by
      have ha : raw2258step1 = -raw2258step0 := by apply Matrix.ext; change ∀ i j, raw2258step1 i j = -(raw2258step0 i j); unfold raw2258step1 raw2258step0; decide +kernel
      have hl : raw2258step1Labels = raw2258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2258step1 raw2258step1Labels = mixedMoment B raw2258step2 raw2258step2Labels := by
      have ha : raw2258step2 = raw2258step1 := by apply Matrix.ext; unfold raw2258step2 raw2258step1; decide +kernel
      have hl : raw2258step1Labels = labelEmbedding1 ∘ raw2258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2258step1 raw2258step1Labels raw2258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3397 node3397Labels := by rfl

theorem canonical2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2259 raw2259Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw2259 raw2259Labels = mixedMoment B raw2259step0 raw2259step0Labels := by
      have ha : raw2259step0 = (fun i j => raw2259 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2259step0 raw2259; decide +kernel
      have hl : raw2259step0Labels = raw2259Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2259 raw2259Labels permutation152 permutation4
    mixedMoment B raw2259step0 raw2259step0Labels = mixedMoment B raw2259step1 raw2259step1Labels := by
      have ha : raw2259step1 = raw2259step0 := by apply Matrix.ext; unfold raw2259step1 raw2259step0; decide +kernel
      have hl : raw2259step0Labels = labelEmbedding7 ∘ raw2259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2259step0 raw2259step0Labels raw2259step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2260 raw2260Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw2260 raw2260Labels = mixedMoment B raw2260step0 raw2260step0Labels := by
      have ha : raw2260step0 = (fun i j => raw2260 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2260step0 raw2260; decide +kernel
      have hl : raw2260step0Labels = raw2260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2260 raw2260Labels permutation152 permutation4
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2261 raw2261Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw2261 raw2261Labels = mixedMoment B raw2261step0 raw2261step0Labels := by
      have ha : raw2261step0 = (fun i j => raw2261 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2261step0 raw2261; decide +kernel
      have hl : raw2261step0Labels = raw2261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2261 raw2261Labels permutation152 permutation6
    mixedMoment B raw2261step0 raw2261step0Labels = mixedMoment B raw2261step1 raw2261step1Labels := by
      have ha : raw2261step1 = -raw2261step0 := by apply Matrix.ext; change ∀ i j, raw2261step1 i j = -(raw2261step0 i j); unfold raw2261step1 raw2261step0; decide +kernel
      have hl : raw2261step1Labels = raw2261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2261step1 raw2261step1Labels = mixedMoment B raw2261step2 raw2261step2Labels := by
      have ha : raw2261step2 = raw2261step1 := by apply Matrix.ext; unfold raw2261step2 raw2261step1; decide +kernel
      have hl : raw2261step1Labels = labelEmbedding1 ∘ raw2261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2261step1 raw2261step1Labels raw2261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3493 node3493Labels := by rfl

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

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

theorem canonical2313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2313 raw2313Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2313 raw2313Labels = mixedMoment B raw2313step0 raw2313step0Labels := by
      have ha : raw2313step0 = (fun i j => raw2313 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2313step0 raw2313; decide +kernel
      have hl : raw2313step0Labels = raw2313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2313 raw2313Labels permutation8 permutation5
    mixedMoment B raw2313step0 raw2313step0Labels = mixedMoment B raw2313step1 raw2313step1Labels := by
      have ha : raw2313step1 = raw2313step0 := by apply Matrix.ext; unfold raw2313step1 raw2313step0; decide +kernel
      have hl : raw2313step0Labels = labelEmbedding8 ∘ raw2313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2313step0 raw2313step0Labels raw2313step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2314 raw2314Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw2314 raw2314Labels = mixedMoment B raw2314step0 raw2314step0Labels := by
      have ha : raw2314step0 = (fun i j => raw2314 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2314step0 raw2314; decide +kernel
      have hl : raw2314step0Labels = raw2314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2314 raw2314Labels permutation8 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical2315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2315 raw2315Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw2315 raw2315Labels = mixedMoment B raw2315step0 raw2315step0Labels := by
      have ha : raw2315step0 = (fun i j => raw2315 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2315step0 raw2315; decide +kernel
      have hl : raw2315step0Labels = raw2315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2315 raw2315Labels permutation11 permutation3
    mixedMoment B raw2315step0 raw2315step0Labels = mixedMoment B raw2315step1 raw2315step1Labels := by
      have ha : raw2315step1 = -raw2315step0 := by apply Matrix.ext; change ∀ i j, raw2315step1 i j = -(raw2315step0 i j); unfold raw2315step1 raw2315step0; decide +kernel
      have hl : raw2315step1Labels = raw2315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2315step1 raw2315step1Labels = mixedMoment B raw2315step2 raw2315step2Labels := by
      have ha : raw2315step2 = raw2315step1 := by apply Matrix.ext; unfold raw2315step2 raw2315step1; decide +kernel
      have hl : raw2315step1Labels = labelEmbedding1 ∘ raw2315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2315step1 raw2315step1Labels raw2315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36038 raw36038Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw36038 raw36038Labels = mixedMoment B raw36038step0 raw36038step0Labels := by
      have hz : ∀ j, raw36038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36038step0 = (fun i j => raw36038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36038step0 raw36038; decide +kernel
      have hl : raw36038step0Labels = raw36038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36038 raw36038Labels permutation346 hz
    mixedMoment B raw36038step0 raw36038step0Labels = mixedMoment B raw36038step1 raw36038step1Labels := by
      have ha : raw36038step1 = (fun i j => raw36038step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36038step1 raw36038step0; decide +kernel
      have hl : raw36038step1Labels = raw36038step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36038step0 raw36038step0Labels permutation58 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical36039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36039 raw36039Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw36039 raw36039Labels = mixedMoment B raw36039step0 raw36039step0Labels := by
      have ha : raw36039step0 = (fun i j => raw36039 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36039step0 raw36039; decide +kernel
      have hl : raw36039step0Labels = raw36039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36039 raw36039Labels permutation267 permutation7
    mixedMoment B raw36039step0 raw36039step0Labels = mixedMoment B raw36039step1 raw36039step1Labels := by
      have ha : raw36039step1 = -raw36039step0 := by apply Matrix.ext; change ∀ i j, raw36039step1 i j = -(raw36039step0 i j); unfold raw36039step1 raw36039step0; decide +kernel
      have hl : raw36039step1Labels = raw36039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36039step1 raw36039step1Labels = mixedMoment B raw36039step2 raw36039step2Labels := by
      have ha : raw36039step2 = raw36039step1 := by apply Matrix.ext; unfold raw36039step2 raw36039step1; decide +kernel
      have hl : raw36039step1Labels = labelEmbedding10 ∘ raw36039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36039step1 raw36039step1Labels raw36039step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical36040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36040 raw36040Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw36040 raw36040Labels = mixedMoment B raw36040step0 raw36040step0Labels := by
      have hz : ∀ j, raw36040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36040step0 = (fun i j => raw36040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36040step0 raw36040; decide +kernel
      have hl : raw36040step0Labels = raw36040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36040 raw36040Labels permutation346 hz
    mixedMoment B raw36040step0 raw36040step0Labels = mixedMoment B raw36040step1 raw36040step1Labels := by
      have ha : raw36040step1 = (fun i j => raw36040step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36040step1 raw36040step0; decide +kernel
      have hl : raw36040step1Labels = raw36040step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36040step0 raw36040step0Labels permutation58 permutation7
    mixedMoment B raw36040step1 raw36040step1Labels = mixedMoment B raw36040step2 raw36040step2Labels := by
      have ha : raw36040step2 = -raw36040step1 := by apply Matrix.ext; change ∀ i j, raw36040step2 i j = -(raw36040step1 i j); unfold raw36040step2 raw36040step1; decide +kernel
      have hl : raw36040step2Labels = raw36040step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36040step2 raw36040step2Labels = mixedMoment B raw36040step3 raw36040step3Labels := by
      have ha : raw36040step3 = raw36040step2 := by apply Matrix.ext; unfold raw36040step3 raw36040step2; decide +kernel
      have hl : raw36040step2Labels = labelEmbedding10 ∘ raw36040step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36040step2 raw36040step2Labels raw36040step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical36041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36041 raw36041Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw36041 raw36041Labels = mixedMoment B raw36041step0 raw36041step0Labels := by
      have hz : ∀ j, raw36041 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36041step0 = (fun i j => raw36041 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36041step0 raw36041; decide +kernel
      have hl : raw36041step0Labels = raw36041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36041 raw36041Labels permutation520 hz
    mixedMoment B raw36041step0 raw36041step0Labels = mixedMoment B raw36041step1 raw36041step1Labels := by
      have hz : ∀ j, raw36041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36041step1 = (fun i j => raw36041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36041step1 raw36041step0; decide +kernel
      have hl : raw36041step1Labels = raw36041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36041step0 raw36041step0Labels permutation80 hz
    mixedMoment B raw36041step1 raw36041step1Labels = mixedMoment B raw36041step2 raw36041step2Labels := by
      have ha : raw36041step2 = (fun i j => raw36041step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36041step2 raw36041step1; decide +kernel
      have hl : raw36041step2Labels = raw36041step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36041step1 raw36041step1Labels permutation14 permutation7
    mixedMoment B raw36041step2 raw36041step2Labels = mixedMoment B raw36041step3 raw36041step3Labels := by
      have ha : raw36041step3 = -raw36041step2 := by apply Matrix.ext; change ∀ i j, raw36041step3 i j = -(raw36041step2 i j); unfold raw36041step3 raw36041step2; decide +kernel
      have hl : raw36041step3Labels = raw36041step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36041step3 raw36041step3Labels = mixedMoment B raw36041step4 raw36041step4Labels := by
      have ha : raw36041step4 = raw36041step3 := by apply Matrix.ext; unfold raw36041step4 raw36041step3; decide +kernel
      have hl : raw36041step3Labels = labelEmbedding10 ∘ raw36041step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36041step3 raw36041step3Labels raw36041step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical36042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36042 raw36042Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw36042 raw36042Labels = mixedMoment B raw36042step0 raw36042step0Labels := by
      have hz : ∀ j, raw36042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36042step0 = (fun i j => raw36042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36042step0 raw36042; decide +kernel
      have hl : raw36042step0Labels = raw36042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36042 raw36042Labels permutation346 hz
    mixedMoment B raw36042step0 raw36042step0Labels = mixedMoment B raw36042step1 raw36042step1Labels := by
      have ha : raw36042step1 = (fun i j => raw36042step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36042step1 raw36042step0; decide +kernel
      have hl : raw36042step1Labels = raw36042step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36042step0 raw36042step0Labels permutation58 permutation7
    mixedMoment B raw36042step1 raw36042step1Labels = mixedMoment B raw36042step2 raw36042step2Labels := by
      have ha : raw36042step2 = -raw36042step1 := by apply Matrix.ext; change ∀ i j, raw36042step2 i j = -(raw36042step1 i j); unfold raw36042step2 raw36042step1; decide +kernel
      have hl : raw36042step2Labels = raw36042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36042step2 raw36042step2Labels = mixedMoment B raw36042step3 raw36042step3Labels := by
      have ha : raw36042step3 = raw36042step2 := by apply Matrix.ext; unfold raw36042step3 raw36042step2; decide +kernel
      have hl : raw36042step2Labels = labelEmbedding10 ∘ raw36042step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36042step2 raw36042step2Labels raw36042step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical36043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36043 raw36043Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw36043 raw36043Labels = mixedMoment B raw36043step0 raw36043step0Labels := by
      have hz : ∀ j, raw36043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36043step0 = (fun i j => raw36043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36043step0 raw36043; decide +kernel
      have hl : raw36043step0Labels = raw36043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36043 raw36043Labels permutation346 hz
    mixedMoment B raw36043step0 raw36043step0Labels = mixedMoment B raw36043step1 raw36043step1Labels := by
      have ha : raw36043step1 = (fun i j => raw36043step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36043step1 raw36043step0; decide +kernel
      have hl : raw36043step1Labels = raw36043step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36043step0 raw36043step0Labels permutation32 permutation3
    mixedMoment B raw36043step1 raw36043step1Labels = mixedMoment B raw36043step2 raw36043step2Labels := by
      have ha : raw36043step2 = raw36043step1 := by apply Matrix.ext; unfold raw36043step2 raw36043step1; decide +kernel
      have hl : raw36043step1Labels = labelEmbedding6 ∘ raw36043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36043step1 raw36043step1Labels raw36043step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

theorem canonical36044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36044 raw36044Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw36044 raw36044Labels = mixedMoment B raw36044step0 raw36044step0Labels := by
      have ha : raw36044step0 = (fun i j => raw36044 (permutation326 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36044step0 raw36044; decide +kernel
      have hl : raw36044step0Labels = raw36044Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36044 raw36044Labels permutation326 permutation6
    mixedMoment B raw36044step0 raw36044step0Labels = mixedMoment B raw36044step1 raw36044step1Labels := by
      have ha : raw36044step1 = -raw36044step0 := by apply Matrix.ext; change ∀ i j, raw36044step1 i j = -(raw36044step0 i j); unfold raw36044step1 raw36044step0; decide +kernel
      have hl : raw36044step1Labels = raw36044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36044step1 raw36044step1Labels = mixedMoment B raw36044step2 raw36044step2Labels := by
      have ha : raw36044step2 = raw36044step1 := by apply Matrix.ext; unfold raw36044step2 raw36044step1; decide +kernel
      have hl : raw36044step1Labels = labelEmbedding9 ∘ raw36044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36044step1 raw36044step1Labels raw36044step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

theorem canonical36045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36045 raw36045Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw36045 raw36045Labels = mixedMoment B raw36045step0 raw36045step0Labels := by
      have hz : ∀ j, raw36045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36045step0 = (fun i j => raw36045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36045step0 raw36045; decide +kernel
      have hl : raw36045step0Labels = raw36045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36045 raw36045Labels permutation346 hz
    mixedMoment B raw36045step0 raw36045step0Labels = mixedMoment B raw36045step1 raw36045step1Labels := by
      have ha : raw36045step1 = (fun i j => raw36045step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36045step1 raw36045step0; decide +kernel
      have hl : raw36045step1Labels = raw36045step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36045step0 raw36045step0Labels permutation68 permutation6
    mixedMoment B raw36045step1 raw36045step1Labels = mixedMoment B raw36045step2 raw36045step2Labels := by
      have ha : raw36045step2 = -raw36045step1 := by apply Matrix.ext; change ∀ i j, raw36045step2 i j = -(raw36045step1 i j); unfold raw36045step2 raw36045step1; decide +kernel
      have hl : raw36045step2Labels = raw36045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36045step2 raw36045step2Labels = mixedMoment B raw36045step3 raw36045step3Labels := by
      have ha : raw36045step3 = raw36045step2 := by apply Matrix.ext; unfold raw36045step3 raw36045step2; decide +kernel
      have hl : raw36045step2Labels = labelEmbedding9 ∘ raw36045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36045step2 raw36045step2Labels raw36045step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical36046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36046 raw36046Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw36046 raw36046Labels = mixedMoment B raw36046step0 raw36046step0Labels := by
      have hz : ∀ j, raw36046 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36046step0 = (fun i j => raw36046 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36046step0 raw36046; decide +kernel
      have hl : raw36046step0Labels = raw36046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36046 raw36046Labels permutation520 hz
    mixedMoment B raw36046step0 raw36046step0Labels = mixedMoment B raw36046step1 raw36046step1Labels := by
      have hz : ∀ j, raw36046step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36046step1 = (fun i j => raw36046step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36046step1 raw36046step0; decide +kernel
      have hl : raw36046step1Labels = raw36046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36046step0 raw36046step0Labels permutation80 hz
    mixedMoment B raw36046step1 raw36046step1Labels = mixedMoment B raw36046step2 raw36046step2Labels := by
      have ha : raw36046step2 = (fun i j => raw36046step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36046step2 raw36046step1; decide +kernel
      have hl : raw36046step2Labels = raw36046step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36046step1 raw36046step1Labels permutation14 permutation6
    mixedMoment B raw36046step2 raw36046step2Labels = mixedMoment B raw36046step3 raw36046step3Labels := by
      have ha : raw36046step3 = -raw36046step2 := by apply Matrix.ext; change ∀ i j, raw36046step3 i j = -(raw36046step2 i j); unfold raw36046step3 raw36046step2; decide +kernel
      have hl : raw36046step3Labels = raw36046step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36046step3 raw36046step3Labels = mixedMoment B raw36046step4 raw36046step4Labels := by
      have ha : raw36046step4 = raw36046step3 := by apply Matrix.ext; unfold raw36046step4 raw36046step3; decide +kernel
      have hl : raw36046step3Labels = labelEmbedding9 ∘ raw36046step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36046step3 raw36046step3Labels raw36046step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical36047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36047 raw36047Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw36047 raw36047Labels = mixedMoment B raw36047step0 raw36047step0Labels := by
      have hz : ∀ j, raw36047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36047step0 = (fun i j => raw36047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36047step0 raw36047; decide +kernel
      have hl : raw36047step0Labels = raw36047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36047 raw36047Labels permutation346 hz
    mixedMoment B raw36047step0 raw36047step0Labels = mixedMoment B raw36047step1 raw36047step1Labels := by
      have ha : raw36047step1 = (fun i j => raw36047step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36047step1 raw36047step0; decide +kernel
      have hl : raw36047step1Labels = raw36047step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36047step0 raw36047step0Labels permutation68 permutation6
    mixedMoment B raw36047step1 raw36047step1Labels = mixedMoment B raw36047step2 raw36047step2Labels := by
      have ha : raw36047step2 = -raw36047step1 := by apply Matrix.ext; change ∀ i j, raw36047step2 i j = -(raw36047step1 i j); unfold raw36047step2 raw36047step1; decide +kernel
      have hl : raw36047step2Labels = raw36047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36047step2 raw36047step2Labels = mixedMoment B raw36047step3 raw36047step3Labels := by
      have ha : raw36047step3 = raw36047step2 := by apply Matrix.ext; unfold raw36047step3 raw36047step2; decide +kernel
      have hl : raw36047step2Labels = labelEmbedding9 ∘ raw36047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36047step2 raw36047step2Labels raw36047step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical36048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36048 raw36048Labels = mixedMoment B node4698 node4698Labels := by
  calc
    mixedMoment B raw36048 raw36048Labels = mixedMoment B raw36048step0 raw36048step0Labels := by
      have ha : raw36048step0 = (fun i j => raw36048 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36048step0 raw36048; decide +kernel
      have hl : raw36048step0Labels = raw36048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36048 raw36048Labels permutation158 permutation3
    mixedMoment B raw36048step0 raw36048step0Labels = mixedMoment B raw36048step1 raw36048step1Labels := by
      have ha : raw36048step1 = raw36048step0 := by apply Matrix.ext; unfold raw36048step1 raw36048step0; decide +kernel
      have hl : raw36048step0Labels = labelEmbedding6 ∘ raw36048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36048step0 raw36048step0Labels raw36048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4698 node4698Labels := by rfl

theorem canonical36049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36049 raw36049Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw36049 raw36049Labels = mixedMoment B raw36049step0 raw36049step0Labels := by
      have ha : raw36049step0 = (fun i j => raw36049 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36049step0 raw36049; decide +kernel
      have hl : raw36049step0Labels = raw36049Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36049 raw36049Labels permutation267 permutation2
    _ = mixedMoment B node4676 node4676Labels := by rfl

theorem canonical36050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36050 raw36050Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw36050 raw36050Labels = mixedMoment B raw36050step0 raw36050step0Labels := by
      have ha : raw36050step0 = (fun i j => raw36050 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36050step0 raw36050; decide +kernel
      have hl : raw36050step0Labels = raw36050Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36050 raw36050Labels permutation267 permutation7
    mixedMoment B raw36050step0 raw36050step0Labels = mixedMoment B raw36050step1 raw36050step1Labels := by
      have ha : raw36050step1 = -raw36050step0 := by apply Matrix.ext; change ∀ i j, raw36050step1 i j = -(raw36050step0 i j); unfold raw36050step1 raw36050step0; decide +kernel
      have hl : raw36050step1Labels = raw36050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36050step1 raw36050step1Labels = mixedMoment B raw36050step2 raw36050step2Labels := by
      have ha : raw36050step2 = raw36050step1 := by apply Matrix.ext; unfold raw36050step2 raw36050step1; decide +kernel
      have hl : raw36050step1Labels = labelEmbedding10 ∘ raw36050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36050step1 raw36050step1Labels raw36050step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

theorem canonical36051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36051 raw36051Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw36051 raw36051Labels = mixedMoment B raw36051step0 raw36051step0Labels := by
      have hz : ∀ j, raw36051 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36051step0 = (fun i j => raw36051 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36051step0 raw36051; decide +kernel
      have hl : raw36051step0Labels = raw36051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36051 raw36051Labels permutation520 hz
    mixedMoment B raw36051step0 raw36051step0Labels = mixedMoment B raw36051step1 raw36051step1Labels := by
      have ha : raw36051step1 = (fun i j => raw36051step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36051step1 raw36051step0; decide +kernel
      have hl : raw36051step1Labels = raw36051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36051step0 raw36051step0Labels permutation56 permutation7
    mixedMoment B raw36051step1 raw36051step1Labels = mixedMoment B raw36051step2 raw36051step2Labels := by
      have ha : raw36051step2 = -raw36051step1 := by apply Matrix.ext; change ∀ i j, raw36051step2 i j = -(raw36051step1 i j); unfold raw36051step2 raw36051step1; decide +kernel
      have hl : raw36051step2Labels = raw36051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36051step2 raw36051step2Labels = mixedMoment B raw36051step3 raw36051step3Labels := by
      have ha : raw36051step3 = raw36051step2 := by apply Matrix.ext; unfold raw36051step3 raw36051step2; decide +kernel
      have hl : raw36051step2Labels = labelEmbedding10 ∘ raw36051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36051step2 raw36051step2Labels raw36051step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical36052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36052 raw36052Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw36052 raw36052Labels = mixedMoment B raw36052step0 raw36052step0Labels := by
      have ha : raw36052step0 = (fun i j => raw36052 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36052step0 raw36052; decide +kernel
      have hl : raw36052step0Labels = raw36052Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36052 raw36052Labels permutation267 permutation7
    mixedMoment B raw36052step0 raw36052step0Labels = mixedMoment B raw36052step1 raw36052step1Labels := by
      have ha : raw36052step1 = -raw36052step0 := by apply Matrix.ext; change ∀ i j, raw36052step1 i j = -(raw36052step0 i j); unfold raw36052step1 raw36052step0; decide +kernel
      have hl : raw36052step1Labels = raw36052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36052step1 raw36052step1Labels = mixedMoment B raw36052step2 raw36052step2Labels := by
      have ha : raw36052step2 = raw36052step1 := by apply Matrix.ext; unfold raw36052step2 raw36052step1; decide +kernel
      have hl : raw36052step1Labels = labelEmbedding10 ∘ raw36052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36052step1 raw36052step1Labels raw36052step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

theorem canonical36053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36053 raw36053Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw36053 raw36053Labels = mixedMoment B raw36053step0 raw36053step0Labels := by
      have hz : ∀ j, raw36053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36053step0 = (fun i j => raw36053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36053step0 raw36053; decide +kernel
      have hl : raw36053step0Labels = raw36053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36053 raw36053Labels permutation346 hz
    mixedMoment B raw36053step0 raw36053step0Labels = mixedMoment B raw36053step1 raw36053step1Labels := by
      have ha : raw36053step1 = (fun i j => raw36053step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36053step1 raw36053step0; decide +kernel
      have hl : raw36053step1Labels = raw36053step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36053step0 raw36053step0Labels permutation35 permutation3
    mixedMoment B raw36053step1 raw36053step1Labels = mixedMoment B raw36053step2 raw36053step2Labels := by
      have ha : raw36053step2 = raw36053step1 := by apply Matrix.ext; unfold raw36053step2 raw36053step1; decide +kernel
      have hl : raw36053step1Labels = labelEmbedding6 ∘ raw36053step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36053step1 raw36053step1Labels raw36053step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4703 node4703Labels := by rfl

theorem canonical36054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36054 raw36054Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw36054 raw36054Labels = mixedMoment B raw36054step0 raw36054step0Labels := by
      have hz : ∀ j, raw36054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36054step0 = (fun i j => raw36054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36054step0 raw36054; decide +kernel
      have hl : raw36054step0Labels = raw36054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36054 raw36054Labels permutation346 hz
    mixedMoment B raw36054step0 raw36054step0Labels = mixedMoment B raw36054step1 raw36054step1Labels := by
      have ha : raw36054step1 = (fun i j => raw36054step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36054step1 raw36054step0; decide +kernel
      have hl : raw36054step1Labels = raw36054step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36054step0 raw36054step0Labels permutation58 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical36055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36055 raw36055Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw36055 raw36055Labels = mixedMoment B raw36055step0 raw36055step0Labels := by
      have ha : raw36055step0 = (fun i j => raw36055 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36055step0 raw36055; decide +kernel
      have hl : raw36055step0Labels = raw36055Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36055 raw36055Labels permutation267 permutation7
    mixedMoment B raw36055step0 raw36055step0Labels = mixedMoment B raw36055step1 raw36055step1Labels := by
      have ha : raw36055step1 = -raw36055step0 := by apply Matrix.ext; change ∀ i j, raw36055step1 i j = -(raw36055step0 i j); unfold raw36055step1 raw36055step0; decide +kernel
      have hl : raw36055step1Labels = raw36055step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36055step1 raw36055step1Labels = mixedMoment B raw36055step2 raw36055step2Labels := by
      have ha : raw36055step2 = raw36055step1 := by apply Matrix.ext; unfold raw36055step2 raw36055step1; decide +kernel
      have hl : raw36055step1Labels = labelEmbedding10 ∘ raw36055step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36055step1 raw36055step1Labels raw36055step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

theorem canonical36056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36056 raw36056Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw36056 raw36056Labels = mixedMoment B raw36056step0 raw36056step0Labels := by
      have hz : ∀ j, raw36056 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36056step0 = (fun i j => raw36056 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36056step0 raw36056; decide +kernel
      have hl : raw36056step0Labels = raw36056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36056 raw36056Labels permutation520 hz
    mixedMoment B raw36056step0 raw36056step0Labels = mixedMoment B raw36056step1 raw36056step1Labels := by
      have hz : ∀ j, raw36056step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36056step1 = (fun i j => raw36056step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36056step1 raw36056step0; decide +kernel
      have hl : raw36056step1Labels = raw36056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36056step0 raw36056step0Labels permutation80 hz
    mixedMoment B raw36056step1 raw36056step1Labels = mixedMoment B raw36056step2 raw36056step2Labels := by
      have ha : raw36056step2 = (fun i j => raw36056step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36056step2 raw36056step1; decide +kernel
      have hl : raw36056step2Labels = raw36056step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36056step1 raw36056step1Labels permutation14 permutation7
    mixedMoment B raw36056step2 raw36056step2Labels = mixedMoment B raw36056step3 raw36056step3Labels := by
      have ha : raw36056step3 = -raw36056step2 := by apply Matrix.ext; change ∀ i j, raw36056step3 i j = -(raw36056step2 i j); unfold raw36056step3 raw36056step2; decide +kernel
      have hl : raw36056step3Labels = raw36056step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36056step3 raw36056step3Labels = mixedMoment B raw36056step4 raw36056step4Labels := by
      have ha : raw36056step4 = raw36056step3 := by apply Matrix.ext; unfold raw36056step4 raw36056step3; decide +kernel
      have hl : raw36056step3Labels = labelEmbedding10 ∘ raw36056step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36056step3 raw36056step3Labels raw36056step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical36057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36057 raw36057Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw36057 raw36057Labels = mixedMoment B raw36057step0 raw36057step0Labels := by
      have hz : ∀ j, raw36057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36057step0 = (fun i j => raw36057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36057step0 raw36057; decide +kernel
      have hl : raw36057step0Labels = raw36057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36057 raw36057Labels permutation346 hz
    mixedMoment B raw36057step0 raw36057step0Labels = mixedMoment B raw36057step1 raw36057step1Labels := by
      have ha : raw36057step1 = (fun i j => raw36057step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36057step1 raw36057step0; decide +kernel
      have hl : raw36057step1Labels = raw36057step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36057step0 raw36057step0Labels permutation58 permutation7
    mixedMoment B raw36057step1 raw36057step1Labels = mixedMoment B raw36057step2 raw36057step2Labels := by
      have ha : raw36057step2 = -raw36057step1 := by apply Matrix.ext; change ∀ i j, raw36057step2 i j = -(raw36057step1 i j); unfold raw36057step2 raw36057step1; decide +kernel
      have hl : raw36057step2Labels = raw36057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36057step2 raw36057step2Labels = mixedMoment B raw36057step3 raw36057step3Labels := by
      have ha : raw36057step3 = raw36057step2 := by apply Matrix.ext; unfold raw36057step3 raw36057step2; decide +kernel
      have hl : raw36057step2Labels = labelEmbedding10 ∘ raw36057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36057step2 raw36057step2Labels raw36057step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

theorem canonical36058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36058 raw36058Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw36058 raw36058Labels = mixedMoment B raw36058step0 raw36058step0Labels := by
      have hz : ∀ j, raw36058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36058step0 = (fun i j => raw36058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36058step0 raw36058; decide +kernel
      have hl : raw36058step0Labels = raw36058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36058 raw36058Labels permutation346 hz
    mixedMoment B raw36058step0 raw36058step0Labels = mixedMoment B raw36058step1 raw36058step1Labels := by
      have ha : raw36058step1 = (fun i j => raw36058step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36058step1 raw36058step0; decide +kernel
      have hl : raw36058step1Labels = raw36058step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36058step0 raw36058step0Labels permutation33 permutation3
    mixedMoment B raw36058step1 raw36058step1Labels = mixedMoment B raw36058step2 raw36058step2Labels := by
      have ha : raw36058step2 = raw36058step1 := by apply Matrix.ext; unfold raw36058step2 raw36058step1; decide +kernel
      have hl : raw36058step1Labels = labelEmbedding6 ∘ raw36058step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36058step1 raw36058step1Labels raw36058step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4700 node4700Labels := by rfl

theorem canonical36059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36059 raw36059Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw36059 raw36059Labels = mixedMoment B raw36059step0 raw36059step0Labels := by
      have hz : ∀ j, raw36059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36059step0 = (fun i j => raw36059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36059step0 raw36059; decide +kernel
      have hl : raw36059step0Labels = raw36059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36059 raw36059Labels permutation346 hz
    mixedMoment B raw36059step0 raw36059step0Labels = mixedMoment B raw36059step1 raw36059step1Labels := by
      have ha : raw36059step1 = (fun i j => raw36059step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36059step1 raw36059step0; decide +kernel
      have hl : raw36059step1Labels = raw36059step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36059step0 raw36059step0Labels permutation56 permutation2
    _ = mixedMoment B node4688 node4688Labels := by rfl

theorem canonical36060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36060 raw36060Labels = mixedMoment B node5216 node5216Labels := by
  calc
    mixedMoment B raw36060 raw36060Labels = mixedMoment B raw36060step0 raw36060step0Labels := by
      have ha : raw36060step0 = (fun i j => raw36060 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36060step0 raw36060; decide +kernel
      have hl : raw36060step0Labels = raw36060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36060 raw36060Labels permutation267 permutation7
    mixedMoment B raw36060step0 raw36060step0Labels = mixedMoment B raw36060step1 raw36060step1Labels := by
      have ha : raw36060step1 = -raw36060step0 := by apply Matrix.ext; change ∀ i j, raw36060step1 i j = -(raw36060step0 i j); unfold raw36060step1 raw36060step0; decide +kernel
      have hl : raw36060step1Labels = raw36060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36060step1 raw36060step1Labels = mixedMoment B raw36060step2 raw36060step2Labels := by
      have ha : raw36060step2 = raw36060step1 := by apply Matrix.ext; unfold raw36060step2 raw36060step1; decide +kernel
      have hl : raw36060step1Labels = labelEmbedding10 ∘ raw36060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36060step1 raw36060step1Labels raw36060step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5216 node5216Labels := by rfl

theorem canonical36061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36061 raw36061Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw36061 raw36061Labels = mixedMoment B raw36061step0 raw36061step0Labels := by
      have hz : ∀ j, raw36061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36061step0 = (fun i j => raw36061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36061step0 raw36061; decide +kernel
      have hl : raw36061step0Labels = raw36061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36061 raw36061Labels permutation346 hz
    mixedMoment B raw36061step0 raw36061step0Labels = mixedMoment B raw36061step1 raw36061step1Labels := by
      have ha : raw36061step1 = (fun i j => raw36061step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36061step1 raw36061step0; decide +kernel
      have hl : raw36061step1Labels = raw36061step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36061step0 raw36061step0Labels permutation58 permutation7
    mixedMoment B raw36061step1 raw36061step1Labels = mixedMoment B raw36061step2 raw36061step2Labels := by
      have ha : raw36061step2 = -raw36061step1 := by apply Matrix.ext; change ∀ i j, raw36061step2 i j = -(raw36061step1 i j); unfold raw36061step2 raw36061step1; decide +kernel
      have hl : raw36061step2Labels = raw36061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36061step2 raw36061step2Labels = mixedMoment B raw36061step3 raw36061step3Labels := by
      have ha : raw36061step3 = raw36061step2 := by apply Matrix.ext; unfold raw36061step3 raw36061step2; decide +kernel
      have hl : raw36061step2Labels = labelEmbedding10 ∘ raw36061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36061step2 raw36061step2Labels raw36061step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical36062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36062 raw36062Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw36062 raw36062Labels = mixedMoment B raw36062step0 raw36062step0Labels := by
      have hz : ∀ j, raw36062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36062step0 = (fun i j => raw36062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36062step0 raw36062; decide +kernel
      have hl : raw36062step0Labels = raw36062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36062 raw36062Labels permutation346 hz
    mixedMoment B raw36062step0 raw36062step0Labels = mixedMoment B raw36062step1 raw36062step1Labels := by
      have ha : raw36062step1 = (fun i j => raw36062step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36062step1 raw36062step0; decide +kernel
      have hl : raw36062step1Labels = raw36062step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36062step0 raw36062step0Labels permutation58 permutation7
    mixedMoment B raw36062step1 raw36062step1Labels = mixedMoment B raw36062step2 raw36062step2Labels := by
      have ha : raw36062step2 = -raw36062step1 := by apply Matrix.ext; change ∀ i j, raw36062step2 i j = -(raw36062step1 i j); unfold raw36062step2 raw36062step1; decide +kernel
      have hl : raw36062step2Labels = raw36062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36062step2 raw36062step2Labels = mixedMoment B raw36062step3 raw36062step3Labels := by
      have ha : raw36062step3 = raw36062step2 := by apply Matrix.ext; unfold raw36062step3 raw36062step2; decide +kernel
      have hl : raw36062step2Labels = labelEmbedding10 ∘ raw36062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36062step2 raw36062step2Labels raw36062step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

theorem canonical36063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36063 raw36063Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw36063 raw36063Labels = mixedMoment B raw36063step0 raw36063step0Labels := by
      have hz : ∀ j, raw36063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36063step0 = (fun i j => raw36063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36063step0 raw36063; decide +kernel
      have hl : raw36063step0Labels = raw36063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36063 raw36063Labels permutation346 hz
    mixedMoment B raw36063step0 raw36063step0Labels = mixedMoment B raw36063step1 raw36063step1Labels := by
      have ha : raw36063step1 = (fun i j => raw36063step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36063step1 raw36063step0; decide +kernel
      have hl : raw36063step1Labels = raw36063step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36063step0 raw36063step0Labels permutation32 permutation3
    mixedMoment B raw36063step1 raw36063step1Labels = mixedMoment B raw36063step2 raw36063step2Labels := by
      have ha : raw36063step2 = raw36063step1 := by apply Matrix.ext; unfold raw36063step2 raw36063step1; decide +kernel
      have hl : raw36063step1Labels = labelEmbedding6 ∘ raw36063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36063step1 raw36063step1Labels raw36063step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4699 node4699Labels := by rfl

theorem canonical36064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36064 raw36064Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw36064 raw36064Labels = mixedMoment B raw36064step0 raw36064step0Labels := by
      have hz : ∀ j, raw36064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36064step0 = (fun i j => raw36064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36064step0 raw36064; decide +kernel
      have hl : raw36064step0Labels = raw36064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36064 raw36064Labels permutation346 hz
    mixedMoment B raw36064step0 raw36064step0Labels = mixedMoment B raw36064step1 raw36064step1Labels := by
      have ha : raw36064step1 = (fun i j => raw36064step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36064step1 raw36064step0; decide +kernel
      have hl : raw36064step1Labels = raw36064step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36064step0 raw36064step0Labels permutation58 permutation2
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical36065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36065 raw36065Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw36065 raw36065Labels = mixedMoment B raw36065step0 raw36065step0Labels := by
      have ha : raw36065step0 = (fun i j => raw36065 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36065step0 raw36065; decide +kernel
      have hl : raw36065step0Labels = raw36065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36065 raw36065Labels permutation663 permutation2
    mixedMoment B raw36065step0 raw36065step0Labels = mixedMoment B raw36065step1 raw36065step1Labels := by
      have ha : raw36065step1 = -raw36065step0 := by apply Matrix.ext; change ∀ i j, raw36065step1 i j = -(raw36065step0 i j); unfold raw36065step1 raw36065step0; decide +kernel
      have hl : raw36065step1Labels = raw36065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5035 node5035Labels := by rfl

theorem canonical36066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36066 raw36066Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw36066 raw36066Labels = mixedMoment B raw36066step0 raw36066step0Labels := by
      have hz : ∀ j, raw36066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36066step0 = (fun i j => raw36066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36066step0 raw36066; decide +kernel
      have hl : raw36066step0Labels = raw36066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36066 raw36066Labels permutation346 hz
    mixedMoment B raw36066step0 raw36066step0Labels = mixedMoment B raw36066step1 raw36066step1Labels := by
      have ha : raw36066step1 = (fun i j => raw36066step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36066step1 raw36066step0; decide +kernel
      have hl : raw36066step1Labels = raw36066step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36066step0 raw36066step0Labels permutation150 permutation2
    mixedMoment B raw36066step1 raw36066step1Labels = mixedMoment B raw36066step2 raw36066step2Labels := by
      have ha : raw36066step2 = -raw36066step1 := by apply Matrix.ext; change ∀ i j, raw36066step2 i j = -(raw36066step1 i j); unfold raw36066step2 raw36066step1; decide +kernel
      have hl : raw36066step2Labels = raw36066step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5140 node5140Labels := by rfl

theorem canonical36067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36067 raw36067Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw36067 raw36067Labels = mixedMoment B raw36067step0 raw36067step0Labels := by
      have hz : ∀ j, raw36067 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36067step0 = (fun i j => raw36067 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36067step0 raw36067; decide +kernel
      have hl : raw36067step0Labels = raw36067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36067 raw36067Labels permutation520 hz
    mixedMoment B raw36067step0 raw36067step0Labels = mixedMoment B raw36067step1 raw36067step1Labels := by
      have hz : ∀ j, raw36067step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36067step1 = (fun i j => raw36067step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36067step1 raw36067step0; decide +kernel
      have hl : raw36067step1Labels = raw36067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36067step0 raw36067step0Labels permutation80 hz
    mixedMoment B raw36067step1 raw36067step1Labels = mixedMoment B raw36067step2 raw36067step2Labels := by
      have ha : raw36067step2 = (fun i j => raw36067step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36067step2 raw36067step1; decide +kernel
      have hl : raw36067step2Labels = raw36067step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36067step1 raw36067step1Labels permutation30 permutation2
    mixedMoment B raw36067step2 raw36067step2Labels = mixedMoment B raw36067step3 raw36067step3Labels := by
      have ha : raw36067step3 = -raw36067step2 := by apply Matrix.ext; change ∀ i j, raw36067step3 i j = -(raw36067step2 i j); unfold raw36067step3 raw36067step2; decide +kernel
      have hl : raw36067step3Labels = raw36067step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5110 node5110Labels := by rfl

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

theorem singleton4676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4676 node4676Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1802 node1802Labels + mixedMoment B node2141 node2141Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1554 singletonSmall4676
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4676) = raw1554Labels := by decide +kernel
  rw [hl, canonical1554 B hB] at h
  have hc0 : mixedMoment B raw1554 (Fin.cases (0 : Fin 2) singletonSmall4676) =
      mixedMoment B node1802 node1802Labels := by
    have ha : raw1554 = raw1555 := by apply Matrix.ext; unfold raw1554 raw1555; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4676 = raw1555Labels := by decide +kernel
    rw [ha, hj, canonical1555 B hB]
  have hc1 : mixedMoment B raw1554 (Fin.cases (1 : Fin 2) singletonSmall4676) =
      mixedMoment B node2141 node2141Labels := by
    have ha : raw1554 = raw1556 := by apply Matrix.ext; unfold raw1554 raw1556; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4676 = raw1556Labels := by decide +kernel
    rw [ha, hj, canonical1556 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4681 node4681Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1807 node1807Labels + mixedMoment B node2151 node2151Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1563 singletonSmall4681
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4681) = raw1563Labels := by decide +kernel
  rw [hl, canonical1563 B hB] at h
  have hc0 : mixedMoment B raw1563 (Fin.cases (0 : Fin 2) singletonSmall4681) =
      mixedMoment B node1807 node1807Labels := by
    have ha : raw1563 = raw1564 := by apply Matrix.ext; unfold raw1563 raw1564; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4681 = raw1564Labels := by decide +kernel
    rw [ha, hj, canonical1564 B hB]
  have hc1 : mixedMoment B raw1563 (Fin.cases (1 : Fin 2) singletonSmall4681) =
      mixedMoment B node2151 node2151Labels := by
    have ha : raw1563 = raw1565 := by apply Matrix.ext; unfold raw1563 raw1565; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4681 = raw1565Labels := by decide +kernel
    rw [ha, hj, canonical1565 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4684 node4684Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1810 node1810Labels + mixedMoment B node2152 node2152Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1566 singletonSmall4684
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4684) = raw1566Labels := by decide +kernel
  rw [hl, canonical1566 B hB] at h
  have hc0 : mixedMoment B raw1566 (Fin.cases (0 : Fin 2) singletonSmall4684) =
      mixedMoment B node1810 node1810Labels := by
    have ha : raw1566 = raw1567 := by apply Matrix.ext; unfold raw1566 raw1567; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4684 = raw1567Labels := by decide +kernel
    rw [ha, hj, canonical1567 B hB]
  have hc1 : mixedMoment B raw1566 (Fin.cases (1 : Fin 2) singletonSmall4684) =
      mixedMoment B node2152 node2152Labels := by
    have ha : raw1566 = raw1568 := by apply Matrix.ext; unfold raw1566 raw1568; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4684 = raw1568Labels := by decide +kernel
    rw [ha, hj, canonical1568 B hB]
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

theorem singleton5110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5110 node5110Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2522 node2522Labels + mixedMoment B node2685 node2685Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2136 singletonSmall5110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5110) = raw2136Labels := by decide +kernel
  rw [hl, canonical2136 B hB] at h
  have hc0 : mixedMoment B raw2136 (Fin.cases (0 : Fin 2) singletonSmall5110) =
      mixedMoment B node2522 node2522Labels := by
    have ha : raw2136 = raw2137 := by apply Matrix.ext; unfold raw2136 raw2137; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5110 = raw2137Labels := by decide +kernel
    rw [ha, hj, canonical2137 B hB]
  have hc1 : mixedMoment B raw2136 (Fin.cases (1 : Fin 2) singletonSmall5110) =
      mixedMoment B node2685 node2685Labels := by
    have ha : raw2136 = raw2138 := by apply Matrix.ext; unfold raw2136 raw2138; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5110 = raw2138Labels := by decide +kernel
    rw [ha, hj, canonical2138 B hB]
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

theorem singleton5228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5228 node5228Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2672 node2672Labels + mixedMoment B node3391 node3391Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2250 singletonSmall5228
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5228) = raw2250Labels := by decide +kernel
  rw [hl, canonical2250 B hB] at h
  have hc0 : mixedMoment B raw2250 (Fin.cases (0 : Fin 2) singletonSmall5228) =
      mixedMoment B node2672 node2672Labels := by
    have ha : raw2250 = raw2251 := by apply Matrix.ext; unfold raw2250 raw2251; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5228 = raw2251Labels := by decide +kernel
    rw [ha, hj, canonical2251 B hB]
  have hc1 : mixedMoment B raw2250 (Fin.cases (1 : Fin 2) singletonSmall5228) =
      mixedMoment B node3391 node3391Labels := by
    have ha : raw2250 = raw2252 := by apply Matrix.ext; unfold raw2250 raw2252; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5228 = raw2252Labels := by decide +kernel
    rw [ha, hj, canonical2252 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5238 node5238Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2686 node2686Labels + mixedMoment B node3397 node3397Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2256 singletonSmall5238
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5238) = raw2256Labels := by decide +kernel
  rw [hl, canonical2256 B hB] at h
  have hc0 : mixedMoment B raw2256 (Fin.cases (0 : Fin 2) singletonSmall5238) =
      mixedMoment B node2686 node2686Labels := by
    have ha : raw2256 = raw2257 := by apply Matrix.ext; unfold raw2256 raw2257; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5238 = raw2257Labels := by decide +kernel
    rw [ha, hj, canonical2257 B hB]
  have hc1 : mixedMoment B raw2256 (Fin.cases (1 : Fin 2) singletonSmall5238) =
      mixedMoment B node3397 node3397Labels := by
    have ha : raw2256 = raw2258 := by apply Matrix.ext; unfold raw2256 raw2258; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5238 = raw2258Labels := by decide +kernel
    rw [ha, hj, canonical2258 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5241 node5241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2694 node2694Labels + mixedMoment B node3493 node3493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2259 singletonSmall5241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5241) = raw2259Labels := by decide +kernel
  rw [hl, canonical2259 B hB] at h
  have hc0 : mixedMoment B raw2259 (Fin.cases (0 : Fin 2) singletonSmall5241) =
      mixedMoment B node2694 node2694Labels := by
    have ha : raw2259 = raw2260 := by apply Matrix.ext; unfold raw2259 raw2260; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5241 = raw2260Labels := by decide +kernel
    rw [ha, hj, canonical2260 B hB]
  have hc1 : mixedMoment B raw2259 (Fin.cases (1 : Fin 2) singletonSmall5241) =
      mixedMoment B node3493 node3493Labels := by
    have ha : raw2259 = raw2261 := by apply Matrix.ext; unfold raw2259 raw2261; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5241 = raw2261Labels := by decide +kernel
    rw [ha, hj, canonical2261 B hB]
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

theorem singleton5258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5258 node5258Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2722 node2722Labels + mixedMoment B node3533 node3533Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2271 singletonSmall5258
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5258) = raw2271Labels := by decide +kernel
  rw [hl, canonical2271 B hB] at h
  have hc0 : mixedMoment B raw2271 (Fin.cases (0 : Fin 2) singletonSmall5258) =
      mixedMoment B node2722 node2722Labels := by
    have ha : raw2271 = raw2272 := by apply Matrix.ext; unfold raw2271 raw2272; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5258 = raw2272Labels := by decide +kernel
    rw [ha, hj, canonical2272 B hB]
  have hc1 : mixedMoment B raw2271 (Fin.cases (1 : Fin 2) singletonSmall5258) =
      mixedMoment B node3533 node3533Labels := by
    have ha : raw2271 = raw2273 := by apply Matrix.ext; unfold raw2271 raw2273; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5258 = raw2273Labels := by decide +kernel
    rw [ha, hj, canonical2273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5302 node5302Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3054 node3054Labels + mixedMoment B node3626 node3626Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2313 singletonSmall5302
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5302) = raw2313Labels := by decide +kernel
  rw [hl, canonical2313 B hB] at h
  have hc0 : mixedMoment B raw2313 (Fin.cases (0 : Fin 2) singletonSmall5302) =
      mixedMoment B node3054 node3054Labels := by
    have ha : raw2313 = raw2314 := by apply Matrix.ext; unfold raw2313 raw2314; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5302 = raw2314Labels := by decide +kernel
    rw [ha, hj, canonical2314 B hB]
  have hc1 : mixedMoment B raw2313 (Fin.cases (1 : Fin 2) singletonSmall5302) =
      mixedMoment B node3626 node3626Labels := by
    have ha : raw2313 = raw2315 := by apply Matrix.ext; unfold raw2313 raw2315; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5302 = raw2315Labels := by decide +kernel
    rw [ha, hj, canonical2315 B hB]
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

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound5302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5302 node5302Labels = Sparse.eval nodeValue5302 (mixedVector B) := by
  have h := singleton5302 B _hB
  rw [sound3054 B _hB _hF, sound3626 B _hB _hF] at h
  norm_num [nodeValue5302, nodeValue3054, nodeValue3626, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1802 node1802Labels = Sparse.eval nodeValue1802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1802) = mixedMoment B node1802 node1802Labels := rfl
  simpa [nodeValue1802, Sparse.eval] using hc.symm

theorem sound1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1807 node1807Labels = Sparse.eval nodeValue1807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1807) = mixedMoment B node1807 node1807Labels := rfl
  simpa [nodeValue1807, Sparse.eval] using hc.symm

theorem sound1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1810 node1810Labels = Sparse.eval nodeValue1810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1810) = mixedMoment B node1810 node1810Labels := rfl
  simpa [nodeValue1810, Sparse.eval] using hc.symm

theorem sound1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1814 node1814Labels = Sparse.eval nodeValue1814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1814) = mixedMoment B node1814 node1814Labels := rfl
  simpa [nodeValue1814, Sparse.eval] using hc.symm

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

theorem sound2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2141 node2141Labels = Sparse.eval nodeValue2141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2141) = mixedMoment B node2141 node2141Labels := rfl
  simpa [nodeValue2141, Sparse.eval] using hc.symm

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

theorem sound2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2157 node2157Labels = Sparse.eval nodeValue2157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2157) = mixedMoment B node2157 node2157Labels := rfl
  simpa [nodeValue2157, Sparse.eval] using hc.symm

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

theorem sound2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2522 node2522Labels = Sparse.eval nodeValue2522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2522) = mixedMoment B node2522 node2522Labels := rfl
  simpa [nodeValue2522, Sparse.eval] using hc.symm

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

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

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

theorem sound3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3391 node3391Labels = Sparse.eval nodeValue3391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3391) = mixedMoment B node3391 node3391Labels := rfl
  simpa [nodeValue3391, Sparse.eval] using hc.symm

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

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

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

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound4676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4676 node4676Labels = Sparse.eval nodeValue4676 (mixedVector B) := by
  have h := singleton4676 B _hB
  rw [sound1802 B _hB _hF, sound2141 B _hB _hF] at h
  norm_num [nodeValue4676, nodeValue1802, nodeValue2141, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4681 node4681Labels = Sparse.eval nodeValue4681 (mixedVector B) := by
  have h := singleton4681 B _hB
  rw [sound1807 B _hB _hF, sound2151 B _hB _hF] at h
  norm_num [nodeValue4681, nodeValue1807, nodeValue2151, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4684 node4684Labels = Sparse.eval nodeValue4684 (mixedVector B) := by
  have h := singleton4684 B _hB
  rw [sound1810 B _hB _hF, sound2152 B _hB _hF] at h
  norm_num [nodeValue4684, nodeValue1810, nodeValue2152, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4688 node4688Labels = Sparse.eval nodeValue4688 (mixedVector B) := by
  have h := singleton4688 B _hB
  rw [sound1814 B _hB _hF, sound2157 B _hB _hF] at h
  norm_num [nodeValue4688, nodeValue1814, nodeValue2157, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4698 node4698Labels = Sparse.eval nodeValue4698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4698) = mixedMoment B node4698 node4698Labels := rfl
  simpa [nodeValue4698, Sparse.eval] using hc.symm

theorem sound4699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4699 node4699Labels = Sparse.eval nodeValue4699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4699) = mixedMoment B node4699 node4699Labels := rfl
  simpa [nodeValue4699, Sparse.eval] using hc.symm

theorem sound4700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4700 node4700Labels = Sparse.eval nodeValue4700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4700) = mixedMoment B node4700 node4700Labels := rfl
  simpa [nodeValue4700, Sparse.eval] using hc.symm

theorem sound4703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4703 node4703Labels = Sparse.eval nodeValue4703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4703) = mixedMoment B node4703 node4703Labels := rfl
  simpa [nodeValue4703, Sparse.eval] using hc.symm

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

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

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

theorem sound4880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4880 node4880Labels = Sparse.eval nodeValue4880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4880) = mixedMoment B node4880 node4880Labels := rfl
  simpa [nodeValue4880, Sparse.eval] using hc.symm

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

theorem sound5035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5035 node5035Labels = Sparse.eval nodeValue5035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5035) = mixedMoment B node5035 node5035Labels := rfl
  simpa [nodeValue5035, Sparse.eval] using hc.symm

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

theorem sound5110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5110 node5110Labels = Sparse.eval nodeValue5110 (mixedVector B) := by
  have h := singleton5110 B _hB
  rw [sound2522 B _hB _hF, sound2685 B _hB _hF] at h
  norm_num [nodeValue5110, nodeValue2522, nodeValue2685, Sparse.eval] at h ⊢
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

theorem sound5140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5140 node5140Labels = Sparse.eval nodeValue5140 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5140) = mixedMoment B node5140 node5140Labels := rfl
  simpa [nodeValue5140, Sparse.eval] using hc.symm

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

theorem sound5215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5215 node5215Labels = Sparse.eval nodeValue5215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5215) = mixedMoment B node5215 node5215Labels := rfl
  simpa [nodeValue5215, Sparse.eval] using hc.symm

theorem sound5216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5216 node5216Labels = Sparse.eval nodeValue5216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5216) = mixedMoment B node5216 node5216Labels := rfl
  simpa [nodeValue5216, Sparse.eval] using hc.symm

theorem sound5219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5219 node5219Labels = Sparse.eval nodeValue5219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5219) = mixedMoment B node5219 node5219Labels := rfl
  simpa [nodeValue5219, Sparse.eval] using hc.symm

theorem sound5220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5220 node5220Labels = Sparse.eval nodeValue5220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5220) = mixedMoment B node5220 node5220Labels := rfl
  simpa [nodeValue5220, Sparse.eval] using hc.symm

theorem sound5228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5228 node5228Labels = Sparse.eval nodeValue5228 (mixedVector B) := by
  have h := singleton5228 B _hB
  rw [sound2672 B _hB _hF, sound3391 B _hB _hF] at h
  norm_num [nodeValue5228, nodeValue2672, nodeValue3391, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5229 node5229Labels = Sparse.eval nodeValue5229 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5229) = mixedMoment B node5229 node5229Labels := rfl
  simpa [nodeValue5229, Sparse.eval] using hc.symm

theorem sound5232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5232 node5232Labels = Sparse.eval nodeValue5232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5232) = mixedMoment B node5232 node5232Labels := rfl
  simpa [nodeValue5232, Sparse.eval] using hc.symm

theorem sound5233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5233 node5233Labels = Sparse.eval nodeValue5233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5233) = mixedMoment B node5233 node5233Labels := rfl
  simpa [nodeValue5233, Sparse.eval] using hc.symm

theorem sound5238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5238 node5238Labels = Sparse.eval nodeValue5238 (mixedVector B) := by
  have h := singleton5238 B _hB
  rw [sound2686 B _hB _hF, sound3397 B _hB _hF] at h
  norm_num [nodeValue5238, nodeValue2686, nodeValue3397, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5241 node5241Labels = Sparse.eval nodeValue5241 (mixedVector B) := by
  have h := singleton5241 B _hB
  rw [sound2694 B _hB _hF, sound3493 B _hB _hF] at h
  norm_num [nodeValue5241, nodeValue2694, nodeValue3493, Sparse.eval] at h ⊢
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

theorem sound5254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5254 node5254Labels = Sparse.eval nodeValue5254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5254) = mixedMoment B node5254 node5254Labels := rfl
  simpa [nodeValue5254, Sparse.eval] using hc.symm

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5266 node5266Labels = Sparse.eval nodeValue5266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5266) = mixedMoment B node5266 node5266Labels := rfl
  simpa [nodeValue5266, Sparse.eval] using hc.symm

theorem sound5267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5267 node5267Labels = Sparse.eval nodeValue5267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5267) = mixedMoment B node5267 node5267Labels := rfl
  simpa [nodeValue5267, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2595 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 1) (sourceB2595 + difference 1 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 1) (sourceB2595 + difference 1 0) sourceC2595) = raw36038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36038; decide +kernel
    rw [ha]
    exact (canonical36038 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 2) (sourceB2595 + difference 2 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 2) (sourceB2595 + difference 2 0) sourceC2595) = raw36039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36039; decide +kernel
    rw [ha]
    exact (canonical36039 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 3) (sourceB2595 + difference 3 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 3) (sourceB2595 + difference 3 0) sourceC2595) = raw36040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36040; decide +kernel
    rw [ha]
    exact (canonical36040 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 4) (sourceB2595 + difference 4 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 4) (sourceB2595 + difference 4 0) sourceC2595) = raw36041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36041; decide +kernel
    rw [ha]
    exact (canonical36041 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 5) (sourceB2595 + difference 5 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 5) (sourceB2595 + difference 5 0) sourceC2595) = raw36042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36042; decide +kernel
    rw [ha]
    exact (canonical36042 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 0) (sourceB2595 + difference 0 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 0) (sourceB2595 + difference 0 1) sourceC2595) = raw36043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36043; decide +kernel
    rw [ha]
    exact (canonical36043 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 2) (sourceB2595 + difference 2 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 2) (sourceB2595 + difference 2 1) sourceC2595) = raw36044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36044; decide +kernel
    rw [ha]
    exact (canonical36044 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 3) (sourceB2595 + difference 3 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 3) (sourceB2595 + difference 3 1) sourceC2595) = raw36045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36045; decide +kernel
    rw [ha]
    exact (canonical36045 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 4) (sourceB2595 + difference 4 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 4) (sourceB2595 + difference 4 1) sourceC2595) = raw36046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36046; decide +kernel
    rw [ha]
    exact (canonical36046 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 5) (sourceB2595 + difference 5 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 5) (sourceB2595 + difference 5 1) sourceC2595) = raw36047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36047; decide +kernel
    rw [ha]
    exact (canonical36047 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 0) (sourceB2595 + difference 0 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4698) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 0) (sourceB2595 + difference 0 2) sourceC2595) = raw36048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36048; decide +kernel
    rw [ha]
    exact (canonical36048 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 1) (sourceB2595 + difference 1 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 1) (sourceB2595 + difference 1 2) sourceC2595) = raw36049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36049; decide +kernel
    rw [ha]
    exact (canonical36049 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 3) (sourceB2595 + difference 3 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 3) (sourceB2595 + difference 3 2) sourceC2595) = raw36050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36050; decide +kernel
    rw [ha]
    exact (canonical36050 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 4) (sourceB2595 + difference 4 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 4) (sourceB2595 + difference 4 2) sourceC2595) = raw36051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36051; decide +kernel
    rw [ha]
    exact (canonical36051 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 5) (sourceB2595 + difference 5 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 5) (sourceB2595 + difference 5 2) sourceC2595) = raw36052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36052; decide +kernel
    rw [ha]
    exact (canonical36052 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 0) (sourceB2595 + difference 0 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 0) (sourceB2595 + difference 0 3) sourceC2595) = raw36053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36053; decide +kernel
    rw [ha]
    exact (canonical36053 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 1) (sourceB2595 + difference 1 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 1) (sourceB2595 + difference 1 3) sourceC2595) = raw36054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36054; decide +kernel
    rw [ha]
    exact (canonical36054 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 2) (sourceB2595 + difference 2 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 2) (sourceB2595 + difference 2 3) sourceC2595) = raw36055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36055; decide +kernel
    rw [ha]
    exact (canonical36055 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 4) (sourceB2595 + difference 4 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 4) (sourceB2595 + difference 4 3) sourceC2595) = raw36056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36056; decide +kernel
    rw [ha]
    exact (canonical36056 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 5) (sourceB2595 + difference 5 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 5) (sourceB2595 + difference 5 3) sourceC2595) = raw36057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36057; decide +kernel
    rw [ha]
    exact (canonical36057 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 0) (sourceB2595 + difference 0 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4700) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 0) (sourceB2595 + difference 0 4) sourceC2595) = raw36058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36058; decide +kernel
    rw [ha]
    exact (canonical36058 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 1) (sourceB2595 + difference 1 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 1) (sourceB2595 + difference 1 4) sourceC2595) = raw36059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36059; decide +kernel
    rw [ha]
    exact (canonical36059 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 2) (sourceB2595 + difference 2 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5216) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 2) (sourceB2595 + difference 2 4) sourceC2595) = raw36060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36060; decide +kernel
    rw [ha]
    exact (canonical36060 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 3) (sourceB2595 + difference 3 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 3) (sourceB2595 + difference 3 4) sourceC2595) = raw36061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36061; decide +kernel
    rw [ha]
    exact (canonical36061 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 5) (sourceB2595 + difference 5 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 5) (sourceB2595 + difference 5 4) sourceC2595) = raw36062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36062; decide +kernel
    rw [ha]
    exact (canonical36062 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 0) (sourceB2595 + difference 0 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 0) (sourceB2595 + difference 0 5) sourceC2595) = raw36063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36063; decide +kernel
    rw [ha]
    exact (canonical36063 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 1) (sourceB2595 + difference 1 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 1) (sourceB2595 + difference 1 5) sourceC2595) = raw36064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36064; decide +kernel
    rw [ha]
    exact (canonical36064 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 2) (sourceB2595 + difference 2 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 2) (sourceB2595 + difference 2 5) sourceC2595) = raw36065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36065; decide +kernel
    rw [ha]
    exact (canonical36065 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 3) (sourceB2595 + difference 3 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 3) (sourceB2595 + difference 3 5) sourceC2595) = raw36066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36066; decide +kernel
    rw [ha]
    exact (canonical36066 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 4) (sourceB2595 + difference 4 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 4) (sourceB2595 + difference 4 5) sourceC2595) = raw36067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36067; decide +kernel
    rw [ha]
    exact (canonical36067 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2595 sourceB2595 sourceC2595
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2595, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2073 : Integer.Sparse.reindex keyMap MixedData.row2073 = numericRow2073 := by decide +kernel

theorem numericCheck2073 (x : Master → ℝ) : Integer.Sparse.eval numericRow2073 x =
    (4 : ℝ) * reducedSource2073 x := by
  norm_num [numericRow2073, reducedSource2073, Integer.Sparse.eval, Sparse.eval, nodeValue4676, nodeValue4681, nodeValue4684, nodeValue4688, nodeValue4698, nodeValue4699, nodeValue4700, nodeValue4703, nodeValue4834, nodeValue4880, nodeValue5035, nodeValue5110, nodeValue5140, nodeValue5215, nodeValue5216, nodeValue5219, nodeValue5220, nodeValue5228, nodeValue5229, nodeValue5232, nodeValue5233, nodeValue5238, nodeValue5241, nodeValue5254, nodeValue5258, nodeValue5259, nodeValue5266, nodeValue5267, nodeValue5274, nodeValue5302]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2073 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2073 (mixedVector B) = 0 := by
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4698 : mixedVector B (Sum.inr 4698) = Sparse.eval nodeValue4698 (mixedVector B) := by
    change mixedMoment B node4698 node4698Labels = _
    exact sound4698 B hB hF
  have h4699 : mixedVector B (Sum.inr 4699) = Sparse.eval nodeValue4699 (mixedVector B) := by
    change mixedMoment B node4699 node4699Labels = _
    exact sound4699 B hB hF
  have h4700 : mixedVector B (Sum.inr 4700) = Sparse.eval nodeValue4700 (mixedVector B) := by
    change mixedMoment B node4700 node4700Labels = _
    exact sound4700 B hB hF
  have h4703 : mixedVector B (Sum.inr 4703) = Sparse.eval nodeValue4703 (mixedVector B) := by
    change mixedMoment B node4703 node4703Labels = _
    exact sound4703 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4880 : mixedVector B (Sum.inr 4880) = Sparse.eval nodeValue4880 (mixedVector B) := by
    change mixedMoment B node4880 node4880Labels = _
    exact sound4880 B hB hF
  have h5035 : mixedVector B (Sum.inr 5035) = Sparse.eval nodeValue5035 (mixedVector B) := by
    change mixedMoment B node5035 node5035Labels = _
    exact sound5035 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5140 : mixedVector B (Sum.inr 5140) = Sparse.eval nodeValue5140 (mixedVector B) := by
    change mixedMoment B node5140 node5140Labels = _
    exact sound5140 B hB hF
  have h5215 : mixedVector B (Sum.inr 5215) = Sparse.eval nodeValue5215 (mixedVector B) := by
    change mixedMoment B node5215 node5215Labels = _
    exact sound5215 B hB hF
  have h5216 : mixedVector B (Sum.inr 5216) = Sparse.eval nodeValue5216 (mixedVector B) := by
    change mixedMoment B node5216 node5216Labels = _
    exact sound5216 B hB hF
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5232 : mixedVector B (Sum.inr 5232) = Sparse.eval nodeValue5232 (mixedVector B) := by
    change mixedMoment B node5232 node5232Labels = _
    exact sound5232 B hB hF
  have h5233 : mixedVector B (Sum.inr 5233) = Sparse.eval nodeValue5233 (mixedVector B) := by
    change mixedMoment B node5233 node5233Labels = _
    exact sound5233 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  simpa only [sourceForm2595, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4676, h4681, h4684, h4688, h4698, h4699, h4700, h4703, h4834, h4880, h5035, h5110, h5140, h5215, h5216, h5219, h5220, h5228, h5229, h5232, h5233, h5238, h5241, h5254, h5258, h5259, h5266, h5267, h5274, h5302, reducedSource2073] using sourceEq2595 B hB

theorem rowSound2073_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2073 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2073, numericCheck2073, reducedZero2073 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e_oai
