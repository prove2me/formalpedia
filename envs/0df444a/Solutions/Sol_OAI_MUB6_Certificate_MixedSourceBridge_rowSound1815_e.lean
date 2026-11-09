-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:35:16.274206+00:00
-- url     : https://prove2.me/submissions/40d28c49-6b40-4a17-a380-c8c2e8bca5b6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical1908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1908 raw1908Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw1908 raw1908Labels = mixedMoment B raw1908step0 raw1908step0Labels := by
      have ha : raw1908step0 = (fun i j => raw1908 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1908step0 raw1908; decide +kernel
      have hl : raw1908step0Labels = raw1908Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1908 raw1908Labels permutation32 permutation4
    mixedMoment B raw1908step0 raw1908step0Labels = mixedMoment B raw1908step1 raw1908step1Labels := by
      have ha : raw1908step1 = raw1908step0 := by apply Matrix.ext; unfold raw1908step1 raw1908step0; decide +kernel
      have hl : raw1908step0Labels = labelEmbedding7 ∘ raw1908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1908step0 raw1908step0Labels raw1908step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

theorem canonical1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1909 raw1909Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw1909 raw1909Labels = mixedMoment B raw1909step0 raw1909step0Labels := by
      have ha : raw1909step0 = (fun i j => raw1909 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1909step0 raw1909; decide +kernel
      have hl : raw1909step0Labels = raw1909Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1909 raw1909Labels permutation32 permutation4
    _ = mixedMoment B node2334 node2334Labels := by rfl

theorem canonical1910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1910 raw1910Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw1910 raw1910Labels = mixedMoment B raw1910step0 raw1910step0Labels := by
      have ha : raw1910step0 = (fun i j => raw1910 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1910step0 raw1910; decide +kernel
      have hl : raw1910step0Labels = raw1910Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1910 raw1910Labels permutation32 permutation6
    mixedMoment B raw1910step0 raw1910step0Labels = mixedMoment B raw1910step1 raw1910step1Labels := by
      have ha : raw1910step1 = -raw1910step0 := by apply Matrix.ext; change ∀ i j, raw1910step1 i j = -(raw1910step0 i j); unfold raw1910step1 raw1910step0; decide +kernel
      have hl : raw1910step1Labels = raw1910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1910step1 raw1910step1Labels = mixedMoment B raw1910step2 raw1910step2Labels := by
      have ha : raw1910step2 = raw1910step1 := by apply Matrix.ext; unfold raw1910step2 raw1910step1; decide +kernel
      have hl : raw1910step1Labels = labelEmbedding1 ∘ raw1910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1910step1 raw1910step1Labels raw1910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

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

theorem canonical1956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1956 raw1956Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw1956 raw1956Labels = mixedMoment B raw1956step0 raw1956step0Labels := by
      have ha : raw1956step0 = (fun i j => raw1956 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1956step0 raw1956; decide +kernel
      have hl : raw1956step0Labels = raw1956Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1956 raw1956Labels permutation32 permutation5
    mixedMoment B raw1956step0 raw1956step0Labels = mixedMoment B raw1956step1 raw1956step1Labels := by
      have ha : raw1956step1 = raw1956step0 := by apply Matrix.ext; unfold raw1956step1 raw1956step0; decide +kernel
      have hl : raw1956step0Labels = labelEmbedding8 ∘ raw1956step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1956step0 raw1956step0Labels raw1956step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

theorem canonical1957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1957 raw1957Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw1957 raw1957Labels = mixedMoment B raw1957step0 raw1957step0Labels := by
      have ha : raw1957step0 = (fun i j => raw1957 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1957step0 raw1957; decide +kernel
      have hl : raw1957step0Labels = raw1957Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1957 raw1957Labels permutation145 permutation4
    mixedMoment B raw1957step0 raw1957step0Labels = mixedMoment B raw1957step1 raw1957step1Labels := by
      have ha : raw1957step1 = -raw1957step0 := by apply Matrix.ext; change ∀ i j, raw1957step1 i j = -(raw1957step0 i j); unfold raw1957step1 raw1957step0; decide +kernel
      have hl : raw1957step1Labels = raw1957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

theorem canonical1958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1958 raw1958Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw1958 raw1958Labels = mixedMoment B raw1958step0 raw1958step0Labels := by
      have ha : raw1958step0 = (fun i j => raw1958 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1958step0 raw1958; decide +kernel
      have hl : raw1958step0Labels = raw1958Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1958 raw1958Labels permutation144 permutation6
    mixedMoment B raw1958step0 raw1958step0Labels = mixedMoment B raw1958step1 raw1958step1Labels := by
      have ha : raw1958step1 = raw1958step0 := by apply Matrix.ext; unfold raw1958step1 raw1958step0; decide +kernel
      have hl : raw1958step0Labels = labelEmbedding1 ∘ raw1958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1958step0 raw1958step0Labels raw1958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

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

theorem canonical2055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2055 raw2055Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw2055 raw2055Labels = mixedMoment B raw2055step0 raw2055step0Labels := by
      have ha : raw2055step0 = (fun i j => raw2055 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2055step0 raw2055; decide +kernel
      have hl : raw2055step0Labels = raw2055Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2055 raw2055Labels permutation152 permutation4
    mixedMoment B raw2055step0 raw2055step0Labels = mixedMoment B raw2055step1 raw2055step1Labels := by
      have ha : raw2055step1 = raw2055step0 := by apply Matrix.ext; unfold raw2055step1 raw2055step0; decide +kernel
      have hl : raw2055step0Labels = labelEmbedding7 ∘ raw2055step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2055step0 raw2055step0Labels raw2055step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

theorem canonical2056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2056 raw2056Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw2056 raw2056Labels = mixedMoment B raw2056step0 raw2056step0Labels := by
      have ha : raw2056step0 = (fun i j => raw2056 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2056step0 raw2056; decide +kernel
      have hl : raw2056step0Labels = raw2056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2056 raw2056Labels permutation152 permutation4
    _ = mixedMoment B node2428 node2428Labels := by rfl

theorem canonical2057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2057 raw2057Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw2057 raw2057Labels = mixedMoment B raw2057step0 raw2057step0Labels := by
      have ha : raw2057step0 = (fun i j => raw2057 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2057step0 raw2057; decide +kernel
      have hl : raw2057step0Labels = raw2057Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2057 raw2057Labels permutation152 permutation6
    mixedMoment B raw2057step0 raw2057step0Labels = mixedMoment B raw2057step1 raw2057step1Labels := by
      have ha : raw2057step1 = -raw2057step0 := by apply Matrix.ext; change ∀ i j, raw2057step1 i j = -(raw2057step0 i j); unfold raw2057step1 raw2057step0; decide +kernel
      have hl : raw2057step1Labels = raw2057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2057step1 raw2057step1Labels = mixedMoment B raw2057step2 raw2057step2Labels := by
      have ha : raw2057step2 = raw2057step1 := by apply Matrix.ext; unfold raw2057step2 raw2057step1; decide +kernel
      have hl : raw2057step1Labels = labelEmbedding1 ∘ raw2057step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2057step1 raw2057step1Labels raw2057step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

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

theorem canonical2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2163 raw2163Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw2163 raw2163Labels = mixedMoment B raw2163step0 raw2163step0Labels := by
      have ha : raw2163step0 = (fun i j => raw2163 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2163step0 raw2163; decide +kernel
      have hl : raw2163step0Labels = raw2163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2163 raw2163Labels permutation152 permutation4
    mixedMoment B raw2163step0 raw2163step0Labels = mixedMoment B raw2163step1 raw2163step1Labels := by
      have ha : raw2163step1 = raw2163step0 := by apply Matrix.ext; unfold raw2163step1 raw2163step0; decide +kernel
      have hl : raw2163step0Labels = labelEmbedding7 ∘ raw2163step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2163step0 raw2163step0Labels raw2163step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2164 raw2164Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw2164 raw2164Labels = mixedMoment B raw2164step0 raw2164step0Labels := by
      have ha : raw2164step0 = (fun i j => raw2164 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2164step0 raw2164; decide +kernel
      have hl : raw2164step0Labels = raw2164Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2164 raw2164Labels permutation152 permutation4
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2165 raw2165Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw2165 raw2165Labels = mixedMoment B raw2165step0 raw2165step0Labels := by
      have ha : raw2165step0 = (fun i j => raw2165 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2165step0 raw2165; decide +kernel
      have hl : raw2165step0Labels = raw2165Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2165 raw2165Labels permutation176 permutation6
    mixedMoment B raw2165step0 raw2165step0Labels = mixedMoment B raw2165step1 raw2165step1Labels := by
      have ha : raw2165step1 = -raw2165step0 := by apply Matrix.ext; change ∀ i j, raw2165step1 i j = -(raw2165step0 i j); unfold raw2165step1 raw2165step0; decide +kernel
      have hl : raw2165step1Labels = raw2165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2165step1 raw2165step1Labels = mixedMoment B raw2165step2 raw2165step2Labels := by
      have ha : raw2165step2 = raw2165step1 := by apply Matrix.ext; unfold raw2165step2 raw2165step1; decide +kernel
      have hl : raw2165step1Labels = labelEmbedding1 ∘ raw2165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2165step1 raw2165step1Labels raw2165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

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

theorem canonical2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2190 raw2190Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw2190 raw2190Labels = mixedMoment B raw2190step0 raw2190step0Labels := by
      have ha : raw2190step0 = (fun i j => raw2190 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2190step0 raw2190; decide +kernel
      have hl : raw2190step0Labels = raw2190Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2190 raw2190Labels permutation32 permutation4
    mixedMoment B raw2190step0 raw2190step0Labels = mixedMoment B raw2190step1 raw2190step1Labels := by
      have ha : raw2190step1 = raw2190step0 := by apply Matrix.ext; unfold raw2190step1 raw2190step0; decide +kernel
      have hl : raw2190step0Labels = labelEmbedding7 ∘ raw2190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2190step0 raw2190step0Labels raw2190step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2191 raw2191Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw2191 raw2191Labels = mixedMoment B raw2191step0 raw2191step0Labels := by
      have ha : raw2191step0 = (fun i j => raw2191 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2191step0 raw2191; decide +kernel
      have hl : raw2191step0Labels = raw2191Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2191 raw2191Labels permutation32 permutation4
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2192 raw2192Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw2192 raw2192Labels = mixedMoment B raw2192step0 raw2192step0Labels := by
      have ha : raw2192step0 = (fun i j => raw2192 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2192step0 raw2192; decide +kernel
      have hl : raw2192step0Labels = raw2192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2192 raw2192Labels permutation38 permutation6
    mixedMoment B raw2192step0 raw2192step0Labels = mixedMoment B raw2192step1 raw2192step1Labels := by
      have ha : raw2192step1 = -raw2192step0 := by apply Matrix.ext; change ∀ i j, raw2192step1 i j = -(raw2192step0 i j); unfold raw2192step1 raw2192step0; decide +kernel
      have hl : raw2192step1Labels = raw2192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2192step1 raw2192step1Labels = mixedMoment B raw2192step2 raw2192step2Labels := by
      have ha : raw2192step2 = raw2192step1 := by apply Matrix.ext; unfold raw2192step2 raw2192step1; decide +kernel
      have hl : raw2192step1Labels = labelEmbedding1 ∘ raw2192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2192step1 raw2192step1Labels raw2192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

theorem canonical2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2286 raw2286Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2286 raw2286Labels = mixedMoment B raw2286step0 raw2286step0Labels := by
      have ha : raw2286step0 = (fun i j => raw2286 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2286step0 raw2286; decide +kernel
      have hl : raw2286step0Labels = raw2286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2286 raw2286Labels permutation8 permutation4
    mixedMoment B raw2286step0 raw2286step0Labels = mixedMoment B raw2286step1 raw2286step1Labels := by
      have ha : raw2286step1 = raw2286step0 := by apply Matrix.ext; unfold raw2286step1 raw2286step0; decide +kernel
      have hl : raw2286step0Labels = labelEmbedding7 ∘ raw2286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2286step0 raw2286step0Labels raw2286step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2287 raw2287Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2287 raw2287Labels = mixedMoment B raw2287step0 raw2287step0Labels := by
      have ha : raw2287step0 = (fun i j => raw2287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2287step0 raw2287; decide +kernel
      have hl : raw2287step0Labels = raw2287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2287 raw2287Labels permutation8 permutation4
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2288 raw2288Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw2288 raw2288Labels = mixedMoment B raw2288step0 raw2288step0Labels := by
      have ha : raw2288step0 = (fun i j => raw2288 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2288step0 raw2288; decide +kernel
      have hl : raw2288step0Labels = raw2288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2288 raw2288Labels permutation9 permutation6
    mixedMoment B raw2288step0 raw2288step0Labels = mixedMoment B raw2288step1 raw2288step1Labels := by
      have ha : raw2288step1 = -raw2288step0 := by apply Matrix.ext; change ∀ i j, raw2288step1 i j = -(raw2288step0 i j); unfold raw2288step1 raw2288step0; decide +kernel
      have hl : raw2288step1Labels = raw2288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2288step1 raw2288step1Labels = mixedMoment B raw2288step2 raw2288step2Labels := by
      have ha : raw2288step2 = raw2288step1 := by apply Matrix.ext; unfold raw2288step2 raw2288step1; decide +kernel
      have hl : raw2288step1Labels = labelEmbedding1 ∘ raw2288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2288step1 raw2288step1Labels raw2288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22655 raw22655Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw22655 raw22655Labels = mixedMoment B raw22655step0 raw22655step0Labels := by
      have hz : ∀ j, raw22655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22655step0 = (fun i j => raw22655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22655step0 raw22655; decide +kernel
      have hl : raw22655step0Labels = raw22655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22655 raw22655Labels permutation346 hz
    mixedMoment B raw22655step0 raw22655step0Labels = mixedMoment B raw22655step1 raw22655step1Labels := by
      have hz : ∀ j, raw22655step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22655step1 = (fun i j => raw22655step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22655step1 raw22655step0; decide +kernel
      have hl : raw22655step1Labels = raw22655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22655step0 raw22655step0Labels permutation56 hz
    _ = mixedMoment B node5275 node5275Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22661 raw22661Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw22661 raw22661Labels = mixedMoment B raw22661step0 raw22661step0Labels := by
      have ha : raw22661step0 = (fun i j => raw22661 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22661step0 raw22661; decide +kernel
      have hl : raw22661step0Labels = raw22661Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22661 raw22661Labels permutation158 permutation3
    mixedMoment B raw22661step0 raw22661step0Labels = mixedMoment B raw22661step1 raw22661step1Labels := by
      have ha : raw22661step1 = raw22661step0 := by apply Matrix.ext; unfold raw22661step1 raw22661step0; decide +kernel
      have hl : raw22661step0Labels = labelEmbedding6 ∘ raw22661step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22661step0 raw22661step0Labels raw22661step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4533 node4533Labels := by rfl

theorem canonical22665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22665 raw22665Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw22665 raw22665Labels = mixedMoment B raw22665step0 raw22665step0Labels := by
      have hz : ∀ j, raw22665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22665step0 = (fun i j => raw22665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22665step0 raw22665; decide +kernel
      have hl : raw22665step0Labels = raw22665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22665 raw22665Labels permutation346 hz
    mixedMoment B raw22665step0 raw22665step0Labels = mixedMoment B raw22665step1 raw22665step1Labels := by
      have ha : raw22665step1 = (fun i j => raw22665step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22665step1 raw22665step0; decide +kernel
      have hl : raw22665step1Labels = raw22665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22665step0 raw22665step0Labels permutation32 permutation3
    mixedMoment B raw22665step1 raw22665step1Labels = mixedMoment B raw22665step2 raw22665step2Labels := by
      have ha : raw22665step2 = raw22665step1 := by apply Matrix.ext; unfold raw22665step2 raw22665step1; decide +kernel
      have hl : raw22665step1Labels = labelEmbedding6 ∘ raw22665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22665step1 raw22665step1Labels raw22665step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4556 node4556Labels := by rfl

theorem canonical22669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22669 raw22669Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw22669 raw22669Labels = mixedMoment B raw22669step0 raw22669step0Labels := by
      have hz : ∀ j, raw22669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22669step0 = (fun i j => raw22669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22669step0 raw22669; decide +kernel
      have hl : raw22669step0Labels = raw22669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22669 raw22669Labels permutation346 hz
    mixedMoment B raw22669step0 raw22669step0Labels = mixedMoment B raw22669step1 raw22669step1Labels := by
      have ha : raw22669step1 = (fun i j => raw22669step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22669step1 raw22669step0; decide +kernel
      have hl : raw22669step1Labels = raw22669step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22669step0 raw22669step0Labels permutation33 permutation3
    mixedMoment B raw22669step1 raw22669step1Labels = mixedMoment B raw22669step2 raw22669step2Labels := by
      have ha : raw22669step2 = raw22669step1 := by apply Matrix.ext; unfold raw22669step2 raw22669step1; decide +kernel
      have hl : raw22669step1Labels = labelEmbedding6 ∘ raw22669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22669step1 raw22669step1Labels raw22669step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical22674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22674 raw22674Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw22674 raw22674Labels = mixedMoment B raw22674step0 raw22674step0Labels := by
      have hz : ∀ j, raw22674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22674step0 = (fun i j => raw22674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22674step0 raw22674; decide +kernel
      have hl : raw22674step0Labels = raw22674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22674 raw22674Labels permutation346 hz
    mixedMoment B raw22674step0 raw22674step0Labels = mixedMoment B raw22674step1 raw22674step1Labels := by
      have ha : raw22674step1 = (fun i j => raw22674step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22674step1 raw22674step0; decide +kernel
      have hl : raw22674step1Labels = raw22674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22674step0 raw22674step0Labels permutation32 permutation3
    mixedMoment B raw22674step1 raw22674step1Labels = mixedMoment B raw22674step2 raw22674step2Labels := by
      have ha : raw22674step2 = raw22674step1 := by apply Matrix.ext; unfold raw22674step2 raw22674step1; decide +kernel
      have hl : raw22674step1Labels = labelEmbedding6 ∘ raw22674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22674step1 raw22674step1Labels raw22674step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4534 node4534Labels := by rfl

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

theorem canonical2391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2391 raw2391Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw2391 raw2391Labels = mixedMoment B raw2391step0 raw2391step0Labels := by
      have ha : raw2391step0 = (fun i j => raw2391 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2391step0 raw2391; decide +kernel
      have hl : raw2391step0Labels = raw2391Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2391 raw2391Labels permutation152 permutation4
    mixedMoment B raw2391step0 raw2391step0Labels = mixedMoment B raw2391step1 raw2391step1Labels := by
      have ha : raw2391step1 = raw2391step0 := by apply Matrix.ext; unfold raw2391step1 raw2391step0; decide +kernel
      have hl : raw2391step0Labels = labelEmbedding7 ∘ raw2391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2391step0 raw2391step0Labels raw2391step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical2392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2392 raw2392Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw2392 raw2392Labels = mixedMoment B raw2392step0 raw2392step0Labels := by
      have ha : raw2392step0 = (fun i j => raw2392 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2392step0 raw2392; decide +kernel
      have hl : raw2392step0Labels = raw2392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2392 raw2392Labels permutation152 permutation4
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical2393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2393 raw2393Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw2393 raw2393Labels = mixedMoment B raw2393step0 raw2393step0Labels := by
      have ha : raw2393step0 = (fun i j => raw2393 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2393step0 raw2393; decide +kernel
      have hl : raw2393step0Labels = raw2393Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2393 raw2393Labels permutation160 permutation6
    mixedMoment B raw2393step0 raw2393step0Labels = mixedMoment B raw2393step1 raw2393step1Labels := by
      have ha : raw2393step1 = -raw2393step0 := by apply Matrix.ext; change ∀ i j, raw2393step1 i j = -(raw2393step0 i j); unfold raw2393step1 raw2393step0; decide +kernel
      have hl : raw2393step1Labels = raw2393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2393step1 raw2393step1Labels = mixedMoment B raw2393step2 raw2393step2Labels := by
      have ha : raw2393step2 = raw2393step1 := by apply Matrix.ext; unfold raw2393step2 raw2393step1; decide +kernel
      have hl : raw2393step1Labels = labelEmbedding1 ∘ raw2393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2393step1 raw2393step1Labels raw2393step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2400 raw2400Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw2400 raw2400Labels = mixedMoment B raw2400step0 raw2400step0Labels := by
      have ha : raw2400step0 = (fun i j => raw2400 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2400step0 raw2400; decide +kernel
      have hl : raw2400step0Labels = raw2400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2400 raw2400Labels permutation32 permutation4
    mixedMoment B raw2400step0 raw2400step0Labels = mixedMoment B raw2400step1 raw2400step1Labels := by
      have ha : raw2400step1 = raw2400step0 := by apply Matrix.ext; unfold raw2400step1 raw2400step0; decide +kernel
      have hl : raw2400step0Labels = labelEmbedding7 ∘ raw2400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2400step0 raw2400step0Labels raw2400step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2401 raw2401Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw2401 raw2401Labels = mixedMoment B raw2401step0 raw2401step0Labels := by
      have ha : raw2401step0 = (fun i j => raw2401 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2401step0 raw2401; decide +kernel
      have hl : raw2401step0Labels = raw2401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2401 raw2401Labels permutation32 permutation4
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2402 raw2402Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw2402 raw2402Labels = mixedMoment B raw2402step0 raw2402step0Labels := by
      have ha : raw2402step0 = (fun i j => raw2402 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2402step0 raw2402; decide +kernel
      have hl : raw2402step0Labels = raw2402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2402 raw2402Labels permutation34 permutation6
    mixedMoment B raw2402step0 raw2402step0Labels = mixedMoment B raw2402step1 raw2402step1Labels := by
      have ha : raw2402step1 = -raw2402step0 := by apply Matrix.ext; change ∀ i j, raw2402step1 i j = -(raw2402step0 i j); unfold raw2402step1 raw2402step0; decide +kernel
      have hl : raw2402step1Labels = raw2402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2402step1 raw2402step1Labels = mixedMoment B raw2402step2 raw2402step2Labels := by
      have ha : raw2402step2 = raw2402step1 := by apply Matrix.ext; unfold raw2402step2 raw2402step1; decide +kernel
      have hl : raw2402step1Labels = labelEmbedding1 ∘ raw2402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2402step1 raw2402step1Labels raw2402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

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

theorem canonical2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2517 raw2517Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw2517 raw2517Labels = mixedMoment B raw2517step0 raw2517step0Labels := by
      have ha : raw2517step0 = (fun i j => raw2517 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2517step0 raw2517; decide +kernel
      have hl : raw2517step0Labels = raw2517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2517 raw2517Labels permutation32 permutation4
    mixedMoment B raw2517step0 raw2517step0Labels = mixedMoment B raw2517step1 raw2517step1Labels := by
      have ha : raw2517step1 = raw2517step0 := by apply Matrix.ext; unfold raw2517step1 raw2517step0; decide +kernel
      have hl : raw2517step0Labels = labelEmbedding7 ∘ raw2517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2517step0 raw2517step0Labels raw2517step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical2518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2518 raw2518Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2518 raw2518Labels = mixedMoment B raw2518step0 raw2518step0Labels := by
      have ha : raw2518step0 = (fun i j => raw2518 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2518step0 raw2518; decide +kernel
      have hl : raw2518step0Labels = raw2518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2518 raw2518Labels permutation32 permutation4
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2519 raw2519Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2519 raw2519Labels = mixedMoment B raw2519step0 raw2519step0Labels := by
      have ha : raw2519step0 = (fun i j => raw2519 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2519step0 raw2519; decide +kernel
      have hl : raw2519step0Labels = raw2519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2519 raw2519Labels permutation39 permutation6
    mixedMoment B raw2519step0 raw2519step0Labels = mixedMoment B raw2519step1 raw2519step1Labels := by
      have ha : raw2519step1 = -raw2519step0 := by apply Matrix.ext; change ∀ i j, raw2519step1 i j = -(raw2519step0 i j); unfold raw2519step1 raw2519step0; decide +kernel
      have hl : raw2519step1Labels = raw2519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2519step1 raw2519step1Labels = mixedMoment B raw2519step2 raw2519step2Labels := by
      have ha : raw2519step2 = raw2519step1 := by apply Matrix.ext; unfold raw2519step2 raw2519step1; decide +kernel
      have hl : raw2519step1Labels = labelEmbedding1 ∘ raw2519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2519step1 raw2519step1Labels raw2519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30076 raw30076Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw30076 raw30076Labels = mixedMoment B raw30076step0 raw30076step0Labels := by
      have hz : ∀ j, raw30076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30076step0 = (fun i j => raw30076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30076step0 raw30076; decide +kernel
      have hl : raw30076step0Labels = raw30076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30076 raw30076Labels permutation346 hz
    mixedMoment B raw30076step0 raw30076step0Labels = mixedMoment B raw30076step1 raw30076step1Labels := by
      have ha : raw30076step1 = (fun i j => raw30076step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30076step1 raw30076step0; decide +kernel
      have hl : raw30076step1Labels = raw30076step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30076step0 raw30076step0Labels permutation127 permutation2
    mixedMoment B raw30076step1 raw30076step1Labels = mixedMoment B raw30076step2 raw30076step2Labels := by
      have ha : raw30076step2 = -raw30076step1 := by apply Matrix.ext; change ∀ i j, raw30076step2 i j = -(raw30076step1 i j); unfold raw30076step2 raw30076step1; decide +kernel
      have hl : raw30076step2Labels = raw30076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical30077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30077 raw30077Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw30077 raw30077Labels = mixedMoment B raw30077step0 raw30077step0Labels := by
      have ha : raw30077step0 = (fun i j => raw30077 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30077step0 raw30077; decide +kernel
      have hl : raw30077step0Labels = raw30077Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30077 raw30077Labels permutation587 permutation2
    mixedMoment B raw30077step0 raw30077step0Labels = mixedMoment B raw30077step1 raw30077step1Labels := by
      have ha : raw30077step1 = -raw30077step0 := by apply Matrix.ext; change ∀ i j, raw30077step1 i j = -(raw30077step0 i j); unfold raw30077step1 raw30077step0; decide +kernel
      have hl : raw30077step1Labels = raw30077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5351 node5351Labels := by rfl

theorem canonical30078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30078 raw30078Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30078 raw30078Labels = mixedMoment B raw30078step0 raw30078step0Labels := by
      have hz : ∀ j, raw30078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30078step0 = (fun i j => raw30078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30078step0 raw30078; decide +kernel
      have hl : raw30078step0Labels = raw30078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30078 raw30078Labels permutation346 hz
    mixedMoment B raw30078step0 raw30078step0Labels = mixedMoment B raw30078step1 raw30078step1Labels := by
      have ha : raw30078step1 = (fun i j => raw30078step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30078step1 raw30078step0; decide +kernel
      have hl : raw30078step1Labels = raw30078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30078step0 raw30078step0Labels permutation125 permutation2
    mixedMoment B raw30078step1 raw30078step1Labels = mixedMoment B raw30078step2 raw30078step2Labels := by
      have ha : raw30078step2 = -raw30078step1 := by apply Matrix.ext; change ∀ i j, raw30078step2 i j = -(raw30078step1 i j); unfold raw30078step2 raw30078step1; decide +kernel
      have hl : raw30078step2Labels = raw30078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical30079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30079 raw30079Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw30079 raw30079Labels = mixedMoment B raw30079step0 raw30079step0Labels := by
      have hz : ∀ j, raw30079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30079step0 = (fun i j => raw30079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30079step0 raw30079; decide +kernel
      have hl : raw30079step0Labels = raw30079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30079 raw30079Labels permutation346 hz
    mixedMoment B raw30079step0 raw30079step0Labels = mixedMoment B raw30079step1 raw30079step1Labels := by
      have ha : raw30079step1 = (fun i j => raw30079step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30079step1 raw30079step0; decide +kernel
      have hl : raw30079step1Labels = raw30079step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30079step0 raw30079step0Labels permutation127 permutation2
    mixedMoment B raw30079step1 raw30079step1Labels = mixedMoment B raw30079step2 raw30079step2Labels := by
      have ha : raw30079step2 = -raw30079step1 := by apply Matrix.ext; change ∀ i j, raw30079step2 i j = -(raw30079step1 i j); unfold raw30079step2 raw30079step1; decide +kernel
      have hl : raw30079step2Labels = raw30079step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

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

theorem canonical30080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30080 raw30080Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw30080 raw30080Labels = mixedMoment B raw30080step0 raw30080step0Labels := by
      have ha : raw30080step0 = (fun i j => raw30080 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30080step0 raw30080; decide +kernel
      have hl : raw30080step0Labels = raw30080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30080 raw30080Labels permutation159 permutation2
    _ = mixedMoment B node4955 node4955Labels := by rfl

theorem canonical30081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30081 raw30081Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw30081 raw30081Labels = mixedMoment B raw30081step0 raw30081step0Labels := by
      have ha : raw30081step0 = (fun i j => raw30081 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30081step0 raw30081; decide +kernel
      have hl : raw30081step0Labels = raw30081Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30081 raw30081Labels permutation201 permutation2
    _ = mixedMoment B node5036 node5036Labels := by rfl

theorem canonical30082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30082 raw30082Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw30082 raw30082Labels = mixedMoment B raw30082step0 raw30082step0Labels := by
      have ha : raw30082step0 = (fun i j => raw30082 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30082step0 raw30082; decide +kernel
      have hl : raw30082step0Labels = raw30082Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30082 raw30082Labels permutation159 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical30083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30083 raw30083Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw30083 raw30083Labels = mixedMoment B raw30083step0 raw30083step0Labels := by
      have hz : ∀ j, raw30083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30083step0 = (fun i j => raw30083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30083step0 raw30083; decide +kernel
      have hl : raw30083step0Labels = raw30083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30083 raw30083Labels permutation346 hz
    mixedMoment B raw30083step0 raw30083step0Labels = mixedMoment B raw30083step1 raw30083step1Labels := by
      have ha : raw30083step1 = (fun i j => raw30083step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30083step1 raw30083step0; decide +kernel
      have hl : raw30083step1Labels = raw30083step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30083step0 raw30083step0Labels permutation33 permutation2
    _ = mixedMoment B node4966 node4966Labels := by rfl

theorem canonical30084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30084 raw30084Labels = mixedMoment B node5112 node5112Labels := by
  calc
    mixedMoment B raw30084 raw30084Labels = mixedMoment B raw30084step0 raw30084step0Labels := by
      have ha : raw30084step0 = (fun i j => raw30084 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30084step0 raw30084; decide +kernel
      have hl : raw30084step0Labels = raw30084Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30084 raw30084Labels permutation153 permutation2
    _ = mixedMoment B node5112 node5112Labels := by rfl

theorem canonical30085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30085 raw30085Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw30085 raw30085Labels = mixedMoment B raw30085step0 raw30085step0Labels := by
      have hz : ∀ j, raw30085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30085step0 = (fun i j => raw30085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30085step0 raw30085; decide +kernel
      have hl : raw30085step0Labels = raw30085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30085 raw30085Labels permutation346 hz
    mixedMoment B raw30085step0 raw30085step0Labels = mixedMoment B raw30085step1 raw30085step1Labels := by
      have ha : raw30085step1 = (fun i j => raw30085step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30085step1 raw30085step0; decide +kernel
      have hl : raw30085step1Labels = raw30085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30085step0 raw30085step0Labels permutation33 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

theorem canonical30086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30086 raw30086Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw30086 raw30086Labels = mixedMoment B raw30086step0 raw30086step0Labels := by
      have hz : ∀ j, raw30086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30086step0 = (fun i j => raw30086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30086step0 raw30086; decide +kernel
      have hl : raw30086step0Labels = raw30086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30086 raw30086Labels permutation346 hz
    mixedMoment B raw30086step0 raw30086step0Labels = mixedMoment B raw30086step1 raw30086step1Labels := by
      have ha : raw30086step1 = (fun i j => raw30086step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30086step1 raw30086step0; decide +kernel
      have hl : raw30086step1Labels = raw30086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30086step0 raw30086step0Labels permutation127 permutation2
    mixedMoment B raw30086step1 raw30086step1Labels = mixedMoment B raw30086step2 raw30086step2Labels := by
      have ha : raw30086step2 = -raw30086step1 := by apply Matrix.ext; change ∀ i j, raw30086step2 i j = -(raw30086step1 i j); unfold raw30086step2 raw30086step1; decide +kernel
      have hl : raw30086step2Labels = raw30086step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4934 node4934Labels := by rfl

theorem canonical30087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30087 raw30087Labels = mixedMoment B node4929 node4929Labels := by
  calc
    mixedMoment B raw30087 raw30087Labels = mixedMoment B raw30087step0 raw30087step0Labels := by
      have ha : raw30087step0 = (fun i j => raw30087 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30087step0 raw30087; decide +kernel
      have hl : raw30087step0Labels = raw30087Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30087 raw30087Labels permutation587 permutation2
    mixedMoment B raw30087step0 raw30087step0Labels = mixedMoment B raw30087step1 raw30087step1Labels := by
      have ha : raw30087step1 = -raw30087step0 := by apply Matrix.ext; change ∀ i j, raw30087step1 i j = -(raw30087step0 i j); unfold raw30087step1 raw30087step0; decide +kernel
      have hl : raw30087step1Labels = raw30087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4929 node4929Labels := by rfl

theorem canonical30088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30088 raw30088Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw30088 raw30088Labels = mixedMoment B raw30088step0 raw30088step0Labels := by
      have hz : ∀ j, raw30088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30088step0 = (fun i j => raw30088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30088step0 raw30088; decide +kernel
      have hl : raw30088step0Labels = raw30088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30088 raw30088Labels permutation346 hz
    mixedMoment B raw30088step0 raw30088step0Labels = mixedMoment B raw30088step1 raw30088step1Labels := by
      have ha : raw30088step1 = (fun i j => raw30088step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30088step1 raw30088step0; decide +kernel
      have hl : raw30088step1Labels = raw30088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30088step0 raw30088step0Labels permutation125 permutation2
    mixedMoment B raw30088step1 raw30088step1Labels = mixedMoment B raw30088step2 raw30088step2Labels := by
      have ha : raw30088step2 = -raw30088step1 := by apply Matrix.ext; change ∀ i j, raw30088step2 i j = -(raw30088step1 i j); unfold raw30088step2 raw30088step1; decide +kernel
      have hl : raw30088step2Labels = raw30088step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4943 node4943Labels := by rfl

theorem canonical30089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30089 raw30089Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw30089 raw30089Labels = mixedMoment B raw30089step0 raw30089step0Labels := by
      have hz : ∀ j, raw30089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30089step0 = (fun i j => raw30089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30089step0 raw30089; decide +kernel
      have hl : raw30089step0Labels = raw30089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30089 raw30089Labels permutation346 hz
    mixedMoment B raw30089step0 raw30089step0Labels = mixedMoment B raw30089step1 raw30089step1Labels := by
      have ha : raw30089step1 = (fun i j => raw30089step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30089step1 raw30089step0; decide +kernel
      have hl : raw30089step1Labels = raw30089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30089step0 raw30089step0Labels permutation127 permutation2
    mixedMoment B raw30089step1 raw30089step1Labels = mixedMoment B raw30089step2 raw30089step2Labels := by
      have ha : raw30089step2 = -raw30089step1 := by apply Matrix.ext; change ∀ i j, raw30089step2 i j = -(raw30089step1 i j); unfold raw30089step2 raw30089step1; decide +kernel
      have hl : raw30089step2Labels = raw30089step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

theorem canonical30090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30090 raw30090Labels = mixedMoment B node4959 node4959Labels := by
  calc
    mixedMoment B raw30090 raw30090Labels = mixedMoment B raw30090step0 raw30090step0Labels := by
      have hz : ∀ j, raw30090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30090step0 = (fun i j => raw30090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30090step0 raw30090; decide +kernel
      have hl : raw30090step0Labels = raw30090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30090 raw30090Labels permutation346 hz
    _ = mixedMoment B node4959 node4959Labels := by rfl

theorem canonical30091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30091 raw30091Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw30091 raw30091Labels = mixedMoment B raw30091step0 raw30091step0Labels := by
      have ha : raw30091step0 = (fun i j => raw30091 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30091step0 raw30091; decide +kernel
      have hl : raw30091step0Labels = raw30091Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30091 raw30091Labels permutation686 permutation3
    mixedMoment B raw30091step0 raw30091step0Labels = mixedMoment B raw30091step1 raw30091step1Labels := by
      have ha : raw30091step1 = -raw30091step0 := by apply Matrix.ext; change ∀ i j, raw30091step1 i j = -(raw30091step0 i j); unfold raw30091step1 raw30091step0; decide +kernel
      have hl : raw30091step1Labels = raw30091step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30091step1 raw30091step1Labels = mixedMoment B raw30091step2 raw30091step2Labels := by
      have ha : raw30091step2 = raw30091step1 := by apply Matrix.ext; unfold raw30091step2 raw30091step1; decide +kernel
      have hl : raw30091step1Labels = labelEmbedding6 ∘ raw30091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30091step1 raw30091step1Labels raw30091step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4956 node4956Labels := by rfl

theorem canonical30092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30092 raw30092Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw30092 raw30092Labels = mixedMoment B raw30092step0 raw30092step0Labels := by
      have hz : ∀ j, raw30092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30092step0 = (fun i j => raw30092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30092step0 raw30092; decide +kernel
      have hl : raw30092step0Labels = raw30092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30092 raw30092Labels permutation346 hz
    mixedMoment B raw30092step0 raw30092step0Labels = mixedMoment B raw30092step1 raw30092step1Labels := by
      have ha : raw30092step1 = (fun i j => raw30092step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30092step1 raw30092step0; decide +kernel
      have hl : raw30092step1Labels = raw30092step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30092step0 raw30092step0Labels permutation151 permutation3
    mixedMoment B raw30092step1 raw30092step1Labels = mixedMoment B raw30092step2 raw30092step2Labels := by
      have ha : raw30092step2 = -raw30092step1 := by apply Matrix.ext; change ∀ i j, raw30092step2 i j = -(raw30092step1 i j); unfold raw30092step2 raw30092step1; decide +kernel
      have hl : raw30092step2Labels = raw30092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30092step2 raw30092step2Labels = mixedMoment B raw30092step3 raw30092step3Labels := by
      have ha : raw30092step3 = raw30092step2 := by apply Matrix.ext; unfold raw30092step3 raw30092step2; decide +kernel
      have hl : raw30092step2Labels = labelEmbedding6 ∘ raw30092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30092step2 raw30092step2Labels raw30092step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10342 raw10342Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw10342 raw10342Labels = mixedMoment B raw10342step0 raw10342step0Labels := by
      have hz : ∀ j, raw10342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10342step0 = (fun i j => raw10342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10342step0 raw10342; decide +kernel
      have hl : raw10342step0Labels = raw10342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10342 raw10342Labels permutation346 hz
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical10353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10353 raw10353Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw10353 raw10353Labels = mixedMoment B raw10353step0 raw10353step0Labels := by
      have ha : raw10353step0 = (fun i j => raw10353 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10353step0 raw10353; decide +kernel
      have hl : raw10353step0Labels = raw10353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10353 raw10353Labels permutation158 permutation2
    _ = mixedMoment B node5135 node5135Labels := by rfl

theorem canonical10358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10358 raw10358Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw10358 raw10358Labels = mixedMoment B raw10358step0 raw10358step0Labels := by
      have hz : ∀ j, raw10358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10358step0 = (fun i j => raw10358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10358step0 raw10358; decide +kernel
      have hl : raw10358step0Labels = raw10358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10358 raw10358Labels permutation346 hz
    _ = mixedMoment B node5164 node5164Labels := by rfl

theorem canonical10362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10362 raw10362Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw10362 raw10362Labels = mixedMoment B raw10362step0 raw10362step0Labels := by
      have hz : ∀ j, raw10362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10362step0 = (fun i j => raw10362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10362step0 raw10362; decide +kernel
      have hl : raw10362step0Labels = raw10362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10362 raw10362Labels permutation346 hz
    mixedMoment B raw10362step0 raw10362step0Labels = mixedMoment B raw10362step1 raw10362step1Labels := by
      have hz : ∀ j, raw10362step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10362step1 = (fun i j => raw10362step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10362step1 raw10362step0; decide +kernel
      have hl : raw10362step1Labels = raw10362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10362step0 raw10362step0Labels permutation56 hz
    mixedMoment B raw10362step1 raw10362step1Labels = mixedMoment B raw10362step2 raw10362step2Labels := by
      have ha : raw10362step2 = (fun i j => raw10362step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10362step2 raw10362step1; decide +kernel
      have hl : raw10362step2Labels = raw10362step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10362step1 raw10362step1Labels permutation9 permutation2
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical10364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10364 raw10364Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10364 raw10364Labels = mixedMoment B raw10364step0 raw10364step0Labels := by
      have hz : ∀ j, raw10364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10364step0 = (fun i j => raw10364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10364step0 raw10364; decide +kernel
      have hl : raw10364step0Labels = raw10364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10364 raw10364Labels permutation265 hz
    mixedMoment B raw10364step0 raw10364step0Labels = mixedMoment B raw10364step1 raw10364step1Labels := by
      have ha : raw10364step1 = (fun i j => raw10364step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10364step1 raw10364step0; decide +kernel
      have hl : raw10364step1Labels = raw10364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10364step0 raw10364step0Labels permutation33 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical10365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10365 raw10365Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw10365 raw10365Labels = mixedMoment B raw10365step0 raw10365step0Labels := by
      have hz : ∀ j, raw10365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10365step0 = (fun i j => raw10365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10365step0 raw10365; decide +kernel
      have hl : raw10365step0Labels = raw10365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10365 raw10365Labels permutation346 hz
    mixedMoment B raw10365step0 raw10365step0Labels = mixedMoment B raw10365step1 raw10365step1Labels := by
      have hz : ∀ j, raw10365step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10365step1 = (fun i j => raw10365step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10365step1 raw10365step0; decide +kernel
      have hl : raw10365step1Labels = raw10365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10365step0 raw10365step0Labels permutation56 hz
    mixedMoment B raw10365step1 raw10365step1Labels = mixedMoment B raw10365step2 raw10365step2Labels := by
      have ha : raw10365step2 = (fun i j => raw10365step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10365step2 raw10365step1; decide +kernel
      have hl : raw10365step2Labels = raw10365step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10365step1 raw10365step1Labels permutation9 permutation2
    _ = mixedMoment B node5111 node5111Labels := by rfl

theorem canonical10366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10366 raw10366Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw10366 raw10366Labels = mixedMoment B raw10366step0 raw10366step0Labels := by
      have hz : ∀ j, raw10366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10366step0 = (fun i j => raw10366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10366step0 raw10366; decide +kernel
      have hl : raw10366step0Labels = raw10366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10366 raw10366Labels permutation346 hz
    mixedMoment B raw10366step0 raw10366step0Labels = mixedMoment B raw10366step1 raw10366step1Labels := by
      have hz : ∀ j, raw10366step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10366step1 = (fun i j => raw10366step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10366step1 raw10366step0; decide +kernel
      have hl : raw10366step1Labels = raw10366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10366step0 raw10366step0Labels permutation56 hz
    mixedMoment B raw10366step1 raw10366step1Labels = mixedMoment B raw10366step2 raw10366step2Labels := by
      have ha : raw10366step2 = (fun i j => raw10366step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10366step2 raw10366step1; decide +kernel
      have hl : raw10366step2Labels = raw10366step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10366step1 raw10366step1Labels permutation9 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10368 raw10368Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw10368 raw10368Labels = mixedMoment B raw10368step0 raw10368step0Labels := by
      have hz : ∀ j, raw10368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10368step0 = (fun i j => raw10368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10368step0 raw10368; decide +kernel
      have hl : raw10368step0Labels = raw10368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10368 raw10368Labels permutation346 hz
    _ = mixedMoment B node5139 node5139Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4943 node4943Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2334 node2334Labels + mixedMoment B node3411 node3411Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1908 singletonSmall4943
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4943) = raw1908Labels := by decide +kernel
  rw [hl, canonical1908 B hB] at h
  have hc0 : mixedMoment B raw1908 (Fin.cases (0 : Fin 2) singletonSmall4943) =
      mixedMoment B node2334 node2334Labels := by
    have ha : raw1908 = raw1909 := by apply Matrix.ext; unfold raw1908 raw1909; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4943 = raw1909Labels := by decide +kernel
    rw [ha, hj, canonical1909 B hB]
  have hc1 : mixedMoment B raw1908 (Fin.cases (1 : Fin 2) singletonSmall4943) =
      mixedMoment B node3411 node3411Labels := by
    have ha : raw1908 = raw1910 := by apply Matrix.ext; unfold raw1908 raw1910; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4943 = raw1910Labels := by decide +kernel
    rw [ha, hj, canonical1910 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4972 node4972Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2434 node2434Labels + mixedMoment B node3457 node3457Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1956 singletonSmall4972
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4972) = raw1956Labels := by decide +kernel
  rw [hl, canonical1956 B hB] at h
  have hc0 : mixedMoment B raw1956 (Fin.cases (0 : Fin 2) singletonSmall4972) =
      mixedMoment B node2434 node2434Labels := by
    have ha : raw1956 = raw1957 := by apply Matrix.ext; unfold raw1956 raw1957; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4972 = raw1957Labels := by decide +kernel
    rw [ha, hj, canonical1957 B hB]
  have hc1 : mixedMoment B raw1956 (Fin.cases (1 : Fin 2) singletonSmall4972) =
      mixedMoment B node3457 node3457Labels := by
    have ha : raw1956 = raw1958 := by apply Matrix.ext; unfold raw1956 raw1958; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4972 = raw1958Labels := by decide +kernel
    rw [ha, hj, canonical1958 B hB]
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

theorem singleton5036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5036 node5036Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2428 node2428Labels + mixedMoment B node3450 node3450Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2055 singletonSmall5036
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5036) = raw2055Labels := by decide +kernel
  rw [hl, canonical2055 B hB] at h
  have hc0 : mixedMoment B raw2055 (Fin.cases (0 : Fin 2) singletonSmall5036) =
      mixedMoment B node2428 node2428Labels := by
    have ha : raw2055 = raw2056 := by apply Matrix.ext; unfold raw2055 raw2056; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5036 = raw2056Labels := by decide +kernel
    rw [ha, hj, canonical2056 B hB]
  have hc1 : mixedMoment B raw2055 (Fin.cases (1 : Fin 2) singletonSmall5036) =
      mixedMoment B node3450 node3450Labels := by
    have ha : raw2055 = raw2057 := by apply Matrix.ext; unfold raw2055 raw2057; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5036 = raw2057Labels := by decide +kernel
    rw [ha, hj, canonical2057 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5134 node5134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2553 node2553Labels + mixedMoment B node3514 node3514Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2163 singletonSmall5134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5134) = raw2163Labels := by decide +kernel
  rw [hl, canonical2163 B hB] at h
  have hc0 : mixedMoment B raw2163 (Fin.cases (0 : Fin 2) singletonSmall5134) =
      mixedMoment B node2553 node2553Labels := by
    have ha : raw2163 = raw2164 := by apply Matrix.ext; unfold raw2163 raw2164; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5134 = raw2164Labels := by decide +kernel
    rw [ha, hj, canonical2164 B hB]
  have hc1 : mixedMoment B raw2163 (Fin.cases (1 : Fin 2) singletonSmall5134) =
      mixedMoment B node3514 node3514Labels := by
    have ha : raw2163 = raw2165 := by apply Matrix.ext; unfold raw2163 raw2165; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5134 = raw2165Labels := by decide +kernel
    rw [ha, hj, canonical2165 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5163 node5163Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2590 node2590Labels + mixedMoment B node3564 node3564Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2190 singletonSmall5163
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5163) = raw2190Labels := by decide +kernel
  rw [hl, canonical2190 B hB] at h
  have hc0 : mixedMoment B raw2190 (Fin.cases (0 : Fin 2) singletonSmall5163) =
      mixedMoment B node2590 node2590Labels := by
    have ha : raw2190 = raw2191 := by apply Matrix.ext; unfold raw2190 raw2191; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5163 = raw2191Labels := by decide +kernel
    rw [ha, hj, canonical2191 B hB]
  have hc1 : mixedMoment B raw2190 (Fin.cases (1 : Fin 2) singletonSmall5163) =
      mixedMoment B node3564 node3564Labels := by
    have ha : raw2190 = raw2192 := by apply Matrix.ext; unfold raw2190 raw2192; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5163 = raw2192Labels := by decide +kernel
    rw [ha, hj, canonical2192 B hB]
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

theorem singleton5275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5275 node5275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2743 node2743Labels + mixedMoment B node3548 node3548Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2286 singletonSmall5275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5275) = raw2286Labels := by decide +kernel
  rw [hl, canonical2286 B hB] at h
  have hc0 : mixedMoment B raw2286 (Fin.cases (0 : Fin 2) singletonSmall5275) =
      mixedMoment B node2743 node2743Labels := by
    have ha : raw2286 = raw2287 := by apply Matrix.ext; unfold raw2286 raw2287; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5275 = raw2287Labels := by decide +kernel
    rw [ha, hj, canonical2287 B hB]
  have hc1 : mixedMoment B raw2286 (Fin.cases (1 : Fin 2) singletonSmall5275) =
      mixedMoment B node3548 node3548Labels := by
    have ha : raw2286 = raw2288 := by apply Matrix.ext; unfold raw2286 raw2288; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5275 = raw2288Labels := by decide +kernel
    rw [ha, hj, canonical2288 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5351 node5351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3689 node3689Labels + mixedMoment B node3757 node3757Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2391 singletonSmall5351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5351) = raw2391Labels := by decide +kernel
  rw [hl, canonical2391 B hB] at h
  have hc0 : mixedMoment B raw2391 (Fin.cases (0 : Fin 2) singletonSmall5351) =
      mixedMoment B node3689 node3689Labels := by
    have ha : raw2391 = raw2392 := by apply Matrix.ext; unfold raw2391 raw2392; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5351 = raw2392Labels := by decide +kernel
    rw [ha, hj, canonical2392 B hB]
  have hc1 : mixedMoment B raw2391 (Fin.cases (1 : Fin 2) singletonSmall5351) =
      mixedMoment B node3757 node3757Labels := by
    have ha : raw2391 = raw2393 := by apply Matrix.ext; unfold raw2391 raw2393; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5351 = raw2393Labels := by decide +kernel
    rw [ha, hj, canonical2393 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5355 node5355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3693 node3693Labels + mixedMoment B node3770 node3770Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2400 singletonSmall5355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5355) = raw2400Labels := by decide +kernel
  rw [hl, canonical2400 B hB] at h
  have hc0 : mixedMoment B raw2400 (Fin.cases (0 : Fin 2) singletonSmall5355) =
      mixedMoment B node3693 node3693Labels := by
    have ha : raw2400 = raw2401 := by apply Matrix.ext; unfold raw2400 raw2401; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5355 = raw2401Labels := by decide +kernel
    rw [ha, hj, canonical2401 B hB]
  have hc1 : mixedMoment B raw2400 (Fin.cases (1 : Fin 2) singletonSmall5355) =
      mixedMoment B node3770 node3770Labels := by
    have ha : raw2400 = raw2402 := by apply Matrix.ext; unfold raw2400 raw2402; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5355 = raw2402Labels := by decide +kernel
    rw [ha, hj, canonical2402 B hB]
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

theorem singleton5428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5428 node5428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3845 node3845Labels + mixedMoment B node3845 node3845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2517 singletonSmall5428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5428) = raw2517Labels := by decide +kernel
  rw [hl, canonical2517 B hB] at h
  have hc0 : mixedMoment B raw2517 (Fin.cases (0 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2518 := by apply Matrix.ext; unfold raw2517 raw2518; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5428 = raw2518Labels := by decide +kernel
    rw [ha, hj, canonical2518 B hB]
  have hc1 : mixedMoment B raw2517 (Fin.cases (1 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2519 := by apply Matrix.ext; unfold raw2517 raw2519; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5428 = raw2519Labels := by decide +kernel
    rw [ha, hj, canonical2519 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2334 node2334Labels = Sparse.eval nodeValue2334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2334) = mixedMoment B node2334 node2334Labels := rfl
  simpa [nodeValue2334, Sparse.eval] using hc.symm

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

theorem sound2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2428 node2428Labels = Sparse.eval nodeValue2428 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2428) = mixedMoment B node2428 node2428Labels := rfl
  simpa [nodeValue2428, Sparse.eval] using hc.symm

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

theorem sound2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2434 node2434Labels = Sparse.eval nodeValue2434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2434) = mixedMoment B node2434 node2434Labels := rfl
  simpa [nodeValue2434, Sparse.eval] using hc.symm

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

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

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

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

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

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

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

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

theorem sound3411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3411 node3411Labels = Sparse.eval nodeValue3411 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3411) = mixedMoment B node3411 node3411Labels := rfl
  simpa [nodeValue3411, Sparse.eval] using hc.symm

theorem sound3450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3450 node3450Labels = Sparse.eval nodeValue3450 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3450) = mixedMoment B node3450 node3450Labels := rfl
  simpa [nodeValue3450, Sparse.eval] using hc.symm

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

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3564 node3564Labels = Sparse.eval nodeValue3564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3564) = mixedMoment B node3564 node3564Labels := rfl
  simpa [nodeValue3564, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

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

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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

theorem sound4533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4533 node4533Labels = Sparse.eval nodeValue4533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4533) = mixedMoment B node4533 node4533Labels := rfl
  simpa [nodeValue4533, Sparse.eval] using hc.symm

theorem sound4534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4534 node4534Labels = Sparse.eval nodeValue4534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4534) = mixedMoment B node4534 node4534Labels := rfl
  simpa [nodeValue4534, Sparse.eval] using hc.symm

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

theorem sound4556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4556 node4556Labels = Sparse.eval nodeValue4556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4556) = mixedMoment B node4556 node4556Labels := rfl
  simpa [nodeValue4556, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4929 node4929Labels = 0 := by
  exact mixedMoment_alpha B hF node4929 node4929Labels 1 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4929 node4929Labels = Sparse.eval nodeValue4929 (mixedVector B) := by
  simpa only [nodeValue4929, Sparse.eval_nil] using zero4929 B _hB _hF

theorem sound4934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4934 node4934Labels = Sparse.eval nodeValue4934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4934) = mixedMoment B node4934 node4934Labels := rfl
  simpa [nodeValue4934, Sparse.eval] using hc.symm

theorem sound4943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4943 node4943Labels = Sparse.eval nodeValue4943 (mixedVector B) := by
  have h := singleton4943 B _hB
  rw [sound2334 B _hB _hF, sound3411 B _hB _hF] at h
  norm_num [nodeValue4943, nodeValue2334, nodeValue3411, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4955 node4955Labels = Sparse.eval nodeValue4955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4955) = mixedMoment B node4955 node4955Labels := rfl
  simpa [nodeValue4955, Sparse.eval] using hc.symm

theorem sound4956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4956 node4956Labels = Sparse.eval nodeValue4956 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4956) = mixedMoment B node4956 node4956Labels := rfl
  simpa [nodeValue4956, Sparse.eval] using hc.symm

theorem sound4959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4959 node4959Labels = Sparse.eval nodeValue4959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4959) = mixedMoment B node4959 node4959Labels := rfl
  simpa [nodeValue4959, Sparse.eval] using hc.symm

theorem sound4966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4966 node4966Labels = Sparse.eval nodeValue4966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4966) = mixedMoment B node4966 node4966Labels := rfl
  simpa [nodeValue4966, Sparse.eval] using hc.symm

theorem sound4972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4972 node4972Labels = Sparse.eval nodeValue4972 (mixedVector B) := by
  have h := singleton4972 B _hB
  rw [sound2434 B _hB _hF, sound3457 B _hB _hF] at h
  norm_num [nodeValue4972, nodeValue2434, nodeValue3457, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5036 node5036Labels = Sparse.eval nodeValue5036 (mixedVector B) := by
  have h := singleton5036 B _hB
  rw [sound2428 B _hB _hF, sound3450 B _hB _hF] at h
  norm_num [nodeValue5036, nodeValue2428, nodeValue3450, Sparse.eval] at h ⊢
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

theorem sound5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5075 node5075Labels = Sparse.eval nodeValue5075 (mixedVector B) := by
  have h := singleton5075 B _hB
  rw [sound2482 B _hB _hF, sound3468 B _hB _hF] at h
  norm_num [nodeValue5075, nodeValue2482, nodeValue3468, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = Sparse.eval nodeValue5111 (mixedVector B) := by
  simpa only [nodeValue5111, Sparse.eval_nil] using zero5111 B _hB _hF

theorem sound5112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5112 node5112Labels = Sparse.eval nodeValue5112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5112) = mixedMoment B node5112 node5112Labels := rfl
  simpa [nodeValue5112, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5135 node5135Labels = 0 := by
  exact mixedMoment_alpha B hF node5135 node5135Labels 1 permutation160
    (by decide +kernel)

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

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5135 node5135Labels = Sparse.eval nodeValue5135 (mixedVector B) := by
  simpa only [nodeValue5135, Sparse.eval_nil] using zero5135 B _hB _hF

theorem sound5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5139 node5139Labels = Sparse.eval nodeValue5139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5139) = mixedMoment B node5139 node5139Labels := rfl
  simpa [nodeValue5139, Sparse.eval] using hc.symm

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5163 node5163Labels = Sparse.eval nodeValue5163 (mixedVector B) := by
  have h := singleton5163 B _hB
  rw [sound2590 B _hB _hF, sound3564 B _hB _hF] at h
  norm_num [nodeValue5163, nodeValue2590, nodeValue3564, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5164 node5164Labels = Sparse.eval nodeValue5164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5164) = mixedMoment B node5164 node5164Labels := rfl
  simpa [nodeValue5164, Sparse.eval] using hc.symm

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

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

theorem sound5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5275 node5275Labels = Sparse.eval nodeValue5275 (mixedVector B) := by
  have h := singleton5275 B _hB
  rw [sound2743 B _hB _hF, sound3548 B _hB _hF] at h
  norm_num [nodeValue5275, nodeValue2743, nodeValue3548, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = 0 := by
  exact mixedMoment_order_one B hB node5367 node5367Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5351 node5351Labels = Sparse.eval nodeValue5351 (mixedVector B) := by
  have h := singleton5351 B _hB
  rw [sound3689 B _hB _hF, sound3757 B _hB _hF] at h
  norm_num [nodeValue5351, nodeValue3689, nodeValue3757, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5409 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = 0 := by
  exact mixedMoment_order_one B hB node5409 node5409Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5409 node5409Labels = Sparse.eval nodeValue5409 (mixedVector B) := by
  simpa only [nodeValue5409, Sparse.eval_nil] using zero5409 B _hB _hF

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources68
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2190 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 1) (sourceB2190 + difference 1 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 1) (sourceB2190 + difference 1 0) sourceC2190) = raw30076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30076; decide +kernel
    rw [ha]
    exact (canonical30076 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 2) (sourceB2190 + difference 2 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 2) (sourceB2190 + difference 2 0) sourceC2190) = raw30077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30077; decide +kernel
    rw [ha]
    exact (canonical30077 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 3) (sourceB2190 + difference 3 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 3) (sourceB2190 + difference 3 0) sourceC2190) = raw30078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30078; decide +kernel
    rw [ha]
    exact (canonical30078 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 4) (sourceB2190 + difference 4 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 4) (sourceB2190 + difference 4 0) sourceC2190) = raw10342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10342; decide +kernel
    rw [ha]
    exact (canonical10342 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 5) (sourceB2190 + difference 5 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 5) (sourceB2190 + difference 5 0) sourceC2190) = raw30079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30079; decide +kernel
    rw [ha]
    exact (canonical30079 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 0) (sourceB2190 + difference 0 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 0) (sourceB2190 + difference 0 1) sourceC2190) = raw10362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10362; decide +kernel
    rw [ha]
    exact (canonical10362 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 2) (sourceB2190 + difference 2 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 2) (sourceB2190 + difference 2 1) sourceC2190) = raw10364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10364; decide +kernel
    rw [ha]
    exact (canonical10364 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 3) (sourceB2190 + difference 3 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 3) (sourceB2190 + difference 3 1) sourceC2190) = raw10365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10365; decide +kernel
    rw [ha]
    exact (canonical10365 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 4) (sourceB2190 + difference 4 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 4) (sourceB2190 + difference 4 1) sourceC2190) = raw22655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22655; decide +kernel
    rw [ha]
    exact (canonical22655 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 5) (sourceB2190 + difference 5 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 5) (sourceB2190 + difference 5 1) sourceC2190) = raw10366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10366; decide +kernel
    rw [ha]
    exact (canonical10366 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 0) (sourceB2190 + difference 0 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 0) (sourceB2190 + difference 0 2) sourceC2190) = raw22661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22661; decide +kernel
    rw [ha]
    exact (canonical22661 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 1) (sourceB2190 + difference 1 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 1) (sourceB2190 + difference 1 2) sourceC2190) = raw30080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30080; decide +kernel
    rw [ha]
    exact (canonical30080 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 3) (sourceB2190 + difference 3 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 3) (sourceB2190 + difference 3 2) sourceC2190) = raw30081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30081; decide +kernel
    rw [ha]
    exact (canonical30081 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 4) (sourceB2190 + difference 4 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 4) (sourceB2190 + difference 4 2) sourceC2190) = raw10353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10353; decide +kernel
    rw [ha]
    exact (canonical10353 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 5) (sourceB2190 + difference 5 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 5) (sourceB2190 + difference 5 2) sourceC2190) = raw30082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30082; decide +kernel
    rw [ha]
    exact (canonical30082 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 0) (sourceB2190 + difference 0 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 0) (sourceB2190 + difference 0 3) sourceC2190) = raw22665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22665; decide +kernel
    rw [ha]
    exact (canonical22665 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 1) (sourceB2190 + difference 1 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 1) (sourceB2190 + difference 1 3) sourceC2190) = raw30083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30083; decide +kernel
    rw [ha]
    exact (canonical30083 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 2) (sourceB2190 + difference 2 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5112) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 2) (sourceB2190 + difference 2 3) sourceC2190) = raw30084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30084; decide +kernel
    rw [ha]
    exact (canonical30084 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 4) (sourceB2190 + difference 4 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 4) (sourceB2190 + difference 4 3) sourceC2190) = raw10358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10358; decide +kernel
    rw [ha]
    exact (canonical10358 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 5) (sourceB2190 + difference 5 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 5) (sourceB2190 + difference 5 3) sourceC2190) = raw30085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30085; decide +kernel
    rw [ha]
    exact (canonical30085 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 0) (sourceB2190 + difference 0 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 0) (sourceB2190 + difference 0 4) sourceC2190) = raw22669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22669; decide +kernel
    rw [ha]
    exact (canonical22669 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 1) (sourceB2190 + difference 1 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 1) (sourceB2190 + difference 1 4) sourceC2190) = raw30086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30086; decide +kernel
    rw [ha]
    exact (canonical30086 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 2) (sourceB2190 + difference 2 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4929) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 2) (sourceB2190 + difference 2 4) sourceC2190) = raw30087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30087; decide +kernel
    rw [ha]
    exact (canonical30087 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 3) (sourceB2190 + difference 3 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 3) (sourceB2190 + difference 3 4) sourceC2190) = raw30088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30088; decide +kernel
    rw [ha]
    exact (canonical30088 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 5) (sourceB2190 + difference 5 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 5) (sourceB2190 + difference 5 4) sourceC2190) = raw30089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30089; decide +kernel
    rw [ha]
    exact (canonical30089 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 0) (sourceB2190 + difference 0 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4534) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 0) (sourceB2190 + difference 0 5) sourceC2190) = raw22674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22674; decide +kernel
    rw [ha]
    exact (canonical22674 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 1) (sourceB2190 + difference 1 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4959) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 1) (sourceB2190 + difference 1 5) sourceC2190) = raw30090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30090; decide +kernel
    rw [ha]
    exact (canonical30090 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 2) (sourceB2190 + difference 2 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4956) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 2) (sourceB2190 + difference 2 5) sourceC2190) = raw30091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30091; decide +kernel
    rw [ha]
    exact (canonical30091 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 3) (sourceB2190 + difference 3 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 3) (sourceB2190 + difference 3 5) sourceC2190) = raw30092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30092; decide +kernel
    rw [ha]
    exact (canonical30092 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 4) (sourceB2190 + difference 4 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 4) (sourceB2190 + difference 4 5) sourceC2190) = raw10368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10368; decide +kernel
    rw [ha]
    exact (canonical10368 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2190 sourceB2190 sourceC2190
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2190, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1815 : Integer.Sparse.reindex keyMap MixedData.row1815 = numericRow1815 := by decide +kernel

theorem numericCheck1815 (x : Master → ℝ) : Integer.Sparse.eval numericRow1815 x =
    (4 : ℝ) * reducedSource1815 x := by
  norm_num [numericRow1815, reducedSource1815, Integer.Sparse.eval, Sparse.eval, nodeValue4533, nodeValue4534, nodeValue4535, nodeValue4556, nodeValue4612, nodeValue4929, nodeValue4934, nodeValue4943, nodeValue4955, nodeValue4956, nodeValue4959, nodeValue4966, nodeValue4972, nodeValue5036, nodeValue5075, nodeValue5111, nodeValue5112, nodeValue5134, nodeValue5135, nodeValue5139, nodeValue5141, nodeValue5163, nodeValue5164, nodeValue5274, nodeValue5275, nodeValue5351, nodeValue5355, nodeValue5367, nodeValue5409, nodeValue5428] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1815 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1815 (mixedVector B) = 0 := by
  have h4533 : mixedVector B (Sum.inr 4533) = Sparse.eval nodeValue4533 (mixedVector B) := by
    change mixedMoment B node4533 node4533Labels = _
    exact sound4533 B hB hF
  have h4534 : mixedVector B (Sum.inr 4534) = Sparse.eval nodeValue4534 (mixedVector B) := by
    change mixedMoment B node4534 node4534Labels = _
    exact sound4534 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4556 : mixedVector B (Sum.inr 4556) = Sparse.eval nodeValue4556 (mixedVector B) := by
    change mixedMoment B node4556 node4556Labels = _
    exact sound4556 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4929 : mixedVector B (Sum.inr 4929) = Sparse.eval nodeValue4929 (mixedVector B) := by
    change mixedMoment B node4929 node4929Labels = _
    exact sound4929 B hB hF
  have h4934 : mixedVector B (Sum.inr 4934) = Sparse.eval nodeValue4934 (mixedVector B) := by
    change mixedMoment B node4934 node4934Labels = _
    exact sound4934 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4955 : mixedVector B (Sum.inr 4955) = Sparse.eval nodeValue4955 (mixedVector B) := by
    change mixedMoment B node4955 node4955Labels = _
    exact sound4955 B hB hF
  have h4956 : mixedVector B (Sum.inr 4956) = Sparse.eval nodeValue4956 (mixedVector B) := by
    change mixedMoment B node4956 node4956Labels = _
    exact sound4956 B hB hF
  have h4959 : mixedVector B (Sum.inr 4959) = Sparse.eval nodeValue4959 (mixedVector B) := by
    change mixedMoment B node4959 node4959Labels = _
    exact sound4959 B hB hF
  have h4966 : mixedVector B (Sum.inr 4966) = Sparse.eval nodeValue4966 (mixedVector B) := by
    change mixedMoment B node4966 node4966Labels = _
    exact sound4966 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h5036 : mixedVector B (Sum.inr 5036) = Sparse.eval nodeValue5036 (mixedVector B) := by
    change mixedMoment B node5036 node5036Labels = _
    exact sound5036 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5112 : mixedVector B (Sum.inr 5112) = Sparse.eval nodeValue5112 (mixedVector B) := by
    change mixedMoment B node5112 node5112Labels = _
    exact sound5112 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5135 : mixedVector B (Sum.inr 5135) = Sparse.eval nodeValue5135 (mixedVector B) := by
    change mixedMoment B node5135 node5135Labels = _
    exact sound5135 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5163 : mixedVector B (Sum.inr 5163) = Sparse.eval nodeValue5163 (mixedVector B) := by
    change mixedMoment B node5163 node5163Labels = _
    exact sound5163 B hB hF
  have h5164 : mixedVector B (Sum.inr 5164) = Sparse.eval nodeValue5164 (mixedVector B) := by
    change mixedMoment B node5164 node5164Labels = _
    exact sound5164 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5351 : mixedVector B (Sum.inr 5351) = Sparse.eval nodeValue5351 (mixedVector B) := by
    change mixedMoment B node5351 node5351Labels = _
    exact sound5351 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5409 : mixedVector B (Sum.inr 5409) = Sparse.eval nodeValue5409 (mixedVector B) := by
    change mixedMoment B node5409 node5409Labels = _
    exact sound5409 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  simpa only [sourceForm2190, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4533, h4534, h4535, h4556, h4612, h4929, h4934, h4943, h4955, h4956, h4959, h4966, h4972, h5036, h5075, h5111, h5112, h5134, h5135, h5139, h5141, h5163, h5164, h5274, h5275, h5351, h5355, h5367, h5409, h5428, reducedSource1815] using sourceEq2190 B hB

theorem rowSound1815_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1815 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1815, numericCheck1815, reducedZero1815 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e_oai
