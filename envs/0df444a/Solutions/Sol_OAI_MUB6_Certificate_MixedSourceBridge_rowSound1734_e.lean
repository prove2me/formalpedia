-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:38:22.772554+00:00
-- url     : https://prove2.me/submissions/13b080cb-d50c-40be-8914-5e78e3c3af05

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E103
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

theorem canonical1392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1392 raw1392Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw1392 raw1392Labels = mixedMoment B raw1392step0 raw1392step0Labels := by
      have ha : raw1392step0 = (fun i j => raw1392 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1392step0 raw1392; decide +kernel
      have hl : raw1392step0Labels = raw1392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1392 raw1392Labels permutation8 permutation4
    mixedMoment B raw1392step0 raw1392step0Labels = mixedMoment B raw1392step1 raw1392step1Labels := by
      have ha : raw1392step1 = raw1392step0 := by apply Matrix.ext; unfold raw1392step1 raw1392step0; decide +kernel
      have hl : raw1392step0Labels = labelEmbedding7 ∘ raw1392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1392step0 raw1392step0Labels raw1392step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

theorem canonical1393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1393 raw1393Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw1393 raw1393Labels = mixedMoment B raw1393step0 raw1393step0Labels := by
      have ha : raw1393step0 = (fun i j => raw1393 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1393step0 raw1393; decide +kernel
      have hl : raw1393step0Labels = raw1393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1393 raw1393Labels permutation8 permutation4
    _ = mixedMoment B node1143 node1143Labels := by rfl

theorem canonical1394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1394 raw1394Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw1394 raw1394Labels = mixedMoment B raw1394step0 raw1394step0Labels := by
      have ha : raw1394step0 = (fun i j => raw1394 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1394step0 raw1394; decide +kernel
      have hl : raw1394step0Labels = raw1394Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1394 raw1394Labels permutation31 permutation6
    mixedMoment B raw1394step0 raw1394step0Labels = mixedMoment B raw1394step1 raw1394step1Labels := by
      have ha : raw1394step1 = raw1394step0 := by apply Matrix.ext; unfold raw1394step1 raw1394step0; decide +kernel
      have hl : raw1394step0Labels = labelEmbedding1 ∘ raw1394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1394step0 raw1394step0Labels raw1394step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

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

theorem canonical1584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1584 raw1584Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw1584 raw1584Labels = mixedMoment B raw1584step0 raw1584step0Labels := by
      have ha : raw1584step0 = (fun i j => raw1584 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1584step0 raw1584; decide +kernel
      have hl : raw1584step0Labels = raw1584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1584 raw1584Labels permutation8 permutation4
    mixedMoment B raw1584step0 raw1584step0Labels = mixedMoment B raw1584step1 raw1584step1Labels := by
      have ha : raw1584step1 = raw1584step0 := by apply Matrix.ext; unfold raw1584step1 raw1584step0; decide +kernel
      have hl : raw1584step0Labels = labelEmbedding7 ∘ raw1584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1584step0 raw1584step0Labels raw1584step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

theorem canonical1585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1585 raw1585Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw1585 raw1585Labels = mixedMoment B raw1585step0 raw1585step0Labels := by
      have ha : raw1585step0 = (fun i j => raw1585 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1585step0 raw1585; decide +kernel
      have hl : raw1585step0Labels = raw1585Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1585 raw1585Labels permutation8 permutation4
    _ = mixedMoment B node1818 node1818Labels := by rfl

theorem canonical1586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1586 raw1586Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw1586 raw1586Labels = mixedMoment B raw1586step0 raw1586step0Labels := by
      have ha : raw1586step0 = (fun i j => raw1586 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1586step0 raw1586; decide +kernel
      have hl : raw1586step0Labels = raw1586Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1586 raw1586Labels permutation8 permutation6
    mixedMoment B raw1586step0 raw1586step0Labels = mixedMoment B raw1586step1 raw1586step1Labels := by
      have ha : raw1586step1 = -raw1586step0 := by apply Matrix.ext; change ∀ i j, raw1586step1 i j = -(raw1586step0 i j); unfold raw1586step1 raw1586step0; decide +kernel
      have hl : raw1586step1Labels = raw1586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1586step1 raw1586step1Labels = mixedMoment B raw1586step2 raw1586step2Labels := by
      have ha : raw1586step2 = raw1586step1 := by apply Matrix.ext; unfold raw1586step2 raw1586step1; decide +kernel
      have hl : raw1586step1Labels = labelEmbedding1 ∘ raw1586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1586step1 raw1586step1Labels raw1586step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

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

theorem canonical1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1689 raw1689Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw1689 raw1689Labels = mixedMoment B raw1689step0 raw1689step0Labels := by
      have ha : raw1689step0 = (fun i j => raw1689 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1689step0 raw1689; decide +kernel
      have hl : raw1689step0Labels = raw1689Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1689 raw1689Labels permutation152 permutation4
    mixedMoment B raw1689step0 raw1689step0Labels = mixedMoment B raw1689step1 raw1689step1Labels := by
      have ha : raw1689step1 = raw1689step0 := by apply Matrix.ext; unfold raw1689step1 raw1689step0; decide +kernel
      have hl : raw1689step0Labels = labelEmbedding7 ∘ raw1689step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1689step0 raw1689step0Labels raw1689step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1690 raw1690Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw1690 raw1690Labels = mixedMoment B raw1690step0 raw1690step0Labels := by
      have ha : raw1690step0 = (fun i j => raw1690 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1690step0 raw1690; decide +kernel
      have hl : raw1690step0Labels = raw1690Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1690 raw1690Labels permutation152 permutation4
    _ = mixedMoment B node1960 node1960Labels := by rfl

theorem canonical1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1691 raw1691Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw1691 raw1691Labels = mixedMoment B raw1691step0 raw1691step0Labels := by
      have ha : raw1691step0 = (fun i j => raw1691 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1691step0 raw1691; decide +kernel
      have hl : raw1691step0Labels = raw1691Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1691 raw1691Labels permutation152 permutation6
    mixedMoment B raw1691step0 raw1691step0Labels = mixedMoment B raw1691step1 raw1691step1Labels := by
      have ha : raw1691step1 = -raw1691step0 := by apply Matrix.ext; change ∀ i j, raw1691step1 i j = -(raw1691step0 i j); unfold raw1691step1 raw1691step0; decide +kernel
      have hl : raw1691step1Labels = raw1691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1691step1 raw1691step1Labels = mixedMoment B raw1691step2 raw1691step2Labels := by
      have ha : raw1691step2 = raw1691step1 := by apply Matrix.ext; unfold raw1691step2 raw1691step1; decide +kernel
      have hl : raw1691step1Labels = labelEmbedding1 ∘ raw1691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1691step1 raw1691step1Labels raw1691step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

theorem canonical1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1704 raw1704Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw1704 raw1704Labels = mixedMoment B raw1704step0 raw1704step0Labels := by
      have ha : raw1704step0 = (fun i j => raw1704 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1704step0 raw1704; decide +kernel
      have hl : raw1704step0Labels = raw1704Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1704 raw1704Labels permutation32 permutation4
    mixedMoment B raw1704step0 raw1704step0Labels = mixedMoment B raw1704step1 raw1704step1Labels := by
      have ha : raw1704step1 = raw1704step0 := by apply Matrix.ext; unfold raw1704step1 raw1704step0; decide +kernel
      have hl : raw1704step0Labels = labelEmbedding7 ∘ raw1704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1704step0 raw1704step0Labels raw1704step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1705 raw1705Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw1705 raw1705Labels = mixedMoment B raw1705step0 raw1705step0Labels := by
      have ha : raw1705step0 = (fun i j => raw1705 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1705step0 raw1705; decide +kernel
      have hl : raw1705step0Labels = raw1705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1705 raw1705Labels permutation32 permutation4
    _ = mixedMoment B node1969 node1969Labels := by rfl

theorem canonical1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1706 raw1706Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw1706 raw1706Labels = mixedMoment B raw1706step0 raw1706step0Labels := by
      have ha : raw1706step0 = (fun i j => raw1706 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1706step0 raw1706; decide +kernel
      have hl : raw1706step0Labels = raw1706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1706 raw1706Labels permutation32 permutation6
    mixedMoment B raw1706step0 raw1706step0Labels = mixedMoment B raw1706step1 raw1706step1Labels := by
      have ha : raw1706step1 = -raw1706step0 := by apply Matrix.ext; change ∀ i j, raw1706step1 i j = -(raw1706step0 i j); unfold raw1706step1 raw1706step0; decide +kernel
      have hl : raw1706step1Labels = raw1706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1706step1 raw1706step1Labels = mixedMoment B raw1706step2 raw1706step2Labels := by
      have ha : raw1706step2 = raw1706step1 := by apply Matrix.ext; unfold raw1706step2 raw1706step1; decide +kernel
      have hl : raw1706step1Labels = labelEmbedding1 ∘ raw1706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1706step1 raw1706step1Labels raw1706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

theorem canonical1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1737 raw1737Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw1737 raw1737Labels = mixedMoment B raw1737step0 raw1737step0Labels := by
      have ha : raw1737step0 = (fun i j => raw1737 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1737step0 raw1737; decide +kernel
      have hl : raw1737step0Labels = raw1737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1737 raw1737Labels permutation32 permutation4
    mixedMoment B raw1737step0 raw1737step0Labels = mixedMoment B raw1737step1 raw1737step1Labels := by
      have ha : raw1737step1 = raw1737step0 := by apply Matrix.ext; unfold raw1737step1 raw1737step0; decide +kernel
      have hl : raw1737step0Labels = labelEmbedding7 ∘ raw1737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1737step0 raw1737step0Labels raw1737step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1738 raw1738Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw1738 raw1738Labels = mixedMoment B raw1738step0 raw1738step0Labels := by
      have ha : raw1738step0 = (fun i j => raw1738 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1738step0 raw1738; decide +kernel
      have hl : raw1738step0Labels = raw1738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1738 raw1738Labels permutation32 permutation4
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1739 raw1739Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw1739 raw1739Labels = mixedMoment B raw1739step0 raw1739step0Labels := by
      have ha : raw1739step0 = (fun i j => raw1739 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1739step0 raw1739; decide +kernel
      have hl : raw1739step0Labels = raw1739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1739 raw1739Labels permutation34 permutation6
    mixedMoment B raw1739step0 raw1739step0Labels = mixedMoment B raw1739step1 raw1739step1Labels := by
      have ha : raw1739step1 = -raw1739step0 := by apply Matrix.ext; change ∀ i j, raw1739step1 i j = -(raw1739step0 i j); unfold raw1739step1 raw1739step0; decide +kernel
      have hl : raw1739step1Labels = raw1739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1739step1 raw1739step1Labels = mixedMoment B raw1739step2 raw1739step2Labels := by
      have ha : raw1739step2 = raw1739step1 := by apply Matrix.ext; unfold raw1739step2 raw1739step1; decide +kernel
      have hl : raw1739step1Labels = labelEmbedding1 ∘ raw1739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1739step1 raw1739step1Labels raw1739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

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

theorem canonical2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2283 raw2283Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw2283 raw2283Labels = mixedMoment B raw2283step0 raw2283step0Labels := by
      have ha : raw2283step0 = (fun i j => raw2283 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2283step0 raw2283; decide +kernel
      have hl : raw2283step0Labels = raw2283Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2283 raw2283Labels permutation8 permutation4
    mixedMoment B raw2283step0 raw2283step0Labels = mixedMoment B raw2283step1 raw2283step1Labels := by
      have ha : raw2283step1 = raw2283step0 := by apply Matrix.ext; unfold raw2283step1 raw2283step0; decide +kernel
      have hl : raw2283step0Labels = labelEmbedding7 ∘ raw2283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2283step0 raw2283step0Labels raw2283step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2284 raw2284Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2284 raw2284Labels = mixedMoment B raw2284step0 raw2284step0Labels := by
      have ha : raw2284step0 = (fun i j => raw2284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2284step0 raw2284; decide +kernel
      have hl : raw2284step0Labels = raw2284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2284 raw2284Labels permutation8 permutation4
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2285 raw2285Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2285 raw2285Labels = mixedMoment B raw2285step0 raw2285step0Labels := by
      have ha : raw2285step0 = (fun i j => raw2285 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2285step0 raw2285; decide +kernel
      have hl : raw2285step0Labels = raw2285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2285 raw2285Labels permutation31 permutation6
    mixedMoment B raw2285step0 raw2285step0Labels = mixedMoment B raw2285step1 raw2285step1Labels := by
      have ha : raw2285step1 = raw2285step0 := by apply Matrix.ext; unfold raw2285step1 raw2285step0; decide +kernel
      have hl : raw2285step0Labels = labelEmbedding1 ∘ raw2285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2285step0 raw2285step0Labels raw2285step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

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

theorem canonical29063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29063 raw29063Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw29063 raw29063Labels = mixedMoment B raw29063step0 raw29063step0Labels := by
      have hz : ∀ j, raw29063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29063step0 = (fun i j => raw29063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29063step0 raw29063; decide +kernel
      have hl : raw29063step0Labels = raw29063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29063 raw29063Labels permutation434 hz
    mixedMoment B raw29063step0 raw29063step0Labels = mixedMoment B raw29063step1 raw29063step1Labels := by
      have hz : ∀ j, raw29063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29063step1 = (fun i j => raw29063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29063step1 raw29063step0; decide +kernel
      have hl : raw29063step1Labels = raw29063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29063step0 raw29063step0Labels permutation80 hz
    mixedMoment B raw29063step1 raw29063step1Labels = mixedMoment B raw29063step2 raw29063step2Labels := by
      have ha : raw29063step2 = (fun i j => raw29063step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29063step2 raw29063step1; decide +kernel
      have hl : raw29063step2Labels = raw29063step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29063step1 raw29063step1Labels permutation31 permutation2
    mixedMoment B raw29063step2 raw29063step2Labels = mixedMoment B raw29063step3 raw29063step3Labels := by
      have ha : raw29063step3 = -raw29063step2 := by apply Matrix.ext; change ∀ i j, raw29063step3 i j = -(raw29063step2 i j); unfold raw29063step3 raw29063step2; decide +kernel
      have hl : raw29063step3Labels = raw29063step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical29064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29064 raw29064Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw29064 raw29064Labels = mixedMoment B raw29064step0 raw29064step0Labels := by
      have hz : ∀ j, raw29064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29064step0 = (fun i j => raw29064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29064step0 raw29064; decide +kernel
      have hl : raw29064step0Labels = raw29064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29064 raw29064Labels permutation434 hz
    mixedMoment B raw29064step0 raw29064step0Labels = mixedMoment B raw29064step1 raw29064step1Labels := by
      have ha : raw29064step1 = (fun i j => raw29064step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29064step1 raw29064step0; decide +kernel
      have hl : raw29064step1Labels = raw29064step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29064step0 raw29064step0Labels permutation151 permutation2
    mixedMoment B raw29064step1 raw29064step1Labels = mixedMoment B raw29064step2 raw29064step2Labels := by
      have ha : raw29064step2 = -raw29064step1 := by apply Matrix.ext; change ∀ i j, raw29064step2 i j = -(raw29064step1 i j); unfold raw29064step2 raw29064step1; decide +kernel
      have hl : raw29064step2Labels = raw29064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical29065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29065 raw29065Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw29065 raw29065Labels = mixedMoment B raw29065step0 raw29065step0Labels := by
      have hz : ∀ j, raw29065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29065step0 = (fun i j => raw29065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29065step0 raw29065; decide +kernel
      have hl : raw29065step0Labels = raw29065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29065 raw29065Labels permutation346 hz
    mixedMoment B raw29065step0 raw29065step0Labels = mixedMoment B raw29065step1 raw29065step1Labels := by
      have ha : raw29065step1 = (fun i j => raw29065step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29065step1 raw29065step0; decide +kernel
      have hl : raw29065step1Labels = raw29065step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29065step0 raw29065step0Labels permutation151 permutation2
    mixedMoment B raw29065step1 raw29065step1Labels = mixedMoment B raw29065step2 raw29065step2Labels := by
      have ha : raw29065step2 = -raw29065step1 := by apply Matrix.ext; change ∀ i j, raw29065step2 i j = -(raw29065step1 i j); unfold raw29065step2 raw29065step1; decide +kernel
      have hl : raw29065step2Labels = raw29065step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical29066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29066 raw29066Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29066 raw29066Labels = mixedMoment B raw29066step0 raw29066step0Labels := by
      have hz : ∀ j, raw29066 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29066step0 = (fun i j => raw29066 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29066step0 raw29066; decide +kernel
      have hl : raw29066step0Labels = raw29066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29066 raw29066Labels permutation520 hz
    mixedMoment B raw29066step0 raw29066step0Labels = mixedMoment B raw29066step1 raw29066step1Labels := by
      have hz : ∀ j, raw29066step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29066step1 = (fun i j => raw29066step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29066step1 raw29066step0; decide +kernel
      have hl : raw29066step1Labels = raw29066step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29066step0 raw29066step0Labels permutation104 hz
    mixedMoment B raw29066step1 raw29066step1Labels = mixedMoment B raw29066step2 raw29066step2Labels := by
      have hz : ∀ j, raw29066step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29066step2 = (fun i j => raw29066step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29066step2 raw29066step1; decide +kernel
      have hl : raw29066step2Labels = raw29066step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29066step1 raw29066step1Labels permutation20 hz
    mixedMoment B raw29066step2 raw29066step2Labels = mixedMoment B raw29066step3 raw29066step3Labels := by
      have hz : ∀ i, raw29066step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw29066step3 = (fun i j => raw29066step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw29066step3 raw29066step2; decide +kernel
      have hl : raw29066step3Labels = (fun j => raw29066step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29066step2 raw29066step2Labels permutation4 hz
    mixedMoment B raw29066step3 raw29066step3Labels = mixedMoment B raw29066step4 raw29066step4Labels := by
      have ha : raw29066step4 = (fun i j => raw29066step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29066step4 raw29066step3; decide +kernel
      have hl : raw29066step4Labels = raw29066step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29066step3 raw29066step3Labels permutation7 permutation0
    mixedMoment B raw29066step4 raw29066step4Labels = mixedMoment B raw29066step5 raw29066step5Labels := by
      have ha : raw29066step5 = -raw29066step4 := by apply Matrix.ext; change ∀ i j, raw29066step5 i j = -(raw29066step4 i j); unfold raw29066step5 raw29066step4; decide +kernel
      have hl : raw29066step5Labels = raw29066step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29066step5 raw29066step5Labels = mixedMoment B raw29066step6 raw29066step6Labels := by
      have ha : raw29066step6 = raw29066step5 := by apply Matrix.ext; unfold raw29066step6 raw29066step5; decide +kernel
      have hl : raw29066step5Labels = labelEmbedding2 ∘ raw29066step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29066step5 raw29066step5Labels raw29066step6Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical29067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29067 raw29067Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw29067 raw29067Labels = mixedMoment B raw29067step0 raw29067step0Labels := by
      have hz : ∀ j, raw29067 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29067step0 = (fun i j => raw29067 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29067step0 raw29067; decide +kernel
      have hl : raw29067step0Labels = raw29067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29067 raw29067Labels permutation434 hz
    mixedMoment B raw29067step0 raw29067step0Labels = mixedMoment B raw29067step1 raw29067step1Labels := by
      have hz : ∀ j, raw29067step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29067step1 = (fun i j => raw29067step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29067step1 raw29067step0; decide +kernel
      have hl : raw29067step1Labels = raw29067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29067step0 raw29067step0Labels permutation80 hz
    mixedMoment B raw29067step1 raw29067step1Labels = mixedMoment B raw29067step2 raw29067step2Labels := by
      have ha : raw29067step2 = (fun i j => raw29067step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29067step2 raw29067step1; decide +kernel
      have hl : raw29067step2Labels = raw29067step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29067step1 raw29067step1Labels permutation31 permutation7
    mixedMoment B raw29067step2 raw29067step2Labels = mixedMoment B raw29067step3 raw29067step3Labels := by
      have ha : raw29067step3 = raw29067step2 := by apply Matrix.ext; unfold raw29067step3 raw29067step2; decide +kernel
      have hl : raw29067step2Labels = labelEmbedding10 ∘ raw29067step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29067step2 raw29067step2Labels raw29067step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical29068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29068 raw29068Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw29068 raw29068Labels = mixedMoment B raw29068step0 raw29068step0Labels := by
      have hz : ∀ j, raw29068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29068step0 = (fun i j => raw29068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29068step0 raw29068; decide +kernel
      have hl : raw29068step0Labels = raw29068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29068 raw29068Labels permutation434 hz
    mixedMoment B raw29068step0 raw29068step0Labels = mixedMoment B raw29068step1 raw29068step1Labels := by
      have hz : ∀ j, raw29068step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29068step1 = (fun i j => raw29068step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29068step1 raw29068step0; decide +kernel
      have hl : raw29068step1Labels = raw29068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29068step0 raw29068step0Labels permutation80 hz
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical29069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29069 raw29069Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw29069 raw29069Labels = mixedMoment B raw29069step0 raw29069step0Labels := by
      have hz : ∀ j, raw29069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29069step0 = (fun i j => raw29069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29069step0 raw29069; decide +kernel
      have hl : raw29069step0Labels = raw29069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29069 raw29069Labels permutation434 hz
    mixedMoment B raw29069step0 raw29069step0Labels = mixedMoment B raw29069step1 raw29069step1Labels := by
      have ha : raw29069step1 = (fun i j => raw29069step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29069step1 raw29069step0; decide +kernel
      have hl : raw29069step1Labels = raw29069step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29069step0 raw29069step0Labels permutation149 permutation2
    mixedMoment B raw29069step1 raw29069step1Labels = mixedMoment B raw29069step2 raw29069step2Labels := by
      have ha : raw29069step2 = -raw29069step1 := by apply Matrix.ext; change ∀ i j, raw29069step2 i j = -(raw29069step1 i j); unfold raw29069step2 raw29069step1; decide +kernel
      have hl : raw29069step2Labels = raw29069step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical29070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29070 raw29070Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw29070 raw29070Labels = mixedMoment B raw29070step0 raw29070step0Labels := by
      have hz : ∀ j, raw29070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29070step0 = (fun i j => raw29070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29070step0 raw29070; decide +kernel
      have hl : raw29070step0Labels = raw29070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29070 raw29070Labels permutation346 hz
    mixedMoment B raw29070step0 raw29070step0Labels = mixedMoment B raw29070step1 raw29070step1Labels := by
      have ha : raw29070step1 = (fun i j => raw29070step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29070step1 raw29070step0; decide +kernel
      have hl : raw29070step1Labels = raw29070step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29070step0 raw29070step0Labels permutation149 permutation2
    mixedMoment B raw29070step1 raw29070step1Labels = mixedMoment B raw29070step2 raw29070step2Labels := by
      have ha : raw29070step2 = -raw29070step1 := by apply Matrix.ext; change ∀ i j, raw29070step2 i j = -(raw29070step1 i j); unfold raw29070step2 raw29070step1; decide +kernel
      have hl : raw29070step2Labels = raw29070step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical29071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29071 raw29071Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw29071 raw29071Labels = mixedMoment B raw29071step0 raw29071step0Labels := by
      have hz : ∀ j, raw29071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29071step0 = (fun i j => raw29071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29071step0 raw29071; decide +kernel
      have hl : raw29071step0Labels = raw29071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29071 raw29071Labels permutation520 hz
    mixedMoment B raw29071step0 raw29071step0Labels = mixedMoment B raw29071step1 raw29071step1Labels := by
      have hz : ∀ j, raw29071step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29071step1 = (fun i j => raw29071step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29071step1 raw29071step0; decide +kernel
      have hl : raw29071step1Labels = raw29071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29071step0 raw29071step0Labels permutation104 hz
    mixedMoment B raw29071step1 raw29071step1Labels = mixedMoment B raw29071step2 raw29071step2Labels := by
      have hz : ∀ j, raw29071step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29071step2 = (fun i j => raw29071step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29071step2 raw29071step1; decide +kernel
      have hl : raw29071step2Labels = raw29071step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29071step1 raw29071step1Labels permutation20 hz
    mixedMoment B raw29071step2 raw29071step2Labels = mixedMoment B raw29071step3 raw29071step3Labels := by
      have ha : raw29071step3 = (fun i j => raw29071step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29071step3 raw29071step2; decide +kernel
      have hl : raw29071step3Labels = raw29071step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29071step2 raw29071step2Labels permutation7 permutation2
    mixedMoment B raw29071step3 raw29071step3Labels = mixedMoment B raw29071step4 raw29071step4Labels := by
      have ha : raw29071step4 = -raw29071step3 := by apply Matrix.ext; change ∀ i j, raw29071step4 i j = -(raw29071step3 i j); unfold raw29071step4 raw29071step3; decide +kernel
      have hl : raw29071step4Labels = raw29071step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical29072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29072 raw29072Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw29072 raw29072Labels = mixedMoment B raw29072step0 raw29072step0Labels := by
      have hz : ∀ j, raw29072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29072step0 = (fun i j => raw29072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29072step0 raw29072; decide +kernel
      have hl : raw29072step0Labels = raw29072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29072 raw29072Labels permutation434 hz
    mixedMoment B raw29072step0 raw29072step0Labels = mixedMoment B raw29072step1 raw29072step1Labels := by
      have hz : ∀ j, raw29072step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29072step1 = (fun i j => raw29072step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29072step1 raw29072step0; decide +kernel
      have hl : raw29072step1Labels = raw29072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29072step0 raw29072step0Labels permutation80 hz
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical29073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29073 raw29073Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw29073 raw29073Labels = mixedMoment B raw29073step0 raw29073step0Labels := by
      have hz : ∀ j, raw29073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29073step0 = (fun i j => raw29073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29073step0 raw29073; decide +kernel
      have hl : raw29073step0Labels = raw29073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29073 raw29073Labels permutation434 hz
    _ = mixedMoment B node4543 node4543Labels := by rfl

theorem canonical29074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29074 raw29074Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw29074 raw29074Labels = mixedMoment B raw29074step0 raw29074step0Labels := by
      have hz : ∀ j, raw29074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29074step0 = (fun i j => raw29074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29074step0 raw29074; decide +kernel
      have hl : raw29074step0Labels = raw29074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29074 raw29074Labels permutation434 hz
    mixedMoment B raw29074step0 raw29074step0Labels = mixedMoment B raw29074step1 raw29074step1Labels := by
      have ha : raw29074step1 = (fun i j => raw29074step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29074step1 raw29074step0; decide +kernel
      have hl : raw29074step1Labels = raw29074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29074step0 raw29074step0Labels permutation145 permutation2
    mixedMoment B raw29074step1 raw29074step1Labels = mixedMoment B raw29074step2 raw29074step2Labels := by
      have ha : raw29074step2 = -raw29074step1 := by apply Matrix.ext; change ∀ i j, raw29074step2 i j = -(raw29074step1 i j); unfold raw29074step2 raw29074step1; decide +kernel
      have hl : raw29074step2Labels = raw29074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical29075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29075 raw29075Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw29075 raw29075Labels = mixedMoment B raw29075step0 raw29075step0Labels := by
      have ha : raw29075step0 = (fun i j => raw29075 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29075step0 raw29075; decide +kernel
      have hl : raw29075step0Labels = raw29075Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29075 raw29075Labels permutation646 permutation2
    mixedMoment B raw29075step0 raw29075step0Labels = mixedMoment B raw29075step1 raw29075step1Labels := by
      have ha : raw29075step1 = -raw29075step0 := by apply Matrix.ext; change ∀ i j, raw29075step1 i j = -(raw29075step0 i j); unfold raw29075step1 raw29075step0; decide +kernel
      have hl : raw29075step1Labels = raw29075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical29076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29076 raw29076Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw29076 raw29076Labels = mixedMoment B raw29076step0 raw29076step0Labels := by
      have hz : ∀ j, raw29076 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29076step0 = (fun i j => raw29076 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29076step0 raw29076; decide +kernel
      have hl : raw29076step0Labels = raw29076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29076 raw29076Labels permutation520 hz
    mixedMoment B raw29076step0 raw29076step0Labels = mixedMoment B raw29076step1 raw29076step1Labels := by
      have hz : ∀ j, raw29076step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29076step1 = (fun i j => raw29076step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29076step1 raw29076step0; decide +kernel
      have hl : raw29076step1Labels = raw29076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29076step0 raw29076step0Labels permutation104 hz
    mixedMoment B raw29076step1 raw29076step1Labels = mixedMoment B raw29076step2 raw29076step2Labels := by
      have ha : raw29076step2 = (fun i j => raw29076step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29076step2 raw29076step1; decide +kernel
      have hl : raw29076step2Labels = raw29076step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29076step1 raw29076step1Labels permutation31 permutation2
    mixedMoment B raw29076step2 raw29076step2Labels = mixedMoment B raw29076step3 raw29076step3Labels := by
      have ha : raw29076step3 = -raw29076step2 := by apply Matrix.ext; change ∀ i j, raw29076step3 i j = -(raw29076step2 i j); unfold raw29076step3 raw29076step2; decide +kernel
      have hl : raw29076step3Labels = raw29076step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical29077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29077 raw29077Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw29077 raw29077Labels = mixedMoment B raw29077step0 raw29077step0Labels := by
      have hz : ∀ j, raw29077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29077step0 = (fun i j => raw29077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29077step0 raw29077; decide +kernel
      have hl : raw29077step0Labels = raw29077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29077 raw29077Labels permutation434 hz
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical29078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29078 raw29078Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw29078 raw29078Labels = mixedMoment B raw29078step0 raw29078step0Labels := by
      have hz : ∀ j, raw29078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29078step0 = (fun i j => raw29078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29078step0 raw29078; decide +kernel
      have hl : raw29078step0Labels = raw29078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29078 raw29078Labels permutation346 hz
    _ = mixedMoment B node4543 node4543Labels := by rfl

theorem canonical29079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29079 raw29079Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw29079 raw29079Labels = mixedMoment B raw29079step0 raw29079step0Labels := by
      have hz : ∀ j, raw29079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29079step0 = (fun i j => raw29079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29079step0 raw29079; decide +kernel
      have hl : raw29079step0Labels = raw29079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29079 raw29079Labels permutation346 hz
    mixedMoment B raw29079step0 raw29079step0Labels = mixedMoment B raw29079step1 raw29079step1Labels := by
      have ha : raw29079step1 = (fun i j => raw29079step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29079step1 raw29079step0; decide +kernel
      have hl : raw29079step1Labels = raw29079step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29079step0 raw29079step0Labels permutation145 permutation2
    mixedMoment B raw29079step1 raw29079step1Labels = mixedMoment B raw29079step2 raw29079step2Labels := by
      have ha : raw29079step2 = -raw29079step1 := by apply Matrix.ext; change ∀ i j, raw29079step2 i j = -(raw29079step1 i j); unfold raw29079step2 raw29079step1; decide +kernel
      have hl : raw29079step2Labels = raw29079step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical29080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29080 raw29080Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw29080 raw29080Labels = mixedMoment B raw29080step0 raw29080step0Labels := by
      have ha : raw29080step0 = (fun i j => raw29080 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29080step0 raw29080; decide +kernel
      have hl : raw29080step0Labels = raw29080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29080 raw29080Labels permutation664 permutation2
    mixedMoment B raw29080step0 raw29080step0Labels = mixedMoment B raw29080step1 raw29080step1Labels := by
      have ha : raw29080step1 = -raw29080step0 := by apply Matrix.ext; change ∀ i j, raw29080step1 i j = -(raw29080step0 i j); unfold raw29080step1 raw29080step0; decide +kernel
      have hl : raw29080step1Labels = raw29080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical29081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29081 raw29081Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw29081 raw29081Labels = mixedMoment B raw29081step0 raw29081step0Labels := by
      have hz : ∀ j, raw29081 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29081step0 = (fun i j => raw29081 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29081step0 raw29081; decide +kernel
      have hl : raw29081step0Labels = raw29081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29081 raw29081Labels permutation520 hz
    mixedMoment B raw29081step0 raw29081step0Labels = mixedMoment B raw29081step1 raw29081step1Labels := by
      have hz : ∀ j, raw29081step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29081step1 = (fun i j => raw29081step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29081step1 raw29081step0; decide +kernel
      have hl : raw29081step1Labels = raw29081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29081step0 raw29081step0Labels permutation80 hz
    mixedMoment B raw29081step1 raw29081step1Labels = mixedMoment B raw29081step2 raw29081step2Labels := by
      have ha : raw29081step2 = (fun i j => raw29081step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29081step2 raw29081step1; decide +kernel
      have hl : raw29081step2Labels = raw29081step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29081step1 raw29081step1Labels permutation31 permutation2
    mixedMoment B raw29081step2 raw29081step2Labels = mixedMoment B raw29081step3 raw29081step3Labels := by
      have ha : raw29081step3 = -raw29081step2 := by apply Matrix.ext; change ∀ i j, raw29081step3 i j = -(raw29081step2 i j); unfold raw29081step3 raw29081step2; decide +kernel
      have hl : raw29081step3Labels = raw29081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical29082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29082 raw29082Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw29082 raw29082Labels = mixedMoment B raw29082step0 raw29082step0Labels := by
      have hz : ∀ j, raw29082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29082step0 = (fun i j => raw29082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29082step0 raw29082; decide +kernel
      have hl : raw29082step0Labels = raw29082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29082 raw29082Labels permutation346 hz
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical29083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29083 raw29083Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw29083 raw29083Labels = mixedMoment B raw29083step0 raw29083step0Labels := by
      have hz : ∀ j, raw29083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29083step0 = (fun i j => raw29083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29083step0 raw29083; decide +kernel
      have hl : raw29083step0Labels = raw29083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29083 raw29083Labels permutation434 hz
    mixedMoment B raw29083step0 raw29083step0Labels = mixedMoment B raw29083step1 raw29083step1Labels := by
      have hz : ∀ j, raw29083step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29083step1 = (fun i j => raw29083step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29083step1 raw29083step0; decide +kernel
      have hl : raw29083step1Labels = raw29083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29083step0 raw29083step0Labels permutation80 hz
    _ = mixedMoment B node4557 node4557Labels := by rfl

theorem canonical29084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29084 raw29084Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw29084 raw29084Labels = mixedMoment B raw29084step0 raw29084step0Labels := by
      have hz : ∀ j, raw29084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29084step0 = (fun i j => raw29084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29084step0 raw29084; decide +kernel
      have hl : raw29084step0Labels = raw29084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29084 raw29084Labels permutation434 hz
    mixedMoment B raw29084step0 raw29084step0Labels = mixedMoment B raw29084step1 raw29084step1Labels := by
      have hz : ∀ j, raw29084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29084step1 = (fun i j => raw29084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29084step1 raw29084step0; decide +kernel
      have hl : raw29084step1Labels = raw29084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29084step0 raw29084step0Labels permutation80 hz
    mixedMoment B raw29084step1 raw29084step1Labels = mixedMoment B raw29084step2 raw29084step2Labels := by
      have ha : raw29084step2 = (fun i j => raw29084step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29084step2 raw29084step1; decide +kernel
      have hl : raw29084step2Labels = raw29084step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29084step1 raw29084step1Labels permutation31 permutation2
    mixedMoment B raw29084step2 raw29084step2Labels = mixedMoment B raw29084step3 raw29084step3Labels := by
      have ha : raw29084step3 = -raw29084step2 := by apply Matrix.ext; change ∀ i j, raw29084step3 i j = -(raw29084step2 i j); unfold raw29084step3 raw29084step2; decide +kernel
      have hl : raw29084step3Labels = raw29084step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4692 node4692Labels := by rfl

theorem canonical29085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29085 raw29085Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw29085 raw29085Labels = mixedMoment B raw29085step0 raw29085step0Labels := by
      have hz : ∀ j, raw29085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29085step0 = (fun i j => raw29085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29085step0 raw29085; decide +kernel
      have hl : raw29085step0Labels = raw29085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29085 raw29085Labels permutation434 hz
    mixedMoment B raw29085step0 raw29085step0Labels = mixedMoment B raw29085step1 raw29085step1Labels := by
      have ha : raw29085step1 = (fun i j => raw29085step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29085step1 raw29085step0; decide +kernel
      have hl : raw29085step1Labels = raw29085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29085step0 raw29085step0Labels permutation151 permutation2
    mixedMoment B raw29085step1 raw29085step1Labels = mixedMoment B raw29085step2 raw29085step2Labels := by
      have ha : raw29085step2 = -raw29085step1 := by apply Matrix.ext; change ∀ i j, raw29085step2 i j = -(raw29085step1 i j); unfold raw29085step2 raw29085step1; decide +kernel
      have hl : raw29085step2Labels = raw29085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical29086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29086 raw29086Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw29086 raw29086Labels = mixedMoment B raw29086step0 raw29086step0Labels := by
      have hz : ∀ j, raw29086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29086step0 = (fun i j => raw29086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29086step0 raw29086; decide +kernel
      have hl : raw29086step0Labels = raw29086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29086 raw29086Labels permutation346 hz
    mixedMoment B raw29086step0 raw29086step0Labels = mixedMoment B raw29086step1 raw29086step1Labels := by
      have ha : raw29086step1 = (fun i j => raw29086step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29086step1 raw29086step0; decide +kernel
      have hl : raw29086step1Labels = raw29086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29086step0 raw29086step0Labels permutation151 permutation2
    mixedMoment B raw29086step1 raw29086step1Labels = mixedMoment B raw29086step2 raw29086step2Labels := by
      have ha : raw29086step2 = -raw29086step1 := by apply Matrix.ext; change ∀ i j, raw29086step2 i j = -(raw29086step1 i j); unfold raw29086step2 raw29086step1; decide +kernel
      have hl : raw29086step2Labels = raw29086step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical29087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29087 raw29087Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw29087 raw29087Labels = mixedMoment B raw29087step0 raw29087step0Labels := by
      have hz : ∀ j, raw29087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29087step0 = (fun i j => raw29087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29087step0 raw29087; decide +kernel
      have hl : raw29087step0Labels = raw29087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29087 raw29087Labels permutation434 hz
    mixedMoment B raw29087step0 raw29087step0Labels = mixedMoment B raw29087step1 raw29087step1Labels := by
      have hz : ∀ j, raw29087step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29087step1 = (fun i j => raw29087step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29087step1 raw29087step0; decide +kernel
      have hl : raw29087step1Labels = raw29087step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29087step0 raw29087step0Labels permutation80 hz
    _ = mixedMoment B node5110 node5110Labels := by rfl

theorem canonical29088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29088 raw29088Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw29088 raw29088Labels = mixedMoment B raw29088step0 raw29088step0Labels := by
      have hz : ∀ j, raw29088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29088step0 = (fun i j => raw29088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29088step0 raw29088; decide +kernel
      have hl : raw29088step0Labels = raw29088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29088 raw29088Labels permutation434 hz
    mixedMoment B raw29088step0 raw29088step0Labels = mixedMoment B raw29088step1 raw29088step1Labels := by
      have hz : ∀ j, raw29088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29088step1 = (fun i j => raw29088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29088step1 raw29088step0; decide +kernel
      have hl : raw29088step1Labels = raw29088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29088step0 raw29088step0Labels permutation80 hz
    mixedMoment B raw29088step1 raw29088step1Labels = mixedMoment B raw29088step2 raw29088step2Labels := by
      have ha : raw29088step2 = (fun i j => raw29088step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29088step2 raw29088step1; decide +kernel
      have hl : raw29088step2Labels = raw29088step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29088step1 raw29088step1Labels permutation31 permutation2
    mixedMoment B raw29088step2 raw29088step2Labels = mixedMoment B raw29088step3 raw29088step3Labels := by
      have ha : raw29088step3 = -raw29088step2 := by apply Matrix.ext; change ∀ i j, raw29088step3 i j = -(raw29088step2 i j); unfold raw29088step3 raw29088step2; decide +kernel
      have hl : raw29088step3Labels = raw29088step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical29089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29089 raw29089Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw29089 raw29089Labels = mixedMoment B raw29089step0 raw29089step0Labels := by
      have hz : ∀ j, raw29089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29089step0 = (fun i j => raw29089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29089step0 raw29089; decide +kernel
      have hl : raw29089step0Labels = raw29089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29089 raw29089Labels permutation434 hz
    mixedMoment B raw29089step0 raw29089step0Labels = mixedMoment B raw29089step1 raw29089step1Labels := by
      have hz : ∀ j, raw29089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29089step1 = (fun i j => raw29089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29089step1 raw29089step0; decide +kernel
      have hl : raw29089step1Labels = raw29089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29089step0 raw29089step0Labels permutation80 hz
    mixedMoment B raw29089step1 raw29089step1Labels = mixedMoment B raw29089step2 raw29089step2Labels := by
      have ha : raw29089step2 = (fun i j => raw29089step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29089step2 raw29089step1; decide +kernel
      have hl : raw29089step2Labels = raw29089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29089step1 raw29089step1Labels permutation31 permutation2
    mixedMoment B raw29089step2 raw29089step2Labels = mixedMoment B raw29089step3 raw29089step3Labels := by
      have ha : raw29089step3 = -raw29089step2 := by apply Matrix.ext; change ∀ i j, raw29089step3 i j = -(raw29089step2 i j); unfold raw29089step3 raw29089step2; decide +kernel
      have hl : raw29089step3Labels = raw29089step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical29090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29090 raw29090Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw29090 raw29090Labels = mixedMoment B raw29090step0 raw29090step0Labels := by
      have hz : ∀ j, raw29090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29090step0 = (fun i j => raw29090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29090step0 raw29090; decide +kernel
      have hl : raw29090step0Labels = raw29090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29090 raw29090Labels permutation434 hz
    mixedMoment B raw29090step0 raw29090step0Labels = mixedMoment B raw29090step1 raw29090step1Labels := by
      have ha : raw29090step1 = (fun i j => raw29090step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29090step1 raw29090step0; decide +kernel
      have hl : raw29090step1Labels = raw29090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29090step0 raw29090step0Labels permutation151 permutation2
    mixedMoment B raw29090step1 raw29090step1Labels = mixedMoment B raw29090step2 raw29090step2Labels := by
      have ha : raw29090step2 = -raw29090step1 := by apply Matrix.ext; change ∀ i j, raw29090step2 i j = -(raw29090step1 i j); unfold raw29090step2 raw29090step1; decide +kernel
      have hl : raw29090step2Labels = raw29090step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical29091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29091 raw29091Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw29091 raw29091Labels = mixedMoment B raw29091step0 raw29091step0Labels := by
      have hz : ∀ j, raw29091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29091step0 = (fun i j => raw29091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29091step0 raw29091; decide +kernel
      have hl : raw29091step0Labels = raw29091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29091 raw29091Labels permutation346 hz
    mixedMoment B raw29091step0 raw29091step0Labels = mixedMoment B raw29091step1 raw29091step1Labels := by
      have ha : raw29091step1 = (fun i j => raw29091step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29091step1 raw29091step0; decide +kernel
      have hl : raw29091step1Labels = raw29091step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29091step0 raw29091step0Labels permutation151 permutation2
    mixedMoment B raw29091step1 raw29091step1Labels = mixedMoment B raw29091step2 raw29091step2Labels := by
      have ha : raw29091step2 = -raw29091step1 := by apply Matrix.ext; change ∀ i j, raw29091step2 i j = -(raw29091step1 i j); unfold raw29091step2 raw29091step1; decide +kernel
      have hl : raw29091step2Labels = raw29091step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical29092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29092 raw29092Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw29092 raw29092Labels = mixedMoment B raw29092step0 raw29092step0Labels := by
      have hz : ∀ j, raw29092 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29092step0 = (fun i j => raw29092 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29092step0 raw29092; decide +kernel
      have hl : raw29092step0Labels = raw29092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29092 raw29092Labels permutation520 hz
    mixedMoment B raw29092step0 raw29092step0Labels = mixedMoment B raw29092step1 raw29092step1Labels := by
      have hz : ∀ j, raw29092step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29092step1 = (fun i j => raw29092step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29092step1 raw29092step0; decide +kernel
      have hl : raw29092step1Labels = raw29092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29092step0 raw29092step0Labels permutation104 hz
    mixedMoment B raw29092step1 raw29092step1Labels = mixedMoment B raw29092step2 raw29092step2Labels := by
      have hz : ∀ j, raw29092step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29092step2 = (fun i j => raw29092step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29092step2 raw29092step1; decide +kernel
      have hl : raw29092step2Labels = raw29092step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29092step1 raw29092step1Labels permutation20 hz
    mixedMoment B raw29092step2 raw29092step2Labels = mixedMoment B raw29092step3 raw29092step3Labels := by
      have ha : raw29092step3 = (fun i j => raw29092step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29092step3 raw29092step2; decide +kernel
      have hl : raw29092step3Labels = raw29092step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29092step2 raw29092step2Labels permutation7 permutation2
    mixedMoment B raw29092step3 raw29092step3Labels = mixedMoment B raw29092step4 raw29092step4Labels := by
      have ha : raw29092step4 = -raw29092step3 := by apply Matrix.ext; change ∀ i j, raw29092step4 i j = -(raw29092step3 i j); unfold raw29092step4 raw29092step3; decide +kernel
      have hl : raw29092step4Labels = raw29092step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4505 node4505Labels := by rfl

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

theorem canonical1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1131 raw1131Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw1131 raw1131Labels = mixedMoment B raw1131step0 raw1131step0Labels := by
      have ha : raw1131step0 = (fun i j => raw1131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1131step0 raw1131; decide +kernel
      have hl : raw1131step0Labels = raw1131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1131 raw1131Labels permutation32 permutation4
    mixedMoment B raw1131step0 raw1131step0Labels = mixedMoment B raw1131step1 raw1131step1Labels := by
      have ha : raw1131step1 = raw1131step0 := by apply Matrix.ext; unfold raw1131step1 raw1131step0; decide +kernel
      have hl : raw1131step0Labels = labelEmbedding7 ∘ raw1131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1131step0 raw1131step0Labels raw1131step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1132 raw1132Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw1132 raw1132Labels = mixedMoment B raw1132step0 raw1132step0Labels := by
      have ha : raw1132step0 = (fun i j => raw1132 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1132step0 raw1132; decide +kernel
      have hl : raw1132step0Labels = raw1132Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1132 raw1132Labels permutation32 permutation4
    _ = mixedMoment B node924 node924Labels := by rfl

theorem canonical1133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1133 raw1133Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw1133 raw1133Labels = mixedMoment B raw1133step0 raw1133step0Labels := by
      have ha : raw1133step0 = (fun i j => raw1133 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1133step0 raw1133; decide +kernel
      have hl : raw1133step0Labels = raw1133Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1133 raw1133Labels permutation32 permutation6
    mixedMoment B raw1133step0 raw1133step0Labels = mixedMoment B raw1133step1 raw1133step1Labels := by
      have ha : raw1133step1 = -raw1133step0 := by apply Matrix.ext; change ∀ i j, raw1133step1 i j = -(raw1133step0 i j); unfold raw1133step1 raw1133step0; decide +kernel
      have hl : raw1133step1Labels = raw1133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1133step1 raw1133step1Labels = mixedMoment B raw1133step2 raw1133step2Labels := by
      have ha : raw1133step2 = raw1133step1 := by apply Matrix.ext; unfold raw1133step2 raw1133step1; decide +kernel
      have hl : raw1133step1Labels = labelEmbedding1 ∘ raw1133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1133step1 raw1133step1Labels raw1133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

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

theorem canonical1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1152 raw1152Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw1152 raw1152Labels = mixedMoment B raw1152step0 raw1152step0Labels := by
      have ha : raw1152step0 = (fun i j => raw1152 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1152step0 raw1152; decide +kernel
      have hl : raw1152step0Labels = raw1152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1152 raw1152Labels permutation8 permutation4
    mixedMoment B raw1152step0 raw1152step0Labels = mixedMoment B raw1152step1 raw1152step1Labels := by
      have ha : raw1152step1 = raw1152step0 := by apply Matrix.ext; unfold raw1152step1 raw1152step0; decide +kernel
      have hl : raw1152step0Labels = labelEmbedding7 ∘ raw1152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1152step0 raw1152step0Labels raw1152step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1153 raw1153Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw1153 raw1153Labels = mixedMoment B raw1153step0 raw1153step0Labels := by
      have ha : raw1153step0 = (fun i j => raw1153 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1153step0 raw1153; decide +kernel
      have hl : raw1153step0Labels = raw1153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1153 raw1153Labels permutation8 permutation4
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1154 raw1154Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw1154 raw1154Labels = mixedMoment B raw1154step0 raw1154step0Labels := by
      have ha : raw1154step0 = (fun i j => raw1154 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1154step0 raw1154; decide +kernel
      have hl : raw1154step0Labels = raw1154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1154 raw1154Labels permutation8 permutation6
    mixedMoment B raw1154step0 raw1154step0Labels = mixedMoment B raw1154step1 raw1154step1Labels := by
      have ha : raw1154step1 = -raw1154step0 := by apply Matrix.ext; change ∀ i j, raw1154step1 i j = -(raw1154step0 i j); unfold raw1154step1 raw1154step0; decide +kernel
      have hl : raw1154step1Labels = raw1154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1154step1 raw1154step1Labels = mixedMoment B raw1154step2 raw1154step2Labels := by
      have ha : raw1154step2 = raw1154step1 := by apply Matrix.ext; unfold raw1154step2 raw1154step1; decide +kernel
      have hl : raw1154step1Labels = labelEmbedding1 ∘ raw1154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1154step1 raw1154step1Labels raw1154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1158 raw1158Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw1158 raw1158Labels = mixedMoment B raw1158step0 raw1158step0Labels := by
      have ha : raw1158step0 = (fun i j => raw1158 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1158step0 raw1158; decide +kernel
      have hl : raw1158step0Labels = raw1158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1158 raw1158Labels permutation8 permutation4
    mixedMoment B raw1158step0 raw1158step0Labels = mixedMoment B raw1158step1 raw1158step1Labels := by
      have ha : raw1158step1 = raw1158step0 := by apply Matrix.ext; unfold raw1158step1 raw1158step0; decide +kernel
      have hl : raw1158step0Labels = labelEmbedding7 ∘ raw1158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1158step0 raw1158step0Labels raw1158step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1159 raw1159Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw1159 raw1159Labels = mixedMoment B raw1159step0 raw1159step0Labels := by
      have ha : raw1159step0 = (fun i j => raw1159 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1159step0 raw1159; decide +kernel
      have hl : raw1159step0Labels = raw1159Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1159 raw1159Labels permutation8 permutation4
    _ = mixedMoment B node938 node938Labels := by rfl

theorem canonical1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1160 raw1160Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw1160 raw1160Labels = mixedMoment B raw1160step0 raw1160step0Labels := by
      have ha : raw1160step0 = (fun i j => raw1160 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1160step0 raw1160; decide +kernel
      have hl : raw1160step0Labels = raw1160Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1160 raw1160Labels permutation8 permutation6
    mixedMoment B raw1160step0 raw1160step0Labels = mixedMoment B raw1160step1 raw1160step1Labels := by
      have ha : raw1160step1 = -raw1160step0 := by apply Matrix.ext; change ∀ i j, raw1160step1 i j = -(raw1160step0 i j); unfold raw1160step1 raw1160step0; decide +kernel
      have hl : raw1160step1Labels = raw1160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1160step1 raw1160step1Labels = mixedMoment B raw1160step2 raw1160step2Labels := by
      have ha : raw1160step2 = raw1160step1 := by apply Matrix.ext; unfold raw1160step2 raw1160step1; decide +kernel
      have hl : raw1160step1Labels = labelEmbedding1 ∘ raw1160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1160step1 raw1160step1Labels raw1160step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

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

theorem singleton4346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4346 node4346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node924 node924Labels + mixedMoment B node1674 node1674Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1131 singletonSmall4346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4346) = raw1131Labels := by decide +kernel
  rw [hl, canonical1131 B hB] at h
  have hc0 : mixedMoment B raw1131 (Fin.cases (0 : Fin 2) singletonSmall4346) =
      mixedMoment B node924 node924Labels := by
    have ha : raw1131 = raw1132 := by apply Matrix.ext; unfold raw1131 raw1132; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4346 = raw1132Labels := by decide +kernel
    rw [ha, hj, canonical1132 B hB]
  have hc1 : mixedMoment B raw1131 (Fin.cases (1 : Fin 2) singletonSmall4346) =
      mixedMoment B node1674 node1674Labels := by
    have ha : raw1131 = raw1133 := by apply Matrix.ext; unfold raw1131 raw1133; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4346 = raw1133Labels := by decide +kernel
    rw [ha, hj, canonical1133 B hB]
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

theorem singleton4356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4356 node4356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node934 node934Labels + mixedMoment B node1692 node1692Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1152 singletonSmall4356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4356) = raw1152Labels := by decide +kernel
  rw [hl, canonical1152 B hB] at h
  have hc0 : mixedMoment B raw1152 (Fin.cases (0 : Fin 2) singletonSmall4356) =
      mixedMoment B node934 node934Labels := by
    have ha : raw1152 = raw1153 := by apply Matrix.ext; unfold raw1152 raw1153; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4356 = raw1153Labels := by decide +kernel
    rw [ha, hj, canonical1153 B hB]
  have hc1 : mixedMoment B raw1152 (Fin.cases (1 : Fin 2) singletonSmall4356) =
      mixedMoment B node1692 node1692Labels := by
    have ha : raw1152 = raw1154 := by apply Matrix.ext; unfold raw1152 raw1154; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4356 = raw1154Labels := by decide +kernel
    rw [ha, hj, canonical1154 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4360 node4360Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node938 node938Labels + mixedMoment B node1693 node1693Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1158 singletonSmall4360
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4360) = raw1158Labels := by decide +kernel
  rw [hl, canonical1158 B hB] at h
  have hc0 : mixedMoment B raw1158 (Fin.cases (0 : Fin 2) singletonSmall4360) =
      mixedMoment B node938 node938Labels := by
    have ha : raw1158 = raw1159 := by apply Matrix.ext; unfold raw1158 raw1159; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4360 = raw1159Labels := by decide +kernel
    rw [ha, hj, canonical1159 B hB]
  have hc1 : mixedMoment B raw1158 (Fin.cases (1 : Fin 2) singletonSmall4360) =
      mixedMoment B node1693 node1693Labels := by
    have ha : raw1158 = raw1160 := by apply Matrix.ext; unfold raw1158 raw1160; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4360 = raw1160Labels := by decide +kernel
    rw [ha, hj, canonical1160 B hB]
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

theorem singleton4557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4557 node4557Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1143 node1143Labels + mixedMoment B node2167 node2167Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1392 singletonSmall4557
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4557) = raw1392Labels := by decide +kernel
  rw [hl, canonical1392 B hB] at h
  have hc0 : mixedMoment B raw1392 (Fin.cases (0 : Fin 2) singletonSmall4557) =
      mixedMoment B node1143 node1143Labels := by
    have ha : raw1392 = raw1393 := by apply Matrix.ext; unfold raw1392 raw1393; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4557 = raw1393Labels := by decide +kernel
    rw [ha, hj, canonical1393 B hB]
  have hc1 : mixedMoment B raw1392 (Fin.cases (1 : Fin 2) singletonSmall4557) =
      mixedMoment B node2167 node2167Labels := by
    have ha : raw1392 = raw1394 := by apply Matrix.ext; unfold raw1392 raw1394; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4557 = raw1394Labels := by decide +kernel
    rw [ha, hj, canonical1394 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4692 node4692Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1818 node1818Labels + mixedMoment B node2168 node2168Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1584 singletonSmall4692
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4692) = raw1584Labels := by decide +kernel
  rw [hl, canonical1584 B hB] at h
  have hc0 : mixedMoment B raw1584 (Fin.cases (0 : Fin 2) singletonSmall4692) =
      mixedMoment B node1818 node1818Labels := by
    have ha : raw1584 = raw1585 := by apply Matrix.ext; unfold raw1584 raw1585; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4692 = raw1585Labels := by decide +kernel
    rw [ha, hj, canonical1585 B hB]
  have hc1 : mixedMoment B raw1584 (Fin.cases (1 : Fin 2) singletonSmall4692) =
      mixedMoment B node2168 node2168Labels := by
    have ha : raw1584 = raw1586 := by apply Matrix.ext; unfold raw1584 raw1586; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4692 = raw1586Labels := by decide +kernel
    rw [ha, hj, canonical1586 B hB]
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

theorem singleton4760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4760 node4760Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1960 node1960Labels + mixedMoment B node2173 node2173Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1689 singletonSmall4760
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4760) = raw1689Labels := by decide +kernel
  rw [hl, canonical1689 B hB] at h
  have hc0 : mixedMoment B raw1689 (Fin.cases (0 : Fin 2) singletonSmall4760) =
      mixedMoment B node1960 node1960Labels := by
    have ha : raw1689 = raw1690 := by apply Matrix.ext; unfold raw1689 raw1690; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4760 = raw1690Labels := by decide +kernel
    rw [ha, hj, canonical1690 B hB]
  have hc1 : mixedMoment B raw1689 (Fin.cases (1 : Fin 2) singletonSmall4760) =
      mixedMoment B node2173 node2173Labels := by
    have ha : raw1689 = raw1691 := by apply Matrix.ext; unfold raw1689 raw1691; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4760 = raw1691Labels := by decide +kernel
    rw [ha, hj, canonical1691 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4769 node4769Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1969 node1969Labels + mixedMoment B node2185 node2185Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1704 singletonSmall4769
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4769) = raw1704Labels := by decide +kernel
  rw [hl, canonical1704 B hB] at h
  have hc0 : mixedMoment B raw1704 (Fin.cases (0 : Fin 2) singletonSmall4769) =
      mixedMoment B node1969 node1969Labels := by
    have ha : raw1704 = raw1705 := by apply Matrix.ext; unfold raw1704 raw1705; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4769 = raw1705Labels := by decide +kernel
    rw [ha, hj, canonical1705 B hB]
  have hc1 : mixedMoment B raw1704 (Fin.cases (1 : Fin 2) singletonSmall4769) =
      mixedMoment B node2185 node2185Labels := by
    have ha : raw1704 = raw1706 := by apply Matrix.ext; unfold raw1704 raw1706; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4769 = raw1706Labels := by decide +kernel
    rw [ha, hj, canonical1706 B hB]
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

theorem singleton4804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4804 node4804Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2022 node2022Labels + mixedMoment B node2203 node2203Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1737 singletonSmall4804
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4804) = raw1737Labels := by decide +kernel
  rw [hl, canonical1737 B hB] at h
  have hc0 : mixedMoment B raw1737 (Fin.cases (0 : Fin 2) singletonSmall4804) =
      mixedMoment B node2022 node2022Labels := by
    have ha : raw1737 = raw1738 := by apply Matrix.ext; unfold raw1737 raw1738; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4804 = raw1738Labels := by decide +kernel
    rw [ha, hj, canonical1738 B hB]
  have hc1 : mixedMoment B raw1737 (Fin.cases (1 : Fin 2) singletonSmall4804) =
      mixedMoment B node2203 node2203Labels := by
    have ha : raw1737 = raw1739 := by apply Matrix.ext; unfold raw1737 raw1739; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4804 = raw1739Labels := by decide +kernel
    rw [ha, hj, canonical1739 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5272 node5272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2740 node2740Labels + mixedMoment B node2740 node2740Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2283 singletonSmall5272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5272) = raw2283Labels := by decide +kernel
  rw [hl, canonical2283 B hB] at h
  have hc0 : mixedMoment B raw2283 (Fin.cases (0 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2284 := by apply Matrix.ext; unfold raw2283 raw2284; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5272 = raw2284Labels := by decide +kernel
    rw [ha, hj, canonical2284 B hB]
  have hc1 : mixedMoment B raw2283 (Fin.cases (1 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2285 := by apply Matrix.ext; unfold raw2283 raw2285; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5272 = raw2285Labels := by decide +kernel
    rw [ha, hj, canonical2285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node924 node924Labels = Sparse.eval nodeValue924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 924) = mixedMoment B node924 node924Labels := rfl
  simpa [nodeValue924, Sparse.eval] using hc.symm

theorem sound934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node934 node934Labels = Sparse.eval nodeValue934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 934) = mixedMoment B node934 node934Labels := rfl
  simpa [nodeValue934, Sparse.eval] using hc.symm

theorem sound938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node938 node938Labels = Sparse.eval nodeValue938 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 938) = mixedMoment B node938 node938Labels := rfl
  simpa [nodeValue938, Sparse.eval] using hc.symm

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

theorem sound1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1128 node1128Labels = Sparse.eval nodeValue1128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1128) = mixedMoment B node1128 node1128Labels := rfl
  simpa [nodeValue1128, Sparse.eval] using hc.symm

theorem sound1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1143 node1143Labels = Sparse.eval nodeValue1143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1143) = mixedMoment B node1143 node1143Labels := rfl
  simpa [nodeValue1143, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1692 node1692Labels = Sparse.eval nodeValue1692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1692) = mixedMoment B node1692 node1692Labels := rfl
  simpa [nodeValue1692, Sparse.eval] using hc.symm

theorem sound1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1693 node1693Labels = Sparse.eval nodeValue1693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1693) = mixedMoment B node1693 node1693Labels := rfl
  simpa [nodeValue1693, Sparse.eval] using hc.symm

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

theorem sound1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1807 node1807Labels = Sparse.eval nodeValue1807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1807) = mixedMoment B node1807 node1807Labels := rfl
  simpa [nodeValue1807, Sparse.eval] using hc.symm

theorem sound1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1818 node1818Labels = Sparse.eval nodeValue1818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1818) = mixedMoment B node1818 node1818Labels := rfl
  simpa [nodeValue1818, Sparse.eval] using hc.symm

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

theorem sound1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1960 node1960Labels = Sparse.eval nodeValue1960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1960) = mixedMoment B node1960 node1960Labels := rfl
  simpa [nodeValue1960, Sparse.eval] using hc.symm

theorem sound1969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1969 node1969Labels = Sparse.eval nodeValue1969 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1969) = mixedMoment B node1969 node1969Labels := rfl
  simpa [nodeValue1969, Sparse.eval] using hc.symm

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

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

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

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2167 node2167Labels = Sparse.eval nodeValue2167 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2167) = mixedMoment B node2167 node2167Labels := rfl
  simpa [nodeValue2167, Sparse.eval] using hc.symm

theorem sound2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2168 node2168Labels = Sparse.eval nodeValue2168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2168) = mixedMoment B node2168 node2168Labels := rfl
  simpa [nodeValue2168, Sparse.eval] using hc.symm

theorem sound2173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2173 node2173Labels = Sparse.eval nodeValue2173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2173) = mixedMoment B node2173 node2173Labels := rfl
  simpa [nodeValue2173, Sparse.eval] using hc.symm

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

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

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

theorem sound2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2509 node2509Labels = Sparse.eval nodeValue2509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2509) = mixedMoment B node2509 node2509Labels := rfl
  simpa [nodeValue2509, Sparse.eval] using hc.symm

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

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

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

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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

theorem sound4346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4346 node4346Labels = Sparse.eval nodeValue4346 (mixedVector B) := by
  have h := singleton4346 B _hB
  rw [sound924 B _hB _hF, sound1674 B _hB _hF] at h
  norm_num [nodeValue4346, nodeValue924, nodeValue1674, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4356 node4356Labels = Sparse.eval nodeValue4356 (mixedVector B) := by
  have h := singleton4356 B _hB
  rw [sound934 B _hB _hF, sound1692 B _hB _hF] at h
  norm_num [nodeValue4356, nodeValue934, nodeValue1692, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4360 node4360Labels = Sparse.eval nodeValue4360 (mixedVector B) := by
  have h := singleton4360 B _hB
  rw [sound938 B _hB _hF, sound1693 B _hB _hF] at h
  norm_num [nodeValue4360, nodeValue938, nodeValue1693, Sparse.eval] at h ⊢
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

theorem zero4505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = 0 := by
  exact mixedMoment_order_one B hB node4505 node4505Labels 1
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

theorem sound4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = Sparse.eval nodeValue4505 (mixedVector B) := by
  simpa only [nodeValue4505, Sparse.eval_nil] using zero4505 B _hB _hF

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

theorem sound4557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4557 node4557Labels = Sparse.eval nodeValue4557 (mixedVector B) := by
  have h := singleton4557 B _hB
  rw [sound1143 B _hB _hF, sound2167 B _hB _hF] at h
  norm_num [nodeValue4557, nodeValue1143, nodeValue2167, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4681 node4681Labels = Sparse.eval nodeValue4681 (mixedVector B) := by
  have h := singleton4681 B _hB
  rw [sound1807 B _hB _hF, sound2151 B _hB _hF] at h
  norm_num [nodeValue4681, nodeValue1807, nodeValue2151, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4692 node4692Labels = Sparse.eval nodeValue4692 (mixedVector B) := by
  have h := singleton4692 B _hB
  rw [sound1818 B _hB _hF, sound2168 B _hB _hF] at h
  norm_num [nodeValue4692, nodeValue1818, nodeValue2168, Sparse.eval] at h ⊢
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

theorem sound4760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4760 node4760Labels = Sparse.eval nodeValue4760 (mixedVector B) := by
  have h := singleton4760 B _hB
  rw [sound1960 B _hB _hF, sound2173 B _hB _hF] at h
  norm_num [nodeValue4760, nodeValue1960, nodeValue2173, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4769 node4769Labels = Sparse.eval nodeValue4769 (mixedVector B) := by
  have h := singleton4769 B _hB
  rw [sound1969 B _hB _hF, sound2185 B _hB _hF] at h
  norm_num [nodeValue4769, nodeValue1969, nodeValue2185, Sparse.eval] at h ⊢
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

theorem zero4841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = 0 := by
  exact mixedMoment_order_one B hB node4841 node4841Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

theorem sound4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = Sparse.eval nodeValue4846 (mixedVector B) := by
  simpa only [nodeValue4846, Sparse.eval_nil] using zero4846 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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

theorem sound5099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5099 node5099Labels = Sparse.eval nodeValue5099 (mixedVector B) := by
  have h := singleton5099 B _hB
  rw [sound2509 B _hB _hF, sound2704 B _hB _hF] at h
  norm_num [nodeValue5099, nodeValue2509, nodeValue2704, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5272 node5272Labels = Sparse.eval nodeValue5272 (mixedVector B) := by
  have h := singleton5272 B _hB
  rw [sound2740 B _hB _hF] at h
  norm_num [nodeValue5272, nodeValue2740, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources64
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2072 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 1) (sourceB2072 + difference 1 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 1) (sourceB2072 + difference 1 0) sourceC2072) = raw29063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29063; decide +kernel
    rw [ha]
    exact (canonical29063 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 2) (sourceB2072 + difference 2 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 2) (sourceB2072 + difference 2 0) sourceC2072) = raw29064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29064; decide +kernel
    rw [ha]
    exact (canonical29064 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 3) (sourceB2072 + difference 3 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 3) (sourceB2072 + difference 3 0) sourceC2072) = raw29065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29065; decide +kernel
    rw [ha]
    exact (canonical29065 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 4) (sourceB2072 + difference 4 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 4) (sourceB2072 + difference 4 0) sourceC2072) = raw29066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29066; decide +kernel
    rw [ha]
    exact (canonical29066 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2072 + difference 0 5) (sourceB2072 + difference 5 0) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2072 + difference 0 5) (sourceB2072 + difference 5 0) sourceC2072) = raw29067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29067; decide +kernel
    rw [ha]
    exact (canonical29067 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 0) (sourceB2072 + difference 0 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 0) (sourceB2072 + difference 0 1) sourceC2072) = raw29068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29068; decide +kernel
    rw [ha]
    exact (canonical29068 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 2) (sourceB2072 + difference 2 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 2) (sourceB2072 + difference 2 1) sourceC2072) = raw29069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29069; decide +kernel
    rw [ha]
    exact (canonical29069 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 3) (sourceB2072 + difference 3 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 3) (sourceB2072 + difference 3 1) sourceC2072) = raw29070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29070; decide +kernel
    rw [ha]
    exact (canonical29070 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 4) (sourceB2072 + difference 4 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 4) (sourceB2072 + difference 4 1) sourceC2072) = raw29071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29071; decide +kernel
    rw [ha]
    exact (canonical29071 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2072 + difference 1 5) (sourceB2072 + difference 5 1) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2072 + difference 1 5) (sourceB2072 + difference 5 1) sourceC2072) = raw29072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29072; decide +kernel
    rw [ha]
    exact (canonical29072 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 0) (sourceB2072 + difference 0 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 0) (sourceB2072 + difference 0 2) sourceC2072) = raw29073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29073; decide +kernel
    rw [ha]
    exact (canonical29073 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 1) (sourceB2072 + difference 1 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 1) (sourceB2072 + difference 1 2) sourceC2072) = raw29074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29074; decide +kernel
    rw [ha]
    exact (canonical29074 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 3) (sourceB2072 + difference 3 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 3) (sourceB2072 + difference 3 2) sourceC2072) = raw29075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29075; decide +kernel
    rw [ha]
    exact (canonical29075 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 4) (sourceB2072 + difference 4 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 4) (sourceB2072 + difference 4 2) sourceC2072) = raw29076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29076; decide +kernel
    rw [ha]
    exact (canonical29076 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2072 + difference 2 5) (sourceB2072 + difference 5 2) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2072 + difference 2 5) (sourceB2072 + difference 5 2) sourceC2072) = raw29077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29077; decide +kernel
    rw [ha]
    exact (canonical29077 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 0) (sourceB2072 + difference 0 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 0) (sourceB2072 + difference 0 3) sourceC2072) = raw29078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29078; decide +kernel
    rw [ha]
    exact (canonical29078 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 1) (sourceB2072 + difference 1 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 1) (sourceB2072 + difference 1 3) sourceC2072) = raw29079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29079; decide +kernel
    rw [ha]
    exact (canonical29079 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 2) (sourceB2072 + difference 2 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 2) (sourceB2072 + difference 2 3) sourceC2072) = raw29080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29080; decide +kernel
    rw [ha]
    exact (canonical29080 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 4) (sourceB2072 + difference 4 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 4) (sourceB2072 + difference 4 3) sourceC2072) = raw29081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29081; decide +kernel
    rw [ha]
    exact (canonical29081 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2072 + difference 3 5) (sourceB2072 + difference 5 3) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2072 + difference 3 5) (sourceB2072 + difference 5 3) sourceC2072) = raw29082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29082; decide +kernel
    rw [ha]
    exact (canonical29082 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 0) (sourceB2072 + difference 0 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 0) (sourceB2072 + difference 0 4) sourceC2072) = raw29083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29083; decide +kernel
    rw [ha]
    exact (canonical29083 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 1) (sourceB2072 + difference 1 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 1) (sourceB2072 + difference 1 4) sourceC2072) = raw29084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29084; decide +kernel
    rw [ha]
    exact (canonical29084 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 2) (sourceB2072 + difference 2 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 2) (sourceB2072 + difference 2 4) sourceC2072) = raw29085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29085; decide +kernel
    rw [ha]
    exact (canonical29085 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 3) (sourceB2072 + difference 3 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 3) (sourceB2072 + difference 3 4) sourceC2072) = raw29086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29086; decide +kernel
    rw [ha]
    exact (canonical29086 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2072 + difference 4 5) (sourceB2072 + difference 5 4) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2072 + difference 4 5) (sourceB2072 + difference 5 4) sourceC2072) = raw29087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29087; decide +kernel
    rw [ha]
    exact (canonical29087 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 0) (sourceB2072 + difference 0 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 0) (sourceB2072 + difference 0 5) sourceC2072) = raw29088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29088; decide +kernel
    rw [ha]
    exact (canonical29088 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 1) (sourceB2072 + difference 1 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 1) (sourceB2072 + difference 1 5) sourceC2072) = raw29089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29089; decide +kernel
    rw [ha]
    exact (canonical29089 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 2) (sourceB2072 + difference 2 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 2) (sourceB2072 + difference 2 5) sourceC2072) = raw29090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29090; decide +kernel
    rw [ha]
    exact (canonical29090 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 3) (sourceB2072 + difference 3 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 3) (sourceB2072 + difference 3 5) sourceC2072) = raw29091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29091; decide +kernel
    rw [ha]
    exact (canonical29091 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2072 + difference 5 4) (sourceB2072 + difference 4 5) sourceC2072) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA2072 + difference 5 4) (sourceB2072 + difference 4 5) sourceC2072) = raw29092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2072 sourceB2072 sourceC2072 difference raw29092; decide +kernel
    rw [ha]
    exact (canonical29092 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2072 sourceB2072 sourceC2072
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2072, Integer.Sparse.eval]
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

theorem reindexCheck1734 : Integer.Sparse.reindex keyMap MixedData.row1734 = numericRow1734 := by decide +kernel

theorem numericCheck1734 (x : Master → ℝ) : Integer.Sparse.eval numericRow1734 x =
    (4 : ℝ) * reducedSource1734 x := by
  norm_num [numericRow1734, reducedSource1734, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4346, nodeValue4356, nodeValue4360, nodeValue4505, nodeValue4543, nodeValue4557, nodeValue4605, nodeValue4681, nodeValue4692, nodeValue4760, nodeValue4769, nodeValue4804, nodeValue4834, nodeValue4841, nodeValue4846, nodeValue4897, nodeValue5099, nodeValue5110, nodeValue5272, nodeValue5274] <;> ring

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

theorem reducedZero1734 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1734 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  simpa only [sourceForm2072, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4346, h4356, h4360, h4505, h4543, h4557, h4605, h4681, h4692, h4760, h4769, h4804, h4834, h4841, h4846, h4897, h5099, h5110, h5272, h5274, reducedSource1734] using sourceEq2072 B hB

theorem rowSound1734_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1734 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1734, numericCheck1734, reducedZero1734 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e_oai
