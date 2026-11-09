-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:16:06.902963+00:00
-- url     : https://prove2.me/submissions/d6550364-885b-4363-8006-771b9c440054

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
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E101
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1557 raw1557Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw1557 raw1557Labels = mixedMoment B raw1557step0 raw1557step0Labels := by
      have ha : raw1557step0 = (fun i j => raw1557 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1557step0 raw1557; decide +kernel
      have hl : raw1557step0Labels = raw1557Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1557 raw1557Labels permutation32 permutation4
    mixedMoment B raw1557step0 raw1557step0Labels = mixedMoment B raw1557step1 raw1557step1Labels := by
      have ha : raw1557step1 = raw1557step0 := by apply Matrix.ext; unfold raw1557step1 raw1557step0; decide +kernel
      have hl : raw1557step0Labels = labelEmbedding7 ∘ raw1557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1557step0 raw1557step0Labels raw1557step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4678 node4678Labels := by rfl

theorem canonical1558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1558 raw1558Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw1558 raw1558Labels = mixedMoment B raw1558step0 raw1558step0Labels := by
      have ha : raw1558step0 = (fun i j => raw1558 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1558step0 raw1558; decide +kernel
      have hl : raw1558step0Labels = raw1558Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1558 raw1558Labels permutation32 permutation4
    _ = mixedMoment B node1804 node1804Labels := by rfl

theorem canonical1559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1559 raw1559Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw1559 raw1559Labels = mixedMoment B raw1559step0 raw1559step0Labels := by
      have ha : raw1559step0 = (fun i j => raw1559 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1559step0 raw1559; decide +kernel
      have hl : raw1559step0Labels = raw1559Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1559 raw1559Labels permutation32 permutation6
    mixedMoment B raw1559step0 raw1559step0Labels = mixedMoment B raw1559step1 raw1559step1Labels := by
      have ha : raw1559step1 = -raw1559step0 := by apply Matrix.ext; change ∀ i j, raw1559step1 i j = -(raw1559step0 i j); unfold raw1559step1 raw1559step0; decide +kernel
      have hl : raw1559step1Labels = raw1559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1559step1 raw1559step1Labels = mixedMoment B raw1559step2 raw1559step2Labels := by
      have ha : raw1559step2 = raw1559step1 := by apply Matrix.ext; unfold raw1559step2 raw1559step1; decide +kernel
      have hl : raw1559step1Labels = labelEmbedding1 ∘ raw1559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1559step1 raw1559step1Labels raw1559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

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

theorem canonical1686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1686 raw1686Labels = mixedMoment B node4759 node4759Labels := by
  calc
    mixedMoment B raw1686 raw1686Labels = mixedMoment B raw1686step0 raw1686step0Labels := by
      have ha : raw1686step0 = (fun i j => raw1686 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1686step0 raw1686; decide +kernel
      have hl : raw1686step0Labels = raw1686Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1686 raw1686Labels permutation152 permutation4
    mixedMoment B raw1686step0 raw1686step0Labels = mixedMoment B raw1686step1 raw1686step1Labels := by
      have ha : raw1686step1 = raw1686step0 := by apply Matrix.ext; unfold raw1686step1 raw1686step0; decide +kernel
      have hl : raw1686step0Labels = labelEmbedding7 ∘ raw1686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1686step0 raw1686step0Labels raw1686step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4759 node4759Labels := by rfl

theorem canonical1687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1687 raw1687Labels = mixedMoment B node1959 node1959Labels := by
  calc
    mixedMoment B raw1687 raw1687Labels = mixedMoment B raw1687step0 raw1687step0Labels := by
      have ha : raw1687step0 = (fun i j => raw1687 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1687step0 raw1687; decide +kernel
      have hl : raw1687step0Labels = raw1687Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1687 raw1687Labels permutation152 permutation4
    _ = mixedMoment B node1959 node1959Labels := by rfl

theorem canonical1688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1688 raw1688Labels = mixedMoment B node2170 node2170Labels := by
  calc
    mixedMoment B raw1688 raw1688Labels = mixedMoment B raw1688step0 raw1688step0Labels := by
      have ha : raw1688step0 = (fun i j => raw1688 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1688step0 raw1688; decide +kernel
      have hl : raw1688step0Labels = raw1688Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1688 raw1688Labels permutation662 permutation6
    mixedMoment B raw1688step0 raw1688step0Labels = mixedMoment B raw1688step1 raw1688step1Labels := by
      have ha : raw1688step1 = raw1688step0 := by apply Matrix.ext; unfold raw1688step1 raw1688step0; decide +kernel
      have hl : raw1688step0Labels = labelEmbedding1 ∘ raw1688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1688step0 raw1688step0Labels raw1688step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2170 node2170Labels := by rfl

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

theorem canonical1776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1776 raw1776Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw1776 raw1776Labels = mixedMoment B raw1776step0 raw1776step0Labels := by
      have ha : raw1776step0 = (fun i j => raw1776 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1776step0 raw1776; decide +kernel
      have hl : raw1776step0Labels = raw1776Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1776 raw1776Labels permutation8 permutation4
    mixedMoment B raw1776step0 raw1776step0Labels = mixedMoment B raw1776step1 raw1776step1Labels := by
      have ha : raw1776step1 = raw1776step0 := by apply Matrix.ext; unfold raw1776step1 raw1776step0; decide +kernel
      have hl : raw1776step0Labels = labelEmbedding7 ∘ raw1776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1776step0 raw1776step0Labels raw1776step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical1777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1777 raw1777Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw1777 raw1777Labels = mixedMoment B raw1777step0 raw1777step0Labels := by
      have ha : raw1777step0 = (fun i j => raw1777 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1777step0 raw1777; decide +kernel
      have hl : raw1777step0Labels = raw1777Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1777 raw1777Labels permutation8 permutation4
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical1778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1778 raw1778Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw1778 raw1778Labels = mixedMoment B raw1778step0 raw1778step0Labels := by
      have ha : raw1778step0 = (fun i j => raw1778 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1778step0 raw1778; decide +kernel
      have hl : raw1778step0Labels = raw1778Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1778 raw1778Labels permutation8 permutation6
    mixedMoment B raw1778step0 raw1778step0Labels = mixedMoment B raw1778step1 raw1778step1Labels := by
      have ha : raw1778step1 = -raw1778step0 := by apply Matrix.ext; change ∀ i j, raw1778step1 i j = -(raw1778step0 i j); unfold raw1778step1 raw1778step0; decide +kernel
      have hl : raw1778step1Labels = raw1778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1778step1 raw1778step1Labels = mixedMoment B raw1778step2 raw1778step2Labels := by
      have ha : raw1778step2 = raw1778step1 := by apply Matrix.ext; unfold raw1778step2 raw1778step1; decide +kernel
      have hl : raw1778step1Labels = labelEmbedding1 ∘ raw1778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1778step1 raw1778step1Labels raw1778step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19887 raw19887Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19887 raw19887Labels = mixedMoment B raw19887step0 raw19887step0Labels := by
      have hz : ∀ j, raw19887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19887step0 = (fun i j => raw19887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19887step0 raw19887; decide +kernel
      have hl : raw19887step0Labels = raw19887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19887 raw19887Labels permutation520 hz
    mixedMoment B raw19887step0 raw19887step0Labels = mixedMoment B raw19887step1 raw19887step1Labels := by
      have hz : ∀ j, raw19887step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19887step1 = (fun i j => raw19887step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19887step1 raw19887step0; decide +kernel
      have hl : raw19887step1Labels = raw19887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19887step0 raw19887step0Labels permutation104 hz
    mixedMoment B raw19887step1 raw19887step1Labels = mixedMoment B raw19887step2 raw19887step2Labels := by
      have hz : ∀ j, raw19887step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19887step2 = (fun i j => raw19887step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19887step2 raw19887step1; decide +kernel
      have hl : raw19887step2Labels = raw19887step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19887step1 raw19887step1Labels permutation20 hz
    mixedMoment B raw19887step2 raw19887step2Labels = mixedMoment B raw19887step3 raw19887step3Labels := by
      have ha : raw19887step3 = (fun i j => raw19887step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19887step3 raw19887step2; decide +kernel
      have hl : raw19887step3Labels = raw19887step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19887step2 raw19887step2Labels permutation7 permutation2
    mixedMoment B raw19887step3 raw19887step3Labels = mixedMoment B raw19887step4 raw19887step4Labels := by
      have ha : raw19887step4 = -raw19887step3 := by apply Matrix.ext; change ∀ i j, raw19887step4 i j = -(raw19887step3 i j); unfold raw19887step4 raw19887step3; decide +kernel
      have hl : raw19887step4Labels = raw19887step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4501 node4501Labels := by rfl

theorem canonical19891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19891 raw19891Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19891 raw19891Labels = mixedMoment B raw19891step0 raw19891step0Labels := by
      have hz : ∀ j, raw19891 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19891step0 = (fun i j => raw19891 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19891step0 raw19891; decide +kernel
      have hl : raw19891step0Labels = raw19891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891 raw19891Labels permutation520 hz
    mixedMoment B raw19891step0 raw19891step0Labels = mixedMoment B raw19891step1 raw19891step1Labels := by
      have hz : ∀ j, raw19891step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19891step1 = (fun i j => raw19891step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19891step1 raw19891step0; decide +kernel
      have hl : raw19891step1Labels = raw19891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step0 raw19891step0Labels permutation104 hz
    mixedMoment B raw19891step1 raw19891step1Labels = mixedMoment B raw19891step2 raw19891step2Labels := by
      have hz : ∀ j, raw19891step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19891step2 = (fun i j => raw19891step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19891step2 raw19891step1; decide +kernel
      have hl : raw19891step2Labels = raw19891step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step1 raw19891step1Labels permutation20 hz
    mixedMoment B raw19891step2 raw19891step2Labels = mixedMoment B raw19891step3 raw19891step3Labels := by
      have hz : ∀ j, raw19891step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19891step3 = (fun i j => raw19891step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19891step3 raw19891step2; decide +kernel
      have hl : raw19891step3Labels = raw19891step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step2 raw19891step2Labels permutation4 hz
    mixedMoment B raw19891step3 raw19891step3Labels = mixedMoment B raw19891step4 raw19891step4Labels := by
      have hz : ∀ i, raw19891step3 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw19891step4 = (fun i j => raw19891step3 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw19891step4 raw19891step3; decide +kernel
      have hl : raw19891step4Labels = (fun j => raw19891step3Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19891step3 raw19891step3Labels permutation4 hz
    mixedMoment B raw19891step4 raw19891step4Labels = mixedMoment B raw19891step5 raw19891step5Labels := by
      have ha : raw19891step5 = raw19891step4 := by apply Matrix.ext; unfold raw19891step5 raw19891step4; decide +kernel
      have hl : raw19891step4Labels = labelEmbedding2 ∘ raw19891step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19891step4 raw19891step4Labels raw19891step5Labels labelEmbedding2 hl
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical19908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19908 raw19908Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19908 raw19908Labels = mixedMoment B raw19908step0 raw19908step0Labels := by
      have hz : ∀ j, raw19908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19908step0 = (fun i j => raw19908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19908step0 raw19908; decide +kernel
      have hl : raw19908step0Labels = raw19908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19908 raw19908Labels permutation434 hz
    mixedMoment B raw19908step0 raw19908step0Labels = mixedMoment B raw19908step1 raw19908step1Labels := by
      have hz : ∀ j, raw19908step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19908step1 = (fun i j => raw19908step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19908step1 raw19908step0; decide +kernel
      have hl : raw19908step1Labels = raw19908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19908step0 raw19908step0Labels permutation80 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

theorem canonical19911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19911 raw19911Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19911 raw19911Labels = mixedMoment B raw19911step0 raw19911step0Labels := by
      have hz : ∀ j, raw19911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19911step0 = (fun i j => raw19911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19911step0 raw19911; decide +kernel
      have hl : raw19911step0Labels = raw19911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19911 raw19911Labels permutation434 hz
    mixedMoment B raw19911step0 raw19911step0Labels = mixedMoment B raw19911step1 raw19911step1Labels := by
      have hz : ∀ j, raw19911step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19911step1 = (fun i j => raw19911step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19911step1 raw19911step0; decide +kernel
      have hl : raw19911step1Labels = raw19911step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19911step0 raw19911step0Labels permutation80 hz
    mixedMoment B raw19911step1 raw19911step1Labels = mixedMoment B raw19911step2 raw19911step2Labels := by
      have hz : ∀ j, raw19911step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19911step2 = (fun i j => raw19911step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19911step2 raw19911step1; decide +kernel
      have hl : raw19911step2Labels = raw19911step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19911step1 raw19911step1Labels permutation14 hz
    _ = mixedMoment B node4501 node4501Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21832 raw21832Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21832 raw21832Labels = mixedMoment B raw21832step0 raw21832step0Labels := by
      have hz : ∀ j, raw21832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21832step0 = (fun i j => raw21832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21832step0 raw21832; decide +kernel
      have hl : raw21832step0Labels = raw21832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21832 raw21832Labels permutation434 hz
    mixedMoment B raw21832step0 raw21832step0Labels = mixedMoment B raw21832step1 raw21832step1Labels := by
      have hz : ∀ j, raw21832step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21832step1 = (fun i j => raw21832step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21832step1 raw21832step0; decide +kernel
      have hl : raw21832step1Labels = raw21832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21832step0 raw21832step0Labels permutation56 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

theorem canonical21833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21833 raw21833Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21833 raw21833Labels = mixedMoment B raw21833step0 raw21833step0Labels := by
      have hz : ∀ j, raw21833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21833step0 = (fun i j => raw21833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21833step0 raw21833; decide +kernel
      have hl : raw21833step0Labels = raw21833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21833 raw21833Labels permutation346 hz
    mixedMoment B raw21833step0 raw21833step0Labels = mixedMoment B raw21833step1 raw21833step1Labels := by
      have hz : ∀ j, raw21833step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21833step1 = (fun i j => raw21833step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21833step1 raw21833step0; decide +kernel
      have hl : raw21833step1Labels = raw21833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21833step0 raw21833step0Labels permutation56 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

theorem canonical21834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21834 raw21834Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw21834 raw21834Labels = mixedMoment B raw21834step0 raw21834step0Labels := by
      have hz : ∀ j, raw21834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21834step0 = (fun i j => raw21834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21834step0 raw21834; decide +kernel
      have hl : raw21834step0Labels = raw21834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834 raw21834Labels permutation434 hz
    mixedMoment B raw21834step0 raw21834step0Labels = mixedMoment B raw21834step1 raw21834step1Labels := by
      have hz : ∀ j, raw21834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21834step1 = (fun i j => raw21834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21834step1 raw21834step0; decide +kernel
      have hl : raw21834step1Labels = raw21834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834step0 raw21834step0Labels permutation80 hz
    mixedMoment B raw21834step1 raw21834step1Labels = mixedMoment B raw21834step2 raw21834step2Labels := by
      have hz : ∀ j, raw21834step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21834step2 = (fun i j => raw21834step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21834step2 raw21834step1; decide +kernel
      have hl : raw21834step2Labels = raw21834step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834step1 raw21834step1Labels permutation14 hz
    mixedMoment B raw21834step2 raw21834step2Labels = mixedMoment B raw21834step3 raw21834step3Labels := by
      have ha : raw21834step3 = (fun i j => raw21834step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21834step3 raw21834step2; decide +kernel
      have hl : raw21834step3Labels = raw21834step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21834step2 raw21834step2Labels permutation2 permutation7
    mixedMoment B raw21834step3 raw21834step3Labels = mixedMoment B raw21834step4 raw21834step4Labels := by
      have ha : raw21834step4 = -raw21834step3 := by apply Matrix.ext; change ∀ i j, raw21834step4 i j = -(raw21834step3 i j); unfold raw21834step4 raw21834step3; decide +kernel
      have hl : raw21834step4Labels = raw21834step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21834step4 raw21834step4Labels = mixedMoment B raw21834step5 raw21834step5Labels := by
      have ha : raw21834step5 = raw21834step4 := by apply Matrix.ext; unfold raw21834step5 raw21834step4; decide +kernel
      have hl : raw21834step4Labels = labelEmbedding10 ∘ raw21834step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21834step4 raw21834step4Labels raw21834step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical21840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21840 raw21840Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21840 raw21840Labels = mixedMoment B raw21840step0 raw21840step0Labels := by
      have hz : ∀ j, raw21840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21840step0 = (fun i j => raw21840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21840step0 raw21840; decide +kernel
      have hl : raw21840step0Labels = raw21840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21840 raw21840Labels permutation434 hz
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical21844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21844 raw21844Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21844 raw21844Labels = mixedMoment B raw21844step0 raw21844step0Labels := by
      have hz : ∀ j, raw21844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21844step0 = (fun i j => raw21844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21844step0 raw21844; decide +kernel
      have hl : raw21844step0Labels = raw21844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21844 raw21844Labels permutation346 hz
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical21848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21848 raw21848Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw21848 raw21848Labels = mixedMoment B raw21848step0 raw21848step0Labels := by
      have hz : ∀ j, raw21848 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21848step0 = (fun i j => raw21848 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21848step0 raw21848; decide +kernel
      have hl : raw21848step0Labels = raw21848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21848 raw21848Labels permutation434 hz
    mixedMoment B raw21848step0 raw21848step0Labels = mixedMoment B raw21848step1 raw21848step1Labels := by
      have hz : ∀ j, raw21848step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21848step1 = (fun i j => raw21848step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21848step1 raw21848step0; decide +kernel
      have hl : raw21848step1Labels = raw21848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21848step0 raw21848step0Labels permutation80 hz
    _ = mixedMoment B node4359 node4359Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25922 raw25922Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw25922 raw25922Labels = mixedMoment B raw25922step0 raw25922step0Labels := by
      have hz : ∀ j, raw25922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25922step0 = (fun i j => raw25922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25922step0 raw25922; decide +kernel
      have hl : raw25922step0Labels = raw25922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25922 raw25922Labels permutation346 hz
    _ = mixedMoment B node4832 node4832Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29229 raw29229Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw29229 raw29229Labels = mixedMoment B raw29229step0 raw29229step0Labels := by
      have hz : ∀ j, raw29229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29229step0 = (fun i j => raw29229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29229step0 raw29229; decide +kernel
      have hl : raw29229step0Labels = raw29229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29229 raw29229Labels permutation434 hz
    mixedMoment B raw29229step0 raw29229step0Labels = mixedMoment B raw29229step1 raw29229step1Labels := by
      have hz : ∀ j, raw29229step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29229step1 = (fun i j => raw29229step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29229step1 raw29229step0; decide +kernel
      have hl : raw29229step1Labels = raw29229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29229step0 raw29229step0Labels permutation80 hz
    mixedMoment B raw29229step1 raw29229step1Labels = mixedMoment B raw29229step2 raw29229step2Labels := by
      have ha : raw29229step2 = (fun i j => raw29229step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29229step2 raw29229step1; decide +kernel
      have hl : raw29229step2Labels = raw29229step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29229step1 raw29229step1Labels permutation31 permutation2
    mixedMoment B raw29229step2 raw29229step2Labels = mixedMoment B raw29229step3 raw29229step3Labels := by
      have ha : raw29229step3 = -raw29229step2 := by apply Matrix.ext; change ∀ i j, raw29229step3 i j = -(raw29229step2 i j); unfold raw29229step3 raw29229step2; decide +kernel
      have hl : raw29229step3Labels = raw29229step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical29230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29230 raw29230Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw29230 raw29230Labels = mixedMoment B raw29230step0 raw29230step0Labels := by
      have hz : ∀ j, raw29230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29230step0 = (fun i j => raw29230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29230step0 raw29230; decide +kernel
      have hl : raw29230step0Labels = raw29230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29230 raw29230Labels permutation434 hz
    mixedMoment B raw29230step0 raw29230step0Labels = mixedMoment B raw29230step1 raw29230step1Labels := by
      have ha : raw29230step1 = (fun i j => raw29230step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29230step1 raw29230step0; decide +kernel
      have hl : raw29230step1Labels = raw29230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29230step0 raw29230step0Labels permutation149 permutation2
    mixedMoment B raw29230step1 raw29230step1Labels = mixedMoment B raw29230step2 raw29230step2Labels := by
      have ha : raw29230step2 = -raw29230step1 := by apply Matrix.ext; change ∀ i j, raw29230step2 i j = -(raw29230step1 i j); unfold raw29230step2 raw29230step1; decide +kernel
      have hl : raw29230step2Labels = raw29230step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical29231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29231 raw29231Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw29231 raw29231Labels = mixedMoment B raw29231step0 raw29231step0Labels := by
      have hz : ∀ j, raw29231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29231step0 = (fun i j => raw29231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29231step0 raw29231; decide +kernel
      have hl : raw29231step0Labels = raw29231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29231 raw29231Labels permutation346 hz
    mixedMoment B raw29231step0 raw29231step0Labels = mixedMoment B raw29231step1 raw29231step1Labels := by
      have ha : raw29231step1 = (fun i j => raw29231step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29231step1 raw29231step0; decide +kernel
      have hl : raw29231step1Labels = raw29231step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29231step0 raw29231step0Labels permutation149 permutation2
    mixedMoment B raw29231step1 raw29231step1Labels = mixedMoment B raw29231step2 raw29231step2Labels := by
      have ha : raw29231step2 = -raw29231step1 := by apply Matrix.ext; change ∀ i j, raw29231step2 i j = -(raw29231step1 i j); unfold raw29231step2 raw29231step1; decide +kernel
      have hl : raw29231step2Labels = raw29231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical29232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29232 raw29232Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw29232 raw29232Labels = mixedMoment B raw29232step0 raw29232step0Labels := by
      have hz : ∀ j, raw29232 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29232step0 = (fun i j => raw29232 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29232step0 raw29232; decide +kernel
      have hl : raw29232step0Labels = raw29232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29232 raw29232Labels permutation520 hz
    mixedMoment B raw29232step0 raw29232step0Labels = mixedMoment B raw29232step1 raw29232step1Labels := by
      have hz : ∀ j, raw29232step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29232step1 = (fun i j => raw29232step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29232step1 raw29232step0; decide +kernel
      have hl : raw29232step1Labels = raw29232step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29232step0 raw29232step0Labels permutation104 hz
    mixedMoment B raw29232step1 raw29232step1Labels = mixedMoment B raw29232step2 raw29232step2Labels := by
      have hz : ∀ j, raw29232step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29232step2 = (fun i j => raw29232step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29232step2 raw29232step1; decide +kernel
      have hl : raw29232step2Labels = raw29232step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29232step1 raw29232step1Labels permutation20 hz
    mixedMoment B raw29232step2 raw29232step2Labels = mixedMoment B raw29232step3 raw29232step3Labels := by
      have ha : raw29232step3 = (fun i j => raw29232step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29232step3 raw29232step2; decide +kernel
      have hl : raw29232step3Labels = raw29232step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29232step2 raw29232step2Labels permutation7 permutation7
    mixedMoment B raw29232step3 raw29232step3Labels = mixedMoment B raw29232step4 raw29232step4Labels := by
      have ha : raw29232step4 = raw29232step3 := by apply Matrix.ext; unfold raw29232step4 raw29232step3; decide +kernel
      have hl : raw29232step3Labels = labelEmbedding10 ∘ raw29232step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29232step3 raw29232step3Labels raw29232step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical29233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29233 raw29233Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw29233 raw29233Labels = mixedMoment B raw29233step0 raw29233step0Labels := by
      have hz : ∀ j, raw29233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29233step0 = (fun i j => raw29233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29233step0 raw29233; decide +kernel
      have hl : raw29233step0Labels = raw29233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29233 raw29233Labels permutation434 hz
    mixedMoment B raw29233step0 raw29233step0Labels = mixedMoment B raw29233step1 raw29233step1Labels := by
      have hz : ∀ j, raw29233step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29233step1 = (fun i j => raw29233step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29233step1 raw29233step0; decide +kernel
      have hl : raw29233step1Labels = raw29233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29233step0 raw29233step0Labels permutation80 hz
    mixedMoment B raw29233step1 raw29233step1Labels = mixedMoment B raw29233step2 raw29233step2Labels := by
      have ha : raw29233step2 = (fun i j => raw29233step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29233step2 raw29233step1; decide +kernel
      have hl : raw29233step2Labels = raw29233step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29233step1 raw29233step1Labels permutation31 permutation7
    mixedMoment B raw29233step2 raw29233step2Labels = mixedMoment B raw29233step3 raw29233step3Labels := by
      have ha : raw29233step3 = raw29233step2 := by apply Matrix.ext; unfold raw29233step3 raw29233step2; decide +kernel
      have hl : raw29233step2Labels = labelEmbedding10 ∘ raw29233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29233step2 raw29233step2Labels raw29233step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

theorem canonical29234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29234 raw29234Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw29234 raw29234Labels = mixedMoment B raw29234step0 raw29234step0Labels := by
      have hz : ∀ j, raw29234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29234step0 = (fun i j => raw29234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29234step0 raw29234; decide +kernel
      have hl : raw29234step0Labels = raw29234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29234 raw29234Labels permutation434 hz
    _ = mixedMoment B node4678 node4678Labels := by rfl

theorem canonical29235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29235 raw29235Labels = mixedMoment B node4759 node4759Labels := by
  calc
    mixedMoment B raw29235 raw29235Labels = mixedMoment B raw29235step0 raw29235step0Labels := by
      have ha : raw29235step0 = (fun i j => raw29235 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29235step0 raw29235; decide +kernel
      have hl : raw29235step0Labels = raw29235Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29235 raw29235Labels permutation158 permutation2
    _ = mixedMoment B node4759 node4759Labels := by rfl

theorem canonical29236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29236 raw29236Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw29236 raw29236Labels = mixedMoment B raw29236step0 raw29236step0Labels := by
      have hz : ∀ j, raw29236 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29236step0 = (fun i j => raw29236 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29236step0 raw29236; decide +kernel
      have hl : raw29236step0Labels = raw29236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29236 raw29236Labels permutation520 hz
    mixedMoment B raw29236step0 raw29236step0Labels = mixedMoment B raw29236step1 raw29236step1Labels := by
      have hz : ∀ j, raw29236step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29236step1 = (fun i j => raw29236step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29236step1 raw29236step0; decide +kernel
      have hl : raw29236step1Labels = raw29236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29236step0 raw29236step0Labels permutation104 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

theorem canonical29237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29237 raw29237Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw29237 raw29237Labels = mixedMoment B raw29237step0 raw29237step0Labels := by
      have hz : ∀ j, raw29237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29237step0 = (fun i j => raw29237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29237step0 raw29237; decide +kernel
      have hl : raw29237step0Labels = raw29237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29237 raw29237Labels permutation434 hz
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical29238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29238 raw29238Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw29238 raw29238Labels = mixedMoment B raw29238step0 raw29238step0Labels := by
      have hz : ∀ j, raw29238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29238step0 = (fun i j => raw29238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29238step0 raw29238; decide +kernel
      have hl : raw29238step0Labels = raw29238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29238 raw29238Labels permutation346 hz
    _ = mixedMoment B node4678 node4678Labels := by rfl

theorem canonical29239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29239 raw29239Labels = mixedMoment B node4759 node4759Labels := by
  calc
    _ = mixedMoment B node4759 node4759Labels := by rfl

theorem canonical29240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29240 raw29240Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw29240 raw29240Labels = mixedMoment B raw29240step0 raw29240step0Labels := by
      have hz : ∀ j, raw29240 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29240step0 = (fun i j => raw29240 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29240step0 raw29240; decide +kernel
      have hl : raw29240step0Labels = raw29240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29240 raw29240Labels permutation520 hz
    mixedMoment B raw29240step0 raw29240step0Labels = mixedMoment B raw29240step1 raw29240step1Labels := by
      have hz : ∀ j, raw29240step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29240step1 = (fun i j => raw29240step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29240step1 raw29240step0; decide +kernel
      have hl : raw29240step1Labels = raw29240step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29240step0 raw29240step0Labels permutation80 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

theorem canonical29241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29241 raw29241Labels = mixedMoment B node4691 node4691Labels := by
  calc
    mixedMoment B raw29241 raw29241Labels = mixedMoment B raw29241step0 raw29241step0Labels := by
      have hz : ∀ j, raw29241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29241step0 = (fun i j => raw29241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29241step0 raw29241; decide +kernel
      have hl : raw29241step0Labels = raw29241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29241 raw29241Labels permutation434 hz
    mixedMoment B raw29241step0 raw29241step0Labels = mixedMoment B raw29241step1 raw29241step1Labels := by
      have hz : ∀ j, raw29241step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29241step1 = (fun i j => raw29241step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29241step1 raw29241step0; decide +kernel
      have hl : raw29241step1Labels = raw29241step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29241step0 raw29241step0Labels permutation80 hz
    _ = mixedMoment B node4691 node4691Labels := by rfl

theorem canonical29242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29242 raw29242Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw29242 raw29242Labels = mixedMoment B raw29242step0 raw29242step0Labels := by
      have hz : ∀ j, raw29242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29242step0 = (fun i j => raw29242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29242step0 raw29242; decide +kernel
      have hl : raw29242step0Labels = raw29242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29242 raw29242Labels permutation434 hz
    mixedMoment B raw29242step0 raw29242step0Labels = mixedMoment B raw29242step1 raw29242step1Labels := by
      have ha : raw29242step1 = (fun i j => raw29242step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29242step1 raw29242step0; decide +kernel
      have hl : raw29242step1Labels = raw29242step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29242step0 raw29242step0Labels permutation149 permutation2
    mixedMoment B raw29242step1 raw29242step1Labels = mixedMoment B raw29242step2 raw29242step2Labels := by
      have ha : raw29242step2 = -raw29242step1 := by apply Matrix.ext; change ∀ i j, raw29242step2 i j = -(raw29242step1 i j); unfold raw29242step2 raw29242step1; decide +kernel
      have hl : raw29242step2Labels = raw29242step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4678 node4678Labels := by rfl

theorem canonical29243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29243 raw29243Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw29243 raw29243Labels = mixedMoment B raw29243step0 raw29243step0Labels := by
      have hz : ∀ j, raw29243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29243step0 = (fun i j => raw29243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29243step0 raw29243; decide +kernel
      have hl : raw29243step0Labels = raw29243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29243 raw29243Labels permutation346 hz
    mixedMoment B raw29243step0 raw29243step0Labels = mixedMoment B raw29243step1 raw29243step1Labels := by
      have ha : raw29243step1 = (fun i j => raw29243step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29243step1 raw29243step0; decide +kernel
      have hl : raw29243step1Labels = raw29243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29243step0 raw29243step0Labels permutation149 permutation2
    mixedMoment B raw29243step1 raw29243step1Labels = mixedMoment B raw29243step2 raw29243step2Labels := by
      have ha : raw29243step2 = -raw29243step1 := by apply Matrix.ext; change ∀ i j, raw29243step2 i j = -(raw29243step1 i j); unfold raw29243step2 raw29243step1; decide +kernel
      have hl : raw29243step2Labels = raw29243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4678 node4678Labels := by rfl

theorem canonical29244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29244 raw29244Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw29244 raw29244Labels = mixedMoment B raw29244step0 raw29244step0Labels := by
      have hz : ∀ j, raw29244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29244step0 = (fun i j => raw29244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29244step0 raw29244; decide +kernel
      have hl : raw29244step0Labels = raw29244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29244 raw29244Labels permutation434 hz
    mixedMoment B raw29244step0 raw29244step0Labels = mixedMoment B raw29244step1 raw29244step1Labels := by
      have hz : ∀ j, raw29244step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29244step1 = (fun i j => raw29244step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29244step1 raw29244step0; decide +kernel
      have hl : raw29244step1Labels = raw29244step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29244step0 raw29244step0Labels permutation80 hz
    _ = mixedMoment B node4845 node4845Labels := by rfl

theorem canonical29245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29245 raw29245Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw29245 raw29245Labels = mixedMoment B raw29245step0 raw29245step0Labels := by
      have hz : ∀ j, raw29245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29245step0 = (fun i j => raw29245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29245step0 raw29245; decide +kernel
      have hl : raw29245step0Labels = raw29245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29245 raw29245Labels permutation434 hz
    mixedMoment B raw29245step0 raw29245step0Labels = mixedMoment B raw29245step1 raw29245step1Labels := by
      have hz : ∀ j, raw29245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29245step1 = (fun i j => raw29245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29245step1 raw29245step0; decide +kernel
      have hl : raw29245step1Labels = raw29245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29245step0 raw29245step0Labels permutation80 hz
    mixedMoment B raw29245step1 raw29245step1Labels = mixedMoment B raw29245step2 raw29245step2Labels := by
      have ha : raw29245step2 = (fun i j => raw29245step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29245step2 raw29245step1; decide +kernel
      have hl : raw29245step2Labels = raw29245step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29245step1 raw29245step1Labels permutation31 permutation2
    mixedMoment B raw29245step2 raw29245step2Labels = mixedMoment B raw29245step3 raw29245step3Labels := by
      have ha : raw29245step3 = -raw29245step2 := by apply Matrix.ext; change ∀ i j, raw29245step3 i j = -(raw29245step2 i j); unfold raw29245step3 raw29245step2; decide +kernel
      have hl : raw29245step3Labels = raw29245step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical29246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29246 raw29246Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw29246 raw29246Labels = mixedMoment B raw29246step0 raw29246step0Labels := by
      have hz : ∀ j, raw29246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29246step0 = (fun i j => raw29246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29246step0 raw29246; decide +kernel
      have hl : raw29246step0Labels = raw29246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29246 raw29246Labels permutation434 hz
    mixedMoment B raw29246step0 raw29246step0Labels = mixedMoment B raw29246step1 raw29246step1Labels := by
      have ha : raw29246step1 = (fun i j => raw29246step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29246step1 raw29246step0; decide +kernel
      have hl : raw29246step1Labels = raw29246step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29246step0 raw29246step0Labels permutation149 permutation2
    mixedMoment B raw29246step1 raw29246step1Labels = mixedMoment B raw29246step2 raw29246step2Labels := by
      have ha : raw29246step2 = -raw29246step1 := by apply Matrix.ext; change ∀ i j, raw29246step2 i j = -(raw29246step1 i j); unfold raw29246step2 raw29246step1; decide +kernel
      have hl : raw29246step2Labels = raw29246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical29247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29247 raw29247Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw29247 raw29247Labels = mixedMoment B raw29247step0 raw29247step0Labels := by
      have hz : ∀ j, raw29247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29247step0 = (fun i j => raw29247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29247step0 raw29247; decide +kernel
      have hl : raw29247step0Labels = raw29247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29247 raw29247Labels permutation346 hz
    mixedMoment B raw29247step0 raw29247step0Labels = mixedMoment B raw29247step1 raw29247step1Labels := by
      have ha : raw29247step1 = (fun i j => raw29247step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29247step1 raw29247step0; decide +kernel
      have hl : raw29247step1Labels = raw29247step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29247step0 raw29247step0Labels permutation149 permutation2
    mixedMoment B raw29247step1 raw29247step1Labels = mixedMoment B raw29247step2 raw29247step2Labels := by
      have ha : raw29247step2 = -raw29247step1 := by apply Matrix.ext; change ∀ i j, raw29247step2 i j = -(raw29247step1 i j); unfold raw29247step2 raw29247step1; decide +kernel
      have hl : raw29247step2Labels = raw29247step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4343 node4343Labels := by rfl

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

theorem canonical1125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1125 raw1125Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw1125 raw1125Labels = mixedMoment B raw1125step0 raw1125step0Labels := by
      have ha : raw1125step0 = (fun i j => raw1125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1125step0 raw1125; decide +kernel
      have hl : raw1125step0Labels = raw1125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1125 raw1125Labels permutation32 permutation4
    mixedMoment B raw1125step0 raw1125step0Labels = mixedMoment B raw1125step1 raw1125step1Labels := by
      have ha : raw1125step1 = raw1125step0 := by apply Matrix.ext; unfold raw1125step1 raw1125step0; decide +kernel
      have hl : raw1125step0Labels = labelEmbedding7 ∘ raw1125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1125step0 raw1125step0Labels raw1125step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1126 raw1126Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw1126 raw1126Labels = mixedMoment B raw1126step0 raw1126step0Labels := by
      have ha : raw1126step0 = (fun i j => raw1126 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1126step0 raw1126; decide +kernel
      have hl : raw1126step0Labels = raw1126Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1126 raw1126Labels permutation32 permutation4
    _ = mixedMoment B node921 node921Labels := by rfl

theorem canonical1127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1127 raw1127Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw1127 raw1127Labels = mixedMoment B raw1127step0 raw1127step0Labels := by
      have ha : raw1127step0 = (fun i j => raw1127 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1127step0 raw1127; decide +kernel
      have hl : raw1127step0Labels = raw1127Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1127 raw1127Labels permutation32 permutation6
    mixedMoment B raw1127step0 raw1127step0Labels = mixedMoment B raw1127step1 raw1127step1Labels := by
      have ha : raw1127step1 = -raw1127step0 := by apply Matrix.ext; change ∀ i j, raw1127step1 i j = -(raw1127step0 i j); unfold raw1127step1 raw1127step0; decide +kernel
      have hl : raw1127step1Labels = raw1127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1127step1 raw1127step1Labels = mixedMoment B raw1127step2 raw1127step2Labels := by
      have ha : raw1127step2 = raw1127step1 := by apply Matrix.ext; unfold raw1127step2 raw1127step1; decide +kernel
      have hl : raw1127step1Labels = labelEmbedding1 ∘ raw1127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1127step1 raw1127step1Labels raw1127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical1137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1137 raw1137Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw1137 raw1137Labels = mixedMoment B raw1137step0 raw1137step0Labels := by
      have ha : raw1137step0 = (fun i j => raw1137 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1137step0 raw1137; decide +kernel
      have hl : raw1137step0Labels = raw1137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1137 raw1137Labels permutation8 permutation4
    mixedMoment B raw1137step0 raw1137step0Labels = mixedMoment B raw1137step1 raw1137step1Labels := by
      have ha : raw1137step1 = raw1137step0 := by apply Matrix.ext; unfold raw1137step1 raw1137step0; decide +kernel
      have hl : raw1137step0Labels = labelEmbedding7 ∘ raw1137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1137step0 raw1137step0Labels raw1137step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4350 node4350Labels := by rfl

theorem canonical1138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1138 raw1138Labels = mixedMoment B node928 node928Labels := by
  calc
    mixedMoment B raw1138 raw1138Labels = mixedMoment B raw1138step0 raw1138step0Labels := by
      have ha : raw1138step0 = (fun i j => raw1138 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1138step0 raw1138; decide +kernel
      have hl : raw1138step0Labels = raw1138Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1138 raw1138Labels permutation8 permutation4
    _ = mixedMoment B node928 node928Labels := by rfl

theorem canonical1139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1139 raw1139Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw1139 raw1139Labels = mixedMoment B raw1139step0 raw1139step0Labels := by
      have ha : raw1139step0 = (fun i j => raw1139 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1139step0 raw1139; decide +kernel
      have hl : raw1139step0Labels = raw1139Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1139 raw1139Labels permutation31 permutation6
    mixedMoment B raw1139step0 raw1139step0Labels = mixedMoment B raw1139step1 raw1139step1Labels := by
      have ha : raw1139step1 = raw1139step0 := by apply Matrix.ext; unfold raw1139step1 raw1139step0; decide +kernel
      have hl : raw1139step0Labels = labelEmbedding1 ∘ raw1139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1139step0 raw1139step0Labels raw1139step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

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

theorem canonical1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1155 raw1155Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw1155 raw1155Labels = mixedMoment B raw1155step0 raw1155step0Labels := by
      have ha : raw1155step0 = (fun i j => raw1155 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1155step0 raw1155; decide +kernel
      have hl : raw1155step0Labels = raw1155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1155 raw1155Labels permutation8 permutation4
    mixedMoment B raw1155step0 raw1155step0Labels = mixedMoment B raw1155step1 raw1155step1Labels := by
      have ha : raw1155step1 = raw1155step0 := by apply Matrix.ext; unfold raw1155step1 raw1155step0; decide +kernel
      have hl : raw1155step0Labels = labelEmbedding7 ∘ raw1155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1155step0 raw1155step0Labels raw1155step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1156 raw1156Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw1156 raw1156Labels = mixedMoment B raw1156step0 raw1156step0Labels := by
      have ha : raw1156step0 = (fun i j => raw1156 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1156step0 raw1156; decide +kernel
      have hl : raw1156step0Labels = raw1156Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1156 raw1156Labels permutation8 permutation4
    _ = mixedMoment B node937 node937Labels := by rfl

theorem canonical1157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1157 raw1157Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw1157 raw1157Labels = mixedMoment B raw1157step0 raw1157step0Labels := by
      have ha : raw1157step0 = (fun i j => raw1157 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1157step0 raw1157; decide +kernel
      have hl : raw1157step0Labels = raw1157Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1157 raw1157Labels permutation8 permutation6
    mixedMoment B raw1157step0 raw1157step0Labels = mixedMoment B raw1157step1 raw1157step1Labels := by
      have ha : raw1157step1 = -raw1157step0 := by apply Matrix.ext; change ∀ i j, raw1157step1 i j = -(raw1157step0 i j); unfold raw1157step1 raw1157step0; decide +kernel
      have hl : raw1157step1Labels = raw1157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1157step1 raw1157step1Labels = mixedMoment B raw1157step2 raw1157step2Labels := by
      have ha : raw1157step2 = raw1157step1 := by apply Matrix.ext; unfold raw1157step2 raw1157step1; decide +kernel
      have hl : raw1157step1Labels = labelEmbedding1 ∘ raw1157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1157step1 raw1157step1Labels raw1157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

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

theorem singleton4343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4343 node4343Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node921 node921Labels + mixedMoment B node1666 node1666Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1125 singletonSmall4343
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4343) = raw1125Labels := by decide +kernel
  rw [hl, canonical1125 B hB] at h
  have hc0 : mixedMoment B raw1125 (Fin.cases (0 : Fin 2) singletonSmall4343) =
      mixedMoment B node921 node921Labels := by
    have ha : raw1125 = raw1126 := by apply Matrix.ext; unfold raw1125 raw1126; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4343 = raw1126Labels := by decide +kernel
    rw [ha, hj, canonical1126 B hB]
  have hc1 : mixedMoment B raw1125 (Fin.cases (1 : Fin 2) singletonSmall4343) =
      mixedMoment B node1666 node1666Labels := by
    have ha : raw1125 = raw1127 := by apply Matrix.ext; unfold raw1125 raw1127; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4343 = raw1127Labels := by decide +kernel
    rw [ha, hj, canonical1127 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4350 node4350Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node928 node928Labels + mixedMoment B node1677 node1677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1137 singletonSmall4350
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4350) = raw1137Labels := by decide +kernel
  rw [hl, canonical1137 B hB] at h
  have hc0 : mixedMoment B raw1137 (Fin.cases (0 : Fin 2) singletonSmall4350) =
      mixedMoment B node928 node928Labels := by
    have ha : raw1137 = raw1138 := by apply Matrix.ext; unfold raw1137 raw1138; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4350 = raw1138Labels := by decide +kernel
    rw [ha, hj, canonical1138 B hB]
  have hc1 : mixedMoment B raw1137 (Fin.cases (1 : Fin 2) singletonSmall4350) =
      mixedMoment B node1677 node1677Labels := by
    have ha : raw1137 = raw1139 := by apply Matrix.ext; unfold raw1137 raw1139; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4350 = raw1139Labels := by decide +kernel
    rw [ha, hj, canonical1139 B hB]
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

theorem singleton4359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4359 node4359Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node937 node937Labels + mixedMoment B node1683 node1683Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1155 singletonSmall4359
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4359) = raw1155Labels := by decide +kernel
  rw [hl, canonical1155 B hB] at h
  have hc0 : mixedMoment B raw1155 (Fin.cases (0 : Fin 2) singletonSmall4359) =
      mixedMoment B node937 node937Labels := by
    have ha : raw1155 = raw1156 := by apply Matrix.ext; unfold raw1155 raw1156; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4359 = raw1156Labels := by decide +kernel
    rw [ha, hj, canonical1156 B hB]
  have hc1 : mixedMoment B raw1155 (Fin.cases (1 : Fin 2) singletonSmall4359) =
      mixedMoment B node1683 node1683Labels := by
    have ha : raw1155 = raw1157 := by apply Matrix.ext; unfold raw1155 raw1157; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4359 = raw1157Labels := by decide +kernel
    rw [ha, hj, canonical1157 B hB]
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

theorem singleton4678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4678 node4678Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1804 node1804Labels + mixedMoment B node2143 node2143Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1557 singletonSmall4678
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4678) = raw1557Labels := by decide +kernel
  rw [hl, canonical1557 B hB] at h
  have hc0 : mixedMoment B raw1557 (Fin.cases (0 : Fin 2) singletonSmall4678) =
      mixedMoment B node1804 node1804Labels := by
    have ha : raw1557 = raw1558 := by apply Matrix.ext; unfold raw1557 raw1558; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4678 = raw1558Labels := by decide +kernel
    rw [ha, hj, canonical1558 B hB]
  have hc1 : mixedMoment B raw1557 (Fin.cases (1 : Fin 2) singletonSmall4678) =
      mixedMoment B node2143 node2143Labels := by
    have ha : raw1557 = raw1559 := by apply Matrix.ext; unfold raw1557 raw1559; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4678 = raw1559Labels := by decide +kernel
    rw [ha, hj, canonical1559 B hB]
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

theorem singleton4759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4759 node4759Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1959 node1959Labels + mixedMoment B node2170 node2170Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1686 singletonSmall4759
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4759) = raw1686Labels := by decide +kernel
  rw [hl, canonical1686 B hB] at h
  have hc0 : mixedMoment B raw1686 (Fin.cases (0 : Fin 2) singletonSmall4759) =
      mixedMoment B node1959 node1959Labels := by
    have ha : raw1686 = raw1687 := by apply Matrix.ext; unfold raw1686 raw1687; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4759 = raw1687Labels := by decide +kernel
    rw [ha, hj, canonical1687 B hB]
  have hc1 : mixedMoment B raw1686 (Fin.cases (1 : Fin 2) singletonSmall4759) =
      mixedMoment B node2170 node2170Labels := by
    have ha : raw1686 = raw1688 := by apply Matrix.ext; unfold raw1686 raw1688; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4759 = raw1688Labels := by decide +kernel
    rw [ha, hj, canonical1688 B hB]
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

theorem singleton4845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4845 node4845Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2065 node2065Labels + mixedMoment B node2218 node2218Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1776 singletonSmall4845
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4845) = raw1776Labels := by decide +kernel
  rw [hl, canonical1776 B hB] at h
  have hc0 : mixedMoment B raw1776 (Fin.cases (0 : Fin 2) singletonSmall4845) =
      mixedMoment B node2065 node2065Labels := by
    have ha : raw1776 = raw1777 := by apply Matrix.ext; unfold raw1776 raw1777; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4845 = raw1777Labels := by decide +kernel
    rw [ha, hj, canonical1777 B hB]
  have hc1 : mixedMoment B raw1776 (Fin.cases (1 : Fin 2) singletonSmall4845) =
      mixedMoment B node2218 node2218Labels := by
    have ha : raw1776 = raw1778 := by apply Matrix.ext; unfold raw1776 raw1778; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4845 = raw1778Labels := by decide +kernel
    rw [ha, hj, canonical1778 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node921 node921Labels = Sparse.eval nodeValue921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 921) = mixedMoment B node921 node921Labels := rfl
  simpa [nodeValue921, Sparse.eval] using hc.symm

theorem sound928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node928 node928Labels = Sparse.eval nodeValue928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 928) = mixedMoment B node928 node928Labels := rfl
  simpa [nodeValue928, Sparse.eval] using hc.symm

theorem sound937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node937 node937Labels = Sparse.eval nodeValue937 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 937) = mixedMoment B node937 node937Labels := rfl
  simpa [nodeValue937, Sparse.eval] using hc.symm

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

theorem sound1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1666 node1666Labels = Sparse.eval nodeValue1666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1666) = mixedMoment B node1666 node1666Labels := rfl
  simpa [nodeValue1666, Sparse.eval] using hc.symm

theorem sound1677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1677 node1677Labels = Sparse.eval nodeValue1677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1677) = mixedMoment B node1677 node1677Labels := rfl
  simpa [nodeValue1677, Sparse.eval] using hc.symm

theorem sound1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1683 node1683Labels = Sparse.eval nodeValue1683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1683) = mixedMoment B node1683 node1683Labels := rfl
  simpa [nodeValue1683, Sparse.eval] using hc.symm

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

theorem sound1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1804 node1804Labels = Sparse.eval nodeValue1804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1804) = mixedMoment B node1804 node1804Labels := rfl
  simpa [nodeValue1804, Sparse.eval] using hc.symm

theorem sound1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1817 node1817Labels = Sparse.eval nodeValue1817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1817) = mixedMoment B node1817 node1817Labels := rfl
  simpa [nodeValue1817, Sparse.eval] using hc.symm

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

theorem sound1959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1959 node1959Labels = Sparse.eval nodeValue1959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1959) = mixedMoment B node1959 node1959Labels := rfl
  simpa [nodeValue1959, Sparse.eval] using hc.symm

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

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

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

theorem sound2143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2143 node2143Labels = Sparse.eval nodeValue2143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2143) = mixedMoment B node2143 node2143Labels := rfl
  simpa [nodeValue2143, Sparse.eval] using hc.symm

theorem sound2159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2159 node2159Labels = Sparse.eval nodeValue2159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2159) = mixedMoment B node2159 node2159Labels := rfl
  simpa [nodeValue2159, Sparse.eval] using hc.symm

theorem sound2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2170 node2170Labels = Sparse.eval nodeValue2170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2170) = mixedMoment B node2170 node2170Labels := rfl
  simpa [nodeValue2170, Sparse.eval] using hc.symm

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

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

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

theorem sound4343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4343 node4343Labels = Sparse.eval nodeValue4343 (mixedVector B) := by
  have h := singleton4343 B _hB
  rw [sound921 B _hB _hF, sound1666 B _hB _hF] at h
  norm_num [nodeValue4343, nodeValue921, nodeValue1666, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4350 node4350Labels = Sparse.eval nodeValue4350 (mixedVector B) := by
  have h := singleton4350 B _hB
  rw [sound928 B _hB _hF, sound1677 B _hB _hF] at h
  norm_num [nodeValue4350, nodeValue928, nodeValue1677, Sparse.eval] at h ⊢
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

theorem sound4359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4359 node4359Labels = Sparse.eval nodeValue4359 (mixedVector B) := by
  have h := singleton4359 B _hB
  rw [sound937 B _hB _hF, sound1683 B _hB _hF] at h
  norm_num [nodeValue4359, nodeValue937, nodeValue1683, Sparse.eval] at h ⊢
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

theorem zero4501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = 0 := by
  exact mixedMoment_order_one B hB node4501 node4501Labels 1
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

theorem sound4501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = Sparse.eval nodeValue4501 (mixedVector B) := by
  simpa only [nodeValue4501, Sparse.eval_nil] using zero4501 B _hB _hF

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

theorem sound4678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4678 node4678Labels = Sparse.eval nodeValue4678 (mixedVector B) := by
  have h := singleton4678 B _hB
  rw [sound1804 B _hB _hF, sound2143 B _hB _hF] at h
  norm_num [nodeValue4678, nodeValue1804, nodeValue2143, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4691 node4691Labels = Sparse.eval nodeValue4691 (mixedVector B) := by
  have h := singleton4691 B _hB
  rw [sound1817 B _hB _hF, sound2159 B _hB _hF] at h
  norm_num [nodeValue4691, nodeValue1817, nodeValue2159, Sparse.eval] at h ⊢
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

theorem sound4759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4759 node4759Labels = Sparse.eval nodeValue4759 (mixedVector B) := by
  have h := singleton4759 B _hB
  rw [sound1959 B _hB _hF, sound2170 B _hB _hF] at h
  norm_num [nodeValue4759, nodeValue1959, nodeValue2170, Sparse.eval] at h ⊢
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

theorem zero4837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4837 node4837Labels = 0 := by
  exact mixedMoment_order_one B hB node4837 node4837Labels 1
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

theorem sound4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4832 node4832Labels = Sparse.eval nodeValue4832 (mixedVector B) := by
  have h := singleton4832 B _hB
  rw [sound2052 B _hB _hF, sound2193 B _hB _hF] at h
  norm_num [nodeValue4832, nodeValue2052, nodeValue2193, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4837 node4837Labels = Sparse.eval nodeValue4837 (mixedVector B) := by
  simpa only [nodeValue4837, Sparse.eval_nil] using zero4837 B _hB _hF

theorem sound4845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4845 node4845Labels = Sparse.eval nodeValue4845 (mixedVector B) := by
  have h := singleton4845 B _hB
  rw [sound2065 B _hB _hF, sound2218 B _hB _hF] at h
  norm_num [nodeValue4845, nodeValue2065, nodeValue2218, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources65
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2085 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2085 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 1) (sourceB2085 + difference 1 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 1) (sourceB2085 + difference 1 0) sourceC2085) = raw29229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29229; decide +kernel
    rw [ha]
    exact (canonical29229 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 2) (sourceB2085 + difference 2 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 2) (sourceB2085 + difference 2 0) sourceC2085) = raw29230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29230; decide +kernel
    rw [ha]
    exact (canonical29230 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 3) (sourceB2085 + difference 3 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 3) (sourceB2085 + difference 3 0) sourceC2085) = raw29231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29231; decide +kernel
    rw [ha]
    exact (canonical29231 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 4) (sourceB2085 + difference 4 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 4) (sourceB2085 + difference 4 0) sourceC2085) = raw29232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29232; decide +kernel
    rw [ha]
    exact (canonical29232 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 5) (sourceB2085 + difference 5 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 5) (sourceB2085 + difference 5 0) sourceC2085) = raw29233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29233; decide +kernel
    rw [ha]
    exact (canonical29233 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 0) (sourceB2085 + difference 0 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 0) (sourceB2085 + difference 0 1) sourceC2085) = raw19911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw19911; decide +kernel
    rw [ha]
    exact (canonical19911 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 2) (sourceB2085 + difference 2 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 2) (sourceB2085 + difference 2 1) sourceC2085) = raw21832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21832; decide +kernel
    rw [ha]
    exact (canonical21832 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 3) (sourceB2085 + difference 3 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 3) (sourceB2085 + difference 3 1) sourceC2085) = raw21833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21833; decide +kernel
    rw [ha]
    exact (canonical21833 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 4) (sourceB2085 + difference 4 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 4) (sourceB2085 + difference 4 1) sourceC2085) = raw19891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw19891; decide +kernel
    rw [ha]
    exact (canonical19891 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 5) (sourceB2085 + difference 5 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 5) (sourceB2085 + difference 5 1) sourceC2085) = raw21834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21834; decide +kernel
    rw [ha]
    exact (canonical21834 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 0) (sourceB2085 + difference 0 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 0) (sourceB2085 + difference 0 2) sourceC2085) = raw21840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21840; decide +kernel
    rw [ha]
    exact (canonical21840 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 1) (sourceB2085 + difference 1 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 1) (sourceB2085 + difference 1 2) sourceC2085) = raw29234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29234; decide +kernel
    rw [ha]
    exact (canonical29234 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 3) (sourceB2085 + difference 3 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4759) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 3) (sourceB2085 + difference 3 2) sourceC2085) = raw29235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29235; decide +kernel
    rw [ha]
    exact (canonical29235 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 4) (sourceB2085 + difference 4 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 4) (sourceB2085 + difference 4 2) sourceC2085) = raw29236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29236; decide +kernel
    rw [ha]
    exact (canonical29236 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 5) (sourceB2085 + difference 5 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 5) (sourceB2085 + difference 5 2) sourceC2085) = raw29237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29237; decide +kernel
    rw [ha]
    exact (canonical29237 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 0) (sourceB2085 + difference 0 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 0) (sourceB2085 + difference 0 3) sourceC2085) = raw21844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21844; decide +kernel
    rw [ha]
    exact (canonical21844 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 1) (sourceB2085 + difference 1 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 1) (sourceB2085 + difference 1 3) sourceC2085) = raw29238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29238; decide +kernel
    rw [ha]
    exact (canonical29238 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 2) (sourceB2085 + difference 2 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4759) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 2) (sourceB2085 + difference 2 3) sourceC2085) = raw29239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29239; decide +kernel
    rw [ha]
    exact (canonical29239 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 4) (sourceB2085 + difference 4 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 4) (sourceB2085 + difference 4 3) sourceC2085) = raw29240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29240; decide +kernel
    rw [ha]
    exact (canonical29240 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 5) (sourceB2085 + difference 5 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 5) (sourceB2085 + difference 5 3) sourceC2085) = raw25922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw25922; decide +kernel
    rw [ha]
    exact (canonical25922 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 0) (sourceB2085 + difference 0 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 0) (sourceB2085 + difference 0 4) sourceC2085) = raw21848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21848; decide +kernel
    rw [ha]
    exact (canonical21848 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 1) (sourceB2085 + difference 1 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4691) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 1) (sourceB2085 + difference 1 4) sourceC2085) = raw29241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29241; decide +kernel
    rw [ha]
    exact (canonical29241 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 2) (sourceB2085 + difference 2 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 2) (sourceB2085 + difference 2 4) sourceC2085) = raw29242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29242; decide +kernel
    rw [ha]
    exact (canonical29242 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 3) (sourceB2085 + difference 3 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 3) (sourceB2085 + difference 3 4) sourceC2085) = raw29243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29243; decide +kernel
    rw [ha]
    exact (canonical29243 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 5) (sourceB2085 + difference 5 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 5) (sourceB2085 + difference 5 4) sourceC2085) = raw29244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29244; decide +kernel
    rw [ha]
    exact (canonical29244 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 0) (sourceB2085 + difference 0 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 0) (sourceB2085 + difference 0 5) sourceC2085) = raw19908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw19908; decide +kernel
    rw [ha]
    exact (canonical19908 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 1) (sourceB2085 + difference 1 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 1) (sourceB2085 + difference 1 5) sourceC2085) = raw29245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29245; decide +kernel
    rw [ha]
    exact (canonical29245 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 2) (sourceB2085 + difference 2 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 2) (sourceB2085 + difference 2 5) sourceC2085) = raw29246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29246; decide +kernel
    rw [ha]
    exact (canonical29246 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 3) (sourceB2085 + difference 3 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 3) (sourceB2085 + difference 3 5) sourceC2085) = raw29247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29247; decide +kernel
    rw [ha]
    exact (canonical29247 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 4) (sourceB2085 + difference 4 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 4) (sourceB2085 + difference 4 5) sourceC2085) = raw19887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw19887; decide +kernel
    rw [ha]
    exact (canonical19887 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2085 sourceB2085 sourceC2085
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2085, Integer.Sparse.eval]
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

theorem reindexCheck1740 : Integer.Sparse.reindex keyMap MixedData.row1740 = numericRow1740 := by decide +kernel

theorem numericCheck1740 (x : Master → ℝ) : Integer.Sparse.eval numericRow1740 x =
    (4 : ℝ) * reducedSource1740 x := by
  norm_num [numericRow1740, reducedSource1740, Integer.Sparse.eval, Sparse.eval, nodeValue4085, nodeValue4343, nodeValue4350, nodeValue4359, nodeValue4501, nodeValue4678, nodeValue4691, nodeValue4759, nodeValue4832, nodeValue4837, nodeValue4845, nodeValue4897, nodeValue5261] <;> ring

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

theorem reducedZero1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1740 (mixedVector B) = 0 := by
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4350 : mixedVector B (Sum.inr 4350) = Sparse.eval nodeValue4350 (mixedVector B) := by
    change mixedMoment B node4350 node4350Labels = _
    exact sound4350 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  have h4678 : mixedVector B (Sum.inr 4678) = Sparse.eval nodeValue4678 (mixedVector B) := by
    change mixedMoment B node4678 node4678Labels = _
    exact sound4678 B hB hF
  have h4691 : mixedVector B (Sum.inr 4691) = Sparse.eval nodeValue4691 (mixedVector B) := by
    change mixedMoment B node4691 node4691Labels = _
    exact sound4691 B hB hF
  have h4759 : mixedVector B (Sum.inr 4759) = Sparse.eval nodeValue4759 (mixedVector B) := by
    change mixedMoment B node4759 node4759Labels = _
    exact sound4759 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4845 : mixedVector B (Sum.inr 4845) = Sparse.eval nodeValue4845 (mixedVector B) := by
    change mixedMoment B node4845 node4845Labels = _
    exact sound4845 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5261 : mixedVector B (Sum.inr 5261) = Sparse.eval nodeValue5261 (mixedVector B) := by
    change mixedMoment B node5261 node5261Labels = _
    exact sound5261 B hB hF
  simpa only [sourceForm2085, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4085, h4343, h4350, h4359, h4501, h4678, h4691, h4759, h4832, h4837, h4845, h4897, h5261, reducedSource1740] using sourceEq2085 B hB

theorem rowSound1740_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1740 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1740, numericCheck1740, reducedZero1740 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1740_e_oai
