-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:41:13.214783+00:00
-- url     : https://prove2.me/submissions/0e972f1d-b6aa-4491-b8af-63ca9450d129

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E117
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1287 raw1287Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw1287 raw1287Labels = mixedMoment B raw1287step0 raw1287step0Labels := by
      have ha : raw1287step0 = (fun i j => raw1287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1287step0 raw1287; decide +kernel
      have hl : raw1287step0Labels = raw1287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1287 raw1287Labels permutation8 permutation4
    mixedMoment B raw1287step0 raw1287step0Labels = mixedMoment B raw1287step1 raw1287step1Labels := by
      have ha : raw1287step1 = raw1287step0 := by apply Matrix.ext; unfold raw1287step1 raw1287step0; decide +kernel
      have hl : raw1287step0Labels = labelEmbedding7 ∘ raw1287step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1287step0 raw1287step0Labels raw1287step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

theorem canonical1288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1288 raw1288Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw1288 raw1288Labels = mixedMoment B raw1288step0 raw1288step0Labels := by
      have ha : raw1288step0 = (fun i j => raw1288 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1288step0 raw1288; decide +kernel
      have hl : raw1288step0Labels = raw1288Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1288 raw1288Labels permutation8 permutation4
    _ = mixedMoment B node1075 node1075Labels := by rfl

theorem canonical1289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1289 raw1289Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw1289 raw1289Labels = mixedMoment B raw1289step0 raw1289step0Labels := by
      have ha : raw1289step0 = (fun i j => raw1289 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1289step0 raw1289; decide +kernel
      have hl : raw1289step0Labels = raw1289Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1289 raw1289Labels permutation8 permutation6
    mixedMoment B raw1289step0 raw1289step0Labels = mixedMoment B raw1289step1 raw1289step1Labels := by
      have ha : raw1289step1 = -raw1289step0 := by apply Matrix.ext; change ∀ i j, raw1289step1 i j = -(raw1289step0 i j); unfold raw1289step1 raw1289step0; decide +kernel
      have hl : raw1289step1Labels = raw1289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1289step1 raw1289step1Labels = mixedMoment B raw1289step2 raw1289step2Labels := by
      have ha : raw1289step2 = raw1289step1 := by apply Matrix.ext; unfold raw1289step2 raw1289step1; decide +kernel
      have hl : raw1289step1Labels = labelEmbedding1 ∘ raw1289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1289step1 raw1289step1Labels raw1289step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1653 node1653Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23579 raw23579Labels = mixedMoment B node4790 node4790Labels := by
  calc
    mixedMoment B raw23579 raw23579Labels = mixedMoment B raw23579step0 raw23579step0Labels := by
      have hz : ∀ j, raw23579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23579step0 = (fun i j => raw23579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23579step0 raw23579; decide +kernel
      have hl : raw23579step0Labels = raw23579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23579 raw23579Labels permutation346 hz
    _ = mixedMoment B node4790 node4790Labels := by rfl

theorem canonical23580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23580 raw23580Labels = mixedMoment B node4790 node4790Labels := by
  calc
    mixedMoment B raw23580 raw23580Labels = mixedMoment B raw23580step0 raw23580step0Labels := by
      have hz : ∀ j, raw23580 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23580step0 = (fun i j => raw23580 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23580step0 raw23580; decide +kernel
      have hl : raw23580step0Labels = raw23580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23580 raw23580Labels permutation265 hz
    _ = mixedMoment B node4790 node4790Labels := by rfl

theorem canonical23581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23581 raw23581Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw23581 raw23581Labels = mixedMoment B raw23581step0 raw23581step0Labels := by
      have hz : ∀ j, raw23581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23581step0 = (fun i j => raw23581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23581step0 raw23581; decide +kernel
      have hl : raw23581step0Labels = raw23581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23581 raw23581Labels permutation346 hz
    mixedMoment B raw23581step0 raw23581step0Labels = mixedMoment B raw23581step1 raw23581step1Labels := by
      have hz : ∀ j, raw23581step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23581step1 = (fun i j => raw23581step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23581step1 raw23581step0; decide +kernel
      have hl : raw23581step1Labels = raw23581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23581step0 raw23581step0Labels permutation56 hz
    mixedMoment B raw23581step1 raw23581step1Labels = mixedMoment B raw23581step2 raw23581step2Labels := by
      have hz : ∀ i, raw23581step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23581step2 = (fun i j => raw23581step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23581step2 raw23581step1; decide +kernel
      have hl : raw23581step2Labels = (fun j => raw23581step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23581step1 raw23581step1Labels permutation4 hz
    mixedMoment B raw23581step2 raw23581step2Labels = mixedMoment B raw23581step3 raw23581step3Labels := by
      have ha : raw23581step3 = raw23581step2 := by apply Matrix.ext; unfold raw23581step3 raw23581step2; decide +kernel
      have hl : raw23581step2Labels = labelEmbedding2 ∘ raw23581step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23581step2 raw23581step2Labels raw23581step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical23582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23582 raw23582Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw23582 raw23582Labels = mixedMoment B raw23582step0 raw23582step0Labels := by
      have hz : ∀ j, raw23582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23582step0 = (fun i j => raw23582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23582step0 raw23582; decide +kernel
      have hl : raw23582step0Labels = raw23582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23582 raw23582Labels permutation346 hz
    mixedMoment B raw23582step0 raw23582step0Labels = mixedMoment B raw23582step1 raw23582step1Labels := by
      have hz : ∀ j, raw23582step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23582step1 = (fun i j => raw23582step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23582step1 raw23582step0; decide +kernel
      have hl : raw23582step1Labels = raw23582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23582step0 raw23582step0Labels permutation56 hz
    mixedMoment B raw23582step1 raw23582step1Labels = mixedMoment B raw23582step2 raw23582step2Labels := by
      have ha : raw23582step2 = (fun i j => raw23582step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23582step2 raw23582step1; decide +kernel
      have hl : raw23582step2Labels = raw23582step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23582step1 raw23582step1Labels permutation8 permutation7
    mixedMoment B raw23582step2 raw23582step2Labels = mixedMoment B raw23582step3 raw23582step3Labels := by
      have ha : raw23582step3 = -raw23582step2 := by apply Matrix.ext; change ∀ i j, raw23582step3 i j = -(raw23582step2 i j); unfold raw23582step3 raw23582step2; decide +kernel
      have hl : raw23582step3Labels = raw23582step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23582step3 raw23582step3Labels = mixedMoment B raw23582step4 raw23582step4Labels := by
      have ha : raw23582step4 = raw23582step3 := by apply Matrix.ext; unfold raw23582step4 raw23582step3; decide +kernel
      have hl : raw23582step3Labels = labelEmbedding10 ∘ raw23582step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23582step3 raw23582step3Labels raw23582step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical23583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23583 raw23583Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw23583 raw23583Labels = mixedMoment B raw23583step0 raw23583step0Labels := by
      have hz : ∀ j, raw23583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23583step0 = (fun i j => raw23583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23583step0 raw23583; decide +kernel
      have hl : raw23583step0Labels = raw23583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23583 raw23583Labels permutation346 hz
    mixedMoment B raw23583step0 raw23583step0Labels = mixedMoment B raw23583step1 raw23583step1Labels := by
      have hz : ∀ j, raw23583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23583step1 = (fun i j => raw23583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23583step1 raw23583step0; decide +kernel
      have hl : raw23583step1Labels = raw23583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23583step0 raw23583step0Labels permutation56 hz
    mixedMoment B raw23583step1 raw23583step1Labels = mixedMoment B raw23583step2 raw23583step2Labels := by
      have ha : raw23583step2 = (fun i j => raw23583step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23583step2 raw23583step1; decide +kernel
      have hl : raw23583step2Labels = raw23583step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23583step1 raw23583step1Labels permutation9 permutation7
    mixedMoment B raw23583step2 raw23583step2Labels = mixedMoment B raw23583step3 raw23583step3Labels := by
      have ha : raw23583step3 = -raw23583step2 := by apply Matrix.ext; change ∀ i j, raw23583step3 i j = -(raw23583step2 i j); unfold raw23583step3 raw23583step2; decide +kernel
      have hl : raw23583step3Labels = raw23583step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23583step3 raw23583step3Labels = mixedMoment B raw23583step4 raw23583step4Labels := by
      have ha : raw23583step4 = raw23583step3 := by apply Matrix.ext; unfold raw23583step4 raw23583step3; decide +kernel
      have hl : raw23583step3Labels = labelEmbedding10 ∘ raw23583step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23583step3 raw23583step3Labels raw23583step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical23584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23584 raw23584Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw23584 raw23584Labels = mixedMoment B raw23584step0 raw23584step0Labels := by
      have hz : ∀ j, raw23584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23584step0 = (fun i j => raw23584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23584step0 raw23584; decide +kernel
      have hl : raw23584step0Labels = raw23584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23584 raw23584Labels permutation346 hz
    mixedMoment B raw23584step0 raw23584step0Labels = mixedMoment B raw23584step1 raw23584step1Labels := by
      have ha : raw23584step1 = (fun i j => raw23584step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23584step1 raw23584step0; decide +kernel
      have hl : raw23584step1Labels = raw23584step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23584step0 raw23584step0Labels permutation38 permutation2
    _ = mixedMoment B node4141 node4141Labels := by rfl

theorem canonical23585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23585 raw23585Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw23585 raw23585Labels = mixedMoment B raw23585step0 raw23585step0Labels := by
      have ha : raw23585step0 = (fun i j => raw23585 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23585step0 raw23585; decide +kernel
      have hl : raw23585step0Labels = raw23585Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23585 raw23585Labels permutation182 permutation2
    _ = mixedMoment B node4321 node4321Labels := by rfl

theorem canonical23586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23586 raw23586Labels = mixedMoment B node4305 node4305Labels := by
  calc
    mixedMoment B raw23586 raw23586Labels = mixedMoment B raw23586step0 raw23586step0Labels := by
      have hz : ∀ j, raw23586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23586step0 = (fun i j => raw23586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23586step0 raw23586; decide +kernel
      have hl : raw23586step0Labels = raw23586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23586 raw23586Labels permutation346 hz
    mixedMoment B raw23586step0 raw23586step0Labels = mixedMoment B raw23586step1 raw23586step1Labels := by
      have ha : raw23586step1 = (fun i j => raw23586step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23586step1 raw23586step0; decide +kernel
      have hl : raw23586step1Labels = raw23586step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23586step0 raw23586step0Labels permutation38 permutation2
    _ = mixedMoment B node4305 node4305Labels := by rfl

theorem canonical23587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23587 raw23587Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23587 raw23587Labels = mixedMoment B raw23587step0 raw23587step0Labels := by
      have hz : ∀ j, raw23587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23587step0 = (fun i j => raw23587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23587step0 raw23587; decide +kernel
      have hl : raw23587step0Labels = raw23587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23587 raw23587Labels permutation346 hz
    mixedMoment B raw23587step0 raw23587step0Labels = mixedMoment B raw23587step1 raw23587step1Labels := by
      have ha : raw23587step1 = (fun i j => raw23587step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23587step1 raw23587step0; decide +kernel
      have hl : raw23587step1Labels = raw23587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23587step0 raw23587step0Labels permutation38 permutation2
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical23588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23588 raw23588Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23588 raw23588Labels = mixedMoment B raw23588step0 raw23588step0Labels := by
      have hz : ∀ j, raw23588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23588step0 = (fun i j => raw23588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23588step0 raw23588; decide +kernel
      have hl : raw23588step0Labels = raw23588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23588 raw23588Labels permutation346 hz
    mixedMoment B raw23588step0 raw23588step0Labels = mixedMoment B raw23588step1 raw23588step1Labels := by
      have ha : raw23588step1 = (fun i j => raw23588step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23588step1 raw23588step0; decide +kernel
      have hl : raw23588step1Labels = raw23588step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23588step0 raw23588step0Labels permutation39 permutation2
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical23589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23589 raw23589Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw23589 raw23589Labels = mixedMoment B raw23589step0 raw23589step0Labels := by
      have hz : ∀ j, raw23589 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23589step0 = (fun i j => raw23589 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23589step0 raw23589; decide +kernel
      have hl : raw23589step0Labels = raw23589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23589 raw23589Labels permutation265 hz
    mixedMoment B raw23589step0 raw23589step0Labels = mixedMoment B raw23589step1 raw23589step1Labels := by
      have ha : raw23589step1 = (fun i j => raw23589step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23589step1 raw23589step0; decide +kernel
      have hl : raw23589step1Labels = raw23589step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23589step0 raw23589step0Labels permutation38 permutation2
    _ = mixedMoment B node4141 node4141Labels := by rfl

theorem canonical23590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23590 raw23590Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw23590 raw23590Labels = mixedMoment B raw23590step0 raw23590step0Labels := by
      have ha : raw23590step0 = (fun i j => raw23590 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23590step0 raw23590; decide +kernel
      have hl : raw23590step0Labels = raw23590Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23590 raw23590Labels permutation158 permutation2
    _ = mixedMoment B node4321 node4321Labels := by rfl

theorem canonical23591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23591 raw23591Labels = mixedMoment B node4305 node4305Labels := by
  calc
    mixedMoment B raw23591 raw23591Labels = mixedMoment B raw23591step0 raw23591step0Labels := by
      have hz : ∀ j, raw23591 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23591step0 = (fun i j => raw23591 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23591step0 raw23591; decide +kernel
      have hl : raw23591step0Labels = raw23591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23591 raw23591Labels permutation265 hz
    mixedMoment B raw23591step0 raw23591step0Labels = mixedMoment B raw23591step1 raw23591step1Labels := by
      have ha : raw23591step1 = (fun i j => raw23591step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23591step1 raw23591step0; decide +kernel
      have hl : raw23591step1Labels = raw23591step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23591step0 raw23591step0Labels permutation38 permutation2
    _ = mixedMoment B node4305 node4305Labels := by rfl

theorem canonical23592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23592 raw23592Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23592 raw23592Labels = mixedMoment B raw23592step0 raw23592step0Labels := by
      have hz : ∀ j, raw23592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23592step0 = (fun i j => raw23592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23592step0 raw23592; decide +kernel
      have hl : raw23592step0Labels = raw23592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23592 raw23592Labels permutation265 hz
    mixedMoment B raw23592step0 raw23592step0Labels = mixedMoment B raw23592step1 raw23592step1Labels := by
      have ha : raw23592step1 = (fun i j => raw23592step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23592step1 raw23592step0; decide +kernel
      have hl : raw23592step1Labels = raw23592step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23592step0 raw23592step0Labels permutation38 permutation2
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical23593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23593 raw23593Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23593 raw23593Labels = mixedMoment B raw23593step0 raw23593step0Labels := by
      have hz : ∀ j, raw23593 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23593step0 = (fun i j => raw23593 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23593step0 raw23593; decide +kernel
      have hl : raw23593step0Labels = raw23593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23593 raw23593Labels permutation265 hz
    mixedMoment B raw23593step0 raw23593step0Labels = mixedMoment B raw23593step1 raw23593step1Labels := by
      have ha : raw23593step1 = (fun i j => raw23593step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23593step1 raw23593step0; decide +kernel
      have hl : raw23593step1Labels = raw23593step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23593step0 raw23593step0Labels permutation39 permutation2
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical23594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23594 raw23594Labels = mixedMoment B node4167 node4167Labels := by
  calc
    mixedMoment B raw23594 raw23594Labels = mixedMoment B raw23594step0 raw23594step0Labels := by
      have hz : ∀ j, raw23594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23594step0 = (fun i j => raw23594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23594step0 raw23594; decide +kernel
      have hl : raw23594step0Labels = raw23594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23594 raw23594Labels permutation346 hz
    mixedMoment B raw23594step0 raw23594step0Labels = mixedMoment B raw23594step1 raw23594step1Labels := by
      have hz : ∀ j, raw23594step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23594step1 = (fun i j => raw23594step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23594step1 raw23594step0; decide +kernel
      have hl : raw23594step1Labels = raw23594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23594step0 raw23594step0Labels permutation56 hz
    _ = mixedMoment B node4167 node4167Labels := by rfl

theorem canonical23595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23595 raw23595Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw23595 raw23595Labels = mixedMoment B raw23595step0 raw23595step0Labels := by
      have hz : ∀ j, raw23595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23595step0 = (fun i j => raw23595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23595step0 raw23595; decide +kernel
      have hl : raw23595step0Labels = raw23595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23595 raw23595Labels permutation346 hz
    _ = mixedMoment B node4339 node4339Labels := by rfl

theorem canonical23596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23596 raw23596Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw23596 raw23596Labels = mixedMoment B raw23596step0 raw23596step0Labels := by
      have hz : ∀ j, raw23596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23596step0 = (fun i j => raw23596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23596step0 raw23596; decide +kernel
      have hl : raw23596step0Labels = raw23596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23596 raw23596Labels permutation265 hz
    _ = mixedMoment B node4339 node4339Labels := by rfl

theorem canonical23597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23597 raw23597Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw23597 raw23597Labels = mixedMoment B raw23597step0 raw23597step0Labels := by
      have hz : ∀ j, raw23597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23597step0 = (fun i j => raw23597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23597step0 raw23597; decide +kernel
      have hl : raw23597step0Labels = raw23597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23597 raw23597Labels permutation346 hz
    mixedMoment B raw23597step0 raw23597step0Labels = mixedMoment B raw23597step1 raw23597step1Labels := by
      have hz : ∀ j, raw23597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23597step1 = (fun i j => raw23597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23597step1 raw23597step0; decide +kernel
      have hl : raw23597step1Labels = raw23597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23597step0 raw23597step0Labels permutation56 hz
    _ = mixedMoment B node4491 node4491Labels := by rfl

theorem canonical23598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23598 raw23598Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw23598 raw23598Labels = mixedMoment B raw23598step0 raw23598step0Labels := by
      have hz : ∀ j, raw23598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23598step0 = (fun i j => raw23598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23598step0 raw23598; decide +kernel
      have hl : raw23598step0Labels = raw23598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23598 raw23598Labels permutation346 hz
    mixedMoment B raw23598step0 raw23598step0Labels = mixedMoment B raw23598step1 raw23598step1Labels := by
      have hz : ∀ j, raw23598step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23598step1 = (fun i j => raw23598step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23598step1 raw23598step0; decide +kernel
      have hl : raw23598step1Labels = raw23598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23598step0 raw23598step0Labels permutation56 hz
    mixedMoment B raw23598step1 raw23598step1Labels = mixedMoment B raw23598step2 raw23598step2Labels := by
      have ha : raw23598step2 = (fun i j => raw23598step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23598step2 raw23598step1; decide +kernel
      have hl : raw23598step2Labels = raw23598step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23598step1 raw23598step1Labels permutation9 permutation2
    _ = mixedMoment B node4491 node4491Labels := by rfl

theorem canonical23599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23599 raw23599Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw23599 raw23599Labels = mixedMoment B raw23599step0 raw23599step0Labels := by
      have hz : ∀ j, raw23599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23599step0 = (fun i j => raw23599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23599step0 raw23599; decide +kernel
      have hl : raw23599step0Labels = raw23599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23599 raw23599Labels permutation346 hz
    mixedMoment B raw23599step0 raw23599step0Labels = mixedMoment B raw23599step1 raw23599step1Labels := by
      have hz : ∀ j, raw23599step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23599step1 = (fun i j => raw23599step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23599step1 raw23599step0; decide +kernel
      have hl : raw23599step1Labels = raw23599step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23599step0 raw23599step0Labels permutation56 hz
    mixedMoment B raw23599step1 raw23599step1Labels = mixedMoment B raw23599step2 raw23599step2Labels := by
      have ha : raw23599step2 = (fun i j => raw23599step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23599step2 raw23599step1; decide +kernel
      have hl : raw23599step2Labels = raw23599step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23599step1 raw23599step1Labels permutation9 permutation2
    _ = mixedMoment B node4148 node4148Labels := by rfl

theorem canonical23600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23600 raw23600Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw23600 raw23600Labels = mixedMoment B raw23600step0 raw23600step0Labels := by
      have hz : ∀ j, raw23600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23600step0 = (fun i j => raw23600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23600step0 raw23600; decide +kernel
      have hl : raw23600step0Labels = raw23600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23600 raw23600Labels permutation346 hz
    mixedMoment B raw23600step0 raw23600step0Labels = mixedMoment B raw23600step1 raw23600step1Labels := by
      have ha : raw23600step1 = (fun i j => raw23600step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23600step1 raw23600step0; decide +kernel
      have hl : raw23600step1Labels = raw23600step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23600step0 raw23600step0Labels permutation33 permutation2
    _ = mixedMoment B node4325 node4325Labels := by rfl

theorem canonical23601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23601 raw23601Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw23601 raw23601Labels = mixedMoment B raw23601step0 raw23601step0Labels := by
      have hz : ∀ j, raw23601 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23601step0 = (fun i j => raw23601 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23601step0 raw23601; decide +kernel
      have hl : raw23601step0Labels = raw23601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23601 raw23601Labels permutation265 hz
    mixedMoment B raw23601step0 raw23601step0Labels = mixedMoment B raw23601step1 raw23601step1Labels := by
      have ha : raw23601step1 = (fun i j => raw23601step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23601step1 raw23601step0; decide +kernel
      have hl : raw23601step1Labels = raw23601step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23601step0 raw23601step0Labels permutation33 permutation2
    _ = mixedMoment B node4325 node4325Labels := by rfl

theorem canonical23602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23602 raw23602Labels = mixedMoment B node4318 node4318Labels := by
  calc
    mixedMoment B raw23602 raw23602Labels = mixedMoment B raw23602step0 raw23602step0Labels := by
      have hz : ∀ j, raw23602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23602step0 = (fun i j => raw23602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23602step0 raw23602; decide +kernel
      have hl : raw23602step0Labels = raw23602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23602 raw23602Labels permutation346 hz
    mixedMoment B raw23602step0 raw23602step0Labels = mixedMoment B raw23602step1 raw23602step1Labels := by
      have hz : ∀ j, raw23602step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23602step1 = (fun i j => raw23602step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23602step1 raw23602step0; decide +kernel
      have hl : raw23602step1Labels = raw23602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23602step0 raw23602step0Labels permutation56 hz
    mixedMoment B raw23602step1 raw23602step1Labels = mixedMoment B raw23602step2 raw23602step2Labels := by
      have ha : raw23602step2 = (fun i j => raw23602step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23602step2 raw23602step1; decide +kernel
      have hl : raw23602step2Labels = raw23602step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23602step1 raw23602step1Labels permutation9 permutation2
    _ = mixedMoment B node4318 node4318Labels := by rfl

theorem canonical23603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23603 raw23603Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw23603 raw23603Labels = mixedMoment B raw23603step0 raw23603step0Labels := by
      have hz : ∀ j, raw23603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23603step0 = (fun i j => raw23603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23603step0 raw23603; decide +kernel
      have hl : raw23603step0Labels = raw23603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23603 raw23603Labels permutation346 hz
    mixedMoment B raw23603step0 raw23603step0Labels = mixedMoment B raw23603step1 raw23603step1Labels := by
      have hz : ∀ j, raw23603step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23603step1 = (fun i j => raw23603step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23603step1 raw23603step0; decide +kernel
      have hl : raw23603step1Labels = raw23603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23603step0 raw23603step0Labels permutation56 hz
    mixedMoment B raw23603step1 raw23603step1Labels = mixedMoment B raw23603step2 raw23603step2Labels := by
      have ha : raw23603step2 = (fun i j => raw23603step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23603step2 raw23603step1; decide +kernel
      have hl : raw23603step2Labels = raw23603step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23603step1 raw23603step1Labels permutation9 permutation2
    _ = mixedMoment B node4428 node4428Labels := by rfl

theorem canonical23604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23604 raw23604Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw23604 raw23604Labels = mixedMoment B raw23604step0 raw23604step0Labels := by
      have hz : ∀ j, raw23604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23604step0 = (fun i j => raw23604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23604step0 raw23604; decide +kernel
      have hl : raw23604step0Labels = raw23604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23604 raw23604Labels permutation346 hz
    mixedMoment B raw23604step0 raw23604step0Labels = mixedMoment B raw23604step1 raw23604step1Labels := by
      have hz : ∀ j, raw23604step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23604step1 = (fun i j => raw23604step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23604step1 raw23604step0; decide +kernel
      have hl : raw23604step1Labels = raw23604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23604step0 raw23604step0Labels permutation56 hz
    _ = mixedMoment B node4148 node4148Labels := by rfl

theorem canonical23605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23605 raw23605Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw23605 raw23605Labels = mixedMoment B raw23605step0 raw23605step0Labels := by
      have hz : ∀ j, raw23605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23605step0 = (fun i j => raw23605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23605step0 raw23605; decide +kernel
      have hl : raw23605step0Labels = raw23605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23605 raw23605Labels permutation346 hz
    _ = mixedMoment B node4325 node4325Labels := by rfl

theorem canonical23606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23606 raw23606Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw23606 raw23606Labels = mixedMoment B raw23606step0 raw23606step0Labels := by
      have hz : ∀ j, raw23606 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23606step0 = (fun i j => raw23606 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23606step0 raw23606; decide +kernel
      have hl : raw23606step0Labels = raw23606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23606 raw23606Labels permutation265 hz
    _ = mixedMoment B node4325 node4325Labels := by rfl

theorem canonical23607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23607 raw23607Labels = mixedMoment B node4318 node4318Labels := by
  calc
    mixedMoment B raw23607 raw23607Labels = mixedMoment B raw23607step0 raw23607step0Labels := by
      have hz : ∀ j, raw23607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23607step0 = (fun i j => raw23607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23607step0 raw23607; decide +kernel
      have hl : raw23607step0Labels = raw23607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23607 raw23607Labels permutation346 hz
    mixedMoment B raw23607step0 raw23607step0Labels = mixedMoment B raw23607step1 raw23607step1Labels := by
      have hz : ∀ j, raw23607step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23607step1 = (fun i j => raw23607step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23607step1 raw23607step0; decide +kernel
      have hl : raw23607step1Labels = raw23607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23607step0 raw23607step0Labels permutation56 hz
    _ = mixedMoment B node4318 node4318Labels := by rfl

theorem canonical23608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23608 raw23608Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw23608 raw23608Labels = mixedMoment B raw23608step0 raw23608step0Labels := by
      have hz : ∀ j, raw23608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23608step0 = (fun i j => raw23608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23608step0 raw23608; decide +kernel
      have hl : raw23608step0Labels = raw23608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23608 raw23608Labels permutation346 hz
    mixedMoment B raw23608step0 raw23608step0Labels = mixedMoment B raw23608step1 raw23608step1Labels := by
      have hz : ∀ j, raw23608step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23608step1 = (fun i j => raw23608step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23608step1 raw23608step0; decide +kernel
      have hl : raw23608step1Labels = raw23608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23608step0 raw23608step0Labels permutation56 hz
    _ = mixedMoment B node4428 node4428Labels := by rfl

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

theorem canonical762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw762 raw762Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw762 raw762Labels = mixedMoment B raw762step0 raw762step0Labels := by
      have ha : raw762step0 = (fun i j => raw762 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw762step0 raw762; decide +kernel
      have hl : raw762step0Labels = raw762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw762 raw762Labels permutation32 permutation4
    mixedMoment B raw762step0 raw762step0Labels = mixedMoment B raw762step1 raw762step1Labels := by
      have ha : raw762step1 = raw762step0 := by apply Matrix.ext; unfold raw762step1 raw762step0; decide +kernel
      have hl : raw762step0Labels = labelEmbedding7 ∘ raw762step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw762step0 raw762step0Labels raw762step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4141 node4141Labels := by rfl

theorem canonical763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw763 raw763Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw763 raw763Labels = mixedMoment B raw763step0 raw763step0Labels := by
      have ha : raw763step0 = (fun i j => raw763 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw763step0 raw763; decide +kernel
      have hl : raw763step0Labels = raw763Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw763 raw763Labels permutation32 permutation4
    _ = mixedMoment B node569 node569Labels := by rfl

theorem canonical764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw764 raw764Labels = mixedMoment B node1490 node1490Labels := by
  calc
    mixedMoment B raw764 raw764Labels = mixedMoment B raw764step0 raw764step0Labels := by
      have ha : raw764step0 = (fun i j => raw764 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw764step0 raw764; decide +kernel
      have hl : raw764step0Labels = raw764Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw764 raw764Labels permutation32 permutation6
    mixedMoment B raw764step0 raw764step0Labels = mixedMoment B raw764step1 raw764step1Labels := by
      have ha : raw764step1 = -raw764step0 := by apply Matrix.ext; change ∀ i j, raw764step1 i j = -(raw764step0 i j); unfold raw764step1 raw764step0; decide +kernel
      have hl : raw764step1Labels = raw764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw764step1 raw764step1Labels = mixedMoment B raw764step2 raw764step2Labels := by
      have ha : raw764step2 = raw764step1 := by apply Matrix.ext; unfold raw764step2 raw764step1; decide +kernel
      have hl : raw764step1Labels = labelEmbedding1 ∘ raw764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw764step1 raw764step1Labels raw764step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1490 node1490Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw783 raw783Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw783 raw783Labels = mixedMoment B raw783step0 raw783step0Labels := by
      have ha : raw783step0 = (fun i j => raw783 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw783step0 raw783; decide +kernel
      have hl : raw783step0Labels = raw783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw783 raw783Labels permutation8 permutation4
    mixedMoment B raw783step0 raw783step0Labels = mixedMoment B raw783step1 raw783step1Labels := by
      have ha : raw783step1 = raw783step0 := by apply Matrix.ext; unfold raw783step1 raw783step0; decide +kernel
      have hl : raw783step0Labels = labelEmbedding7 ∘ raw783step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw783step0 raw783step0Labels raw783step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4148 node4148Labels := by rfl

theorem canonical784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw784 raw784Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw784 raw784Labels = mixedMoment B raw784step0 raw784step0Labels := by
      have ha : raw784step0 = (fun i j => raw784 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw784step0 raw784; decide +kernel
      have hl : raw784step0Labels = raw784Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw784 raw784Labels permutation8 permutation4
    _ = mixedMoment B node576 node576Labels := by rfl

theorem canonical785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw785 raw785Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw785 raw785Labels = mixedMoment B raw785step0 raw785step0Labels := by
      have ha : raw785step0 = (fun i j => raw785 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw785step0 raw785; decide +kernel
      have hl : raw785step0Labels = raw785Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw785 raw785Labels permutation8 permutation6
    mixedMoment B raw785step0 raw785step0Labels = mixedMoment B raw785step1 raw785step1Labels := by
      have ha : raw785step1 = -raw785step0 := by apply Matrix.ext; change ∀ i j, raw785step1 i j = -(raw785step0 i j); unfold raw785step1 raw785step0; decide +kernel
      have hl : raw785step1Labels = raw785step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw785step1 raw785step1Labels = mixedMoment B raw785step2 raw785step2Labels := by
      have ha : raw785step2 = raw785step1 := by apply Matrix.ext; unfold raw785step2 raw785step1; decide +kernel
      have hl : raw785step1Labels = labelEmbedding1 ∘ raw785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw785step1 raw785step1Labels raw785step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1496 node1496Labels := by rfl

theorem canonical795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw795 raw795Labels = mixedMoment B node4167 node4167Labels := by
  calc
    mixedMoment B raw795 raw795Labels = mixedMoment B raw795step0 raw795step0Labels := by
      have ha : raw795step0 = (fun i j => raw795 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw795step0 raw795; decide +kernel
      have hl : raw795step0Labels = raw795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw795 raw795Labels permutation8 permutation4
    mixedMoment B raw795step0 raw795step0Labels = mixedMoment B raw795step1 raw795step1Labels := by
      have ha : raw795step1 = raw795step0 := by apply Matrix.ext; unfold raw795step1 raw795step0; decide +kernel
      have hl : raw795step0Labels = labelEmbedding7 ∘ raw795step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw795step0 raw795step0Labels raw795step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4167 node4167Labels := by rfl

theorem canonical796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw796 raw796Labels = mixedMoment B node595 node595Labels := by
  calc
    mixedMoment B raw796 raw796Labels = mixedMoment B raw796step0 raw796step0Labels := by
      have ha : raw796step0 = (fun i j => raw796 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw796step0 raw796; decide +kernel
      have hl : raw796step0Labels = raw796Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw796 raw796Labels permutation8 permutation4
    _ = mixedMoment B node595 node595Labels := by rfl

theorem canonical797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw797 raw797Labels = mixedMoment B node1500 node1500Labels := by
  calc
    mixedMoment B raw797 raw797Labels = mixedMoment B raw797step0 raw797step0Labels := by
      have ha : raw797step0 = (fun i j => raw797 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw797step0 raw797; decide +kernel
      have hl : raw797step0Labels = raw797Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw797 raw797Labels permutation8 permutation6
    mixedMoment B raw797step0 raw797step0Labels = mixedMoment B raw797step1 raw797step1Labels := by
      have ha : raw797step1 = -raw797step0 := by apply Matrix.ext; change ∀ i j, raw797step1 i j = -(raw797step0 i j); unfold raw797step1 raw797step0; decide +kernel
      have hl : raw797step1Labels = raw797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw797step1 raw797step1Labels = mixedMoment B raw797step2 raw797step2Labels := by
      have ha : raw797step2 = raw797step1 := by apply Matrix.ext; unfold raw797step2 raw797step1; decide +kernel
      have hl : raw797step1Labels = labelEmbedding1 ∘ raw797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw797step1 raw797step1Labels raw797step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1500 node1500Labels := by rfl

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

theorem canonical1098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1098 raw1098Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw1098 raw1098Labels = mixedMoment B raw1098step0 raw1098step0Labels := by
      have ha : raw1098step0 = (fun i j => raw1098 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1098step0 raw1098; decide +kernel
      have hl : raw1098step0Labels = raw1098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1098 raw1098Labels permutation152 permutation4
    mixedMoment B raw1098step0 raw1098step0Labels = mixedMoment B raw1098step1 raw1098step1Labels := by
      have ha : raw1098step1 = raw1098step0 := by apply Matrix.ext; unfold raw1098step1 raw1098step0; decide +kernel
      have hl : raw1098step0Labels = labelEmbedding7 ∘ raw1098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1098step0 raw1098step0Labels raw1098step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4321 node4321Labels := by rfl

theorem canonical1099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1099 raw1099Labels = mixedMoment B node899 node899Labels := by
  calc
    mixedMoment B raw1099 raw1099Labels = mixedMoment B raw1099step0 raw1099step0Labels := by
      have ha : raw1099step0 = (fun i j => raw1099 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1099step0 raw1099; decide +kernel
      have hl : raw1099step0Labels = raw1099Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1099 raw1099Labels permutation152 permutation4
    _ = mixedMoment B node899 node899Labels := by rfl

theorem canonical1100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1100 raw1100Labels = mixedMoment B node1587 node1587Labels := by
  calc
    mixedMoment B raw1100 raw1100Labels = mixedMoment B raw1100step0 raw1100step0Labels := by
      have ha : raw1100step0 = (fun i j => raw1100 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1100step0 raw1100; decide +kernel
      have hl : raw1100step0Labels = raw1100Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1100 raw1100Labels permutation176 permutation6
    mixedMoment B raw1100step0 raw1100step0Labels = mixedMoment B raw1100step1 raw1100step1Labels := by
      have ha : raw1100step1 = -raw1100step0 := by apply Matrix.ext; change ∀ i j, raw1100step1 i j = -(raw1100step0 i j); unfold raw1100step1 raw1100step0; decide +kernel
      have hl : raw1100step1Labels = raw1100step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1100step1 raw1100step1Labels = mixedMoment B raw1100step2 raw1100step2Labels := by
      have ha : raw1100step2 = raw1100step1 := by apply Matrix.ext; unfold raw1100step2 raw1100step1; decide +kernel
      have hl : raw1100step1Labels = labelEmbedding1 ∘ raw1100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1100step1 raw1100step1Labels raw1100step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1587 node1587Labels := by rfl

theorem canonical1110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1110 raw1110Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw1110 raw1110Labels = mixedMoment B raw1110step0 raw1110step0Labels := by
      have ha : raw1110step0 = (fun i j => raw1110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1110step0 raw1110; decide +kernel
      have hl : raw1110step0Labels = raw1110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1110 raw1110Labels permutation32 permutation4
    mixedMoment B raw1110step0 raw1110step0Labels = mixedMoment B raw1110step1 raw1110step1Labels := by
      have ha : raw1110step1 = raw1110step0 := by apply Matrix.ext; unfold raw1110step1 raw1110step0; decide +kernel
      have hl : raw1110step0Labels = labelEmbedding7 ∘ raw1110step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1110step0 raw1110step0Labels raw1110step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4325 node4325Labels := by rfl

theorem canonical1111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1111 raw1111Labels = mixedMoment B node903 node903Labels := by
  calc
    mixedMoment B raw1111 raw1111Labels = mixedMoment B raw1111step0 raw1111step0Labels := by
      have ha : raw1111step0 = (fun i j => raw1111 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1111step0 raw1111; decide +kernel
      have hl : raw1111step0Labels = raw1111Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1111 raw1111Labels permutation32 permutation4
    _ = mixedMoment B node903 node903Labels := by rfl

theorem canonical1112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1112 raw1112Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw1112 raw1112Labels = mixedMoment B raw1112step0 raw1112step0Labels := by
      have ha : raw1112step0 = (fun i j => raw1112 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1112step0 raw1112; decide +kernel
      have hl : raw1112step0Labels = raw1112Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1112 raw1112Labels permutation38 permutation6
    mixedMoment B raw1112step0 raw1112step0Labels = mixedMoment B raw1112step1 raw1112step1Labels := by
      have ha : raw1112step1 = -raw1112step0 := by apply Matrix.ext; change ∀ i j, raw1112step1 i j = -(raw1112step0 i j); unfold raw1112step1 raw1112step0; decide +kernel
      have hl : raw1112step1Labels = raw1112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1112step1 raw1112step1Labels = mixedMoment B raw1112step2 raw1112step2Labels := by
      have ha : raw1112step2 = raw1112step1 := by apply Matrix.ext; unfold raw1112step2 raw1112step1; decide +kernel
      have hl : raw1112step1Labels = labelEmbedding1 ∘ raw1112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1112step1 raw1112step1Labels raw1112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1591 node1591Labels := by rfl

theorem canonical1119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1119 raw1119Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw1119 raw1119Labels = mixedMoment B raw1119step0 raw1119step0Labels := by
      have ha : raw1119step0 = (fun i j => raw1119 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1119step0 raw1119; decide +kernel
      have hl : raw1119step0Labels = raw1119Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1119 raw1119Labels permutation32 permutation4
    mixedMoment B raw1119step0 raw1119step0Labels = mixedMoment B raw1119step1 raw1119step1Labels := by
      have ha : raw1119step1 = raw1119step0 := by apply Matrix.ext; unfold raw1119step1 raw1119step0; decide +kernel
      have hl : raw1119step0Labels = labelEmbedding7 ∘ raw1119step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1119step0 raw1119step0Labels raw1119step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4339 node4339Labels := by rfl

theorem canonical1120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1120 raw1120Labels = mixedMoment B node917 node917Labels := by
  calc
    mixedMoment B raw1120 raw1120Labels = mixedMoment B raw1120step0 raw1120step0Labels := by
      have ha : raw1120step0 = (fun i j => raw1120 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1120step0 raw1120; decide +kernel
      have hl : raw1120step0Labels = raw1120Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1120 raw1120Labels permutation32 permutation4
    _ = mixedMoment B node917 node917Labels := by rfl

theorem canonical1121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1121 raw1121Labels = mixedMoment B node1634 node1634Labels := by
  calc
    mixedMoment B raw1121 raw1121Labels = mixedMoment B raw1121step0 raw1121step0Labels := by
      have ha : raw1121step0 = (fun i j => raw1121 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1121step0 raw1121; decide +kernel
      have hl : raw1121step0Labels = raw1121Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1121 raw1121Labels permutation38 permutation6
    mixedMoment B raw1121step0 raw1121step0Labels = mixedMoment B raw1121step1 raw1121step1Labels := by
      have ha : raw1121step1 = -raw1121step0 := by apply Matrix.ext; change ∀ i j, raw1121step1 i j = -(raw1121step0 i j); unfold raw1121step1 raw1121step0; decide +kernel
      have hl : raw1121step1Labels = raw1121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1121step1 raw1121step1Labels = mixedMoment B raw1121step2 raw1121step2Labels := by
      have ha : raw1121step2 = raw1121step1 := by apply Matrix.ext; unfold raw1121step2 raw1121step1; decide +kernel
      have hl : raw1121step1Labels = labelEmbedding1 ∘ raw1121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1121step1 raw1121step1Labels raw1121step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1634 node1634Labels := by rfl

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

theorem canonical1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1239 raw1239Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw1239 raw1239Labels = mixedMoment B raw1239step0 raw1239step0Labels := by
      have ha : raw1239step0 = (fun i j => raw1239 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1239step0 raw1239; decide +kernel
      have hl : raw1239step0Labels = raw1239Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1239 raw1239Labels permutation8 permutation4
    mixedMoment B raw1239step0 raw1239step0Labels = mixedMoment B raw1239step1 raw1239step1Labels := by
      have ha : raw1239step1 = raw1239step0 := by apply Matrix.ext; unfold raw1239step1 raw1239step0; decide +kernel
      have hl : raw1239step0Labels = labelEmbedding7 ∘ raw1239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1239step0 raw1239step0Labels raw1239step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

theorem canonical1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1240 raw1240Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw1240 raw1240Labels = mixedMoment B raw1240step0 raw1240step0Labels := by
      have ha : raw1240step0 = (fun i j => raw1240 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1240step0 raw1240; decide +kernel
      have hl : raw1240step0Labels = raw1240Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1240 raw1240Labels permutation8 permutation4
    _ = mixedMoment B node1009 node1009Labels := by rfl

theorem canonical1241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1241 raw1241Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw1241 raw1241Labels = mixedMoment B raw1241step0 raw1241step0Labels := by
      have ha : raw1241step0 = (fun i j => raw1241 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1241step0 raw1241; decide +kernel
      have hl : raw1241step0Labels = raw1241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1241 raw1241Labels permutation8 permutation6
    mixedMoment B raw1241step0 raw1241step0Labels = mixedMoment B raw1241step1 raw1241step1Labels := by
      have ha : raw1241step1 = -raw1241step0 := by apply Matrix.ext; change ∀ i j, raw1241step1 i j = -(raw1241step0 i j); unfold raw1241step1 raw1241step0; decide +kernel
      have hl : raw1241step1Labels = raw1241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1241step1 raw1241step1Labels = mixedMoment B raw1241step2 raw1241step2Labels := by
      have ha : raw1241step2 = raw1241step1 := by apply Matrix.ext; unfold raw1241step2 raw1241step1; decide +kernel
      have hl : raw1241step1Labels = labelEmbedding1 ∘ raw1241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1241step1 raw1241step1Labels raw1241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1630 node1630Labels := by rfl

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

theorem singleton4141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4141 node4141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node569 node569Labels + mixedMoment B node1490 node1490Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw762 singletonSmall4141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4141) = raw762Labels := by decide +kernel
  rw [hl, canonical762 B hB] at h
  have hc0 : mixedMoment B raw762 (Fin.cases (0 : Fin 2) singletonSmall4141) =
      mixedMoment B node569 node569Labels := by
    have ha : raw762 = raw763 := by apply Matrix.ext; unfold raw762 raw763; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4141 = raw763Labels := by decide +kernel
    rw [ha, hj, canonical763 B hB]
  have hc1 : mixedMoment B raw762 (Fin.cases (1 : Fin 2) singletonSmall4141) =
      mixedMoment B node1490 node1490Labels := by
    have ha : raw762 = raw764 := by apply Matrix.ext; unfold raw762 raw764; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4141 = raw764Labels := by decide +kernel
    rw [ha, hj, canonical764 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4148 node4148Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node576 node576Labels + mixedMoment B node1496 node1496Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw783 singletonSmall4148
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4148) = raw783Labels := by decide +kernel
  rw [hl, canonical783 B hB] at h
  have hc0 : mixedMoment B raw783 (Fin.cases (0 : Fin 2) singletonSmall4148) =
      mixedMoment B node576 node576Labels := by
    have ha : raw783 = raw784 := by apply Matrix.ext; unfold raw783 raw784; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4148 = raw784Labels := by decide +kernel
    rw [ha, hj, canonical784 B hB]
  have hc1 : mixedMoment B raw783 (Fin.cases (1 : Fin 2) singletonSmall4148) =
      mixedMoment B node1496 node1496Labels := by
    have ha : raw783 = raw785 := by apply Matrix.ext; unfold raw783 raw785; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4148 = raw785Labels := by decide +kernel
    rw [ha, hj, canonical785 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4167 node4167Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node595 node595Labels + mixedMoment B node1500 node1500Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw795 singletonSmall4167
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4167) = raw795Labels := by decide +kernel
  rw [hl, canonical795 B hB] at h
  have hc0 : mixedMoment B raw795 (Fin.cases (0 : Fin 2) singletonSmall4167) =
      mixedMoment B node595 node595Labels := by
    have ha : raw795 = raw796 := by apply Matrix.ext; unfold raw795 raw796; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4167 = raw796Labels := by decide +kernel
    rw [ha, hj, canonical796 B hB]
  have hc1 : mixedMoment B raw795 (Fin.cases (1 : Fin 2) singletonSmall4167) =
      mixedMoment B node1500 node1500Labels := by
    have ha : raw795 = raw797 := by apply Matrix.ext; unfold raw795 raw797; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4167 = raw797Labels := by decide +kernel
    rw [ha, hj, canonical797 B hB]
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

theorem singleton4321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4321 node4321Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node899 node899Labels + mixedMoment B node1587 node1587Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1098 singletonSmall4321
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4321) = raw1098Labels := by decide +kernel
  rw [hl, canonical1098 B hB] at h
  have hc0 : mixedMoment B raw1098 (Fin.cases (0 : Fin 2) singletonSmall4321) =
      mixedMoment B node899 node899Labels := by
    have ha : raw1098 = raw1099 := by apply Matrix.ext; unfold raw1098 raw1099; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4321 = raw1099Labels := by decide +kernel
    rw [ha, hj, canonical1099 B hB]
  have hc1 : mixedMoment B raw1098 (Fin.cases (1 : Fin 2) singletonSmall4321) =
      mixedMoment B node1587 node1587Labels := by
    have ha : raw1098 = raw1100 := by apply Matrix.ext; unfold raw1098 raw1100; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4321 = raw1100Labels := by decide +kernel
    rw [ha, hj, canonical1100 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4325 node4325Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node903 node903Labels + mixedMoment B node1591 node1591Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1110 singletonSmall4325
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4325) = raw1110Labels := by decide +kernel
  rw [hl, canonical1110 B hB] at h
  have hc0 : mixedMoment B raw1110 (Fin.cases (0 : Fin 2) singletonSmall4325) =
      mixedMoment B node903 node903Labels := by
    have ha : raw1110 = raw1111 := by apply Matrix.ext; unfold raw1110 raw1111; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4325 = raw1111Labels := by decide +kernel
    rw [ha, hj, canonical1111 B hB]
  have hc1 : mixedMoment B raw1110 (Fin.cases (1 : Fin 2) singletonSmall4325) =
      mixedMoment B node1591 node1591Labels := by
    have ha : raw1110 = raw1112 := by apply Matrix.ext; unfold raw1110 raw1112; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4325 = raw1112Labels := by decide +kernel
    rw [ha, hj, canonical1112 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4339 node4339Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node917 node917Labels + mixedMoment B node1634 node1634Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1119 singletonSmall4339
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4339) = raw1119Labels := by decide +kernel
  rw [hl, canonical1119 B hB] at h
  have hc0 : mixedMoment B raw1119 (Fin.cases (0 : Fin 2) singletonSmall4339) =
      mixedMoment B node917 node917Labels := by
    have ha : raw1119 = raw1120 := by apply Matrix.ext; unfold raw1119 raw1120; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4339 = raw1120Labels := by decide +kernel
    rw [ha, hj, canonical1120 B hB]
  have hc1 : mixedMoment B raw1119 (Fin.cases (1 : Fin 2) singletonSmall4339) =
      mixedMoment B node1634 node1634Labels := by
    have ha : raw1119 = raw1121 := by apply Matrix.ext; unfold raw1119 raw1121; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4339 = raw1121Labels := by decide +kernel
    rw [ha, hj, canonical1121 B hB]
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

theorem singleton4428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4428 node4428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1009 node1009Labels + mixedMoment B node1630 node1630Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1239 singletonSmall4428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4428) = raw1239Labels := by decide +kernel
  rw [hl, canonical1239 B hB] at h
  have hc0 : mixedMoment B raw1239 (Fin.cases (0 : Fin 2) singletonSmall4428) =
      mixedMoment B node1009 node1009Labels := by
    have ha : raw1239 = raw1240 := by apply Matrix.ext; unfold raw1239 raw1240; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4428 = raw1240Labels := by decide +kernel
    rw [ha, hj, canonical1240 B hB]
  have hc1 : mixedMoment B raw1239 (Fin.cases (1 : Fin 2) singletonSmall4428) =
      mixedMoment B node1630 node1630Labels := by
    have ha : raw1239 = raw1241 := by apply Matrix.ext; unfold raw1239 raw1241; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4428 = raw1241Labels := by decide +kernel
    rw [ha, hj, canonical1241 B hB]
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

theorem singleton4491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4491 node4491Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1075 node1075Labels + mixedMoment B node1653 node1653Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1287 singletonSmall4491
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4491) = raw1287Labels := by decide +kernel
  rw [hl, canonical1287 B hB] at h
  have hc0 : mixedMoment B raw1287 (Fin.cases (0 : Fin 2) singletonSmall4491) =
      mixedMoment B node1075 node1075Labels := by
    have ha : raw1287 = raw1288 := by apply Matrix.ext; unfold raw1287 raw1288; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4491 = raw1288Labels := by decide +kernel
    rw [ha, hj, canonical1288 B hB]
  have hc1 : mixedMoment B raw1287 (Fin.cases (1 : Fin 2) singletonSmall4491) =
      mixedMoment B node1653 node1653Labels := by
    have ha : raw1287 = raw1289 := by apply Matrix.ext; unfold raw1287 raw1289; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4491 = raw1289Labels := by decide +kernel
    rw [ha, hj, canonical1289 B hB]
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

theorem sound899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node899 node899Labels = Sparse.eval nodeValue899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 899) = mixedMoment B node899 node899Labels := rfl
  simpa [nodeValue899, Sparse.eval] using hc.symm

theorem sound903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node903 node903Labels = Sparse.eval nodeValue903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 903) = mixedMoment B node903 node903Labels := rfl
  simpa [nodeValue903, Sparse.eval] using hc.symm

theorem sound917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node917 node917Labels = Sparse.eval nodeValue917 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 917) = mixedMoment B node917 node917Labels := rfl
  simpa [nodeValue917, Sparse.eval] using hc.symm

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

theorem sound1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1009 node1009Labels = Sparse.eval nodeValue1009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1009) = mixedMoment B node1009 node1009Labels := rfl
  simpa [nodeValue1009, Sparse.eval] using hc.symm

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

theorem sound1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1075 node1075Labels = Sparse.eval nodeValue1075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1075) = mixedMoment B node1075 node1075Labels := rfl
  simpa [nodeValue1075, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1490 node1490Labels = Sparse.eval nodeValue1490 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1490) = mixedMoment B node1490 node1490Labels := rfl
  simpa [nodeValue1490, Sparse.eval] using hc.symm

theorem sound1496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1496 node1496Labels = Sparse.eval nodeValue1496 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1496) = mixedMoment B node1496 node1496Labels := rfl
  simpa [nodeValue1496, Sparse.eval] using hc.symm

theorem sound1500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1500 node1500Labels = Sparse.eval nodeValue1500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1500) = mixedMoment B node1500 node1500Labels := rfl
  simpa [nodeValue1500, Sparse.eval] using hc.symm

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

theorem sound1587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1587 node1587Labels = Sparse.eval nodeValue1587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1587) = mixedMoment B node1587 node1587Labels := rfl
  simpa [nodeValue1587, Sparse.eval] using hc.symm

theorem sound1591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1591 node1591Labels = Sparse.eval nodeValue1591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1591) = mixedMoment B node1591 node1591Labels := rfl
  simpa [nodeValue1591, Sparse.eval] using hc.symm

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

theorem sound1630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1630 node1630Labels = Sparse.eval nodeValue1630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1630) = mixedMoment B node1630 node1630Labels := rfl
  simpa [nodeValue1630, Sparse.eval] using hc.symm

theorem sound1634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1634 node1634Labels = Sparse.eval nodeValue1634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1634) = mixedMoment B node1634 node1634Labels := rfl
  simpa [nodeValue1634, Sparse.eval] using hc.symm

theorem sound1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1653 node1653Labels = Sparse.eval nodeValue1653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1653) = mixedMoment B node1653 node1653Labels := rfl
  simpa [nodeValue1653, Sparse.eval] using hc.symm

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

theorem sound569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node569 node569Labels = Sparse.eval nodeValue569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 569) = mixedMoment B node569 node569Labels := rfl
  simpa [nodeValue569, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node576 node576Labels = Sparse.eval nodeValue576 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 576) = mixedMoment B node576 node576Labels := rfl
  simpa [nodeValue576, Sparse.eval] using hc.symm

theorem sound595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node595 node595Labels = Sparse.eval nodeValue595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 595) = mixedMoment B node595 node595Labels := rfl
  simpa [nodeValue595, Sparse.eval] using hc.symm

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

theorem sound4141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4141 node4141Labels = Sparse.eval nodeValue4141 (mixedVector B) := by
  have h := singleton4141 B _hB
  rw [sound569 B _hB _hF, sound1490 B _hB _hF] at h
  norm_num [nodeValue4141, nodeValue569, nodeValue1490, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4148 node4148Labels = Sparse.eval nodeValue4148 (mixedVector B) := by
  have h := singleton4148 B _hB
  rw [sound576 B _hB _hF, sound1496 B _hB _hF] at h
  norm_num [nodeValue4148, nodeValue576, nodeValue1496, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4167 node4167Labels = Sparse.eval nodeValue4167 (mixedVector B) := by
  have h := singleton4167 B _hB
  rw [sound595 B _hB _hF, sound1500 B _hB _hF] at h
  norm_num [nodeValue4167, nodeValue595, nodeValue1500, Sparse.eval] at h ⊢
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

theorem zero4305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4305 node4305Labels = 0 := by
  exact mixedMoment_order_one B hB node4305 node4305Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4318 node4318Labels = 0 := by
  exact mixedMoment_order_one B hB node4318 node4318Labels 1
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

theorem sound4305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4305 node4305Labels = Sparse.eval nodeValue4305 (mixedVector B) := by
  simpa only [nodeValue4305, Sparse.eval_nil] using zero4305 B _hB _hF

theorem sound4318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4318 node4318Labels = Sparse.eval nodeValue4318 (mixedVector B) := by
  simpa only [nodeValue4318, Sparse.eval_nil] using zero4318 B _hB _hF

theorem sound4321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4321 node4321Labels = Sparse.eval nodeValue4321 (mixedVector B) := by
  have h := singleton4321 B _hB
  rw [sound899 B _hB _hF, sound1587 B _hB _hF] at h
  norm_num [nodeValue4321, nodeValue899, nodeValue1587, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4325 node4325Labels = Sparse.eval nodeValue4325 (mixedVector B) := by
  have h := singleton4325 B _hB
  rw [sound903 B _hB _hF, sound1591 B _hB _hF] at h
  norm_num [nodeValue4325, nodeValue903, nodeValue1591, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4339 node4339Labels = Sparse.eval nodeValue4339 (mixedVector B) := by
  have h := singleton4339 B _hB
  rw [sound917 B _hB _hF, sound1634 B _hB _hF] at h
  norm_num [nodeValue4339, nodeValue917, nodeValue1634, Sparse.eval] at h ⊢
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

theorem sound4428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4428 node4428Labels = Sparse.eval nodeValue4428 (mixedVector B) := by
  have h := singleton4428 B _hB
  rw [sound1009 B _hB _hF, sound1630 B _hB _hF] at h
  norm_num [nodeValue4428, nodeValue1009, nodeValue1630, Sparse.eval] at h ⊢
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

theorem sound4491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4491 node4491Labels = Sparse.eval nodeValue4491 (mixedVector B) := by
  have h := singleton4491 B _hB
  rw [sound1075 B _hB _hF, sound1653 B _hB _hF] at h
  norm_num [nodeValue4491, nodeValue1075, nodeValue1653, Sparse.eval] at h ⊢
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

theorem zero4790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4790 node4790Labels = 0 := by
  exact mixedMoment_order_one B hB node4790 node4790Labels 1
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

theorem sound4790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4790 node4790Labels = Sparse.eval nodeValue4790 (mixedVector B) := by
  simpa only [nodeValue4790, Sparse.eval_nil] using zero4790 B _hB _hF

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

theorem sound4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = Sparse.eval nodeValue4846 (mixedVector B) := by
  simpa only [nodeValue4846, Sparse.eval_nil] using zero4846 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources48
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1556 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 1) (sourceB1556 + difference 1 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4790) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 1) (sourceB1556 + difference 1 0) sourceC1556) = raw23579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23579; decide +kernel
    rw [ha]
    exact (canonical23579 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 2) (sourceB1556 + difference 2 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4790) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 2) (sourceB1556 + difference 2 0) sourceC1556) = raw23580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23580; decide +kernel
    rw [ha]
    exact (canonical23580 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 3) (sourceB1556 + difference 3 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 3) (sourceB1556 + difference 3 0) sourceC1556) = raw23581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23581; decide +kernel
    rw [ha]
    exact (canonical23581 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 4) (sourceB1556 + difference 4 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 4) (sourceB1556 + difference 4 0) sourceC1556) = raw23582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23582; decide +kernel
    rw [ha]
    exact (canonical23582 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 5) (sourceB1556 + difference 5 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 5) (sourceB1556 + difference 5 0) sourceC1556) = raw23583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23583; decide +kernel
    rw [ha]
    exact (canonical23583 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 0) (sourceB1556 + difference 0 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4141) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 0) (sourceB1556 + difference 0 1) sourceC1556) = raw23584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23584; decide +kernel
    rw [ha]
    exact (canonical23584 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 2) (sourceB1556 + difference 2 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4321) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 2) (sourceB1556 + difference 2 1) sourceC1556) = raw23585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23585; decide +kernel
    rw [ha]
    exact (canonical23585 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 3) (sourceB1556 + difference 3 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4305) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 3) (sourceB1556 + difference 3 1) sourceC1556) = raw23586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23586; decide +kernel
    rw [ha]
    exact (canonical23586 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 4) (sourceB1556 + difference 4 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 4) (sourceB1556 + difference 4 1) sourceC1556) = raw23587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23587; decide +kernel
    rw [ha]
    exact (canonical23587 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 5) (sourceB1556 + difference 5 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 5) (sourceB1556 + difference 5 1) sourceC1556) = raw23588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23588; decide +kernel
    rw [ha]
    exact (canonical23588 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 0) (sourceB1556 + difference 0 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4141) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 0) (sourceB1556 + difference 0 2) sourceC1556) = raw23589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23589; decide +kernel
    rw [ha]
    exact (canonical23589 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 1) (sourceB1556 + difference 1 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4321) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 1) (sourceB1556 + difference 1 2) sourceC1556) = raw23590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23590; decide +kernel
    rw [ha]
    exact (canonical23590 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 3) (sourceB1556 + difference 3 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4305) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 3) (sourceB1556 + difference 3 2) sourceC1556) = raw23591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23591; decide +kernel
    rw [ha]
    exact (canonical23591 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 4) (sourceB1556 + difference 4 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 4) (sourceB1556 + difference 4 2) sourceC1556) = raw23592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23592; decide +kernel
    rw [ha]
    exact (canonical23592 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 5) (sourceB1556 + difference 5 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 5) (sourceB1556 + difference 5 2) sourceC1556) = raw23593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23593; decide +kernel
    rw [ha]
    exact (canonical23593 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 0) (sourceB1556 + difference 0 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4167) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 0) (sourceB1556 + difference 0 3) sourceC1556) = raw23594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23594; decide +kernel
    rw [ha]
    exact (canonical23594 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 1) (sourceB1556 + difference 1 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4339) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 1) (sourceB1556 + difference 1 3) sourceC1556) = raw23595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23595; decide +kernel
    rw [ha]
    exact (canonical23595 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 2) (sourceB1556 + difference 2 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4339) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 2) (sourceB1556 + difference 2 3) sourceC1556) = raw23596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23596; decide +kernel
    rw [ha]
    exact (canonical23596 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 4) (sourceB1556 + difference 4 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 4) (sourceB1556 + difference 4 3) sourceC1556) = raw23597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23597; decide +kernel
    rw [ha]
    exact (canonical23597 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 5) (sourceB1556 + difference 5 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 5) (sourceB1556 + difference 5 3) sourceC1556) = raw23598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23598; decide +kernel
    rw [ha]
    exact (canonical23598 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 0) (sourceB1556 + difference 0 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4148) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 0) (sourceB1556 + difference 0 4) sourceC1556) = raw23599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23599; decide +kernel
    rw [ha]
    exact (canonical23599 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 1) (sourceB1556 + difference 1 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 1) (sourceB1556 + difference 1 4) sourceC1556) = raw23600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23600; decide +kernel
    rw [ha]
    exact (canonical23600 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 2) (sourceB1556 + difference 2 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 2) (sourceB1556 + difference 2 4) sourceC1556) = raw23601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23601; decide +kernel
    rw [ha]
    exact (canonical23601 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 3) (sourceB1556 + difference 3 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4318) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 3) (sourceB1556 + difference 3 4) sourceC1556) = raw23602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23602; decide +kernel
    rw [ha]
    exact (canonical23602 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 5) (sourceB1556 + difference 5 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 5) (sourceB1556 + difference 5 4) sourceC1556) = raw23603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23603; decide +kernel
    rw [ha]
    exact (canonical23603 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 0) (sourceB1556 + difference 0 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4148) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 0) (sourceB1556 + difference 0 5) sourceC1556) = raw23604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23604; decide +kernel
    rw [ha]
    exact (canonical23604 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 1) (sourceB1556 + difference 1 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 1) (sourceB1556 + difference 1 5) sourceC1556) = raw23605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23605; decide +kernel
    rw [ha]
    exact (canonical23605 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 2) (sourceB1556 + difference 2 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 2) (sourceB1556 + difference 2 5) sourceC1556) = raw23606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23606; decide +kernel
    rw [ha]
    exact (canonical23606 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 3) (sourceB1556 + difference 3 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4318) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 3) (sourceB1556 + difference 3 5) sourceC1556) = raw23607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23607; decide +kernel
    rw [ha]
    exact (canonical23607 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 4) (sourceB1556 + difference 4 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 4) (sourceB1556 + difference 4 5) sourceC1556) = raw23608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23608; decide +kernel
    rw [ha]
    exact (canonical23608 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1556 sourceB1556 sourceC1556
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1556, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1326 : Integer.Sparse.reindex keyMap MixedData.row1326 = numericRow1326 := by decide +kernel

theorem numericCheck1326 (x : Master → ℝ) : Integer.Sparse.eval numericRow1326 x =
    (4 : ℝ) * reducedSource1326 x := by
  norm_num [numericRow1326, reducedSource1326, Integer.Sparse.eval, Sparse.eval, nodeValue4082, nodeValue4141, nodeValue4148, nodeValue4167, nodeValue4305, nodeValue4318, nodeValue4321, nodeValue4325, nodeValue4339, nodeValue4419, nodeValue4428, nodeValue4491, nodeValue4790, nodeValue4846]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1326 (mixedVector B) = 0 := by
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4141 : mixedVector B (Sum.inr 4141) = Sparse.eval nodeValue4141 (mixedVector B) := by
    change mixedMoment B node4141 node4141Labels = _
    exact sound4141 B hB hF
  have h4148 : mixedVector B (Sum.inr 4148) = Sparse.eval nodeValue4148 (mixedVector B) := by
    change mixedMoment B node4148 node4148Labels = _
    exact sound4148 B hB hF
  have h4167 : mixedVector B (Sum.inr 4167) = Sparse.eval nodeValue4167 (mixedVector B) := by
    change mixedMoment B node4167 node4167Labels = _
    exact sound4167 B hB hF
  have h4305 : mixedVector B (Sum.inr 4305) = Sparse.eval nodeValue4305 (mixedVector B) := by
    change mixedMoment B node4305 node4305Labels = _
    exact sound4305 B hB hF
  have h4318 : mixedVector B (Sum.inr 4318) = Sparse.eval nodeValue4318 (mixedVector B) := by
    change mixedMoment B node4318 node4318Labels = _
    exact sound4318 B hB hF
  have h4321 : mixedVector B (Sum.inr 4321) = Sparse.eval nodeValue4321 (mixedVector B) := by
    change mixedMoment B node4321 node4321Labels = _
    exact sound4321 B hB hF
  have h4325 : mixedVector B (Sum.inr 4325) = Sparse.eval nodeValue4325 (mixedVector B) := by
    change mixedMoment B node4325 node4325Labels = _
    exact sound4325 B hB hF
  have h4339 : mixedVector B (Sum.inr 4339) = Sparse.eval nodeValue4339 (mixedVector B) := by
    change mixedMoment B node4339 node4339Labels = _
    exact sound4339 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4428 : mixedVector B (Sum.inr 4428) = Sparse.eval nodeValue4428 (mixedVector B) := by
    change mixedMoment B node4428 node4428Labels = _
    exact sound4428 B hB hF
  have h4491 : mixedVector B (Sum.inr 4491) = Sparse.eval nodeValue4491 (mixedVector B) := by
    change mixedMoment B node4491 node4491Labels = _
    exact sound4491 B hB hF
  have h4790 : mixedVector B (Sum.inr 4790) = Sparse.eval nodeValue4790 (mixedVector B) := by
    change mixedMoment B node4790 node4790Labels = _
    exact sound4790 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  simpa only [sourceForm1556, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4082, h4141, h4148, h4167, h4305, h4318, h4321, h4325, h4339, h4419, h4428, h4491, h4790, h4846, reducedSource1326] using sourceEq1556 B hB

theorem rowSound1326_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1326 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1326, numericCheck1326, reducedZero1326 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e_oai
