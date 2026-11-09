-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:46:33.482733+00:00
-- url     : https://prove2.me/submissions/b3ca1dd0-c386-408e-8924-25714f5f5c7f

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

theorem canonical1476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1476 raw1476Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw1476 raw1476Labels = mixedMoment B raw1476step0 raw1476step0Labels := by
      have ha : raw1476step0 = (fun i j => raw1476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1476step0 raw1476; decide +kernel
      have hl : raw1476step0Labels = raw1476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1476 raw1476Labels permutation152 permutation4
    mixedMoment B raw1476step0 raw1476step0Labels = mixedMoment B raw1476step1 raw1476step1Labels := by
      have ha : raw1476step1 = raw1476step0 := by apply Matrix.ext; unfold raw1476step1 raw1476step0; decide +kernel
      have hl : raw1476step0Labels = labelEmbedding7 ∘ raw1476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1476step0 raw1476step0Labels raw1476step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

theorem canonical1477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1477 raw1477Labels = mixedMoment B node1761 node1761Labels := by
  calc
    mixedMoment B raw1477 raw1477Labels = mixedMoment B raw1477step0 raw1477step0Labels := by
      have ha : raw1477step0 = (fun i j => raw1477 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1477step0 raw1477; decide +kernel
      have hl : raw1477step0Labels = raw1477Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1477 raw1477Labels permutation152 permutation4
    _ = mixedMoment B node1761 node1761Labels := by rfl

theorem canonical1478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1478 raw1478Labels = mixedMoment B node1837 node1837Labels := by
  calc
    mixedMoment B raw1478 raw1478Labels = mixedMoment B raw1478step0 raw1478step0Labels := by
      have ha : raw1478step0 = (fun i j => raw1478 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1478step0 raw1478; decide +kernel
      have hl : raw1478step0Labels = raw1478Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1478 raw1478Labels permutation158 permutation6
    mixedMoment B raw1478step0 raw1478step0Labels = mixedMoment B raw1478step1 raw1478step1Labels := by
      have ha : raw1478step1 = -raw1478step0 := by apply Matrix.ext; change ∀ i j, raw1478step1 i j = -(raw1478step0 i j); unfold raw1478step1 raw1478step0; decide +kernel
      have hl : raw1478step1Labels = raw1478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1478step1 raw1478step1Labels = mixedMoment B raw1478step2 raw1478step2Labels := by
      have ha : raw1478step2 = raw1478step1 := by apply Matrix.ext; unfold raw1478step2 raw1478step1; decide +kernel
      have hl : raw1478step1Labels = labelEmbedding1 ∘ raw1478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1478step1 raw1478step1Labels raw1478step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1837 node1837Labels := by rfl

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

theorem canonical1494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1494 raw1494Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw1494 raw1494Labels = mixedMoment B raw1494step0 raw1494step0Labels := by
      have ha : raw1494step0 = (fun i j => raw1494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1494step0 raw1494; decide +kernel
      have hl : raw1494step0Labels = raw1494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1494 raw1494Labels permutation32 permutation4
    mixedMoment B raw1494step0 raw1494step0Labels = mixedMoment B raw1494step1 raw1494step1Labels := by
      have ha : raw1494step1 = raw1494step0 := by apply Matrix.ext; unfold raw1494step1 raw1494step0; decide +kernel
      have hl : raw1494step0Labels = labelEmbedding7 ∘ raw1494step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1494step0 raw1494step0Labels raw1494step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

theorem canonical1495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1495 raw1495Labels = mixedMoment B node1767 node1767Labels := by
  calc
    mixedMoment B raw1495 raw1495Labels = mixedMoment B raw1495step0 raw1495step0Labels := by
      have ha : raw1495step0 = (fun i j => raw1495 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1495step0 raw1495; decide +kernel
      have hl : raw1495step0Labels = raw1495Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1495 raw1495Labels permutation32 permutation4
    _ = mixedMoment B node1767 node1767Labels := by rfl

theorem canonical1496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1496 raw1496Labels = mixedMoment B node1851 node1851Labels := by
  calc
    mixedMoment B raw1496 raw1496Labels = mixedMoment B raw1496step0 raw1496step0Labels := by
      have ha : raw1496step0 = (fun i j => raw1496 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1496step0 raw1496; decide +kernel
      have hl : raw1496step0Labels = raw1496Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1496 raw1496Labels permutation33 permutation6
    mixedMoment B raw1496step0 raw1496step0Labels = mixedMoment B raw1496step1 raw1496step1Labels := by
      have ha : raw1496step1 = -raw1496step0 := by apply Matrix.ext; change ∀ i j, raw1496step1 i j = -(raw1496step0 i j); unfold raw1496step1 raw1496step0; decide +kernel
      have hl : raw1496step1Labels = raw1496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1496step1 raw1496step1Labels = mixedMoment B raw1496step2 raw1496step2Labels := by
      have ha : raw1496step2 = raw1496step1 := by apply Matrix.ext; unfold raw1496step2 raw1496step1; decide +kernel
      have hl : raw1496step1Labels = labelEmbedding1 ∘ raw1496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1496step1 raw1496step1Labels raw1496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1851 node1851Labels := by rfl

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

theorem canonical1593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1593 raw1593Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw1593 raw1593Labels = mixedMoment B raw1593step0 raw1593step0Labels := by
      have ha : raw1593step0 = (fun i j => raw1593 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1593step0 raw1593; decide +kernel
      have hl : raw1593step0Labels = raw1593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1593 raw1593Labels permutation152 permutation4
    mixedMoment B raw1593step0 raw1593step0Labels = mixedMoment B raw1593step1 raw1593step1Labels := by
      have ha : raw1593step1 = raw1593step0 := by apply Matrix.ext; unfold raw1593step1 raw1593step0; decide +kernel
      have hl : raw1593step0Labels = labelEmbedding7 ∘ raw1593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1593step0 raw1593step0Labels raw1593step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

theorem canonical1594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1594 raw1594Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw1594 raw1594Labels = mixedMoment B raw1594step0 raw1594step0Labels := by
      have ha : raw1594step0 = (fun i j => raw1594 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1594step0 raw1594; decide +kernel
      have hl : raw1594step0Labels = raw1594Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1594 raw1594Labels permutation152 permutation4
    _ = mixedMoment B node1861 node1861Labels := by rfl

theorem canonical1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1595 raw1595Labels = mixedMoment B node1889 node1889Labels := by
  calc
    mixedMoment B raw1595 raw1595Labels = mixedMoment B raw1595step0 raw1595step0Labels := by
      have ha : raw1595step0 = (fun i j => raw1595 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1595step0 raw1595; decide +kernel
      have hl : raw1595step0Labels = raw1595Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1595 raw1595Labels permutation153 permutation6
    mixedMoment B raw1595step0 raw1595step0Labels = mixedMoment B raw1595step1 raw1595step1Labels := by
      have ha : raw1595step1 = -raw1595step0 := by apply Matrix.ext; change ∀ i j, raw1595step1 i j = -(raw1595step0 i j); unfold raw1595step1 raw1595step0; decide +kernel
      have hl : raw1595step1Labels = raw1595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1595step1 raw1595step1Labels = mixedMoment B raw1595step2 raw1595step2Labels := by
      have ha : raw1595step2 = raw1595step1 := by apply Matrix.ext; unfold raw1595step2 raw1595step1; decide +kernel
      have hl : raw1595step1Labels = labelEmbedding1 ∘ raw1595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1595step1 raw1595step1Labels raw1595step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1889 node1889Labels := by rfl

theorem canonical1623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1623 raw1623Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw1623 raw1623Labels = mixedMoment B raw1623step0 raw1623step0Labels := by
      have ha : raw1623step0 = (fun i j => raw1623 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1623step0 raw1623; decide +kernel
      have hl : raw1623step0Labels = raw1623Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1623 raw1623Labels permutation152 permutation4
    mixedMoment B raw1623step0 raw1623step0Labels = mixedMoment B raw1623step1 raw1623step1Labels := by
      have ha : raw1623step1 = raw1623step0 := by apply Matrix.ext; unfold raw1623step1 raw1623step0; decide +kernel
      have hl : raw1623step0Labels = labelEmbedding7 ∘ raw1623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1623step0 raw1623step0Labels raw1623step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

theorem canonical1624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1624 raw1624Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw1624 raw1624Labels = mixedMoment B raw1624step0 raw1624step0Labels := by
      have ha : raw1624step0 = (fun i j => raw1624 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1624step0 raw1624; decide +kernel
      have hl : raw1624step0Labels = raw1624Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1624 raw1624Labels permutation152 permutation4
    _ = mixedMoment B node1876 node1876Labels := by rfl

theorem canonical1625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1625 raw1625Labels = mixedMoment B node1906 node1906Labels := by
  calc
    mixedMoment B raw1625 raw1625Labels = mixedMoment B raw1625step0 raw1625step0Labels := by
      have ha : raw1625step0 = (fun i j => raw1625 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1625step0 raw1625; decide +kernel
      have hl : raw1625step0Labels = raw1625Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1625 raw1625Labels permutation158 permutation6
    mixedMoment B raw1625step0 raw1625step0Labels = mixedMoment B raw1625step1 raw1625step1Labels := by
      have ha : raw1625step1 = -raw1625step0 := by apply Matrix.ext; change ∀ i j, raw1625step1 i j = -(raw1625step0 i j); unfold raw1625step1 raw1625step0; decide +kernel
      have hl : raw1625step1Labels = raw1625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1625step1 raw1625step1Labels = mixedMoment B raw1625step2 raw1625step2Labels := by
      have ha : raw1625step2 = raw1625step1 := by apply Matrix.ext; unfold raw1625step2 raw1625step1; decide +kernel
      have hl : raw1625step1Labels = labelEmbedding1 ∘ raw1625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1625step1 raw1625step1Labels raw1625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1906 node1906Labels := by rfl

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

theorem canonical1638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1638 raw1638Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw1638 raw1638Labels = mixedMoment B raw1638step0 raw1638step0Labels := by
      have ha : raw1638step0 = (fun i j => raw1638 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1638step0 raw1638; decide +kernel
      have hl : raw1638step0Labels = raw1638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1638 raw1638Labels permutation32 permutation4
    mixedMoment B raw1638step0 raw1638step0Labels = mixedMoment B raw1638step1 raw1638step1Labels := by
      have ha : raw1638step1 = raw1638step0 := by apply Matrix.ext; unfold raw1638step1 raw1638step0; decide +kernel
      have hl : raw1638step0Labels = labelEmbedding7 ∘ raw1638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1638step0 raw1638step0Labels raw1638step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

theorem canonical1639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1639 raw1639Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw1639 raw1639Labels = mixedMoment B raw1639step0 raw1639step0Labels := by
      have ha : raw1639step0 = (fun i j => raw1639 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1639step0 raw1639; decide +kernel
      have hl : raw1639step0Labels = raw1639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1639 raw1639Labels permutation32 permutation4
    _ = mixedMoment B node1881 node1881Labels := by rfl

theorem canonical1640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1640 raw1640Labels = mixedMoment B node1939 node1939Labels := by
  calc
    mixedMoment B raw1640 raw1640Labels = mixedMoment B raw1640step0 raw1640step0Labels := by
      have ha : raw1640step0 = (fun i j => raw1640 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1640step0 raw1640; decide +kernel
      have hl : raw1640step0Labels = raw1640Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1640 raw1640Labels permutation33 permutation6
    mixedMoment B raw1640step0 raw1640step0Labels = mixedMoment B raw1640step1 raw1640step1Labels := by
      have ha : raw1640step1 = -raw1640step0 := by apply Matrix.ext; change ∀ i j, raw1640step1 i j = -(raw1640step0 i j); unfold raw1640step1 raw1640step0; decide +kernel
      have hl : raw1640step1Labels = raw1640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1640step1 raw1640step1Labels = mixedMoment B raw1640step2 raw1640step2Labels := by
      have ha : raw1640step2 = raw1640step1 := by apply Matrix.ext; unfold raw1640step2 raw1640step1; decide +kernel
      have hl : raw1640step1Labels = labelEmbedding1 ∘ raw1640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1640step1 raw1640step1Labels raw1640step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1939 node1939Labels := by rfl

theorem canonical1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1653 raw1653Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw1653 raw1653Labels = mixedMoment B raw1653step0 raw1653step0Labels := by
      have ha : raw1653step0 = (fun i j => raw1653 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1653step0 raw1653; decide +kernel
      have hl : raw1653step0Labels = raw1653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1653 raw1653Labels permutation152 permutation4
    mixedMoment B raw1653step0 raw1653step0Labels = mixedMoment B raw1653step1 raw1653step1Labels := by
      have ha : raw1653step1 = raw1653step0 := by apply Matrix.ext; unfold raw1653step1 raw1653step0; decide +kernel
      have hl : raw1653step0Labels = labelEmbedding7 ∘ raw1653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1653step0 raw1653step0Labels raw1653step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical1654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1654 raw1654Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw1654 raw1654Labels = mixedMoment B raw1654step0 raw1654step0Labels := by
      have ha : raw1654step0 = (fun i j => raw1654 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1654step0 raw1654; decide +kernel
      have hl : raw1654step0Labels = raw1654Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1654 raw1654Labels permutation152 permutation4
    _ = mixedMoment B node1909 node1909Labels := by rfl

theorem canonical1655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1655 raw1655Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw1655 raw1655Labels = mixedMoment B raw1655step0 raw1655step0Labels := by
      have ha : raw1655step0 = (fun i j => raw1655 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1655step0 raw1655; decide +kernel
      have hl : raw1655step0Labels = raw1655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1655 raw1655Labels permutation159 permutation6
    mixedMoment B raw1655step0 raw1655step0Labels = mixedMoment B raw1655step1 raw1655step1Labels := by
      have ha : raw1655step1 = -raw1655step0 := by apply Matrix.ext; change ∀ i j, raw1655step1 i j = -(raw1655step0 i j); unfold raw1655step1 raw1655step0; decide +kernel
      have hl : raw1655step1Labels = raw1655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1655step1 raw1655step1Labels = mixedMoment B raw1655step2 raw1655step2Labels := by
      have ha : raw1655step2 = raw1655step1 := by apply Matrix.ext; unfold raw1655step2 raw1655step1; decide +kernel
      have hl : raw1655step1Labels = labelEmbedding1 ∘ raw1655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1655step1 raw1655step1Labels raw1655step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1909 node1909Labels := by rfl

theorem canonical1659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1659 raw1659Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw1659 raw1659Labels = mixedMoment B raw1659step0 raw1659step0Labels := by
      have ha : raw1659step0 = (fun i j => raw1659 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1659step0 raw1659; decide +kernel
      have hl : raw1659step0Labels = raw1659Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1659 raw1659Labels permutation32 permutation4
    mixedMoment B raw1659step0 raw1659step0Labels = mixedMoment B raw1659step1 raw1659step1Labels := by
      have ha : raw1659step1 = raw1659step0 := by apply Matrix.ext; unfold raw1659step1 raw1659step0; decide +kernel
      have hl : raw1659step0Labels = labelEmbedding7 ∘ raw1659step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1659step0 raw1659step0Labels raw1659step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical1660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1660 raw1660Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw1660 raw1660Labels = mixedMoment B raw1660step0 raw1660step0Labels := by
      have ha : raw1660step0 = (fun i j => raw1660 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1660step0 raw1660; decide +kernel
      have hl : raw1660step0Labels = raw1660Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1660 raw1660Labels permutation32 permutation4
    _ = mixedMoment B node1915 node1915Labels := by rfl

theorem canonical1661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1661 raw1661Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw1661 raw1661Labels = mixedMoment B raw1661step0 raw1661step0Labels := by
      have ha : raw1661step0 = (fun i j => raw1661 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1661step0 raw1661; decide +kernel
      have hl : raw1661step0Labels = raw1661Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1661 raw1661Labels permutation33 permutation6
    mixedMoment B raw1661step0 raw1661step0Labels = mixedMoment B raw1661step1 raw1661step1Labels := by
      have ha : raw1661step1 = -raw1661step0 := by apply Matrix.ext; change ∀ i j, raw1661step1 i j = -(raw1661step0 i j); unfold raw1661step1 raw1661step0; decide +kernel
      have hl : raw1661step1Labels = raw1661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1661step1 raw1661step1Labels = mixedMoment B raw1661step2 raw1661step2Labels := by
      have ha : raw1661step2 = raw1661step1 := by apply Matrix.ext; unfold raw1661step2 raw1661step1; decide +kernel
      have hl : raw1661step1Labels = labelEmbedding1 ∘ raw1661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1661step1 raw1661step1Labels raw1661step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1946 node1946Labels := by rfl

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

theorem canonical1758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1758 raw1758Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw1758 raw1758Labels = mixedMoment B raw1758step0 raw1758step0Labels := by
      have ha : raw1758step0 = (fun i j => raw1758 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1758step0 raw1758; decide +kernel
      have hl : raw1758step0Labels = raw1758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1758 raw1758Labels permutation32 permutation4
    mixedMoment B raw1758step0 raw1758step0Labels = mixedMoment B raw1758step1 raw1758step1Labels := by
      have ha : raw1758step1 = raw1758step0 := by apply Matrix.ext; unfold raw1758step1 raw1758step0; decide +kernel
      have hl : raw1758step0Labels = labelEmbedding7 ∘ raw1758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1758step0 raw1758step0Labels raw1758step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical1759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1759 raw1759Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw1759 raw1759Labels = mixedMoment B raw1759step0 raw1759step0Labels := by
      have ha : raw1759step0 = (fun i j => raw1759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1759step0 raw1759; decide +kernel
      have hl : raw1759step0Labels = raw1759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1759 raw1759Labels permutation32 permutation4
    _ = mixedMoment B node2048 node2048Labels := by rfl

theorem canonical1760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1760 raw1760Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw1760 raw1760Labels = mixedMoment B raw1760step0 raw1760step0Labels := by
      have ha : raw1760step0 = (fun i j => raw1760 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1760step0 raw1760; decide +kernel
      have hl : raw1760step0Labels = raw1760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1760 raw1760Labels permutation38 permutation6
    mixedMoment B raw1760step0 raw1760step0Labels = mixedMoment B raw1760step1 raw1760step1Labels := by
      have ha : raw1760step1 = -raw1760step0 := by apply Matrix.ext; change ∀ i j, raw1760step1 i j = -(raw1760step0 i j); unfold raw1760step1 raw1760step0; decide +kernel
      have hl : raw1760step1Labels = raw1760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1760step1 raw1760step1Labels = mixedMoment B raw1760step2 raw1760step2Labels := by
      have ha : raw1760step2 = raw1760step1 := by apply Matrix.ext; unfold raw1760step2 raw1760step1; decide +kernel
      have hl : raw1760step1Labels = labelEmbedding1 ∘ raw1760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1760step1 raw1760step1Labels raw1760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2082 node2082Labels := by rfl

theorem canonical1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1767 raw1767Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw1767 raw1767Labels = mixedMoment B raw1767step0 raw1767step0Labels := by
      have ha : raw1767step0 = (fun i j => raw1767 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1767step0 raw1767; decide +kernel
      have hl : raw1767step0Labels = raw1767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1767 raw1767Labels permutation32 permutation4
    mixedMoment B raw1767step0 raw1767step0Labels = mixedMoment B raw1767step1 raw1767step1Labels := by
      have ha : raw1767step1 = raw1767step0 := by apply Matrix.ext; unfold raw1767step1 raw1767step0; decide +kernel
      have hl : raw1767step0Labels = labelEmbedding7 ∘ raw1767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1767step0 raw1767step0Labels raw1767step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical1768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1768 raw1768Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw1768 raw1768Labels = mixedMoment B raw1768step0 raw1768step0Labels := by
      have ha : raw1768step0 = (fun i j => raw1768 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1768step0 raw1768; decide +kernel
      have hl : raw1768step0Labels = raw1768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1768 raw1768Labels permutation32 permutation4
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1769 raw1769Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw1769 raw1769Labels = mixedMoment B raw1769step0 raw1769step0Labels := by
      have ha : raw1769step0 = (fun i j => raw1769 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1769step0 raw1769; decide +kernel
      have hl : raw1769step0Labels = raw1769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1769 raw1769Labels permutation33 permutation6
    mixedMoment B raw1769step0 raw1769step0Labels = mixedMoment B raw1769step1 raw1769step1Labels := by
      have ha : raw1769step1 = -raw1769step0 := by apply Matrix.ext; change ∀ i j, raw1769step1 i j = -(raw1769step0 i j); unfold raw1769step1 raw1769step0; decide +kernel
      have hl : raw1769step1Labels = raw1769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1769step1 raw1769step1Labels = mixedMoment B raw1769step2 raw1769step2Labels := by
      have ha : raw1769step2 = raw1769step1 := by apply Matrix.ext; unfold raw1769step2 raw1769step1; decide +kernel
      have hl : raw1769step1Labels = labelEmbedding1 ∘ raw1769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1769step1 raw1769step1Labels raw1769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

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

theorem canonical2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2025 raw2025Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw2025 raw2025Labels = mixedMoment B raw2025step0 raw2025step0Labels := by
      have ha : raw2025step0 = (fun i j => raw2025 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2025step0 raw2025; decide +kernel
      have hl : raw2025step0Labels = raw2025Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2025 raw2025Labels permutation32 permutation4
    mixedMoment B raw2025step0 raw2025step0Labels = mixedMoment B raw2025step1 raw2025step1Labels := by
      have ha : raw2025step1 = raw2025step0 := by apply Matrix.ext; unfold raw2025step1 raw2025step0; decide +kernel
      have hl : raw2025step0Labels = labelEmbedding7 ∘ raw2025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2025step0 raw2025step0Labels raw2025step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2026 raw2026Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw2026 raw2026Labels = mixedMoment B raw2026step0 raw2026step0Labels := by
      have ha : raw2026step0 = (fun i j => raw2026 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2026step0 raw2026; decide +kernel
      have hl : raw2026step0Labels = raw2026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2026 raw2026Labels permutation32 permutation4
    _ = mixedMoment B node2400 node2400Labels := by rfl

theorem canonical2027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2027 raw2027Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw2027 raw2027Labels = mixedMoment B raw2027step0 raw2027step0Labels := by
      have ha : raw2027step0 = (fun i j => raw2027 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2027step0 raw2027; decide +kernel
      have hl : raw2027step0Labels = raw2027Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2027 raw2027Labels permutation32 permutation6
    mixedMoment B raw2027step0 raw2027step0Labels = mixedMoment B raw2027step1 raw2027step1Labels := by
      have ha : raw2027step1 = -raw2027step0 := by apply Matrix.ext; change ∀ i j, raw2027step1 i j = -(raw2027step0 i j); unfold raw2027step1 raw2027step0; decide +kernel
      have hl : raw2027step1Labels = raw2027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2027step1 raw2027step1Labels = mixedMoment B raw2027step2 raw2027step2Labels := by
      have ha : raw2027step2 = raw2027step1 := by apply Matrix.ext; unfold raw2027step2 raw2027step1; decide +kernel
      have hl : raw2027step1Labels = labelEmbedding1 ∘ raw2027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2027step1 raw2027step1Labels raw2027step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3344 node3344Labels := by rfl

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

theorem canonical2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2082 raw2082Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw2082 raw2082Labels = mixedMoment B raw2082step0 raw2082step0Labels := by
      have ha : raw2082step0 = (fun i j => raw2082 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2082step0 raw2082; decide +kernel
      have hl : raw2082step0Labels = raw2082Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2082 raw2082Labels permutation152 permutation4
    mixedMoment B raw2082step0 raw2082step0Labels = mixedMoment B raw2082step1 raw2082step1Labels := by
      have ha : raw2082step1 = raw2082step0 := by apply Matrix.ext; unfold raw2082step1 raw2082step0; decide +kernel
      have hl : raw2082step0Labels = labelEmbedding7 ∘ raw2082step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2082step0 raw2082step0Labels raw2082step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

theorem canonical2083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2083 raw2083Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw2083 raw2083Labels = mixedMoment B raw2083step0 raw2083step0Labels := by
      have ha : raw2083step0 = (fun i j => raw2083 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2083step0 raw2083; decide +kernel
      have hl : raw2083step0Labels = raw2083Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2083 raw2083Labels permutation152 permutation4
    _ = mixedMoment B node2459 node2459Labels := by rfl

theorem canonical2084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2084 raw2084Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw2084 raw2084Labels = mixedMoment B raw2084step0 raw2084step0Labels := by
      have ha : raw2084step0 = (fun i j => raw2084 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2084step0 raw2084; decide +kernel
      have hl : raw2084step0Labels = raw2084Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2084 raw2084Labels permutation152 permutation6
    mixedMoment B raw2084step0 raw2084step0Labels = mixedMoment B raw2084step1 raw2084step1Labels := by
      have ha : raw2084step1 = -raw2084step0 := by apply Matrix.ext; change ∀ i j, raw2084step1 i j = -(raw2084step0 i j); unfold raw2084step1 raw2084step0; decide +kernel
      have hl : raw2084step1Labels = raw2084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2084step1 raw2084step1Labels = mixedMoment B raw2084step2 raw2084step2Labels := by
      have ha : raw2084step2 = raw2084step1 := by apply Matrix.ext; unfold raw2084step2 raw2084step1; decide +kernel
      have hl : raw2084step1Labels = labelEmbedding1 ∘ raw2084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2084step1 raw2084step1Labels raw2084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3429 node3429Labels := by rfl

theorem canonical2118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2118 raw2118Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw2118 raw2118Labels = mixedMoment B raw2118step0 raw2118step0Labels := by
      have ha : raw2118step0 = (fun i j => raw2118 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2118step0 raw2118; decide +kernel
      have hl : raw2118step0Labels = raw2118Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2118 raw2118Labels permutation32 permutation4
    mixedMoment B raw2118step0 raw2118step0Labels = mixedMoment B raw2118step1 raw2118step1Labels := by
      have ha : raw2118step1 = raw2118step0 := by apply Matrix.ext; unfold raw2118step1 raw2118step0; decide +kernel
      have hl : raw2118step0Labels = labelEmbedding7 ∘ raw2118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2118step0 raw2118step0Labels raw2118step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

theorem canonical2119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2119 raw2119Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw2119 raw2119Labels = mixedMoment B raw2119step0 raw2119step0Labels := by
      have ha : raw2119step0 = (fun i j => raw2119 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2119step0 raw2119; decide +kernel
      have hl : raw2119step0Labels = raw2119Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2119 raw2119Labels permutation32 permutation4
    _ = mixedMoment B node2505 node2505Labels := by rfl

theorem canonical2120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2120 raw2120Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw2120 raw2120Labels = mixedMoment B raw2120step0 raw2120step0Labels := by
      have ha : raw2120step0 = (fun i j => raw2120 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2120step0 raw2120; decide +kernel
      have hl : raw2120step0Labels = raw2120Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2120 raw2120Labels permutation32 permutation6
    mixedMoment B raw2120step0 raw2120step0Labels = mixedMoment B raw2120step1 raw2120step1Labels := by
      have ha : raw2120step1 = -raw2120step0 := by apply Matrix.ext; change ∀ i j, raw2120step1 i j = -(raw2120step0 i j); unfold raw2120step1 raw2120step0; decide +kernel
      have hl : raw2120step1Labels = raw2120step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2120step1 raw2120step1Labels = mixedMoment B raw2120step2 raw2120step2Labels := by
      have ha : raw2120step2 = raw2120step1 := by apply Matrix.ext; unfold raw2120step2 raw2120step1; decide +kernel
      have hl : raw2120step1Labels = labelEmbedding1 ∘ raw2120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2120step1 raw2120step1Labels raw2120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3448 node3448Labels := by rfl

theorem canonical2127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2127 raw2127Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw2127 raw2127Labels = mixedMoment B raw2127step0 raw2127step0Labels := by
      have ha : raw2127step0 = (fun i j => raw2127 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2127step0 raw2127; decide +kernel
      have hl : raw2127step0Labels = raw2127Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2127 raw2127Labels permutation32 permutation4
    mixedMoment B raw2127step0 raw2127step0Labels = mixedMoment B raw2127step1 raw2127step1Labels := by
      have ha : raw2127step1 = raw2127step0 := by apply Matrix.ext; unfold raw2127step1 raw2127step0; decide +kernel
      have hl : raw2127step0Labels = labelEmbedding7 ∘ raw2127step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2127step0 raw2127step0Labels raw2127step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2128 raw2128Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw2128 raw2128Labels = mixedMoment B raw2128step0 raw2128step0Labels := by
      have ha : raw2128step0 = (fun i j => raw2128 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2128step0 raw2128; decide +kernel
      have hl : raw2128step0Labels = raw2128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2128 raw2128Labels permutation32 permutation4
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2129 raw2129Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw2129 raw2129Labels = mixedMoment B raw2129step0 raw2129step0Labels := by
      have ha : raw2129step0 = (fun i j => raw2129 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2129step0 raw2129; decide +kernel
      have hl : raw2129step0Labels = raw2129Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2129 raw2129Labels permutation33 permutation6
    mixedMoment B raw2129step0 raw2129step0Labels = mixedMoment B raw2129step1 raw2129step1Labels := by
      have ha : raw2129step1 = -raw2129step0 := by apply Matrix.ext; change ∀ i j, raw2129step1 i j = -(raw2129step0 i j); unfold raw2129step1 raw2129step0; decide +kernel
      have hl : raw2129step1Labels = raw2129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2129step1 raw2129step1Labels = mixedMoment B raw2129step2 raw2129step2Labels := by
      have ha : raw2129step2 = raw2129step1 := by apply Matrix.ext; unfold raw2129step2 raw2129step1; decide +kernel
      have hl : raw2129step1Labels = labelEmbedding1 ∘ raw2129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2129step1 raw2129step1Labels raw2129step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

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

theorem canonical31807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31807 raw31807Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw31807 raw31807Labels = mixedMoment B raw31807step0 raw31807step0Labels := by
      have hz : ∀ j, raw31807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31807step0 = (fun i j => raw31807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31807step0 raw31807; decide +kernel
      have hl : raw31807step0Labels = raw31807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31807 raw31807Labels permutation434 hz
    mixedMoment B raw31807step0 raw31807step0Labels = mixedMoment B raw31807step1 raw31807step1Labels := by
      have ha : raw31807step1 = (fun i j => raw31807step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31807step1 raw31807step0; decide +kernel
      have hl : raw31807step1Labels = raw31807step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31807step0 raw31807step0Labels permutation33 permutation7
    mixedMoment B raw31807step1 raw31807step1Labels = mixedMoment B raw31807step2 raw31807step2Labels := by
      have ha : raw31807step2 = -raw31807step1 := by apply Matrix.ext; change ∀ i j, raw31807step2 i j = -(raw31807step1 i j); unfold raw31807step2 raw31807step1; decide +kernel
      have hl : raw31807step2Labels = raw31807step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31807step2 raw31807step2Labels = mixedMoment B raw31807step3 raw31807step3Labels := by
      have ha : raw31807step3 = raw31807step2 := by apply Matrix.ext; unfold raw31807step3 raw31807step2; decide +kernel
      have hl : raw31807step2Labels = labelEmbedding10 ∘ raw31807step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31807step2 raw31807step2Labels raw31807step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical31808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31808 raw31808Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw31808 raw31808Labels = mixedMoment B raw31808step0 raw31808step0Labels := by
      have hz : ∀ j, raw31808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31808step0 = (fun i j => raw31808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31808step0 raw31808; decide +kernel
      have hl : raw31808step0Labels = raw31808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31808 raw31808Labels permutation434 hz
    mixedMoment B raw31808step0 raw31808step0Labels = mixedMoment B raw31808step1 raw31808step1Labels := by
      have ha : raw31808step1 = (fun i j => raw31808step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31808step1 raw31808step0; decide +kernel
      have hl : raw31808step1Labels = raw31808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31808step0 raw31808step0Labels permutation33 permutation7
    mixedMoment B raw31808step1 raw31808step1Labels = mixedMoment B raw31808step2 raw31808step2Labels := by
      have ha : raw31808step2 = -raw31808step1 := by apply Matrix.ext; change ∀ i j, raw31808step2 i j = -(raw31808step1 i j); unfold raw31808step2 raw31808step1; decide +kernel
      have hl : raw31808step2Labels = raw31808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31808step2 raw31808step2Labels = mixedMoment B raw31808step3 raw31808step3Labels := by
      have ha : raw31808step3 = raw31808step2 := by apply Matrix.ext; unfold raw31808step3 raw31808step2; decide +kernel
      have hl : raw31808step2Labels = labelEmbedding10 ∘ raw31808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31808step2 raw31808step2Labels raw31808step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

theorem canonical31809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31809 raw31809Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw31809 raw31809Labels = mixedMoment B raw31809step0 raw31809step0Labels := by
      have ha : raw31809step0 = (fun i j => raw31809 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31809step0 raw31809; decide +kernel
      have hl : raw31809step0Labels = raw31809Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31809 raw31809Labels permutation159 permutation7
    mixedMoment B raw31809step0 raw31809step0Labels = mixedMoment B raw31809step1 raw31809step1Labels := by
      have ha : raw31809step1 = -raw31809step0 := by apply Matrix.ext; change ∀ i j, raw31809step1 i j = -(raw31809step0 i j); unfold raw31809step1 raw31809step0; decide +kernel
      have hl : raw31809step1Labels = raw31809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31809step1 raw31809step1Labels = mixedMoment B raw31809step2 raw31809step2Labels := by
      have ha : raw31809step2 = raw31809step1 := by apply Matrix.ext; unfold raw31809step2 raw31809step1; decide +kernel
      have hl : raw31809step1Labels = labelEmbedding10 ∘ raw31809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31809step1 raw31809step1Labels raw31809step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

theorem canonical31810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31810 raw31810Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw31810 raw31810Labels = mixedMoment B raw31810step0 raw31810step0Labels := by
      have hz : ∀ j, raw31810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31810step0 = (fun i j => raw31810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31810step0 raw31810; decide +kernel
      have hl : raw31810step0Labels = raw31810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31810 raw31810Labels permutation434 hz
    mixedMoment B raw31810step0 raw31810step0Labels = mixedMoment B raw31810step1 raw31810step1Labels := by
      have ha : raw31810step1 = (fun i j => raw31810step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31810step1 raw31810step0; decide +kernel
      have hl : raw31810step1Labels = raw31810step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31810step0 raw31810step0Labels permutation33 permutation7
    mixedMoment B raw31810step1 raw31810step1Labels = mixedMoment B raw31810step2 raw31810step2Labels := by
      have ha : raw31810step2 = -raw31810step1 := by apply Matrix.ext; change ∀ i j, raw31810step2 i j = -(raw31810step1 i j); unfold raw31810step2 raw31810step1; decide +kernel
      have hl : raw31810step2Labels = raw31810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31810step2 raw31810step2Labels = mixedMoment B raw31810step3 raw31810step3Labels := by
      have ha : raw31810step3 = raw31810step2 := by apply Matrix.ext; unfold raw31810step3 raw31810step2; decide +kernel
      have hl : raw31810step2Labels = labelEmbedding10 ∘ raw31810step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31810step2 raw31810step2Labels raw31810step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical31811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31811 raw31811Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw31811 raw31811Labels = mixedMoment B raw31811step0 raw31811step0Labels := by
      have hz : ∀ j, raw31811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31811step0 = (fun i j => raw31811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31811step0 raw31811; decide +kernel
      have hl : raw31811step0Labels = raw31811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31811 raw31811Labels permutation434 hz
    mixedMoment B raw31811step0 raw31811step0Labels = mixedMoment B raw31811step1 raw31811step1Labels := by
      have ha : raw31811step1 = (fun i j => raw31811step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31811step1 raw31811step0; decide +kernel
      have hl : raw31811step1Labels = raw31811step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31811step0 raw31811step0Labels permutation33 permutation7
    mixedMoment B raw31811step1 raw31811step1Labels = mixedMoment B raw31811step2 raw31811step2Labels := by
      have ha : raw31811step2 = -raw31811step1 := by apply Matrix.ext; change ∀ i j, raw31811step2 i j = -(raw31811step1 i j); unfold raw31811step2 raw31811step1; decide +kernel
      have hl : raw31811step2Labels = raw31811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31811step2 raw31811step2Labels = mixedMoment B raw31811step3 raw31811step3Labels := by
      have ha : raw31811step3 = raw31811step2 := by apply Matrix.ext; unfold raw31811step3 raw31811step2; decide +kernel
      have hl : raw31811step2Labels = labelEmbedding10 ∘ raw31811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31811step2 raw31811step2Labels raw31811step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical31812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31812 raw31812Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw31812 raw31812Labels = mixedMoment B raw31812step0 raw31812step0Labels := by
      have hz : ∀ j, raw31812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31812step0 = (fun i j => raw31812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31812step0 raw31812; decide +kernel
      have hl : raw31812step0Labels = raw31812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31812 raw31812Labels permutation434 hz
    mixedMoment B raw31812step0 raw31812step0Labels = mixedMoment B raw31812step1 raw31812step1Labels := by
      have ha : raw31812step1 = (fun i j => raw31812step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31812step1 raw31812step0; decide +kernel
      have hl : raw31812step1Labels = raw31812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31812step0 raw31812step0Labels permutation33 permutation2
    _ = mixedMoment B node4404 node4404Labels := by rfl

theorem canonical31813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31813 raw31813Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31813 raw31813Labels = mixedMoment B raw31813step0 raw31813step0Labels := by
      have hz : ∀ j, raw31813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31813step0 = (fun i j => raw31813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31813step0 raw31813; decide +kernel
      have hl : raw31813step0Labels = raw31813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31813 raw31813Labels permutation434 hz
    mixedMoment B raw31813step0 raw31813step0Labels = mixedMoment B raw31813step1 raw31813step1Labels := by
      have ha : raw31813step1 = (fun i j => raw31813step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31813step1 raw31813step0; decide +kernel
      have hl : raw31813step1Labels = raw31813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31813step0 raw31813step0Labels permutation33 permutation7
    mixedMoment B raw31813step1 raw31813step1Labels = mixedMoment B raw31813step2 raw31813step2Labels := by
      have ha : raw31813step2 = -raw31813step1 := by apply Matrix.ext; change ∀ i j, raw31813step2 i j = -(raw31813step1 i j); unfold raw31813step2 raw31813step1; decide +kernel
      have hl : raw31813step2Labels = raw31813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31813step2 raw31813step2Labels = mixedMoment B raw31813step3 raw31813step3Labels := by
      have ha : raw31813step3 = raw31813step2 := by apply Matrix.ext; unfold raw31813step3 raw31813step2; decide +kernel
      have hl : raw31813step2Labels = labelEmbedding10 ∘ raw31813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31813step2 raw31813step2Labels raw31813step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical31814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31814 raw31814Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw31814 raw31814Labels = mixedMoment B raw31814step0 raw31814step0Labels := by
      have ha : raw31814step0 = (fun i j => raw31814 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31814step0 raw31814; decide +kernel
      have hl : raw31814step0Labels = raw31814Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31814 raw31814Labels permutation201 permutation2
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical31815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31815 raw31815Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw31815 raw31815Labels = mixedMoment B raw31815step0 raw31815step0Labels := by
      have hz : ∀ j, raw31815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31815step0 = (fun i j => raw31815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31815step0 raw31815; decide +kernel
      have hl : raw31815step0Labels = raw31815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31815 raw31815Labels permutation434 hz
    mixedMoment B raw31815step0 raw31815step0Labels = mixedMoment B raw31815step1 raw31815step1Labels := by
      have ha : raw31815step1 = (fun i j => raw31815step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31815step1 raw31815step0; decide +kernel
      have hl : raw31815step1Labels = raw31815step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31815step0 raw31815step0Labels permutation33 permutation7
    mixedMoment B raw31815step1 raw31815step1Labels = mixedMoment B raw31815step2 raw31815step2Labels := by
      have ha : raw31815step2 = -raw31815step1 := by apply Matrix.ext; change ∀ i j, raw31815step2 i j = -(raw31815step1 i j); unfold raw31815step2 raw31815step1; decide +kernel
      have hl : raw31815step2Labels = raw31815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31815step2 raw31815step2Labels = mixedMoment B raw31815step3 raw31815step3Labels := by
      have ha : raw31815step3 = raw31815step2 := by apply Matrix.ext; unfold raw31815step3 raw31815step2; decide +kernel
      have hl : raw31815step2Labels = labelEmbedding10 ∘ raw31815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31815step2 raw31815step2Labels raw31815step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical31816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31816 raw31816Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw31816 raw31816Labels = mixedMoment B raw31816step0 raw31816step0Labels := by
      have hz : ∀ j, raw31816 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31816step0 = (fun i j => raw31816 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31816step0 raw31816; decide +kernel
      have hl : raw31816step0Labels = raw31816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31816 raw31816Labels permutation434 hz
    mixedMoment B raw31816step0 raw31816step0Labels = mixedMoment B raw31816step1 raw31816step1Labels := by
      have ha : raw31816step1 = (fun i j => raw31816step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31816step1 raw31816step0; decide +kernel
      have hl : raw31816step1Labels = raw31816step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31816step0 raw31816step0Labels permutation33 permutation7
    mixedMoment B raw31816step1 raw31816step1Labels = mixedMoment B raw31816step2 raw31816step2Labels := by
      have ha : raw31816step2 = -raw31816step1 := by apply Matrix.ext; change ∀ i j, raw31816step2 i j = -(raw31816step1 i j); unfold raw31816step2 raw31816step1; decide +kernel
      have hl : raw31816step2Labels = raw31816step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31816step2 raw31816step2Labels = mixedMoment B raw31816step3 raw31816step3Labels := by
      have ha : raw31816step3 = raw31816step2 := by apply Matrix.ext; unfold raw31816step3 raw31816step2; decide +kernel
      have hl : raw31816step2Labels = labelEmbedding10 ∘ raw31816step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31816step2 raw31816step2Labels raw31816step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical31817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31817 raw31817Labels = mixedMoment B node4311 node4311Labels := by
  calc
    mixedMoment B raw31817 raw31817Labels = mixedMoment B raw31817step0 raw31817step0Labels := by
      have hz : ∀ j, raw31817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31817step0 = (fun i j => raw31817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31817step0 raw31817; decide +kernel
      have hl : raw31817step0Labels = raw31817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31817 raw31817Labels permutation434 hz
    mixedMoment B raw31817step0 raw31817step0Labels = mixedMoment B raw31817step1 raw31817step1Labels := by
      have ha : raw31817step1 = (fun i j => raw31817step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31817step1 raw31817step0; decide +kernel
      have hl : raw31817step1Labels = raw31817step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31817step0 raw31817step0Labels permutation33 permutation2
    _ = mixedMoment B node4311 node4311Labels := by rfl

theorem canonical31818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31818 raw31818Labels = mixedMoment B node4652 node4652Labels := by
  calc
    mixedMoment B raw31818 raw31818Labels = mixedMoment B raw31818step0 raw31818step0Labels := by
      have hz : ∀ j, raw31818 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31818step0 = (fun i j => raw31818 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31818step0 raw31818; decide +kernel
      have hl : raw31818step0Labels = raw31818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31818 raw31818Labels permutation434 hz
    mixedMoment B raw31818step0 raw31818step0Labels = mixedMoment B raw31818step1 raw31818step1Labels := by
      have ha : raw31818step1 = (fun i j => raw31818step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31818step1 raw31818step0; decide +kernel
      have hl : raw31818step1Labels = raw31818step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31818step0 raw31818step0Labels permutation33 permutation2
    _ = mixedMoment B node4652 node4652Labels := by rfl

theorem canonical31819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31819 raw31819Labels = mixedMoment B node4715 node4715Labels := by
  calc
    mixedMoment B raw31819 raw31819Labels = mixedMoment B raw31819step0 raw31819step0Labels := by
      have ha : raw31819step0 = (fun i j => raw31819 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31819step0 raw31819; decide +kernel
      have hl : raw31819step0Labels = raw31819Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31819 raw31819Labels permutation159 permutation2
    _ = mixedMoment B node4715 node4715Labels := by rfl

theorem canonical31820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31820 raw31820Labels = mixedMoment B node4752 node4752Labels := by
  calc
    mixedMoment B raw31820 raw31820Labels = mixedMoment B raw31820step0 raw31820step0Labels := by
      have hz : ∀ j, raw31820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31820step0 = (fun i j => raw31820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31820step0 raw31820; decide +kernel
      have hl : raw31820step0Labels = raw31820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31820 raw31820Labels permutation434 hz
    _ = mixedMoment B node4752 node4752Labels := by rfl

theorem canonical31821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31821 raw31821Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31821 raw31821Labels = mixedMoment B raw31821step0 raw31821step0Labels := by
      have hz : ∀ j, raw31821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31821step0 = (fun i j => raw31821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31821step0 raw31821; decide +kernel
      have hl : raw31821step0Labels = raw31821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31821 raw31821Labels permutation434 hz
    mixedMoment B raw31821step0 raw31821step0Labels = mixedMoment B raw31821step1 raw31821step1Labels := by
      have hz : ∀ i, raw31821step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw31821step1 = (fun i j => raw31821step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw31821step1 raw31821step0; decide +kernel
      have hl : raw31821step1Labels = (fun j => raw31821step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31821step0 raw31821step0Labels permutation4 hz
    mixedMoment B raw31821step1 raw31821step1Labels = mixedMoment B raw31821step2 raw31821step2Labels := by
      have ha : raw31821step2 = (fun i j => raw31821step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31821step2 raw31821step1; decide +kernel
      have hl : raw31821step2Labels = raw31821step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31821step1 raw31821step1Labels permutation33 permutation0
    mixedMoment B raw31821step2 raw31821step2Labels = mixedMoment B raw31821step3 raw31821step3Labels := by
      have ha : raw31821step3 = raw31821step2 := by apply Matrix.ext; unfold raw31821step3 raw31821step2; decide +kernel
      have hl : raw31821step2Labels = labelEmbedding2 ∘ raw31821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31821step2 raw31821step2Labels raw31821step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical31822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31822 raw31822Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw31822 raw31822Labels = mixedMoment B raw31822step0 raw31822step0Labels := by
      have ha : raw31822step0 = (fun i j => raw31822 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31822step0 raw31822; decide +kernel
      have hl : raw31822step0Labels = raw31822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31822 raw31822Labels permutation153 permutation2
    _ = mixedMoment B node4288 node4288Labels := by rfl

theorem canonical31823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31823 raw31823Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw31823 raw31823Labels = mixedMoment B raw31823step0 raw31823step0Labels := by
      have ha : raw31823step0 = (fun i j => raw31823 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31823step0 raw31823; decide +kernel
      have hl : raw31823step0Labels = raw31823Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31823 raw31823Labels permutation153 permutation2
    _ = mixedMoment B node4632 node4632Labels := by rfl

theorem canonical31824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31824 raw31824Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw31824 raw31824Labels = mixedMoment B raw31824step0 raw31824step0Labels := by
      have ha : raw31824step0 = (fun i j => raw31824 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31824step0 raw31824; decide +kernel
      have hl : raw31824step0Labels = raw31824Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31824 raw31824Labels permutation153 permutation2
    _ = mixedMoment B node4722 node4722Labels := by rfl

theorem canonical31825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31825 raw31825Labels = mixedMoment B node4737 node4737Labels := by
  calc
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical31826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31826 raw31826Labels = mixedMoment B node4736 node4736Labels := by
  calc
    mixedMoment B raw31826 raw31826Labels = mixedMoment B raw31826step0 raw31826step0Labels := by
      have ha : raw31826step0 = (fun i j => raw31826 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31826step0 raw31826; decide +kernel
      have hl : raw31826step0Labels = raw31826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31826 raw31826Labels permutation153 permutation2
    _ = mixedMoment B node4736 node4736Labels := by rfl

theorem canonical31827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31827 raw31827Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw31827 raw31827Labels = mixedMoment B raw31827step0 raw31827step0Labels := by
      have hz : ∀ j, raw31827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31827step0 = (fun i j => raw31827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31827step0 raw31827; decide +kernel
      have hl : raw31827step0Labels = raw31827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31827 raw31827Labels permutation434 hz
    mixedMoment B raw31827step0 raw31827step0Labels = mixedMoment B raw31827step1 raw31827step1Labels := by
      have ha : raw31827step1 = (fun i j => raw31827step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31827step1 raw31827step0; decide +kernel
      have hl : raw31827step1Labels = raw31827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31827step0 raw31827step0Labels permutation33 permutation2
    _ = mixedMoment B node4295 node4295Labels := by rfl

theorem canonical31828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31828 raw31828Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw31828 raw31828Labels = mixedMoment B raw31828step0 raw31828step0Labels := by
      have hz : ∀ j, raw31828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31828step0 = (fun i j => raw31828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31828step0 raw31828; decide +kernel
      have hl : raw31828step0Labels = raw31828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31828 raw31828Labels permutation434 hz
    mixedMoment B raw31828step0 raw31828step0Labels = mixedMoment B raw31828step1 raw31828step1Labels := by
      have ha : raw31828step1 = (fun i j => raw31828step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31828step1 raw31828step0; decide +kernel
      have hl : raw31828step1Labels = raw31828step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31828step0 raw31828step0Labels permutation33 permutation2
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical31829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31829 raw31829Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw31829 raw31829Labels = mixedMoment B raw31829step0 raw31829step0Labels := by
      have hz : ∀ j, raw31829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31829step0 = (fun i j => raw31829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31829step0 raw31829; decide +kernel
      have hl : raw31829step0Labels = raw31829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31829 raw31829Labels permutation434 hz
    mixedMoment B raw31829step0 raw31829step0Labels = mixedMoment B raw31829step1 raw31829step1Labels := by
      have ha : raw31829step1 = (fun i j => raw31829step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31829step1 raw31829step0; decide +kernel
      have hl : raw31829step1Labels = raw31829step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31829step0 raw31829step0Labels permutation33 permutation2
    _ = mixedMoment B node4726 node4726Labels := by rfl

theorem canonical31830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31830 raw31830Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw31830 raw31830Labels = mixedMoment B raw31830step0 raw31830step0Labels := by
      have ha : raw31830step0 = (fun i j => raw31830 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31830step0 raw31830; decide +kernel
      have hl : raw31830step0Labels = raw31830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31830 raw31830Labels permutation159 permutation2
    _ = mixedMoment B node4706 node4706Labels := by rfl

theorem canonical31831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31831 raw31831Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw31831 raw31831Labels = mixedMoment B raw31831step0 raw31831step0Labels := by
      have hz : ∀ j, raw31831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31831step0 = (fun i j => raw31831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31831step0 raw31831; decide +kernel
      have hl : raw31831step0Labels = raw31831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31831 raw31831Labels permutation434 hz
    mixedMoment B raw31831step0 raw31831step0Labels = mixedMoment B raw31831step1 raw31831step1Labels := by
      have ha : raw31831step1 = (fun i j => raw31831step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31831step1 raw31831step0; decide +kernel
      have hl : raw31831step1Labels = raw31831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31831step0 raw31831step0Labels permutation33 permutation2
    _ = mixedMoment B node4741 node4741Labels := by rfl

theorem canonical31832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31832 raw31832Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw31832 raw31832Labels = mixedMoment B raw31832step0 raw31832step0Labels := by
      have hz : ∀ j, raw31832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31832step0 = (fun i j => raw31832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31832step0 raw31832; decide +kernel
      have hl : raw31832step0Labels = raw31832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31832 raw31832Labels permutation434 hz
    _ = mixedMoment B node4296 node4296Labels := by rfl

theorem canonical31833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31833 raw31833Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw31833 raw31833Labels = mixedMoment B raw31833step0 raw31833step0Labels := by
      have hz : ∀ j, raw31833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31833step0 = (fun i j => raw31833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31833step0 raw31833; decide +kernel
      have hl : raw31833step0Labels = raw31833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31833 raw31833Labels permutation434 hz
    _ = mixedMoment B node4638 node4638Labels := by rfl

theorem canonical31834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31834 raw31834Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw31834 raw31834Labels = mixedMoment B raw31834step0 raw31834step0Labels := by
      have hz : ∀ j, raw31834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31834step0 = (fun i j => raw31834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31834step0 raw31834; decide +kernel
      have hl : raw31834step0Labels = raw31834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31834 raw31834Labels permutation434 hz
    _ = mixedMoment B node4727 node4727Labels := by rfl

theorem canonical31835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31835 raw31835Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw31835 raw31835Labels = mixedMoment B raw31835step0 raw31835step0Labels := by
      have ha : raw31835step0 = (fun i j => raw31835 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31835step0 raw31835; decide +kernel
      have hl : raw31835step0Labels = raw31835Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31835 raw31835Labels permutation158 permutation2
    _ = mixedMoment B node4707 node4707Labels := by rfl

theorem canonical31836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31836 raw31836Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw31836 raw31836Labels = mixedMoment B raw31836step0 raw31836step0Labels := by
      have hz : ∀ j, raw31836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31836step0 = (fun i j => raw31836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31836step0 raw31836; decide +kernel
      have hl : raw31836step0Labels = raw31836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31836 raw31836Labels permutation434 hz
    _ = mixedMoment B node4742 node4742Labels := by rfl

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

theorem canonical1026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1026 raw1026Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw1026 raw1026Labels = mixedMoment B raw1026step0 raw1026step0Labels := by
      have ha : raw1026step0 = (fun i j => raw1026 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1026step0 raw1026; decide +kernel
      have hl : raw1026step0Labels = raw1026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1026 raw1026Labels permutation152 permutation4
    mixedMoment B raw1026step0 raw1026step0Labels = mixedMoment B raw1026step1 raw1026step1Labels := by
      have ha : raw1026step1 = raw1026step0 := by apply Matrix.ext; unfold raw1026step1 raw1026step0; decide +kernel
      have hl : raw1026step0Labels = labelEmbedding7 ∘ raw1026step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1026step0 raw1026step0Labels raw1026step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

theorem canonical1027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1027 raw1027Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw1027 raw1027Labels = mixedMoment B raw1027step0 raw1027step0Labels := by
      have ha : raw1027step0 = (fun i j => raw1027 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1027step0 raw1027; decide +kernel
      have hl : raw1027step0Labels = raw1027Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1027 raw1027Labels permutation152 permutation4
    _ = mixedMoment B node866 node866Labels := by rfl

theorem canonical1028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1028 raw1028Labels = mixedMoment B node1554 node1554Labels := by
  calc
    mixedMoment B raw1028 raw1028Labels = mixedMoment B raw1028step0 raw1028step0Labels := by
      have ha : raw1028step0 = (fun i j => raw1028 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1028step0 raw1028; decide +kernel
      have hl : raw1028step0Labels = raw1028Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1028 raw1028Labels permutation158 permutation6
    mixedMoment B raw1028step0 raw1028step0Labels = mixedMoment B raw1028step1 raw1028step1Labels := by
      have ha : raw1028step1 = -raw1028step0 := by apply Matrix.ext; change ∀ i j, raw1028step1 i j = -(raw1028step0 i j); unfold raw1028step1 raw1028step0; decide +kernel
      have hl : raw1028step1Labels = raw1028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1028step1 raw1028step1Labels = mixedMoment B raw1028step2 raw1028step2Labels := by
      have ha : raw1028step2 = raw1028step1 := by apply Matrix.ext; unfold raw1028step2 raw1028step1; decide +kernel
      have hl : raw1028step1Labels = labelEmbedding1 ∘ raw1028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1028step1 raw1028step1Labels raw1028step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1554 node1554Labels := by rfl

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

theorem canonical1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1050 raw1050Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw1050 raw1050Labels = mixedMoment B raw1050step0 raw1050step0Labels := by
      have ha : raw1050step0 = (fun i j => raw1050 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1050step0 raw1050; decide +kernel
      have hl : raw1050step0Labels = raw1050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1050 raw1050Labels permutation32 permutation4
    mixedMoment B raw1050step0 raw1050step0Labels = mixedMoment B raw1050step1 raw1050step1Labels := by
      have ha : raw1050step1 = raw1050step0 := by apply Matrix.ext; unfold raw1050step1 raw1050step0; decide +kernel
      have hl : raw1050step0Labels = labelEmbedding7 ∘ raw1050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1050step0 raw1050step0Labels raw1050step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

theorem canonical1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1051 raw1051Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw1051 raw1051Labels = mixedMoment B raw1051step0 raw1051step0Labels := by
      have ha : raw1051step0 = (fun i j => raw1051 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1051step0 raw1051; decide +kernel
      have hl : raw1051step0Labels = raw1051Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1051 raw1051Labels permutation32 permutation4
    _ = mixedMoment B node874 node874Labels := by rfl

theorem canonical1052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1052 raw1052Labels = mixedMoment B node1570 node1570Labels := by
  calc
    mixedMoment B raw1052 raw1052Labels = mixedMoment B raw1052step0 raw1052step0Labels := by
      have ha : raw1052step0 = (fun i j => raw1052 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1052step0 raw1052; decide +kernel
      have hl : raw1052step0Labels = raw1052Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1052 raw1052Labels permutation33 permutation6
    mixedMoment B raw1052step0 raw1052step0Labels = mixedMoment B raw1052step1 raw1052step1Labels := by
      have ha : raw1052step1 = -raw1052step0 := by apply Matrix.ext; change ∀ i j, raw1052step1 i j = -(raw1052step0 i j); unfold raw1052step1 raw1052step0; decide +kernel
      have hl : raw1052step1Labels = raw1052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1052step1 raw1052step1Labels = mixedMoment B raw1052step2 raw1052step2Labels := by
      have ha : raw1052step2 = raw1052step1 := by apply Matrix.ext; unfold raw1052step2 raw1052step1; decide +kernel
      have hl : raw1052step1Labels = labelEmbedding1 ∘ raw1052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1052step1 raw1052step1Labels raw1052step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1570 node1570Labels := by rfl

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

theorem canonical1218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1218 raw1218Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw1218 raw1218Labels = mixedMoment B raw1218step0 raw1218step0Labels := by
      have ha : raw1218step0 = (fun i j => raw1218 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1218step0 raw1218; decide +kernel
      have hl : raw1218step0Labels = raw1218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1218 raw1218Labels permutation32 permutation4
    mixedMoment B raw1218step0 raw1218step0Labels = mixedMoment B raw1218step1 raw1218step1Labels := by
      have ha : raw1218step1 = raw1218step0 := by apply Matrix.ext; unfold raw1218step1 raw1218step0; decide +kernel
      have hl : raw1218step0Labels = labelEmbedding7 ∘ raw1218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1218step0 raw1218step0Labels raw1218step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

theorem canonical1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1219 raw1219Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw1219 raw1219Labels = mixedMoment B raw1219step0 raw1219step0Labels := by
      have ha : raw1219step0 = (fun i j => raw1219 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1219step0 raw1219; decide +kernel
      have hl : raw1219step0Labels = raw1219Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1219 raw1219Labels permutation32 permutation4
    _ = mixedMoment B node985 node985Labels := by rfl

theorem canonical1220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1220 raw1220Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw1220 raw1220Labels = mixedMoment B raw1220step0 raw1220step0Labels := by
      have ha : raw1220step0 = (fun i j => raw1220 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1220step0 raw1220; decide +kernel
      have hl : raw1220step0Labels = raw1220Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1220 raw1220Labels permutation32 permutation6
    mixedMoment B raw1220step0 raw1220step0Labels = mixedMoment B raw1220step1 raw1220step1Labels := by
      have ha : raw1220step1 = -raw1220step0 := by apply Matrix.ext; change ∀ i j, raw1220step1 i j = -(raw1220step0 i j); unfold raw1220step1 raw1220step0; decide +kernel
      have hl : raw1220step1Labels = raw1220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1220step1 raw1220step1Labels = mixedMoment B raw1220step2 raw1220step2Labels := by
      have ha : raw1220step2 = raw1220step1 := by apply Matrix.ext; unfold raw1220step2 raw1220step1; decide +kernel
      have hl : raw1220step1Labels = labelEmbedding1 ∘ raw1220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1220step1 raw1220step1Labels raw1220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1618 node1618Labels := by rfl

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

theorem singleton4288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4288 node4288Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node866 node866Labels + mixedMoment B node1554 node1554Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1026 singletonSmall4288
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4288) = raw1026Labels := by decide +kernel
  rw [hl, canonical1026 B hB] at h
  have hc0 : mixedMoment B raw1026 (Fin.cases (0 : Fin 2) singletonSmall4288) =
      mixedMoment B node866 node866Labels := by
    have ha : raw1026 = raw1027 := by apply Matrix.ext; unfold raw1026 raw1027; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4288 = raw1027Labels := by decide +kernel
    rw [ha, hj, canonical1027 B hB]
  have hc1 : mixedMoment B raw1026 (Fin.cases (1 : Fin 2) singletonSmall4288) =
      mixedMoment B node1554 node1554Labels := by
    have ha : raw1026 = raw1028 := by apply Matrix.ext; unfold raw1026 raw1028; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4288 = raw1028Labels := by decide +kernel
    rw [ha, hj, canonical1028 B hB]
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

theorem singleton4296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4296 node4296Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node874 node874Labels + mixedMoment B node1570 node1570Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1050 singletonSmall4296
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4296) = raw1050Labels := by decide +kernel
  rw [hl, canonical1050 B hB] at h
  have hc0 : mixedMoment B raw1050 (Fin.cases (0 : Fin 2) singletonSmall4296) =
      mixedMoment B node874 node874Labels := by
    have ha : raw1050 = raw1051 := by apply Matrix.ext; unfold raw1050 raw1051; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4296 = raw1051Labels := by decide +kernel
    rw [ha, hj, canonical1051 B hB]
  have hc1 : mixedMoment B raw1050 (Fin.cases (1 : Fin 2) singletonSmall4296) =
      mixedMoment B node1570 node1570Labels := by
    have ha : raw1050 = raw1052 := by apply Matrix.ext; unfold raw1050 raw1052; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4296 = raw1052Labels := by decide +kernel
    rw [ha, hj, canonical1052 B hB]
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

theorem singleton4404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4404 node4404Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node985 node985Labels + mixedMoment B node1618 node1618Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1218 singletonSmall4404
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4404) = raw1218Labels := by decide +kernel
  rw [hl, canonical1218 B hB] at h
  have hc0 : mixedMoment B raw1218 (Fin.cases (0 : Fin 2) singletonSmall4404) =
      mixedMoment B node985 node985Labels := by
    have ha : raw1218 = raw1219 := by apply Matrix.ext; unfold raw1218 raw1219; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4404 = raw1219Labels := by decide +kernel
    rw [ha, hj, canonical1219 B hB]
  have hc1 : mixedMoment B raw1218 (Fin.cases (1 : Fin 2) singletonSmall4404) =
      mixedMoment B node1618 node1618Labels := by
    have ha : raw1218 = raw1220 := by apply Matrix.ext; unfold raw1218 raw1220; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4404 = raw1220Labels := by decide +kernel
    rw [ha, hj, canonical1220 B hB]
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

theorem singleton4632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4632 node4632Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1761 node1761Labels + mixedMoment B node1837 node1837Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1476 singletonSmall4632
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4632) = raw1476Labels := by decide +kernel
  rw [hl, canonical1476 B hB] at h
  have hc0 : mixedMoment B raw1476 (Fin.cases (0 : Fin 2) singletonSmall4632) =
      mixedMoment B node1761 node1761Labels := by
    have ha : raw1476 = raw1477 := by apply Matrix.ext; unfold raw1476 raw1477; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4632 = raw1477Labels := by decide +kernel
    rw [ha, hj, canonical1477 B hB]
  have hc1 : mixedMoment B raw1476 (Fin.cases (1 : Fin 2) singletonSmall4632) =
      mixedMoment B node1837 node1837Labels := by
    have ha : raw1476 = raw1478 := by apply Matrix.ext; unfold raw1476 raw1478; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4632 = raw1478Labels := by decide +kernel
    rw [ha, hj, canonical1478 B hB]
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

theorem singleton4638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4638 node4638Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1767 node1767Labels + mixedMoment B node1851 node1851Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1494 singletonSmall4638
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4638) = raw1494Labels := by decide +kernel
  rw [hl, canonical1494 B hB] at h
  have hc0 : mixedMoment B raw1494 (Fin.cases (0 : Fin 2) singletonSmall4638) =
      mixedMoment B node1767 node1767Labels := by
    have ha : raw1494 = raw1495 := by apply Matrix.ext; unfold raw1494 raw1495; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4638 = raw1495Labels := by decide +kernel
    rw [ha, hj, canonical1495 B hB]
  have hc1 : mixedMoment B raw1494 (Fin.cases (1 : Fin 2) singletonSmall4638) =
      mixedMoment B node1851 node1851Labels := by
    have ha : raw1494 = raw1496 := by apply Matrix.ext; unfold raw1494 raw1496; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4638 = raw1496Labels := by decide +kernel
    rw [ha, hj, canonical1496 B hB]
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

theorem singleton4707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4707 node4707Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1861 node1861Labels + mixedMoment B node1889 node1889Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1593 singletonSmall4707
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4707) = raw1593Labels := by decide +kernel
  rw [hl, canonical1593 B hB] at h
  have hc0 : mixedMoment B raw1593 (Fin.cases (0 : Fin 2) singletonSmall4707) =
      mixedMoment B node1861 node1861Labels := by
    have ha : raw1593 = raw1594 := by apply Matrix.ext; unfold raw1593 raw1594; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4707 = raw1594Labels := by decide +kernel
    rw [ha, hj, canonical1594 B hB]
  have hc1 : mixedMoment B raw1593 (Fin.cases (1 : Fin 2) singletonSmall4707) =
      mixedMoment B node1889 node1889Labels := by
    have ha : raw1593 = raw1595 := by apply Matrix.ext; unfold raw1593 raw1595; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4707 = raw1595Labels := by decide +kernel
    rw [ha, hj, canonical1595 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4722 node4722Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1876 node1876Labels + mixedMoment B node1906 node1906Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1623 singletonSmall4722
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4722) = raw1623Labels := by decide +kernel
  rw [hl, canonical1623 B hB] at h
  have hc0 : mixedMoment B raw1623 (Fin.cases (0 : Fin 2) singletonSmall4722) =
      mixedMoment B node1876 node1876Labels := by
    have ha : raw1623 = raw1624 := by apply Matrix.ext; unfold raw1623 raw1624; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4722 = raw1624Labels := by decide +kernel
    rw [ha, hj, canonical1624 B hB]
  have hc1 : mixedMoment B raw1623 (Fin.cases (1 : Fin 2) singletonSmall4722) =
      mixedMoment B node1906 node1906Labels := by
    have ha : raw1623 = raw1625 := by apply Matrix.ext; unfold raw1623 raw1625; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4722 = raw1625Labels := by decide +kernel
    rw [ha, hj, canonical1625 B hB]
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

theorem singleton4727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4727 node4727Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1881 node1881Labels + mixedMoment B node1939 node1939Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1638 singletonSmall4727
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4727) = raw1638Labels := by decide +kernel
  rw [hl, canonical1638 B hB] at h
  have hc0 : mixedMoment B raw1638 (Fin.cases (0 : Fin 2) singletonSmall4727) =
      mixedMoment B node1881 node1881Labels := by
    have ha : raw1638 = raw1639 := by apply Matrix.ext; unfold raw1638 raw1639; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4727 = raw1639Labels := by decide +kernel
    rw [ha, hj, canonical1639 B hB]
  have hc1 : mixedMoment B raw1638 (Fin.cases (1 : Fin 2) singletonSmall4727) =
      mixedMoment B node1939 node1939Labels := by
    have ha : raw1638 = raw1640 := by apply Matrix.ext; unfold raw1638 raw1640; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4727 = raw1640Labels := by decide +kernel
    rw [ha, hj, canonical1640 B hB]
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

theorem singleton4737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4737 node4737Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1909 node1909Labels + mixedMoment B node1909 node1909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1653 singletonSmall4737
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4737) = raw1653Labels := by decide +kernel
  rw [hl, canonical1653 B hB] at h
  have hc0 : mixedMoment B raw1653 (Fin.cases (0 : Fin 2) singletonSmall4737) =
      mixedMoment B node1909 node1909Labels := by
    have ha : raw1653 = raw1654 := by apply Matrix.ext; unfold raw1653 raw1654; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4737 = raw1654Labels := by decide +kernel
    rw [ha, hj, canonical1654 B hB]
  have hc1 : mixedMoment B raw1653 (Fin.cases (1 : Fin 2) singletonSmall4737) =
      mixedMoment B node1909 node1909Labels := by
    have ha : raw1653 = raw1655 := by apply Matrix.ext; unfold raw1653 raw1655; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4737 = raw1655Labels := by decide +kernel
    rw [ha, hj, canonical1655 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4742 node4742Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1915 node1915Labels + mixedMoment B node1946 node1946Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1659 singletonSmall4742
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4742) = raw1659Labels := by decide +kernel
  rw [hl, canonical1659 B hB] at h
  have hc0 : mixedMoment B raw1659 (Fin.cases (0 : Fin 2) singletonSmall4742) =
      mixedMoment B node1915 node1915Labels := by
    have ha : raw1659 = raw1660 := by apply Matrix.ext; unfold raw1659 raw1660; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4742 = raw1660Labels := by decide +kernel
    rw [ha, hj, canonical1660 B hB]
  have hc1 : mixedMoment B raw1659 (Fin.cases (1 : Fin 2) singletonSmall4742) =
      mixedMoment B node1946 node1946Labels := by
    have ha : raw1659 = raw1661 := by apply Matrix.ext; unfold raw1659 raw1661; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4742 = raw1661Labels := by decide +kernel
    rw [ha, hj, canonical1661 B hB]
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

theorem singleton4828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4828 node4828Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2048 node2048Labels + mixedMoment B node2082 node2082Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1758 singletonSmall4828
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4828) = raw1758Labels := by decide +kernel
  rw [hl, canonical1758 B hB] at h
  have hc0 : mixedMoment B raw1758 (Fin.cases (0 : Fin 2) singletonSmall4828) =
      mixedMoment B node2048 node2048Labels := by
    have ha : raw1758 = raw1759 := by apply Matrix.ext; unfold raw1758 raw1759; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4828 = raw1759Labels := by decide +kernel
    rw [ha, hj, canonical1759 B hB]
  have hc1 : mixedMoment B raw1758 (Fin.cases (1 : Fin 2) singletonSmall4828) =
      mixedMoment B node2082 node2082Labels := by
    have ha : raw1758 = raw1760 := by apply Matrix.ext; unfold raw1758 raw1760; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4828 = raw1760Labels := by decide +kernel
    rw [ha, hj, canonical1760 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4835 node4835Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2054 node2054Labels + mixedMoment B node2206 node2206Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1767 singletonSmall4835
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4835) = raw1767Labels := by decide +kernel
  rw [hl, canonical1767 B hB] at h
  have hc0 : mixedMoment B raw1767 (Fin.cases (0 : Fin 2) singletonSmall4835) =
      mixedMoment B node2054 node2054Labels := by
    have ha : raw1767 = raw1768 := by apply Matrix.ext; unfold raw1767 raw1768; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4835 = raw1768Labels := by decide +kernel
    rw [ha, hj, canonical1768 B hB]
  have hc1 : mixedMoment B raw1767 (Fin.cases (1 : Fin 2) singletonSmall4835) =
      mixedMoment B node2206 node2206Labels := by
    have ha : raw1767 = raw1769 := by apply Matrix.ext; unfold raw1767 raw1769; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4835 = raw1769Labels := by decide +kernel
    rw [ha, hj, canonical1769 B hB]
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

theorem singleton5015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5015 node5015Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2400 node2400Labels + mixedMoment B node3344 node3344Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2025 singletonSmall5015
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5015) = raw2025Labels := by decide +kernel
  rw [hl, canonical2025 B hB] at h
  have hc0 : mixedMoment B raw2025 (Fin.cases (0 : Fin 2) singletonSmall5015) =
      mixedMoment B node2400 node2400Labels := by
    have ha : raw2025 = raw2026 := by apply Matrix.ext; unfold raw2025 raw2026; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5015 = raw2026Labels := by decide +kernel
    rw [ha, hj, canonical2026 B hB]
  have hc1 : mixedMoment B raw2025 (Fin.cases (1 : Fin 2) singletonSmall5015) =
      mixedMoment B node3344 node3344Labels := by
    have ha : raw2025 = raw2027 := by apply Matrix.ext; unfold raw2025 raw2027; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5015 = raw2027Labels := by decide +kernel
    rw [ha, hj, canonical2027 B hB]
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

theorem singleton5056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5056 node5056Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2459 node2459Labels + mixedMoment B node3429 node3429Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2082 singletonSmall5056
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5056) = raw2082Labels := by decide +kernel
  rw [hl, canonical2082 B hB] at h
  have hc0 : mixedMoment B raw2082 (Fin.cases (0 : Fin 2) singletonSmall5056) =
      mixedMoment B node2459 node2459Labels := by
    have ha : raw2082 = raw2083 := by apply Matrix.ext; unfold raw2082 raw2083; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5056 = raw2083Labels := by decide +kernel
    rw [ha, hj, canonical2083 B hB]
  have hc1 : mixedMoment B raw2082 (Fin.cases (1 : Fin 2) singletonSmall5056) =
      mixedMoment B node3429 node3429Labels := by
    have ha : raw2082 = raw2084 := by apply Matrix.ext; unfold raw2082 raw2084; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5056 = raw2084Labels := by decide +kernel
    rw [ha, hj, canonical2084 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5095 node5095Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2505 node2505Labels + mixedMoment B node3448 node3448Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2118 singletonSmall5095
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5095) = raw2118Labels := by decide +kernel
  rw [hl, canonical2118 B hB] at h
  have hc0 : mixedMoment B raw2118 (Fin.cases (0 : Fin 2) singletonSmall5095) =
      mixedMoment B node2505 node2505Labels := by
    have ha : raw2118 = raw2119 := by apply Matrix.ext; unfold raw2118 raw2119; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5095 = raw2119Labels := by decide +kernel
    rw [ha, hj, canonical2119 B hB]
  have hc1 : mixedMoment B raw2118 (Fin.cases (1 : Fin 2) singletonSmall5095) =
      mixedMoment B node3448 node3448Labels := by
    have ha : raw2118 = raw2120 := by apply Matrix.ext; unfold raw2118 raw2120; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5095 = raw2120Labels := by decide +kernel
    rw [ha, hj, canonical2120 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5102 node5102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2512 node2512Labels + mixedMoment B node3471 node3471Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2127 singletonSmall5102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5102) = raw2127Labels := by decide +kernel
  rw [hl, canonical2127 B hB] at h
  have hc0 : mixedMoment B raw2127 (Fin.cases (0 : Fin 2) singletonSmall5102) =
      mixedMoment B node2512 node2512Labels := by
    have ha : raw2127 = raw2128 := by apply Matrix.ext; unfold raw2127 raw2128; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5102 = raw2128Labels := by decide +kernel
    rw [ha, hj, canonical2128 B hB]
  have hc1 : mixedMoment B raw2127 (Fin.cases (1 : Fin 2) singletonSmall5102) =
      mixedMoment B node3471 node3471Labels := by
    have ha : raw2127 = raw2129 := by apply Matrix.ext; unfold raw2127 raw2129; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5102 = raw2129Labels := by decide +kernel
    rw [ha, hj, canonical2129 B hB]
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

theorem sound866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node866 node866Labels = Sparse.eval nodeValue866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 866) = mixedMoment B node866 node866Labels := rfl
  simpa [nodeValue866, Sparse.eval] using hc.symm

theorem sound873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node873 node873Labels = Sparse.eval nodeValue873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 873) = mixedMoment B node873 node873Labels := rfl
  simpa [nodeValue873, Sparse.eval] using hc.symm

theorem sound874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node874 node874Labels = Sparse.eval nodeValue874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 874) = mixedMoment B node874 node874Labels := rfl
  simpa [nodeValue874, Sparse.eval] using hc.symm

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

theorem sound985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node985 node985Labels = Sparse.eval nodeValue985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 985) = mixedMoment B node985 node985Labels := rfl
  simpa [nodeValue985, Sparse.eval] using hc.symm

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

theorem sound1554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1554 node1554Labels = Sparse.eval nodeValue1554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1554) = mixedMoment B node1554 node1554Labels := rfl
  simpa [nodeValue1554, Sparse.eval] using hc.symm

theorem sound1569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1569 node1569Labels = Sparse.eval nodeValue1569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1569) = mixedMoment B node1569 node1569Labels := rfl
  simpa [nodeValue1569, Sparse.eval] using hc.symm

theorem sound1570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1570 node1570Labels = Sparse.eval nodeValue1570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1570) = mixedMoment B node1570 node1570Labels := rfl
  simpa [nodeValue1570, Sparse.eval] using hc.symm

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

theorem sound1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1618 node1618Labels = Sparse.eval nodeValue1618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1618) = mixedMoment B node1618 node1618Labels := rfl
  simpa [nodeValue1618, Sparse.eval] using hc.symm

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

theorem sound1761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1761 node1761Labels = Sparse.eval nodeValue1761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1761) = mixedMoment B node1761 node1761Labels := rfl
  simpa [nodeValue1761, Sparse.eval] using hc.symm

theorem sound1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1766 node1766Labels = Sparse.eval nodeValue1766 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1766) = mixedMoment B node1766 node1766Labels := rfl
  simpa [nodeValue1766, Sparse.eval] using hc.symm

theorem sound1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1767 node1767Labels = Sparse.eval nodeValue1767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1767) = mixedMoment B node1767 node1767Labels := rfl
  simpa [nodeValue1767, Sparse.eval] using hc.symm

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

theorem sound1837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1837 node1837Labels = Sparse.eval nodeValue1837 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1837) = mixedMoment B node1837 node1837Labels := rfl
  simpa [nodeValue1837, Sparse.eval] using hc.symm

theorem sound1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1850 node1850Labels = Sparse.eval nodeValue1850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1850) = mixedMoment B node1850 node1850Labels := rfl
  simpa [nodeValue1850, Sparse.eval] using hc.symm

theorem sound1851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1851 node1851Labels = Sparse.eval nodeValue1851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1851) = mixedMoment B node1851 node1851Labels := rfl
  simpa [nodeValue1851, Sparse.eval] using hc.symm

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

theorem sound1861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1861 node1861Labels = Sparse.eval nodeValue1861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1861) = mixedMoment B node1861 node1861Labels := rfl
  simpa [nodeValue1861, Sparse.eval] using hc.symm

theorem sound1876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1876 node1876Labels = Sparse.eval nodeValue1876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1876) = mixedMoment B node1876 node1876Labels := rfl
  simpa [nodeValue1876, Sparse.eval] using hc.symm

theorem sound1880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1880 node1880Labels = Sparse.eval nodeValue1880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1880) = mixedMoment B node1880 node1880Labels := rfl
  simpa [nodeValue1880, Sparse.eval] using hc.symm

theorem sound1881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1881 node1881Labels = Sparse.eval nodeValue1881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1881) = mixedMoment B node1881 node1881Labels := rfl
  simpa [nodeValue1881, Sparse.eval] using hc.symm

theorem sound1888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1888 node1888Labels = Sparse.eval nodeValue1888 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1888) = mixedMoment B node1888 node1888Labels := rfl
  simpa [nodeValue1888, Sparse.eval] using hc.symm

theorem sound1889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1889 node1889Labels = Sparse.eval nodeValue1889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1889) = mixedMoment B node1889 node1889Labels := rfl
  simpa [nodeValue1889, Sparse.eval] using hc.symm

theorem sound1906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1906 node1906Labels = Sparse.eval nodeValue1906 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1906) = mixedMoment B node1906 node1906Labels := rfl
  simpa [nodeValue1906, Sparse.eval] using hc.symm

theorem sound1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1909 node1909Labels = Sparse.eval nodeValue1909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1909) = mixedMoment B node1909 node1909Labels := rfl
  simpa [nodeValue1909, Sparse.eval] using hc.symm

theorem sound1915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1915 node1915Labels = Sparse.eval nodeValue1915 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1915) = mixedMoment B node1915 node1915Labels := rfl
  simpa [nodeValue1915, Sparse.eval] using hc.symm

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

theorem sound1938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1938 node1938Labels = Sparse.eval nodeValue1938 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1938) = mixedMoment B node1938 node1938Labels := rfl
  simpa [nodeValue1938, Sparse.eval] using hc.symm

theorem sound1939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1939 node1939Labels = Sparse.eval nodeValue1939 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1939) = mixedMoment B node1939 node1939Labels := rfl
  simpa [nodeValue1939, Sparse.eval] using hc.symm

theorem sound1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1946 node1946Labels = Sparse.eval nodeValue1946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1946) = mixedMoment B node1946 node1946Labels := rfl
  simpa [nodeValue1946, Sparse.eval] using hc.symm

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

theorem sound2048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2048 node2048Labels = Sparse.eval nodeValue2048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2048) = mixedMoment B node2048 node2048Labels := rfl
  simpa [nodeValue2048, Sparse.eval] using hc.symm

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2082 node2082Labels = Sparse.eval nodeValue2082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2082) = mixedMoment B node2082 node2082Labels := rfl
  simpa [nodeValue2082, Sparse.eval] using hc.symm

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

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

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

theorem sound2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2400 node2400Labels = Sparse.eval nodeValue2400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2400) = mixedMoment B node2400 node2400Labels := rfl
  simpa [nodeValue2400, Sparse.eval] using hc.symm

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

theorem sound2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2459 node2459Labels = Sparse.eval nodeValue2459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2459) = mixedMoment B node2459 node2459Labels := rfl
  simpa [nodeValue2459, Sparse.eval] using hc.symm

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

theorem sound2505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2505 node2505Labels = Sparse.eval nodeValue2505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2505) = mixedMoment B node2505 node2505Labels := rfl
  simpa [nodeValue2505, Sparse.eval] using hc.symm

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

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

theorem sound3344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3344 node3344Labels = Sparse.eval nodeValue3344 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3344) = mixedMoment B node3344 node3344Labels := rfl
  simpa [nodeValue3344, Sparse.eval] using hc.symm

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

theorem sound3429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3429 node3429Labels = Sparse.eval nodeValue3429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3429) = mixedMoment B node3429 node3429Labels := rfl
  simpa [nodeValue3429, Sparse.eval] using hc.symm

theorem sound3448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3448 node3448Labels = Sparse.eval nodeValue3448 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3448) = mixedMoment B node3448 node3448Labels := rfl
  simpa [nodeValue3448, Sparse.eval] using hc.symm

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

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4311 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4311 node4311Labels = 0 := by
  exact mixedMoment_order_one B hB node4311 node4311Labels 1
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

theorem sound4288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4288 node4288Labels = Sparse.eval nodeValue4288 (mixedVector B) := by
  have h := singleton4288 B _hB
  rw [sound866 B _hB _hF, sound1554 B _hB _hF] at h
  norm_num [nodeValue4288, nodeValue866, nodeValue1554, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4295 node4295Labels = Sparse.eval nodeValue4295 (mixedVector B) := by
  have h := singleton4295 B _hB
  rw [sound873 B _hB _hF, sound1569 B _hB _hF] at h
  norm_num [nodeValue4295, nodeValue873, nodeValue1569, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4296 node4296Labels = Sparse.eval nodeValue4296 (mixedVector B) := by
  have h := singleton4296 B _hB
  rw [sound874 B _hB _hF, sound1570 B _hB _hF] at h
  norm_num [nodeValue4296, nodeValue874, nodeValue1570, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4311 node4311Labels = Sparse.eval nodeValue4311 (mixedVector B) := by
  simpa only [nodeValue4311, Sparse.eval_nil] using zero4311 B _hB _hF

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

theorem sound4404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4404 node4404Labels = Sparse.eval nodeValue4404 (mixedVector B) := by
  have h := singleton4404 B _hB
  rw [sound985 B _hB _hF, sound1618 B _hB _hF] at h
  norm_num [nodeValue4404, nodeValue985, nodeValue1618, Sparse.eval] at h ⊢
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

theorem zero4652 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4652 node4652Labels = 0 := by
  exact mixedMoment_order_one B hB node4652 node4652Labels 1
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

theorem sound4632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4632 node4632Labels = Sparse.eval nodeValue4632 (mixedVector B) := by
  have h := singleton4632 B _hB
  rw [sound1761 B _hB _hF, sound1837 B _hB _hF] at h
  norm_num [nodeValue4632, nodeValue1761, nodeValue1837, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4637 node4637Labels = Sparse.eval nodeValue4637 (mixedVector B) := by
  have h := singleton4637 B _hB
  rw [sound1766 B _hB _hF, sound1850 B _hB _hF] at h
  norm_num [nodeValue4637, nodeValue1766, nodeValue1850, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4638 node4638Labels = Sparse.eval nodeValue4638 (mixedVector B) := by
  have h := singleton4638 B _hB
  rw [sound1767 B _hB _hF, sound1851 B _hB _hF] at h
  norm_num [nodeValue4638, nodeValue1767, nodeValue1851, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4652 node4652Labels = Sparse.eval nodeValue4652 (mixedVector B) := by
  simpa only [nodeValue4652, Sparse.eval_nil] using zero4652 B _hB _hF

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

theorem zero4715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4715 node4715Labels = 0 := by
  exact mixedMoment_order_one B hB node4715 node4715Labels 1
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

theorem sound4707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4707 node4707Labels = Sparse.eval nodeValue4707 (mixedVector B) := by
  have h := singleton4707 B _hB
  rw [sound1861 B _hB _hF, sound1889 B _hB _hF] at h
  norm_num [nodeValue4707, nodeValue1861, nodeValue1889, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4715 node4715Labels = Sparse.eval nodeValue4715 (mixedVector B) := by
  simpa only [nodeValue4715, Sparse.eval_nil] using zero4715 B _hB _hF

theorem sound4722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4722 node4722Labels = Sparse.eval nodeValue4722 (mixedVector B) := by
  have h := singleton4722 B _hB
  rw [sound1876 B _hB _hF, sound1906 B _hB _hF] at h
  norm_num [nodeValue4722, nodeValue1876, nodeValue1906, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4726 node4726Labels = Sparse.eval nodeValue4726 (mixedVector B) := by
  have h := singleton4726 B _hB
  rw [sound1880 B _hB _hF, sound1938 B _hB _hF] at h
  norm_num [nodeValue4726, nodeValue1880, nodeValue1938, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4727 node4727Labels = Sparse.eval nodeValue4727 (mixedVector B) := by
  have h := singleton4727 B _hB
  rw [sound1881 B _hB _hF, sound1939 B _hB _hF] at h
  norm_num [nodeValue4727, nodeValue1881, nodeValue1939, Sparse.eval] at h ⊢
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

theorem zero4752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4752 node4752Labels = 0 := by
  exact mixedMoment_order_one B hB node4752 node4752Labels 1
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

theorem sound4737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4737 node4737Labels = Sparse.eval nodeValue4737 (mixedVector B) := by
  have h := singleton4737 B _hB
  rw [sound1909 B _hB _hF] at h
  norm_num [nodeValue4737, nodeValue1909, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4741 node4741Labels = Sparse.eval nodeValue4741 (mixedVector B) := by
  simpa only [nodeValue4741, Sparse.eval_nil] using zero4741 B _hB _hF

theorem sound4742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4742 node4742Labels = Sparse.eval nodeValue4742 (mixedVector B) := by
  have h := singleton4742 B _hB
  rw [sound1915 B _hB _hF, sound1946 B _hB _hF] at h
  norm_num [nodeValue4742, nodeValue1915, nodeValue1946, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4752 node4752Labels = Sparse.eval nodeValue4752 (mixedVector B) := by
  simpa only [nodeValue4752, Sparse.eval_nil] using zero4752 B _hB _hF

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

theorem sound4828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4828 node4828Labels = Sparse.eval nodeValue4828 (mixedVector B) := by
  have h := singleton4828 B _hB
  rw [sound2048 B _hB _hF, sound2082 B _hB _hF] at h
  norm_num [nodeValue4828, nodeValue2048, nodeValue2082, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
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

theorem sound5015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5015 node5015Labels = Sparse.eval nodeValue5015 (mixedVector B) := by
  have h := singleton5015 B _hB
  rw [sound2400 B _hB _hF, sound3344 B _hB _hF] at h
  norm_num [nodeValue5015, nodeValue2400, nodeValue3344, Sparse.eval] at h ⊢
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

theorem sound5056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5056 node5056Labels = Sparse.eval nodeValue5056 (mixedVector B) := by
  have h := singleton5056 B _hB
  rw [sound2459 B _hB _hF, sound3429 B _hB _hF] at h
  norm_num [nodeValue5056, nodeValue2459, nodeValue3429, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5095 node5095Labels = Sparse.eval nodeValue5095 (mixedVector B) := by
  have h := singleton5095 B _hB
  rw [sound2505 B _hB _hF, sound3448 B _hB _hF] at h
  norm_num [nodeValue5095, nodeValue2505, nodeValue3448, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = Sparse.eval nodeValue5101 (mixedVector B) := by
  simpa only [nodeValue5101, Sparse.eval_nil] using zero5101 B _hB _hF

theorem sound5102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5102 node5102Labels = Sparse.eval nodeValue5102 (mixedVector B) := by
  have h := singleton5102 B _hB
  rw [sound2512 B _hB _hF, sound3471 B _hB _hF] at h
  norm_num [nodeValue5102, nodeValue2512, nodeValue3471, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources72
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2308 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 1) (sourceB2308 + difference 1 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 1) (sourceB2308 + difference 1 0) sourceC2308) = raw31807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31807; decide +kernel
    rw [ha]
    exact (canonical31807 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 2) (sourceB2308 + difference 2 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 2) (sourceB2308 + difference 2 0) sourceC2308) = raw31808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31808; decide +kernel
    rw [ha]
    exact (canonical31808 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 3) (sourceB2308 + difference 3 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 3) (sourceB2308 + difference 3 0) sourceC2308) = raw31809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31809; decide +kernel
    rw [ha]
    exact (canonical31809 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 4) (sourceB2308 + difference 4 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 4) (sourceB2308 + difference 4 0) sourceC2308) = raw31810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31810; decide +kernel
    rw [ha]
    exact (canonical31810 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2308 + difference 0 5) (sourceB2308 + difference 5 0) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2308 + difference 0 5) (sourceB2308 + difference 5 0) sourceC2308) = raw31811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31811; decide +kernel
    rw [ha]
    exact (canonical31811 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 0) (sourceB2308 + difference 0 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 0) (sourceB2308 + difference 0 1) sourceC2308) = raw31812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31812; decide +kernel
    rw [ha]
    exact (canonical31812 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 2) (sourceB2308 + difference 2 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 2) (sourceB2308 + difference 2 1) sourceC2308) = raw31813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31813; decide +kernel
    rw [ha]
    exact (canonical31813 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 3) (sourceB2308 + difference 3 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 3) (sourceB2308 + difference 3 1) sourceC2308) = raw31814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31814; decide +kernel
    rw [ha]
    exact (canonical31814 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 4) (sourceB2308 + difference 4 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 4) (sourceB2308 + difference 4 1) sourceC2308) = raw31815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31815; decide +kernel
    rw [ha]
    exact (canonical31815 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2308 + difference 1 5) (sourceB2308 + difference 5 1) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2308 + difference 1 5) (sourceB2308 + difference 5 1) sourceC2308) = raw31816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31816; decide +kernel
    rw [ha]
    exact (canonical31816 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 0) (sourceB2308 + difference 0 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4311) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 0) (sourceB2308 + difference 0 2) sourceC2308) = raw31817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31817; decide +kernel
    rw [ha]
    exact (canonical31817 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 1) (sourceB2308 + difference 1 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4652) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 1) (sourceB2308 + difference 1 2) sourceC2308) = raw31818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31818; decide +kernel
    rw [ha]
    exact (canonical31818 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 3) (sourceB2308 + difference 3 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4715) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 3) (sourceB2308 + difference 3 2) sourceC2308) = raw31819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31819; decide +kernel
    rw [ha]
    exact (canonical31819 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 4) (sourceB2308 + difference 4 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 4) (sourceB2308 + difference 4 2) sourceC2308) = raw31820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31820; decide +kernel
    rw [ha]
    exact (canonical31820 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2308 + difference 2 5) (sourceB2308 + difference 5 2) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2308 + difference 2 5) (sourceB2308 + difference 5 2) sourceC2308) = raw31821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31821; decide +kernel
    rw [ha]
    exact (canonical31821 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 0) (sourceB2308 + difference 0 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 0) (sourceB2308 + difference 0 3) sourceC2308) = raw31822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31822; decide +kernel
    rw [ha]
    exact (canonical31822 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 1) (sourceB2308 + difference 1 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 1) (sourceB2308 + difference 1 3) sourceC2308) = raw31823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31823; decide +kernel
    rw [ha]
    exact (canonical31823 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 2) (sourceB2308 + difference 2 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4722) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 2) (sourceB2308 + difference 2 3) sourceC2308) = raw31824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31824; decide +kernel
    rw [ha]
    exact (canonical31824 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 4) (sourceB2308 + difference 4 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 4) (sourceB2308 + difference 4 3) sourceC2308) = raw31825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31825; decide +kernel
    rw [ha]
    exact (canonical31825 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2308 + difference 3 5) (sourceB2308 + difference 5 3) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2308 + difference 3 5) (sourceB2308 + difference 5 3) sourceC2308) = raw31826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31826; decide +kernel
    rw [ha]
    exact (canonical31826 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 0) (sourceB2308 + difference 0 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 0) (sourceB2308 + difference 0 4) sourceC2308) = raw31827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31827; decide +kernel
    rw [ha]
    exact (canonical31827 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 1) (sourceB2308 + difference 1 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 1) (sourceB2308 + difference 1 4) sourceC2308) = raw31828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31828; decide +kernel
    rw [ha]
    exact (canonical31828 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 2) (sourceB2308 + difference 2 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 2) (sourceB2308 + difference 2 4) sourceC2308) = raw31829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31829; decide +kernel
    rw [ha]
    exact (canonical31829 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 3) (sourceB2308 + difference 3 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 3) (sourceB2308 + difference 3 4) sourceC2308) = raw31830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31830; decide +kernel
    rw [ha]
    exact (canonical31830 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2308 + difference 4 5) (sourceB2308 + difference 5 4) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2308 + difference 4 5) (sourceB2308 + difference 5 4) sourceC2308) = raw31831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31831; decide +kernel
    rw [ha]
    exact (canonical31831 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 0) (sourceB2308 + difference 0 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 0) (sourceB2308 + difference 0 5) sourceC2308) = raw31832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31832; decide +kernel
    rw [ha]
    exact (canonical31832 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 1) (sourceB2308 + difference 1 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4638) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 1) (sourceB2308 + difference 1 5) sourceC2308) = raw31833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31833; decide +kernel
    rw [ha]
    exact (canonical31833 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 2) (sourceB2308 + difference 2 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 2) (sourceB2308 + difference 2 5) sourceC2308) = raw31834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31834; decide +kernel
    rw [ha]
    exact (canonical31834 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 3) (sourceB2308 + difference 3 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4707) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 3) (sourceB2308 + difference 3 5) sourceC2308) = raw31835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31835; decide +kernel
    rw [ha]
    exact (canonical31835 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2308 + difference 5 4) (sourceB2308 + difference 4 5) sourceC2308) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2308 + difference 5 4) (sourceB2308 + difference 4 5) sourceC2308) = raw31836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2308 sourceB2308 sourceC2308 difference raw31836; decide +kernel
    rw [ha]
    exact (canonical31836 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2308 sourceB2308 sourceC2308
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2308, Integer.Sparse.eval]
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

theorem reindexCheck1880 : Integer.Sparse.reindex keyMap MixedData.row1880 = numericRow1880 := by decide +kernel

theorem numericCheck1880 (x : Master → ℝ) : Integer.Sparse.eval numericRow1880 x =
    (4 : ℝ) * reducedSource1880 x := by
  norm_num [numericRow1880, reducedSource1880, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4288, nodeValue4295, nodeValue4296, nodeValue4311, nodeValue4404, nodeValue4632, nodeValue4637, nodeValue4638, nodeValue4652, nodeValue4706, nodeValue4707, nodeValue4715, nodeValue4722, nodeValue4726, nodeValue4727, nodeValue4736, nodeValue4737, nodeValue4741, nodeValue4742, nodeValue4752, nodeValue4782, nodeValue4828, nodeValue4834, nodeValue4835, nodeValue5015, nodeValue5056, nodeValue5095, nodeValue5101, nodeValue5102] <;> ring

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

theorem reducedZero1880 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1880 (mixedVector B) = 0 := by
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4288 : mixedVector B (Sum.inr 4288) = Sparse.eval nodeValue4288 (mixedVector B) := by
    change mixedMoment B node4288 node4288Labels = _
    exact sound4288 B hB hF
  have h4295 : mixedVector B (Sum.inr 4295) = Sparse.eval nodeValue4295 (mixedVector B) := by
    change mixedMoment B node4295 node4295Labels = _
    exact sound4295 B hB hF
  have h4296 : mixedVector B (Sum.inr 4296) = Sparse.eval nodeValue4296 (mixedVector B) := by
    change mixedMoment B node4296 node4296Labels = _
    exact sound4296 B hB hF
  have h4311 : mixedVector B (Sum.inr 4311) = Sparse.eval nodeValue4311 (mixedVector B) := by
    change mixedMoment B node4311 node4311Labels = _
    exact sound4311 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4632 : mixedVector B (Sum.inr 4632) = Sparse.eval nodeValue4632 (mixedVector B) := by
    change mixedMoment B node4632 node4632Labels = _
    exact sound4632 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4638 : mixedVector B (Sum.inr 4638) = Sparse.eval nodeValue4638 (mixedVector B) := by
    change mixedMoment B node4638 node4638Labels = _
    exact sound4638 B hB hF
  have h4652 : mixedVector B (Sum.inr 4652) = Sparse.eval nodeValue4652 (mixedVector B) := by
    change mixedMoment B node4652 node4652Labels = _
    exact sound4652 B hB hF
  have h4706 : mixedVector B (Sum.inr 4706) = Sparse.eval nodeValue4706 (mixedVector B) := by
    change mixedMoment B node4706 node4706Labels = _
    exact sound4706 B hB hF
  have h4707 : mixedVector B (Sum.inr 4707) = Sparse.eval nodeValue4707 (mixedVector B) := by
    change mixedMoment B node4707 node4707Labels = _
    exact sound4707 B hB hF
  have h4715 : mixedVector B (Sum.inr 4715) = Sparse.eval nodeValue4715 (mixedVector B) := by
    change mixedMoment B node4715 node4715Labels = _
    exact sound4715 B hB hF
  have h4722 : mixedVector B (Sum.inr 4722) = Sparse.eval nodeValue4722 (mixedVector B) := by
    change mixedMoment B node4722 node4722Labels = _
    exact sound4722 B hB hF
  have h4726 : mixedVector B (Sum.inr 4726) = Sparse.eval nodeValue4726 (mixedVector B) := by
    change mixedMoment B node4726 node4726Labels = _
    exact sound4726 B hB hF
  have h4727 : mixedVector B (Sum.inr 4727) = Sparse.eval nodeValue4727 (mixedVector B) := by
    change mixedMoment B node4727 node4727Labels = _
    exact sound4727 B hB hF
  have h4736 : mixedVector B (Sum.inr 4736) = Sparse.eval nodeValue4736 (mixedVector B) := by
    change mixedMoment B node4736 node4736Labels = _
    exact sound4736 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4752 : mixedVector B (Sum.inr 4752) = Sparse.eval nodeValue4752 (mixedVector B) := by
    change mixedMoment B node4752 node4752Labels = _
    exact sound4752 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h5015 : mixedVector B (Sum.inr 5015) = Sparse.eval nodeValue5015 (mixedVector B) := by
    change mixedMoment B node5015 node5015Labels = _
    exact sound5015 B hB hF
  have h5056 : mixedVector B (Sum.inr 5056) = Sparse.eval nodeValue5056 (mixedVector B) := by
    change mixedMoment B node5056 node5056Labels = _
    exact sound5056 B hB hF
  have h5095 : mixedVector B (Sum.inr 5095) = Sparse.eval nodeValue5095 (mixedVector B) := by
    change mixedMoment B node5095 node5095Labels = _
    exact sound5095 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  simpa only [sourceForm2308, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4080, h4288, h4295, h4296, h4311, h4404, h4632, h4637, h4638, h4652, h4706, h4707, h4715, h4722, h4726, h4727, h4736, h4737, h4741, h4742, h4752, h4782, h4828, h4834, h4835, h5015, h5056, h5095, h5101, h5102, reducedSource1880] using sourceEq2308 B hB

theorem rowSound1880_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1880 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1880, numericCheck1880, reducedZero1880 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880_e_oai
