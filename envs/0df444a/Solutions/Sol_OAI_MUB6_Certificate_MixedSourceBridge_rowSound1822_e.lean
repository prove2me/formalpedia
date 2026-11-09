-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:49:54.455475+00:00
-- url     : https://prove2.me/submissions/a038e205-8e1d-4521-b455-e31bac164273

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5169_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e

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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
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

theorem canonical1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1506 raw1506Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw1506 raw1506Labels = mixedMoment B raw1506step0 raw1506step0Labels := by
      have ha : raw1506step0 = (fun i j => raw1506 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1506step0 raw1506; decide +kernel
      have hl : raw1506step0Labels = raw1506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1506 raw1506Labels permutation32 permutation4
    mixedMoment B raw1506step0 raw1506step0Labels = mixedMoment B raw1506step1 raw1506step1Labels := by
      have ha : raw1506step1 = raw1506step0 := by apply Matrix.ext; unfold raw1506step1 raw1506step0; decide +kernel
      have hl : raw1506step0Labels = labelEmbedding7 ∘ raw1506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1506step0 raw1506step0Labels raw1506step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

theorem canonical1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1507 raw1507Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw1507 raw1507Labels = mixedMoment B raw1507step0 raw1507step0Labels := by
      have ha : raw1507step0 = (fun i j => raw1507 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1507step0 raw1507; decide +kernel
      have hl : raw1507step0Labels = raw1507Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1507 raw1507Labels permutation32 permutation4
    _ = mixedMoment B node1773 node1773Labels := by rfl

theorem canonical1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1508 raw1508Labels = mixedMoment B node1841 node1841Labels := by
  calc
    mixedMoment B raw1508 raw1508Labels = mixedMoment B raw1508step0 raw1508step0Labels := by
      have ha : raw1508step0 = (fun i j => raw1508 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1508step0 raw1508; decide +kernel
      have hl : raw1508step0Labels = raw1508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1508 raw1508Labels permutation32 permutation6
    mixedMoment B raw1508step0 raw1508step0Labels = mixedMoment B raw1508step1 raw1508step1Labels := by
      have ha : raw1508step1 = -raw1508step0 := by apply Matrix.ext; change ∀ i j, raw1508step1 i j = -(raw1508step0 i j); unfold raw1508step1 raw1508step0; decide +kernel
      have hl : raw1508step1Labels = raw1508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1508step1 raw1508step1Labels = mixedMoment B raw1508step2 raw1508step2Labels := by
      have ha : raw1508step2 = raw1508step1 := by apply Matrix.ext; unfold raw1508step2 raw1508step1; decide +kernel
      have hl : raw1508step1Labels = labelEmbedding1 ∘ raw1508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1508step1 raw1508step1Labels raw1508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1841 node1841Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17096 raw17096Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw17096 raw17096Labels = mixedMoment B raw17096step0 raw17096step0Labels := by
      have hz : ∀ j, raw17096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17096step0 = (fun i j => raw17096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17096step0 raw17096; decide +kernel
      have hl : raw17096step0Labels = raw17096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17096 raw17096Labels permutation346 hz
    mixedMoment B raw17096step0 raw17096step0Labels = mixedMoment B raw17096step1 raw17096step1Labels := by
      have ha : raw17096step1 = (fun i j => raw17096step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17096step1 raw17096step0; decide +kernel
      have hl : raw17096step1Labels = raw17096step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17096step0 raw17096step0Labels permutation126 permutation3
    mixedMoment B raw17096step1 raw17096step1Labels = mixedMoment B raw17096step2 raw17096step2Labels := by
      have ha : raw17096step2 = -raw17096step1 := by apply Matrix.ext; change ∀ i j, raw17096step2 i j = -(raw17096step1 i j); unfold raw17096step2 raw17096step1; decide +kernel
      have hl : raw17096step2Labels = raw17096step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17096step2 raw17096step2Labels = mixedMoment B raw17096step3 raw17096step3Labels := by
      have ha : raw17096step3 = raw17096step2 := by apply Matrix.ext; unfold raw17096step3 raw17096step2; decide +kernel
      have hl : raw17096step2Labels = labelEmbedding6 ∘ raw17096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17096step2 raw17096step2Labels raw17096step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical17097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17097 raw17097Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17097 raw17097Labels = mixedMoment B raw17097step0 raw17097step0Labels := by
      have ha : raw17097step0 = (fun i j => raw17097 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17097step0 raw17097; decide +kernel
      have hl : raw17097step0Labels = raw17097Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17097 raw17097Labels permutation587 permutation3
    mixedMoment B raw17097step0 raw17097step0Labels = mixedMoment B raw17097step1 raw17097step1Labels := by
      have ha : raw17097step1 = -raw17097step0 := by apply Matrix.ext; change ∀ i j, raw17097step1 i j = -(raw17097step0 i j); unfold raw17097step1 raw17097step0; decide +kernel
      have hl : raw17097step1Labels = raw17097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17097step1 raw17097step1Labels = mixedMoment B raw17097step2 raw17097step2Labels := by
      have ha : raw17097step2 = raw17097step1 := by apply Matrix.ext; unfold raw17097step2 raw17097step1; decide +kernel
      have hl : raw17097step1Labels = labelEmbedding6 ∘ raw17097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17097step1 raw17097step1Labels raw17097step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical17098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17098 raw17098Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17098 raw17098Labels = mixedMoment B raw17098step0 raw17098step0Labels := by
      have hz : ∀ j, raw17098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17098step0 = (fun i j => raw17098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17098step0 raw17098; decide +kernel
      have hl : raw17098step0Labels = raw17098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17098 raw17098Labels permutation346 hz
    mixedMoment B raw17098step0 raw17098step0Labels = mixedMoment B raw17098step1 raw17098step1Labels := by
      have ha : raw17098step1 = (fun i j => raw17098step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17098step1 raw17098step0; decide +kernel
      have hl : raw17098step1Labels = raw17098step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17098step0 raw17098step0Labels permutation125 permutation3
    mixedMoment B raw17098step1 raw17098step1Labels = mixedMoment B raw17098step2 raw17098step2Labels := by
      have ha : raw17098step2 = -raw17098step1 := by apply Matrix.ext; change ∀ i j, raw17098step2 i j = -(raw17098step1 i j); unfold raw17098step2 raw17098step1; decide +kernel
      have hl : raw17098step2Labels = raw17098step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17098step2 raw17098step2Labels = mixedMoment B raw17098step3 raw17098step3Labels := by
      have ha : raw17098step3 = raw17098step2 := by apply Matrix.ext; unfold raw17098step3 raw17098step2; decide +kernel
      have hl : raw17098step2Labels = labelEmbedding6 ∘ raw17098step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17098step2 raw17098step2Labels raw17098step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

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

theorem canonical1833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1833 raw1833Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw1833 raw1833Labels = mixedMoment B raw1833step0 raw1833step0Labels := by
      have ha : raw1833step0 = (fun i j => raw1833 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1833step0 raw1833; decide +kernel
      have hl : raw1833step0Labels = raw1833Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1833 raw1833Labels permutation152 permutation4
    mixedMoment B raw1833step0 raw1833step0Labels = mixedMoment B raw1833step1 raw1833step1Labels := by
      have ha : raw1833step1 = raw1833step0 := by apply Matrix.ext; unfold raw1833step1 raw1833step0; decide +kernel
      have hl : raw1833step0Labels = labelEmbedding7 ∘ raw1833step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1833step0 raw1833step0Labels raw1833step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4902 node4902Labels := by rfl

theorem canonical1834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1834 raw1834Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw1834 raw1834Labels = mixedMoment B raw1834step0 raw1834step0Labels := by
      have ha : raw1834step0 = (fun i j => raw1834 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1834step0 raw1834; decide +kernel
      have hl : raw1834step0Labels = raw1834Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1834 raw1834Labels permutation152 permutation4
    _ = mixedMoment B node2295 node2295Labels := by rfl

theorem canonical1835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1835 raw1835Labels = mixedMoment B node3315 node3315Labels := by
  calc
    mixedMoment B raw1835 raw1835Labels = mixedMoment B raw1835step0 raw1835step0Labels := by
      have ha : raw1835step0 = (fun i j => raw1835 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1835step0 raw1835; decide +kernel
      have hl : raw1835step0Labels = raw1835Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1835 raw1835Labels permutation158 permutation6
    mixedMoment B raw1835step0 raw1835step0Labels = mixedMoment B raw1835step1 raw1835step1Labels := by
      have ha : raw1835step1 = -raw1835step0 := by apply Matrix.ext; change ∀ i j, raw1835step1 i j = -(raw1835step0 i j); unfold raw1835step1 raw1835step0; decide +kernel
      have hl : raw1835step1Labels = raw1835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1835step1 raw1835step1Labels = mixedMoment B raw1835step2 raw1835step2Labels := by
      have ha : raw1835step2 = raw1835step1 := by apply Matrix.ext; unfold raw1835step2 raw1835step1; decide +kernel
      have hl : raw1835step1Labels = labelEmbedding1 ∘ raw1835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1835step1 raw1835step1Labels raw1835step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3315 node3315Labels := by rfl

theorem canonical1848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1848 raw1848Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw1848 raw1848Labels = mixedMoment B raw1848step0 raw1848step0Labels := by
      have ha : raw1848step0 = (fun i j => raw1848 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1848step0 raw1848; decide +kernel
      have hl : raw1848step0Labels = raw1848Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1848 raw1848Labels permutation32 permutation4
    mixedMoment B raw1848step0 raw1848step0Labels = mixedMoment B raw1848step1 raw1848step1Labels := by
      have ha : raw1848step1 = raw1848step0 := by apply Matrix.ext; unfold raw1848step1 raw1848step0; decide +kernel
      have hl : raw1848step0Labels = labelEmbedding7 ∘ raw1848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1848step0 raw1848step0Labels raw1848step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

theorem canonical1849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1849 raw1849Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw1849 raw1849Labels = mixedMoment B raw1849step0 raw1849step0Labels := by
      have ha : raw1849step0 = (fun i j => raw1849 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1849step0 raw1849; decide +kernel
      have hl : raw1849step0Labels = raw1849Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1849 raw1849Labels permutation32 permutation4
    _ = mixedMoment B node2300 node2300Labels := by rfl

theorem canonical1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1850 raw1850Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw1850 raw1850Labels = mixedMoment B raw1850step0 raw1850step0Labels := by
      have ha : raw1850step0 = (fun i j => raw1850 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1850step0 raw1850; decide +kernel
      have hl : raw1850step0Labels = raw1850Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1850 raw1850Labels permutation32 permutation6
    mixedMoment B raw1850step0 raw1850step0Labels = mixedMoment B raw1850step1 raw1850step1Labels := by
      have ha : raw1850step1 = -raw1850step0 := by apply Matrix.ext; change ∀ i j, raw1850step1 i j = -(raw1850step0 i j); unfold raw1850step1 raw1850step0; decide +kernel
      have hl : raw1850step1Labels = raw1850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1850step1 raw1850step1Labels = mixedMoment B raw1850step2 raw1850step2Labels := by
      have ha : raw1850step2 = raw1850step1 := by apply Matrix.ext; unfold raw1850step2 raw1850step1; decide +kernel
      have hl : raw1850step1Labels = labelEmbedding1 ∘ raw1850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1850step1 raw1850step1Labels raw1850step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

theorem canonical1863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1863 raw1863Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw1863 raw1863Labels = mixedMoment B raw1863step0 raw1863step0Labels := by
      have ha : raw1863step0 = (fun i j => raw1863 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1863step0 raw1863; decide +kernel
      have hl : raw1863step0Labels = raw1863Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1863 raw1863Labels permutation32 permutation4
    mixedMoment B raw1863step0 raw1863step0Labels = mixedMoment B raw1863step1 raw1863step1Labels := by
      have ha : raw1863step1 = raw1863step0 := by apply Matrix.ext; unfold raw1863step1 raw1863step0; decide +kernel
      have hl : raw1863step0Labels = labelEmbedding7 ∘ raw1863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1863step0 raw1863step0Labels raw1863step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

theorem canonical1864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1864 raw1864Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw1864 raw1864Labels = mixedMoment B raw1864step0 raw1864step0Labels := by
      have ha : raw1864step0 = (fun i j => raw1864 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1864step0 raw1864; decide +kernel
      have hl : raw1864step0Labels = raw1864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1864 raw1864Labels permutation32 permutation4
    _ = mixedMoment B node2306 node2306Labels := by rfl

theorem canonical1865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1865 raw1865Labels = mixedMoment B node3318 node3318Labels := by
  calc
    mixedMoment B raw1865 raw1865Labels = mixedMoment B raw1865step0 raw1865step0Labels := by
      have ha : raw1865step0 = (fun i j => raw1865 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1865step0 raw1865; decide +kernel
      have hl : raw1865step0Labels = raw1865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1865 raw1865Labels permutation32 permutation6
    mixedMoment B raw1865step0 raw1865step0Labels = mixedMoment B raw1865step1 raw1865step1Labels := by
      have ha : raw1865step1 = -raw1865step0 := by apply Matrix.ext; change ∀ i j, raw1865step1 i j = -(raw1865step0 i j); unfold raw1865step1 raw1865step0; decide +kernel
      have hl : raw1865step1Labels = raw1865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1865step1 raw1865step1Labels = mixedMoment B raw1865step2 raw1865step2Labels := by
      have ha : raw1865step2 = raw1865step1 := by apply Matrix.ext; unfold raw1865step2 raw1865step1; decide +kernel
      have hl : raw1865step1Labels = labelEmbedding1 ∘ raw1865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1865step1 raw1865step1Labels raw1865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3318 node3318Labels := by rfl

theorem canonical1893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1893 raw1893Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw1893 raw1893Labels = mixedMoment B raw1893step0 raw1893step0Labels := by
      have ha : raw1893step0 = (fun i j => raw1893 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1893step0 raw1893; decide +kernel
      have hl : raw1893step0Labels = raw1893Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1893 raw1893Labels permutation152 permutation4
    mixedMoment B raw1893step0 raw1893step0Labels = mixedMoment B raw1893step1 raw1893step1Labels := by
      have ha : raw1893step1 = raw1893step0 := by apply Matrix.ext; unfold raw1893step1 raw1893step0; decide +kernel
      have hl : raw1893step0Labels = labelEmbedding7 ∘ raw1893step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1893step0 raw1893step0Labels raw1893step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical1894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1894 raw1894Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw1894 raw1894Labels = mixedMoment B raw1894step0 raw1894step0Labels := by
      have ha : raw1894step0 = (fun i j => raw1894 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1894step0 raw1894; decide +kernel
      have hl : raw1894step0Labels = raw1894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1894 raw1894Labels permutation152 permutation4
    _ = mixedMoment B node2318 node2318Labels := by rfl

theorem canonical1895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1895 raw1895Labels = mixedMoment B node3400 node3400Labels := by
  calc
    mixedMoment B raw1895 raw1895Labels = mixedMoment B raw1895step0 raw1895step0Labels := by
      have ha : raw1895step0 = (fun i j => raw1895 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1895step0 raw1895; decide +kernel
      have hl : raw1895step0Labels = raw1895Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1895 raw1895Labels permutation152 permutation6
    mixedMoment B raw1895step0 raw1895step0Labels = mixedMoment B raw1895step1 raw1895step1Labels := by
      have ha : raw1895step1 = -raw1895step0 := by apply Matrix.ext; change ∀ i j, raw1895step1 i j = -(raw1895step0 i j); unfold raw1895step1 raw1895step0; decide +kernel
      have hl : raw1895step1Labels = raw1895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1895step1 raw1895step1Labels = mixedMoment B raw1895step2 raw1895step2Labels := by
      have ha : raw1895step2 = raw1895step1 := by apply Matrix.ext; unfold raw1895step2 raw1895step1; decide +kernel
      have hl : raw1895step1Labels = labelEmbedding1 ∘ raw1895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1895step1 raw1895step1Labels raw1895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3400 node3400Labels := by rfl

theorem canonical1911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1911 raw1911Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw1911 raw1911Labels = mixedMoment B raw1911step0 raw1911step0Labels := by
      have ha : raw1911step0 = (fun i j => raw1911 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1911step0 raw1911; decide +kernel
      have hl : raw1911step0Labels = raw1911Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1911 raw1911Labels permutation32 permutation4
    mixedMoment B raw1911step0 raw1911step0Labels = mixedMoment B raw1911step1 raw1911step1Labels := by
      have ha : raw1911step1 = raw1911step0 := by apply Matrix.ext; unfold raw1911step1 raw1911step0; decide +kernel
      have hl : raw1911step0Labels = labelEmbedding7 ∘ raw1911step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1911step0 raw1911step0Labels raw1911step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical1912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1912 raw1912Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw1912 raw1912Labels = mixedMoment B raw1912step0 raw1912step0Labels := by
      have ha : raw1912step0 = (fun i j => raw1912 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1912step0 raw1912; decide +kernel
      have hl : raw1912step0Labels = raw1912Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1912 raw1912Labels permutation32 permutation4
    _ = mixedMoment B node2337 node2337Labels := by rfl

theorem canonical1913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1913 raw1913Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw1913 raw1913Labels = mixedMoment B raw1913step0 raw1913step0Labels := by
      have ha : raw1913step0 = (fun i j => raw1913 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1913step0 raw1913; decide +kernel
      have hl : raw1913step0Labels = raw1913Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1913 raw1913Labels permutation32 permutation6
    mixedMoment B raw1913step0 raw1913step0Labels = mixedMoment B raw1913step1 raw1913step1Labels := by
      have ha : raw1913step1 = -raw1913step0 := by apply Matrix.ext; change ∀ i j, raw1913step1 i j = -(raw1913step0 i j); unfold raw1913step1 raw1913step0; decide +kernel
      have hl : raw1913step1Labels = raw1913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1913step1 raw1913step1Labels = mixedMoment B raw1913step2 raw1913step2Labels := by
      have ha : raw1913step2 = raw1913step1 := by apply Matrix.ext; unfold raw1913step2 raw1913step1; decide +kernel
      have hl : raw1913step1Labels = labelEmbedding1 ∘ raw1913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1913step1 raw1913step1Labels raw1913step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

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

theorem canonical1995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1995 raw1995Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw1995 raw1995Labels = mixedMoment B raw1995step0 raw1995step0Labels := by
      have ha : raw1995step0 = (fun i j => raw1995 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1995step0 raw1995; decide +kernel
      have hl : raw1995step0Labels = raw1995Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1995 raw1995Labels permutation152 permutation4
    mixedMoment B raw1995step0 raw1995step0Labels = mixedMoment B raw1995step1 raw1995step1Labels := by
      have ha : raw1995step1 = raw1995step0 := by apply Matrix.ext; unfold raw1995step1 raw1995step0; decide +kernel
      have hl : raw1995step0Labels = labelEmbedding7 ∘ raw1995step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1995step0 raw1995step0Labels raw1995step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1996 raw1996Labels = mixedMoment B node2372 node2372Labels := by
  calc
    mixedMoment B raw1996 raw1996Labels = mixedMoment B raw1996step0 raw1996step0Labels := by
      have ha : raw1996step0 = (fun i j => raw1996 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1996step0 raw1996; decide +kernel
      have hl : raw1996step0Labels = raw1996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1996 raw1996Labels permutation152 permutation4
    _ = mixedMoment B node2372 node2372Labels := by rfl

theorem canonical1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1997 raw1997Labels = mixedMoment B node3336 node3336Labels := by
  calc
    mixedMoment B raw1997 raw1997Labels = mixedMoment B raw1997step0 raw1997step0Labels := by
      have ha : raw1997step0 = (fun i j => raw1997 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1997step0 raw1997; decide +kernel
      have hl : raw1997step0Labels = raw1997Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1997 raw1997Labels permutation152 permutation6
    mixedMoment B raw1997step0 raw1997step0Labels = mixedMoment B raw1997step1 raw1997step1Labels := by
      have ha : raw1997step1 = -raw1997step0 := by apply Matrix.ext; change ∀ i j, raw1997step1 i j = -(raw1997step0 i j); unfold raw1997step1 raw1997step0; decide +kernel
      have hl : raw1997step1Labels = raw1997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1997step1 raw1997step1Labels = mixedMoment B raw1997step2 raw1997step2Labels := by
      have ha : raw1997step2 = raw1997step1 := by apply Matrix.ext; unfold raw1997step2 raw1997step1; decide +kernel
      have hl : raw1997step1Labels = labelEmbedding1 ∘ raw1997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1997step1 raw1997step1Labels raw1997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3336 node3336Labels := by rfl

theorem canonical2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2016 raw2016Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw2016 raw2016Labels = mixedMoment B raw2016step0 raw2016step0Labels := by
      have ha : raw2016step0 = (fun i j => raw2016 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2016step0 raw2016; decide +kernel
      have hl : raw2016step0Labels = raw2016Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2016 raw2016Labels permutation32 permutation4
    mixedMoment B raw2016step0 raw2016step0Labels = mixedMoment B raw2016step1 raw2016step1Labels := by
      have ha : raw2016step1 = raw2016step0 := by apply Matrix.ext; unfold raw2016step1 raw2016step0; decide +kernel
      have hl : raw2016step0Labels = labelEmbedding7 ∘ raw2016step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2016step0 raw2016step0Labels raw2016step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical2017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2017 raw2017Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw2017 raw2017Labels = mixedMoment B raw2017step0 raw2017step0Labels := by
      have ha : raw2017step0 = (fun i j => raw2017 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2017step0 raw2017; decide +kernel
      have hl : raw2017step0Labels = raw2017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2017 raw2017Labels permutation32 permutation4
    _ = mixedMoment B node2388 node2388Labels := by rfl

theorem canonical2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2018 raw2018Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw2018 raw2018Labels = mixedMoment B raw2018step0 raw2018step0Labels := by
      have ha : raw2018step0 = (fun i j => raw2018 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2018step0 raw2018; decide +kernel
      have hl : raw2018step0Labels = raw2018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2018 raw2018Labels permutation32 permutation6
    mixedMoment B raw2018step0 raw2018step0Labels = mixedMoment B raw2018step1 raw2018step1Labels := by
      have ha : raw2018step1 = -raw2018step0 := by apply Matrix.ext; change ∀ i j, raw2018step1 i j = -(raw2018step0 i j); unfold raw2018step1 raw2018step0; decide +kernel
      have hl : raw2018step1Labels = raw2018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2018step1 raw2018step1Labels = mixedMoment B raw2018step2 raw2018step2Labels := by
      have ha : raw2018step2 = raw2018step1 := by apply Matrix.ext; unfold raw2018step2 raw2018step1; decide +kernel
      have hl : raw2018step1Labels = labelEmbedding1 ∘ raw2018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2018step1 raw2018step1Labels raw2018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3354 node3354Labels := by rfl

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

theorem canonical2076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2076 raw2076Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw2076 raw2076Labels = mixedMoment B raw2076step0 raw2076step0Labels := by
      have ha : raw2076step0 = (fun i j => raw2076 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2076step0 raw2076; decide +kernel
      have hl : raw2076step0Labels = raw2076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2076 raw2076Labels permutation152 permutation4
    mixedMoment B raw2076step0 raw2076step0Labels = mixedMoment B raw2076step1 raw2076step1Labels := by
      have ha : raw2076step1 = raw2076step0 := by apply Matrix.ext; unfold raw2076step1 raw2076step0; decide +kernel
      have hl : raw2076step0Labels = labelEmbedding7 ∘ raw2076step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2076step0 raw2076step0Labels raw2076step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

theorem canonical2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2077 raw2077Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw2077 raw2077Labels = mixedMoment B raw2077step0 raw2077step0Labels := by
      have ha : raw2077step0 = (fun i j => raw2077 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2077step0 raw2077; decide +kernel
      have hl : raw2077step0Labels = raw2077Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2077 raw2077Labels permutation152 permutation4
    _ = mixedMoment B node2452 node2452Labels := by rfl

theorem canonical2078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2078 raw2078Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw2078 raw2078Labels = mixedMoment B raw2078step0 raw2078step0Labels := by
      have ha : raw2078step0 = (fun i j => raw2078 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2078step0 raw2078; decide +kernel
      have hl : raw2078step0Labels = raw2078Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2078 raw2078Labels permutation152 permutation6
    mixedMoment B raw2078step0 raw2078step0Labels = mixedMoment B raw2078step1 raw2078step1Labels := by
      have ha : raw2078step1 = -raw2078step0 := by apply Matrix.ext; change ∀ i j, raw2078step1 i j = -(raw2078step0 i j); unfold raw2078step1 raw2078step0; decide +kernel
      have hl : raw2078step1Labels = raw2078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2078step1 raw2078step1Labels = mixedMoment B raw2078step2 raw2078step2Labels := by
      have ha : raw2078step2 = raw2078step1 := by apply Matrix.ext; unfold raw2078step2 raw2078step1; decide +kernel
      have hl : raw2078step1Labels = labelEmbedding1 ∘ raw2078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2078step1 raw2078step1Labels raw2078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3433 node3433Labels := by rfl

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

theorem canonical2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2166 raw2166Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw2166 raw2166Labels = mixedMoment B raw2166step0 raw2166step0Labels := by
      have ha : raw2166step0 = (fun i j => raw2166 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2166step0 raw2166; decide +kernel
      have hl : raw2166step0Labels = raw2166Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2166 raw2166Labels permutation152 permutation4
    mixedMoment B raw2166step0 raw2166step0Labels = mixedMoment B raw2166step1 raw2166step1Labels := by
      have ha : raw2166step1 = raw2166step0 := by apply Matrix.ext; unfold raw2166step1 raw2166step0; decide +kernel
      have hl : raw2166step0Labels = labelEmbedding7 ∘ raw2166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2166step0 raw2166step0Labels raw2166step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2167 raw2167Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw2167 raw2167Labels = mixedMoment B raw2167step0 raw2167step0Labels := by
      have ha : raw2167step0 = (fun i j => raw2167 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2167step0 raw2167; decide +kernel
      have hl : raw2167step0Labels = raw2167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2167 raw2167Labels permutation152 permutation4
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2168 raw2168Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw2168 raw2168Labels = mixedMoment B raw2168step0 raw2168step0Labels := by
      have ha : raw2168step0 = (fun i j => raw2168 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2168step0 raw2168; decide +kernel
      have hl : raw2168step0Labels = raw2168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2168 raw2168Labels permutation176 permutation6
    mixedMoment B raw2168step0 raw2168step0Labels = mixedMoment B raw2168step1 raw2168step1Labels := by
      have ha : raw2168step1 = -raw2168step0 := by apply Matrix.ext; change ∀ i j, raw2168step1 i j = -(raw2168step0 i j); unfold raw2168step1 raw2168step0; decide +kernel
      have hl : raw2168step1Labels = raw2168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2168step1 raw2168step1Labels = mixedMoment B raw2168step2 raw2168step2Labels := by
      have ha : raw2168step2 = raw2168step1 := by apply Matrix.ext; unfold raw2168step2 raw2168step1; decide +kernel
      have hl : raw2168step1Labels = labelEmbedding1 ∘ raw2168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2168step1 raw2168step1Labels raw2168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

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

theorem canonical2394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2394 raw2394Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw2394 raw2394Labels = mixedMoment B raw2394step0 raw2394step0Labels := by
      have ha : raw2394step0 = (fun i j => raw2394 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2394step0 raw2394; decide +kernel
      have hl : raw2394step0Labels = raw2394Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2394 raw2394Labels permutation152 permutation4
    mixedMoment B raw2394step0 raw2394step0Labels = mixedMoment B raw2394step1 raw2394step1Labels := by
      have ha : raw2394step1 = raw2394step0 := by apply Matrix.ext; unfold raw2394step1 raw2394step0; decide +kernel
      have hl : raw2394step0Labels = labelEmbedding7 ∘ raw2394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2394step0 raw2394step0Labels raw2394step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical2395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2395 raw2395Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw2395 raw2395Labels = mixedMoment B raw2395step0 raw2395step0Labels := by
      have ha : raw2395step0 = (fun i j => raw2395 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2395step0 raw2395; decide +kernel
      have hl : raw2395step0Labels = raw2395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2395 raw2395Labels permutation152 permutation4
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical2396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2396 raw2396Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw2396 raw2396Labels = mixedMoment B raw2396step0 raw2396step0Labels := by
      have ha : raw2396step0 = (fun i j => raw2396 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2396step0 raw2396; decide +kernel
      have hl : raw2396step0Labels = raw2396Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2396 raw2396Labels permutation158 permutation6
    mixedMoment B raw2396step0 raw2396step0Labels = mixedMoment B raw2396step1 raw2396step1Labels := by
      have ha : raw2396step1 = -raw2396step0 := by apply Matrix.ext; change ∀ i j, raw2396step1 i j = -(raw2396step0 i j); unfold raw2396step1 raw2396step0; decide +kernel
      have hl : raw2396step1Labels = raw2396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2396step1 raw2396step1Labels = mixedMoment B raw2396step2 raw2396step2Labels := by
      have ha : raw2396step2 = raw2396step1 := by apply Matrix.ext; unfold raw2396step2 raw2396step1; decide +kernel
      have hl : raw2396step1Labels = labelEmbedding1 ∘ raw2396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2396step1 raw2396step1Labels raw2396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

theorem canonical2403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2403 raw2403Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw2403 raw2403Labels = mixedMoment B raw2403step0 raw2403step0Labels := by
      have ha : raw2403step0 = (fun i j => raw2403 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2403step0 raw2403; decide +kernel
      have hl : raw2403step0Labels = raw2403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2403 raw2403Labels permutation32 permutation4
    mixedMoment B raw2403step0 raw2403step0Labels = mixedMoment B raw2403step1 raw2403step1Labels := by
      have ha : raw2403step1 = raw2403step0 := by apply Matrix.ext; unfold raw2403step1 raw2403step0; decide +kernel
      have hl : raw2403step0Labels = labelEmbedding7 ∘ raw2403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2403step0 raw2403step0Labels raw2403step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2404 raw2404Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw2404 raw2404Labels = mixedMoment B raw2404step0 raw2404step0Labels := by
      have ha : raw2404step0 = (fun i j => raw2404 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2404step0 raw2404; decide +kernel
      have hl : raw2404step0Labels = raw2404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2404 raw2404Labels permutation32 permutation4
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical2405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2405 raw2405Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw2405 raw2405Labels = mixedMoment B raw2405step0 raw2405step0Labels := by
      have ha : raw2405step0 = (fun i j => raw2405 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2405step0 raw2405; decide +kernel
      have hl : raw2405step0Labels = raw2405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2405 raw2405Labels permutation32 permutation6
    mixedMoment B raw2405step0 raw2405step0Labels = mixedMoment B raw2405step1 raw2405step1Labels := by
      have ha : raw2405step1 = -raw2405step0 := by apply Matrix.ext; change ∀ i j, raw2405step1 i j = -(raw2405step0 i j); unfold raw2405step1 raw2405step0; decide +kernel
      have hl : raw2405step1Labels = raw2405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2405step1 raw2405step1Labels = mixedMoment B raw2405step2 raw2405step2Labels := by
      have ha : raw2405step2 = raw2405step1 := by apply Matrix.ext; unfold raw2405step2 raw2405step1; decide +kernel
      have hl : raw2405step1Labels = labelEmbedding1 ∘ raw2405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2405step1 raw2405step1Labels raw2405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

theorem canonical2415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2415 raw2415Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw2415 raw2415Labels = mixedMoment B raw2415step0 raw2415step0Labels := by
      have ha : raw2415step0 = (fun i j => raw2415 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2415step0 raw2415; decide +kernel
      have hl : raw2415step0Labels = raw2415Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2415 raw2415Labels permutation32 permutation4
    mixedMoment B raw2415step0 raw2415step0Labels = mixedMoment B raw2415step1 raw2415step1Labels := by
      have ha : raw2415step1 = raw2415step0 := by apply Matrix.ext; unfold raw2415step1 raw2415step0; decide +kernel
      have hl : raw2415step0Labels = labelEmbedding7 ∘ raw2415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2415step0 raw2415step0Labels raw2415step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical2416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2416 raw2416Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw2416 raw2416Labels = mixedMoment B raw2416step0 raw2416step0Labels := by
      have ha : raw2416step0 = (fun i j => raw2416 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2416step0 raw2416; decide +kernel
      have hl : raw2416step0Labels = raw2416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2416 raw2416Labels permutation32 permutation4
    _ = mixedMoment B node3705 node3705Labels := by rfl

theorem canonical2417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2417 raw2417Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw2417 raw2417Labels = mixedMoment B raw2417step0 raw2417step0Labels := by
      have ha : raw2417step0 = (fun i j => raw2417 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2417step0 raw2417; decide +kernel
      have hl : raw2417step0Labels = raw2417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2417 raw2417Labels permutation33 permutation6
    mixedMoment B raw2417step0 raw2417step0Labels = mixedMoment B raw2417step1 raw2417step1Labels := by
      have ha : raw2417step1 = -raw2417step0 := by apply Matrix.ext; change ∀ i j, raw2417step1 i j = -(raw2417step0 i j); unfold raw2417step1 raw2417step0; decide +kernel
      have hl : raw2417step1Labels = raw2417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2417step1 raw2417step1Labels = mixedMoment B raw2417step2 raw2417step2Labels := by
      have ha : raw2417step2 = raw2417step1 := by apply Matrix.ext; unfold raw2417step2 raw2417step1; decide +kernel
      have hl : raw2417step1Labels = labelEmbedding1 ∘ raw2417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2417step1 raw2417step1Labels raw2417step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28772 raw28772Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw28772 raw28772Labels = mixedMoment B raw28772step0 raw28772step0Labels := by
      have hz : ∀ j, raw28772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28772step0 = (fun i j => raw28772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28772step0 raw28772; decide +kernel
      have hl : raw28772step0Labels = raw28772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28772 raw28772Labels permutation346 hz
    mixedMoment B raw28772step0 raw28772step0Labels = mixedMoment B raw28772step1 raw28772step1Labels := by
      have ha : raw28772step1 = (fun i j => raw28772step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28772step1 raw28772step0; decide +kernel
      have hl : raw28772step1Labels = raw28772step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28772step0 raw28772step0Labels permutation32 permutation3
    mixedMoment B raw28772step1 raw28772step1Labels = mixedMoment B raw28772step2 raw28772step2Labels := by
      have ha : raw28772step2 = raw28772step1 := by apply Matrix.ext; unfold raw28772step2 raw28772step1; decide +kernel
      have hl : raw28772step1Labels = labelEmbedding6 ∘ raw28772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28772step1 raw28772step1Labels raw28772step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4325 node4325Labels := by rfl

theorem canonical28773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28773 raw28773Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw28773 raw28773Labels = mixedMoment B raw28773step0 raw28773step0Labels := by
      have hz : ∀ j, raw28773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28773step0 = (fun i j => raw28773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28773step0 raw28773; decide +kernel
      have hl : raw28773step0Labels = raw28773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28773 raw28773Labels permutation346 hz
    mixedMoment B raw28773step0 raw28773step0Labels = mixedMoment B raw28773step1 raw28773step1Labels := by
      have ha : raw28773step1 = (fun i j => raw28773step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28773step1 raw28773step0; decide +kernel
      have hl : raw28773step1Labels = raw28773step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28773step0 raw28773step0Labels permutation151 permutation3
    mixedMoment B raw28773step1 raw28773step1Labels = mixedMoment B raw28773step2 raw28773step2Labels := by
      have ha : raw28773step2 = -raw28773step1 := by apply Matrix.ext; change ∀ i j, raw28773step2 i j = -(raw28773step1 i j); unfold raw28773step2 raw28773step1; decide +kernel
      have hl : raw28773step2Labels = raw28773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28773step2 raw28773step2Labels = mixedMoment B raw28773step3 raw28773step3Labels := by
      have ha : raw28773step3 = raw28773step2 := by apply Matrix.ext; unfold raw28773step3 raw28773step2; decide +kernel
      have hl : raw28773step2Labels = labelEmbedding6 ∘ raw28773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28773step2 raw28773step2Labels raw28773step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

theorem canonical28774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28774 raw28774Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw28774 raw28774Labels = mixedMoment B raw28774step0 raw28774step0Labels := by
      have ha : raw28774step0 = (fun i j => raw28774 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28774step0 raw28774; decide +kernel
      have hl : raw28774step0Labels = raw28774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28774 raw28774Labels permutation686 permutation3
    mixedMoment B raw28774step0 raw28774step0Labels = mixedMoment B raw28774step1 raw28774step1Labels := by
      have ha : raw28774step1 = -raw28774step0 := by apply Matrix.ext; change ∀ i j, raw28774step1 i j = -(raw28774step0 i j); unfold raw28774step1 raw28774step0; decide +kernel
      have hl : raw28774step1Labels = raw28774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28774step1 raw28774step1Labels = mixedMoment B raw28774step2 raw28774step2Labels := by
      have ha : raw28774step2 = raw28774step1 := by apply Matrix.ext; unfold raw28774step2 raw28774step1; decide +kernel
      have hl : raw28774step1Labels = labelEmbedding6 ∘ raw28774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28774step1 raw28774step1Labels raw28774step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4902 node4902Labels := by rfl

theorem canonical28775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28775 raw28775Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw28775 raw28775Labels = mixedMoment B raw28775step0 raw28775step0Labels := by
      have hz : ∀ j, raw28775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28775step0 = (fun i j => raw28775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28775step0 raw28775; decide +kernel
      have hl : raw28775step0Labels = raw28775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28775 raw28775Labels permutation346 hz
    mixedMoment B raw28775step0 raw28775step0Labels = mixedMoment B raw28775step1 raw28775step1Labels := by
      have ha : raw28775step1 = (fun i j => raw28775step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28775step1 raw28775step0; decide +kernel
      have hl : raw28775step1Labels = raw28775step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28775step0 raw28775step0Labels permutation149 permutation3
    mixedMoment B raw28775step1 raw28775step1Labels = mixedMoment B raw28775step2 raw28775step2Labels := by
      have ha : raw28775step2 = -raw28775step1 := by apply Matrix.ext; change ∀ i j, raw28775step2 i j = -(raw28775step1 i j); unfold raw28775step2 raw28775step1; decide +kernel
      have hl : raw28775step2Labels = raw28775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28775step2 raw28775step2Labels = mixedMoment B raw28775step3 raw28775step3Labels := by
      have ha : raw28775step3 = raw28775step2 := by apply Matrix.ext; unfold raw28775step3 raw28775step2; decide +kernel
      have hl : raw28775step2Labels = labelEmbedding6 ∘ raw28775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28775step2 raw28775step2Labels raw28775step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

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

theorem canonical30139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30139 raw30139Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw30139 raw30139Labels = mixedMoment B raw30139step0 raw30139step0Labels := by
      have ha : raw30139step0 = (fun i j => raw30139 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30139step0 raw30139; decide +kernel
      have hl : raw30139step0Labels = raw30139Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30139 raw30139Labels permutation159 permutation3
    mixedMoment B raw30139step0 raw30139step0Labels = mixedMoment B raw30139step1 raw30139step1Labels := by
      have ha : raw30139step1 = raw30139step0 := by apply Matrix.ext; unfold raw30139step1 raw30139step0; decide +kernel
      have hl : raw30139step0Labels = labelEmbedding6 ∘ raw30139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30139step0 raw30139step0Labels raw30139step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical30140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30140 raw30140Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw30140 raw30140Labels = mixedMoment B raw30140step0 raw30140step0Labels := by
      have ha : raw30140step0 = (fun i j => raw30140 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30140step0 raw30140; decide +kernel
      have hl : raw30140step0Labels = raw30140Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30140 raw30140Labels permutation159 permutation3
    mixedMoment B raw30140step0 raw30140step0Labels = mixedMoment B raw30140step1 raw30140step1Labels := by
      have ha : raw30140step1 = raw30140step0 := by apply Matrix.ext; unfold raw30140step1 raw30140step0; decide +kernel
      have hl : raw30140step0Labels = labelEmbedding6 ∘ raw30140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30140step0 raw30140step0Labels raw30140step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

theorem canonical30141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30141 raw30141Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw30141 raw30141Labels = mixedMoment B raw30141step0 raw30141step0Labels := by
      have ha : raw30141step0 = (fun i j => raw30141 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30141step0 raw30141; decide +kernel
      have hl : raw30141step0Labels = raw30141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30141 raw30141Labels permutation201 permutation3
    mixedMoment B raw30141step0 raw30141step0Labels = mixedMoment B raw30141step1 raw30141step1Labels := by
      have ha : raw30141step1 = raw30141step0 := by apply Matrix.ext; unfold raw30141step1 raw30141step0; decide +kernel
      have hl : raw30141step0Labels = labelEmbedding6 ∘ raw30141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30141step0 raw30141step0Labels raw30141step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

theorem canonical30142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30142 raw30142Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw30142 raw30142Labels = mixedMoment B raw30142step0 raw30142step0Labels := by
      have ha : raw30142step0 = (fun i j => raw30142 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30142step0 raw30142; decide +kernel
      have hl : raw30142step0Labels = raw30142Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30142 raw30142Labels permutation162 permutation3
    mixedMoment B raw30142step0 raw30142step0Labels = mixedMoment B raw30142step1 raw30142step1Labels := by
      have ha : raw30142step1 = raw30142step0 := by apply Matrix.ext; unfold raw30142step1 raw30142step0; decide +kernel
      have hl : raw30142step0Labels = labelEmbedding6 ∘ raw30142step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30142step0 raw30142step0Labels raw30142step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical30143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30143 raw30143Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw30143 raw30143Labels = mixedMoment B raw30143step0 raw30143step0Labels := by
      have hz : ∀ j, raw30143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30143step0 = (fun i j => raw30143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30143step0 raw30143; decide +kernel
      have hl : raw30143step0Labels = raw30143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30143 raw30143Labels permutation346 hz
    mixedMoment B raw30143step0 raw30143step0Labels = mixedMoment B raw30143step1 raw30143step1Labels := by
      have ha : raw30143step1 = (fun i j => raw30143step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30143step1 raw30143step0; decide +kernel
      have hl : raw30143step1Labels = raw30143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30143step0 raw30143step0Labels permutation33 permutation3
    mixedMoment B raw30143step1 raw30143step1Labels = mixedMoment B raw30143step2 raw30143step2Labels := by
      have ha : raw30143step2 = raw30143step1 := by apply Matrix.ext; unfold raw30143step2 raw30143step1; decide +kernel
      have hl : raw30143step1Labels = labelEmbedding6 ∘ raw30143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30143step1 raw30143step1Labels raw30143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical30144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30144 raw30144Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw30144 raw30144Labels = mixedMoment B raw30144step0 raw30144step0Labels := by
      have hz : ∀ j, raw30144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30144step0 = (fun i j => raw30144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30144step0 raw30144; decide +kernel
      have hl : raw30144step0Labels = raw30144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30144 raw30144Labels permutation346 hz
    mixedMoment B raw30144step0 raw30144step0Labels = mixedMoment B raw30144step1 raw30144step1Labels := by
      have ha : raw30144step1 = (fun i j => raw30144step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30144step1 raw30144step0; decide +kernel
      have hl : raw30144step1Labels = raw30144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30144step0 raw30144step0Labels permutation33 permutation3
    mixedMoment B raw30144step1 raw30144step1Labels = mixedMoment B raw30144step2 raw30144step2Labels := by
      have ha : raw30144step2 = raw30144step1 := by apply Matrix.ext; unfold raw30144step2 raw30144step1; decide +kernel
      have hl : raw30144step1Labels = labelEmbedding6 ∘ raw30144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30144step1 raw30144step1Labels raw30144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical30145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30145 raw30145Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw30145 raw30145Labels = mixedMoment B raw30145step0 raw30145step0Labels := by
      have ha : raw30145step0 = (fun i j => raw30145 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30145step0 raw30145; decide +kernel
      have hl : raw30145step0Labels = raw30145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30145 raw30145Labels permutation177 permutation3
    mixedMoment B raw30145step0 raw30145step0Labels = mixedMoment B raw30145step1 raw30145step1Labels := by
      have ha : raw30145step1 = raw30145step0 := by apply Matrix.ext; unfold raw30145step1 raw30145step0; decide +kernel
      have hl : raw30145step0Labels = labelEmbedding6 ∘ raw30145step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30145step0 raw30145step0Labels raw30145step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

theorem canonical30146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30146 raw30146Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw30146 raw30146Labels = mixedMoment B raw30146step0 raw30146step0Labels := by
      have hz : ∀ j, raw30146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30146step0 = (fun i j => raw30146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30146step0 raw30146; decide +kernel
      have hl : raw30146step0Labels = raw30146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30146 raw30146Labels permutation346 hz
    mixedMoment B raw30146step0 raw30146step0Labels = mixedMoment B raw30146step1 raw30146step1Labels := by
      have ha : raw30146step1 = (fun i j => raw30146step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30146step1 raw30146step0; decide +kernel
      have hl : raw30146step1Labels = raw30146step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30146step0 raw30146step0Labels permutation33 permutation3
    mixedMoment B raw30146step1 raw30146step1Labels = mixedMoment B raw30146step2 raw30146step2Labels := by
      have ha : raw30146step2 = raw30146step1 := by apply Matrix.ext; unfold raw30146step2 raw30146step1; decide +kernel
      have hl : raw30146step1Labels = labelEmbedding6 ∘ raw30146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30146step1 raw30146step1Labels raw30146step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

theorem canonical30147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30147 raw30147Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw30147 raw30147Labels = mixedMoment B raw30147step0 raw30147step0Labels := by
      have hz : ∀ j, raw30147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30147step0 = (fun i j => raw30147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30147step0 raw30147; decide +kernel
      have hl : raw30147step0Labels = raw30147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30147 raw30147Labels permutation346 hz
    mixedMoment B raw30147step0 raw30147step0Labels = mixedMoment B raw30147step1 raw30147step1Labels := by
      have ha : raw30147step1 = (fun i j => raw30147step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30147step1 raw30147step0; decide +kernel
      have hl : raw30147step1Labels = raw30147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30147step0 raw30147step0Labels permutation33 permutation3
    mixedMoment B raw30147step1 raw30147step1Labels = mixedMoment B raw30147step2 raw30147step2Labels := by
      have ha : raw30147step2 = raw30147step1 := by apply Matrix.ext; unfold raw30147step2 raw30147step1; decide +kernel
      have hl : raw30147step1Labels = labelEmbedding6 ∘ raw30147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30147step1 raw30147step1Labels raw30147step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4324 node4324Labels := by rfl

theorem canonical30148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30148 raw30148Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw30148 raw30148Labels = mixedMoment B raw30148step0 raw30148step0Labels := by
      have hz : ∀ j, raw30148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30148step0 = (fun i j => raw30148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30148step0 raw30148; decide +kernel
      have hl : raw30148step0Labels = raw30148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30148 raw30148Labels permutation346 hz
    mixedMoment B raw30148step0 raw30148step0Labels = mixedMoment B raw30148step1 raw30148step1Labels := by
      have ha : raw30148step1 = (fun i j => raw30148step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30148step1 raw30148step0; decide +kernel
      have hl : raw30148step1Labels = raw30148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30148step0 raw30148step0Labels permutation127 permutation3
    mixedMoment B raw30148step1 raw30148step1Labels = mixedMoment B raw30148step2 raw30148step2Labels := by
      have ha : raw30148step2 = -raw30148step1 := by apply Matrix.ext; change ∀ i j, raw30148step2 i j = -(raw30148step1 i j); unfold raw30148step2 raw30148step1; decide +kernel
      have hl : raw30148step2Labels = raw30148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30148step2 raw30148step2Labels = mixedMoment B raw30148step3 raw30148step3Labels := by
      have ha : raw30148step3 = raw30148step2 := by apply Matrix.ext; unfold raw30148step3 raw30148step2; decide +kernel
      have hl : raw30148step2Labels = labelEmbedding6 ∘ raw30148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30148step2 raw30148step2Labels raw30148step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

theorem canonical30149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30149 raw30149Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw30149 raw30149Labels = mixedMoment B raw30149step0 raw30149step0Labels := by
      have ha : raw30149step0 = (fun i j => raw30149 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30149step0 raw30149; decide +kernel
      have hl : raw30149step0Labels = raw30149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30149 raw30149Labels permutation587 permutation3
    mixedMoment B raw30149step0 raw30149step0Labels = mixedMoment B raw30149step1 raw30149step1Labels := by
      have ha : raw30149step1 = -raw30149step0 := by apply Matrix.ext; change ∀ i j, raw30149step1 i j = -(raw30149step0 i j); unfold raw30149step1 raw30149step0; decide +kernel
      have hl : raw30149step1Labels = raw30149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30149step1 raw30149step1Labels = mixedMoment B raw30149step2 raw30149step2Labels := by
      have ha : raw30149step2 = raw30149step1 := by apply Matrix.ext; unfold raw30149step2 raw30149step1; decide +kernel
      have hl : raw30149step1Labels = labelEmbedding6 ∘ raw30149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30149step1 raw30149step1Labels raw30149step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

theorem canonical30150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30150 raw30150Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw30150 raw30150Labels = mixedMoment B raw30150step0 raw30150step0Labels := by
      have hz : ∀ j, raw30150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30150step0 = (fun i j => raw30150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30150step0 raw30150; decide +kernel
      have hl : raw30150step0Labels = raw30150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30150 raw30150Labels permutation346 hz
    mixedMoment B raw30150step0 raw30150step0Labels = mixedMoment B raw30150step1 raw30150step1Labels := by
      have ha : raw30150step1 = (fun i j => raw30150step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30150step1 raw30150step0; decide +kernel
      have hl : raw30150step1Labels = raw30150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30150step0 raw30150step0Labels permutation125 permutation3
    mixedMoment B raw30150step1 raw30150step1Labels = mixedMoment B raw30150step2 raw30150step2Labels := by
      have ha : raw30150step2 = -raw30150step1 := by apply Matrix.ext; change ∀ i j, raw30150step2 i j = -(raw30150step1 i j); unfold raw30150step2 raw30150step1; decide +kernel
      have hl : raw30150step2Labels = raw30150step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30150step2 raw30150step2Labels = mixedMoment B raw30150step3 raw30150step3Labels := by
      have ha : raw30150step3 = raw30150step2 := by apply Matrix.ext; unfold raw30150step3 raw30150step2; decide +kernel
      have hl : raw30150step2Labels = labelEmbedding6 ∘ raw30150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30150step2 raw30150step2Labels raw30150step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

theorem canonical30151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30151 raw30151Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw30151 raw30151Labels = mixedMoment B raw30151step0 raw30151step0Labels := by
      have hz : ∀ j, raw30151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30151step0 = (fun i j => raw30151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30151step0 raw30151; decide +kernel
      have hl : raw30151step0Labels = raw30151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30151 raw30151Labels permutation346 hz
    mixedMoment B raw30151step0 raw30151step0Labels = mixedMoment B raw30151step1 raw30151step1Labels := by
      have ha : raw30151step1 = (fun i j => raw30151step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30151step1 raw30151step0; decide +kernel
      have hl : raw30151step1Labels = raw30151step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30151step0 raw30151step0Labels permutation127 permutation3
    mixedMoment B raw30151step1 raw30151step1Labels = mixedMoment B raw30151step2 raw30151step2Labels := by
      have ha : raw30151step2 = -raw30151step1 := by apply Matrix.ext; change ∀ i j, raw30151step2 i j = -(raw30151step1 i j); unfold raw30151step2 raw30151step1; decide +kernel
      have hl : raw30151step2Labels = raw30151step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30151step2 raw30151step2Labels = mixedMoment B raw30151step3 raw30151step3Labels := by
      have ha : raw30151step3 = raw30151step2 := by apply Matrix.ext; unfold raw30151step3 raw30151step2; decide +kernel
      have hl : raw30151step2Labels = labelEmbedding6 ∘ raw30151step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30151step2 raw30151step2Labels raw30151step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3139 raw3139Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw3139 raw3139Labels = mixedMoment B raw3139step0 raw3139step0Labels := by
      have hz : ∀ j, raw3139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3139step0 = (fun i j => raw3139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3139step0 raw3139; decide +kernel
      have hl : raw3139step0Labels = raw3139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3139 raw3139Labels permutation346 hz
    mixedMoment B raw3139step0 raw3139step0Labels = mixedMoment B raw3139step1 raw3139step1Labels := by
      have ha : raw3139step1 = (fun i j => raw3139step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3139step1 raw3139step0; decide +kernel
      have hl : raw3139step1Labels = raw3139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3139step0 raw3139step0Labels permutation39 permutation3
    mixedMoment B raw3139step1 raw3139step1Labels = mixedMoment B raw3139step2 raw3139step2Labels := by
      have ha : raw3139step2 = raw3139step1 := by apply Matrix.ext; unfold raw3139step2 raw3139step1; decide +kernel
      have hl : raw3139step1Labels = labelEmbedding6 ∘ raw3139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3139step1 raw3139step1Labels raw3139step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical3140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3140 raw3140Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3140 raw3140Labels = mixedMoment B raw3140step0 raw3140step0Labels := by
      have hz : ∀ j, raw3140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3140step0 = (fun i j => raw3140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3140step0 raw3140; decide +kernel
      have hl : raw3140step0Labels = raw3140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3140 raw3140Labels permutation346 hz
    mixedMoment B raw3140step0 raw3140step0Labels = mixedMoment B raw3140step1 raw3140step1Labels := by
      have ha : raw3140step1 = (fun i j => raw3140step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3140step1 raw3140step0; decide +kernel
      have hl : raw3140step1Labels = raw3140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3140step0 raw3140step0Labels permutation127 permutation3
    mixedMoment B raw3140step1 raw3140step1Labels = mixedMoment B raw3140step2 raw3140step2Labels := by
      have ha : raw3140step2 = -raw3140step1 := by apply Matrix.ext; change ∀ i j, raw3140step2 i j = -(raw3140step1 i j); unfold raw3140step2 raw3140step1; decide +kernel
      have hl : raw3140step2Labels = raw3140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3140step2 raw3140step2Labels = mixedMoment B raw3140step3 raw3140step3Labels := by
      have ha : raw3140step3 = raw3140step2 := by apply Matrix.ext; unfold raw3140step3 raw3140step2; decide +kernel
      have hl : raw3140step2Labels = labelEmbedding6 ∘ raw3140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3140step2 raw3140step2Labels raw3140step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical3144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3144 raw3144Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw3144 raw3144Labels = mixedMoment B raw3144step0 raw3144step0Labels := by
      have hz : ∀ j, raw3144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3144step0 = (fun i j => raw3144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3144step0 raw3144; decide +kernel
      have hl : raw3144step0Labels = raw3144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3144 raw3144Labels permutation346 hz
    mixedMoment B raw3144step0 raw3144step0Labels = mixedMoment B raw3144step1 raw3144step1Labels := by
      have ha : raw3144step1 = (fun i j => raw3144step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3144step1 raw3144step0; decide +kernel
      have hl : raw3144step1Labels = raw3144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3144step0 raw3144step0Labels permutation38 permutation3
    mixedMoment B raw3144step1 raw3144step1Labels = mixedMoment B raw3144step2 raw3144step2Labels := by
      have ha : raw3144step2 = raw3144step1 := by apply Matrix.ext; unfold raw3144step2 raw3144step1; decide +kernel
      have hl : raw3144step1Labels = labelEmbedding6 ∘ raw3144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3144step1 raw3144step1Labels raw3144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical3145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3145 raw3145Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3145 raw3145Labels = mixedMoment B raw3145step0 raw3145step0Labels := by
      have hz : ∀ j, raw3145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3145step0 = (fun i j => raw3145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3145step0 raw3145; decide +kernel
      have hl : raw3145step0Labels = raw3145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3145 raw3145Labels permutation346 hz
    _ = mixedMoment B node5483 node5483Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9853 raw9853Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw9853 raw9853Labels = mixedMoment B raw9853step0 raw9853step0Labels := by
      have ha : raw9853step0 = (fun i j => raw9853 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9853step0 raw9853; decide +kernel
      have hl : raw9853step0Labels = raw9853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9853 raw9853Labels permutation158 permutation3
    mixedMoment B raw9853step0 raw9853step0Labels = mixedMoment B raw9853step1 raw9853step1Labels := by
      have ha : raw9853step1 = raw9853step0 := by apply Matrix.ext; unfold raw9853step1 raw9853step0; decide +kernel
      have hl : raw9853step0Labels = labelEmbedding6 ∘ raw9853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9853step0 raw9853step0Labels raw9853step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9857 raw9857Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw9857 raw9857Labels = mixedMoment B raw9857step0 raw9857step0Labels := by
      have hz : ∀ j, raw9857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9857step0 = (fun i j => raw9857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9857step0 raw9857; decide +kernel
      have hl : raw9857step0Labels = raw9857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9857 raw9857Labels permutation346 hz
    mixedMoment B raw9857step0 raw9857step0Labels = mixedMoment B raw9857step1 raw9857step1Labels := by
      have ha : raw9857step1 = (fun i j => raw9857step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9857step1 raw9857step0; decide +kernel
      have hl : raw9857step1Labels = raw9857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9857step0 raw9857step0Labels permutation32 permutation3
    mixedMoment B raw9857step1 raw9857step1Labels = mixedMoment B raw9857step2 raw9857step2Labels := by
      have ha : raw9857step2 = raw9857step1 := by apply Matrix.ext; unfold raw9857step2 raw9857step1; decide +kernel
      have hl : raw9857step1Labels = labelEmbedding6 ∘ raw9857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9857step1 raw9857step1Labels raw9857step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

theorem canonical9860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9860 raw9860Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw9860 raw9860Labels = mixedMoment B raw9860step0 raw9860step0Labels := by
      have hz : ∀ j, raw9860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9860step0 = (fun i j => raw9860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9860step0 raw9860; decide +kernel
      have hl : raw9860step0Labels = raw9860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9860 raw9860Labels permutation346 hz
    mixedMoment B raw9860step0 raw9860step0Labels = mixedMoment B raw9860step1 raw9860step1Labels := by
      have ha : raw9860step1 = (fun i j => raw9860step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9860step1 raw9860step0; decide +kernel
      have hl : raw9860step1Labels = raw9860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9860step0 raw9860step0Labels permutation39 permutation3
    mixedMoment B raw9860step1 raw9860step1Labels = mixedMoment B raw9860step2 raw9860step2Labels := by
      have ha : raw9860step2 = raw9860step1 := by apply Matrix.ext; unfold raw9860step2 raw9860step1; decide +kernel
      have hl : raw9860step1Labels = labelEmbedding6 ∘ raw9860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9860step1 raw9860step1Labels raw9860step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

theorem canonical9862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9862 raw9862Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw9862 raw9862Labels = mixedMoment B raw9862step0 raw9862step0Labels := by
      have ha : raw9862step0 = (fun i j => raw9862 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9862step0 raw9862; decide +kernel
      have hl : raw9862step0Labels = raw9862Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9862 raw9862Labels permutation183 permutation3
    mixedMoment B raw9862step0 raw9862step0Labels = mixedMoment B raw9862step1 raw9862step1Labels := by
      have ha : raw9862step1 = raw9862step0 := by apply Matrix.ext; unfold raw9862step1 raw9862step0; decide +kernel
      have hl : raw9862step0Labels = labelEmbedding6 ∘ raw9862step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9862step0 raw9862step0Labels raw9862step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

theorem canonical9863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9863 raw9863Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw9863 raw9863Labels = mixedMoment B raw9863step0 raw9863step0Labels := by
      have hz : ∀ j, raw9863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9863step0 = (fun i j => raw9863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9863step0 raw9863; decide +kernel
      have hl : raw9863step0Labels = raw9863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9863 raw9863Labels permutation346 hz
    mixedMoment B raw9863step0 raw9863step0Labels = mixedMoment B raw9863step1 raw9863step1Labels := by
      have ha : raw9863step1 = (fun i j => raw9863step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9863step1 raw9863step0; decide +kernel
      have hl : raw9863step1Labels = raw9863step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9863step0 raw9863step0Labels permutation39 permutation3
    mixedMoment B raw9863step1 raw9863step1Labels = mixedMoment B raw9863step2 raw9863step2Labels := by
      have ha : raw9863step2 = raw9863step1 := by apply Matrix.ext; unfold raw9863step2 raw9863step1; decide +kernel
      have hl : raw9863step1Labels = labelEmbedding6 ∘ raw9863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9863step1 raw9863step1Labels raw9863step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical9865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9865 raw9865Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw9865 raw9865Labels = mixedMoment B raw9865step0 raw9865step0Labels := by
      have hz : ∀ j, raw9865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9865step0 = (fun i j => raw9865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9865step0 raw9865; decide +kernel
      have hl : raw9865step0Labels = raw9865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9865 raw9865Labels permutation346 hz
    mixedMoment B raw9865step0 raw9865step0Labels = mixedMoment B raw9865step1 raw9865step1Labels := by
      have ha : raw9865step1 = (fun i j => raw9865step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9865step1 raw9865step0; decide +kernel
      have hl : raw9865step1Labels = raw9865step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9865step0 raw9865step0Labels permutation151 permutation3
    mixedMoment B raw9865step1 raw9865step1Labels = mixedMoment B raw9865step2 raw9865step2Labels := by
      have ha : raw9865step2 = -raw9865step1 := by apply Matrix.ext; change ∀ i j, raw9865step2 i j = -(raw9865step1 i j); unfold raw9865step2 raw9865step1; decide +kernel
      have hl : raw9865step2Labels = raw9865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9865step2 raw9865step2Labels = mixedMoment B raw9865step3 raw9865step3Labels := by
      have ha : raw9865step3 = raw9865step2 := by apply Matrix.ext; unfold raw9865step3 raw9865step2; decide +kernel
      have hl : raw9865step2Labels = labelEmbedding6 ∘ raw9865step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9865step2 raw9865step2Labels raw9865step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

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

theorem canonical1104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1104 raw1104Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw1104 raw1104Labels = mixedMoment B raw1104step0 raw1104step0Labels := by
      have ha : raw1104step0 = (fun i j => raw1104 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1104step0 raw1104; decide +kernel
      have hl : raw1104step0Labels = raw1104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1104 raw1104Labels permutation152 permutation4
    mixedMoment B raw1104step0 raw1104step0Labels = mixedMoment B raw1104step1 raw1104step1Labels := by
      have ha : raw1104step1 = raw1104step0 := by apply Matrix.ext; unfold raw1104step1 raw1104step0; decide +kernel
      have hl : raw1104step0Labels = labelEmbedding7 ∘ raw1104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1104step0 raw1104step0Labels raw1104step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical1105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1105 raw1105Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw1105 raw1105Labels = mixedMoment B raw1105step0 raw1105step0Labels := by
      have ha : raw1105step0 = (fun i j => raw1105 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1105step0 raw1105; decide +kernel
      have hl : raw1105step0Labels = raw1105Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1105 raw1105Labels permutation152 permutation4
    _ = mixedMoment B node901 node901Labels := by rfl

theorem canonical1106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1106 raw1106Labels = mixedMoment B node1589 node1589Labels := by
  calc
    mixedMoment B raw1106 raw1106Labels = mixedMoment B raw1106step0 raw1106step0Labels := by
      have ha : raw1106step0 = (fun i j => raw1106 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1106step0 raw1106; decide +kernel
      have hl : raw1106step0Labels = raw1106Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1106 raw1106Labels permutation176 permutation6
    mixedMoment B raw1106step0 raw1106step0Labels = mixedMoment B raw1106step1 raw1106step1Labels := by
      have ha : raw1106step1 = -raw1106step0 := by apply Matrix.ext; change ∀ i j, raw1106step1 i j = -(raw1106step0 i j); unfold raw1106step1 raw1106step0; decide +kernel
      have hl : raw1106step1Labels = raw1106step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1106step1 raw1106step1Labels = mixedMoment B raw1106step2 raw1106step2Labels := by
      have ha : raw1106step2 = raw1106step1 := by apply Matrix.ext; unfold raw1106step2 raw1106step1; decide +kernel
      have hl : raw1106step1Labels = labelEmbedding1 ∘ raw1106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1106step1 raw1106step1Labels raw1106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1589 node1589Labels := by rfl

theorem canonical1107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1107 raw1107Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw1107 raw1107Labels = mixedMoment B raw1107step0 raw1107step0Labels := by
      have ha : raw1107step0 = (fun i j => raw1107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1107step0 raw1107; decide +kernel
      have hl : raw1107step0Labels = raw1107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1107 raw1107Labels permutation32 permutation4
    mixedMoment B raw1107step0 raw1107step0Labels = mixedMoment B raw1107step1 raw1107step1Labels := by
      have ha : raw1107step1 = raw1107step0 := by apply Matrix.ext; unfold raw1107step1 raw1107step0; decide +kernel
      have hl : raw1107step0Labels = labelEmbedding7 ∘ raw1107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1107step0 raw1107step0Labels raw1107step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4324 node4324Labels := by rfl

theorem canonical1108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1108 raw1108Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw1108 raw1108Labels = mixedMoment B raw1108step0 raw1108step0Labels := by
      have ha : raw1108step0 = (fun i j => raw1108 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1108step0 raw1108; decide +kernel
      have hl : raw1108step0Labels = raw1108Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1108 raw1108Labels permutation32 permutation4
    _ = mixedMoment B node902 node902Labels := by rfl

theorem canonical1109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1109 raw1109Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw1109 raw1109Labels = mixedMoment B raw1109step0 raw1109step0Labels := by
      have ha : raw1109step0 = (fun i j => raw1109 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1109step0 raw1109; decide +kernel
      have hl : raw1109step0Labels = raw1109Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1109 raw1109Labels permutation38 permutation6
    mixedMoment B raw1109step0 raw1109step0Labels = mixedMoment B raw1109step1 raw1109step1Labels := by
      have ha : raw1109step1 = -raw1109step0 := by apply Matrix.ext; change ∀ i j, raw1109step1 i j = -(raw1109step0 i j); unfold raw1109step1 raw1109step0; decide +kernel
      have hl : raw1109step1Labels = raw1109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1109step1 raw1109step1Labels = mixedMoment B raw1109step2 raw1109step2Labels := by
      have ha : raw1109step2 = raw1109step1 := by apply Matrix.ext; unfold raw1109step2 raw1109step1; decide +kernel
      have hl : raw1109step1Labels = labelEmbedding1 ∘ raw1109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1109step1 raw1109step1Labels raw1109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

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

theorem canonical1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1134 raw1134Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw1134 raw1134Labels = mixedMoment B raw1134step0 raw1134step0Labels := by
      have ha : raw1134step0 = (fun i j => raw1134 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1134step0 raw1134; decide +kernel
      have hl : raw1134step0Labels = raw1134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1134 raw1134Labels permutation32 permutation4
    mixedMoment B raw1134step0 raw1134step0Labels = mixedMoment B raw1134step1 raw1134step1Labels := by
      have ha : raw1134step1 = raw1134step0 := by apply Matrix.ext; unfold raw1134step1 raw1134step0; decide +kernel
      have hl : raw1134step0Labels = labelEmbedding7 ∘ raw1134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1134step0 raw1134step0Labels raw1134step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1135 raw1135Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw1135 raw1135Labels = mixedMoment B raw1135step0 raw1135step0Labels := by
      have ha : raw1135step0 = (fun i j => raw1135 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1135step0 raw1135; decide +kernel
      have hl : raw1135step0Labels = raw1135Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1135 raw1135Labels permutation32 permutation4
    _ = mixedMoment B node927 node927Labels := by rfl

theorem canonical1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1136 raw1136Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw1136 raw1136Labels = mixedMoment B raw1136step0 raw1136step0Labels := by
      have ha : raw1136step0 = (fun i j => raw1136 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1136step0 raw1136; decide +kernel
      have hl : raw1136step0Labels = raw1136Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1136 raw1136Labels permutation32 permutation6
    mixedMoment B raw1136step0 raw1136step0Labels = mixedMoment B raw1136step1 raw1136step1Labels := by
      have ha : raw1136step1 = -raw1136step0 := by apply Matrix.ext; change ∀ i j, raw1136step1 i j = -(raw1136step0 i j); unfold raw1136step1 raw1136step0; decide +kernel
      have hl : raw1136step1Labels = raw1136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1136step1 raw1136step1Labels = mixedMoment B raw1136step2 raw1136step2Labels := by
      have ha : raw1136step2 = raw1136step1 := by apply Matrix.ext; unfold raw1136step2 raw1136step1; decide +kernel
      have hl : raw1136step1Labels = labelEmbedding1 ∘ raw1136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1136step1 raw1136step1Labels raw1136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

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

theorem singleton4323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4323 node4323Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node901 node901Labels + mixedMoment B node1589 node1589Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1104 singletonSmall4323
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4323) = raw1104Labels := by decide +kernel
  rw [hl, canonical1104 B hB] at h
  have hc0 : mixedMoment B raw1104 (Fin.cases (0 : Fin 2) singletonSmall4323) =
      mixedMoment B node901 node901Labels := by
    have ha : raw1104 = raw1105 := by apply Matrix.ext; unfold raw1104 raw1105; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4323 = raw1105Labels := by decide +kernel
    rw [ha, hj, canonical1105 B hB]
  have hc1 : mixedMoment B raw1104 (Fin.cases (1 : Fin 2) singletonSmall4323) =
      mixedMoment B node1589 node1589Labels := by
    have ha : raw1104 = raw1106 := by apply Matrix.ext; unfold raw1104 raw1106; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4323 = raw1106Labels := by decide +kernel
    rw [ha, hj, canonical1106 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4324 node4324Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node902 node902Labels + mixedMoment B node1590 node1590Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1107 singletonSmall4324
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4324) = raw1107Labels := by decide +kernel
  rw [hl, canonical1107 B hB] at h
  have hc0 : mixedMoment B raw1107 (Fin.cases (0 : Fin 2) singletonSmall4324) =
      mixedMoment B node902 node902Labels := by
    have ha : raw1107 = raw1108 := by apply Matrix.ext; unfold raw1107 raw1108; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4324 = raw1108Labels := by decide +kernel
    rw [ha, hj, canonical1108 B hB]
  have hc1 : mixedMoment B raw1107 (Fin.cases (1 : Fin 2) singletonSmall4324) =
      mixedMoment B node1590 node1590Labels := by
    have ha : raw1107 = raw1109 := by apply Matrix.ext; unfold raw1107 raw1109; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4324 = raw1109Labels := by decide +kernel
    rw [ha, hj, canonical1109 B hB]
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

theorem singleton4349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4349 node4349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node927 node927Labels + mixedMoment B node1675 node1675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1134 singletonSmall4349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4349) = raw1134Labels := by decide +kernel
  rw [hl, canonical1134 B hB] at h
  have hc0 : mixedMoment B raw1134 (Fin.cases (0 : Fin 2) singletonSmall4349) =
      mixedMoment B node927 node927Labels := by
    have ha : raw1134 = raw1135 := by apply Matrix.ext; unfold raw1134 raw1135; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4349 = raw1135Labels := by decide +kernel
    rw [ha, hj, canonical1135 B hB]
  have hc1 : mixedMoment B raw1134 (Fin.cases (1 : Fin 2) singletonSmall4349) =
      mixedMoment B node1675 node1675Labels := by
    have ha : raw1134 = raw1136 := by apply Matrix.ext; unfold raw1134 raw1136; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4349 = raw1136Labels := by decide +kernel
    rw [ha, hj, canonical1136 B hB]
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

theorem singleton4644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4644 node4644Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1773 node1773Labels + mixedMoment B node1841 node1841Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1506 singletonSmall4644
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4644) = raw1506Labels := by decide +kernel
  rw [hl, canonical1506 B hB] at h
  have hc0 : mixedMoment B raw1506 (Fin.cases (0 : Fin 2) singletonSmall4644) =
      mixedMoment B node1773 node1773Labels := by
    have ha : raw1506 = raw1507 := by apply Matrix.ext; unfold raw1506 raw1507; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4644 = raw1507Labels := by decide +kernel
    rw [ha, hj, canonical1507 B hB]
  have hc1 : mixedMoment B raw1506 (Fin.cases (1 : Fin 2) singletonSmall4644) =
      mixedMoment B node1841 node1841Labels := by
    have ha : raw1506 = raw1508 := by apply Matrix.ext; unfold raw1506 raw1508; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4644 = raw1508Labels := by decide +kernel
    rw [ha, hj, canonical1508 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4902 node4902Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2295 node2295Labels + mixedMoment B node3315 node3315Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1833 singletonSmall4902
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4902) = raw1833Labels := by decide +kernel
  rw [hl, canonical1833 B hB] at h
  have hc0 : mixedMoment B raw1833 (Fin.cases (0 : Fin 2) singletonSmall4902) =
      mixedMoment B node2295 node2295Labels := by
    have ha : raw1833 = raw1834 := by apply Matrix.ext; unfold raw1833 raw1834; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4902 = raw1834Labels := by decide +kernel
    rw [ha, hj, canonical1834 B hB]
  have hc1 : mixedMoment B raw1833 (Fin.cases (1 : Fin 2) singletonSmall4902) =
      mixedMoment B node3315 node3315Labels := by
    have ha : raw1833 = raw1835 := by apply Matrix.ext; unfold raw1833 raw1835; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4902 = raw1835Labels := by decide +kernel
    rw [ha, hj, canonical1835 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4907 node4907Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2300 node2300Labels + mixedMoment B node3325 node3325Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1848 singletonSmall4907
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4907) = raw1848Labels := by decide +kernel
  rw [hl, canonical1848 B hB] at h
  have hc0 : mixedMoment B raw1848 (Fin.cases (0 : Fin 2) singletonSmall4907) =
      mixedMoment B node2300 node2300Labels := by
    have ha : raw1848 = raw1849 := by apply Matrix.ext; unfold raw1848 raw1849; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4907 = raw1849Labels := by decide +kernel
    rw [ha, hj, canonical1849 B hB]
  have hc1 : mixedMoment B raw1848 (Fin.cases (1 : Fin 2) singletonSmall4907) =
      mixedMoment B node3325 node3325Labels := by
    have ha : raw1848 = raw1850 := by apply Matrix.ext; unfold raw1848 raw1850; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4907 = raw1850Labels := by decide +kernel
    rw [ha, hj, canonical1850 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4913 node4913Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2306 node2306Labels + mixedMoment B node3318 node3318Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1863 singletonSmall4913
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4913) = raw1863Labels := by decide +kernel
  rw [hl, canonical1863 B hB] at h
  have hc0 : mixedMoment B raw1863 (Fin.cases (0 : Fin 2) singletonSmall4913) =
      mixedMoment B node2306 node2306Labels := by
    have ha : raw1863 = raw1864 := by apply Matrix.ext; unfold raw1863 raw1864; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4913 = raw1864Labels := by decide +kernel
    rw [ha, hj, canonical1864 B hB]
  have hc1 : mixedMoment B raw1863 (Fin.cases (1 : Fin 2) singletonSmall4913) =
      mixedMoment B node3318 node3318Labels := by
    have ha : raw1863 = raw1865 := by apply Matrix.ext; unfold raw1863 raw1865; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4913 = raw1865Labels := by decide +kernel
    rw [ha, hj, canonical1865 B hB]
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

theorem singleton4928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4928 node4928Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2318 node2318Labels + mixedMoment B node3400 node3400Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1893 singletonSmall4928
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4928) = raw1893Labels := by decide +kernel
  rw [hl, canonical1893 B hB] at h
  have hc0 : mixedMoment B raw1893 (Fin.cases (0 : Fin 2) singletonSmall4928) =
      mixedMoment B node2318 node2318Labels := by
    have ha : raw1893 = raw1894 := by apply Matrix.ext; unfold raw1893 raw1894; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4928 = raw1894Labels := by decide +kernel
    rw [ha, hj, canonical1894 B hB]
  have hc1 : mixedMoment B raw1893 (Fin.cases (1 : Fin 2) singletonSmall4928) =
      mixedMoment B node3400 node3400Labels := by
    have ha : raw1893 = raw1895 := by apply Matrix.ext; unfold raw1893 raw1895; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4928 = raw1895Labels := by decide +kernel
    rw [ha, hj, canonical1895 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4946 node4946Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2337 node2337Labels + mixedMoment B node3412 node3412Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1911 singletonSmall4946
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4946) = raw1911Labels := by decide +kernel
  rw [hl, canonical1911 B hB] at h
  have hc0 : mixedMoment B raw1911 (Fin.cases (0 : Fin 2) singletonSmall4946) =
      mixedMoment B node2337 node2337Labels := by
    have ha : raw1911 = raw1912 := by apply Matrix.ext; unfold raw1911 raw1912; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4946 = raw1912Labels := by decide +kernel
    rw [ha, hj, canonical1912 B hB]
  have hc1 : mixedMoment B raw1911 (Fin.cases (1 : Fin 2) singletonSmall4946) =
      mixedMoment B node3412 node3412Labels := by
    have ha : raw1911 = raw1913 := by apply Matrix.ext; unfold raw1911 raw1913; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4946 = raw1913Labels := by decide +kernel
    rw [ha, hj, canonical1913 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4987 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4987 node4987Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2372 node2372Labels + mixedMoment B node3336 node3336Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1995 singletonSmall4987
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4987) = raw1995Labels := by decide +kernel
  rw [hl, canonical1995 B hB] at h
  have hc0 : mixedMoment B raw1995 (Fin.cases (0 : Fin 2) singletonSmall4987) =
      mixedMoment B node2372 node2372Labels := by
    have ha : raw1995 = raw1996 := by apply Matrix.ext; unfold raw1995 raw1996; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4987 = raw1996Labels := by decide +kernel
    rw [ha, hj, canonical1996 B hB]
  have hc1 : mixedMoment B raw1995 (Fin.cases (1 : Fin 2) singletonSmall4987) =
      mixedMoment B node3336 node3336Labels := by
    have ha : raw1995 = raw1997 := by apply Matrix.ext; unfold raw1995 raw1997; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4987 = raw1997Labels := by decide +kernel
    rw [ha, hj, canonical1997 B hB]
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

theorem singleton5003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5003 node5003Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2388 node2388Labels + mixedMoment B node3354 node3354Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2016 singletonSmall5003
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5003) = raw2016Labels := by decide +kernel
  rw [hl, canonical2016 B hB] at h
  have hc0 : mixedMoment B raw2016 (Fin.cases (0 : Fin 2) singletonSmall5003) =
      mixedMoment B node2388 node2388Labels := by
    have ha : raw2016 = raw2017 := by apply Matrix.ext; unfold raw2016 raw2017; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5003 = raw2017Labels := by decide +kernel
    rw [ha, hj, canonical2017 B hB]
  have hc1 : mixedMoment B raw2016 (Fin.cases (1 : Fin 2) singletonSmall5003) =
      mixedMoment B node3354 node3354Labels := by
    have ha : raw2016 = raw2018 := by apply Matrix.ext; unfold raw2016 raw2018; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5003 = raw2018Labels := by decide +kernel
    rw [ha, hj, canonical2018 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5050 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5050 node5050Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2452 node2452Labels + mixedMoment B node3433 node3433Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2076 singletonSmall5050
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5050) = raw2076Labels := by decide +kernel
  rw [hl, canonical2076 B hB] at h
  have hc0 : mixedMoment B raw2076 (Fin.cases (0 : Fin 2) singletonSmall5050) =
      mixedMoment B node2452 node2452Labels := by
    have ha : raw2076 = raw2077 := by apply Matrix.ext; unfold raw2076 raw2077; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5050 = raw2077Labels := by decide +kernel
    rw [ha, hj, canonical2077 B hB]
  have hc1 : mixedMoment B raw2076 (Fin.cases (1 : Fin 2) singletonSmall5050) =
      mixedMoment B node3433 node3433Labels := by
    have ha : raw2076 = raw2078 := by apply Matrix.ext; unfold raw2076 raw2078; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5050 = raw2078Labels := by decide +kernel
    rw [ha, hj, canonical2078 B hB]
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

theorem singleton5137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5137 node5137Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2556 node2556Labels + mixedMoment B node3521 node3521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2166 singletonSmall5137
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5137) = raw2166Labels := by decide +kernel
  rw [hl, canonical2166 B hB] at h
  have hc0 : mixedMoment B raw2166 (Fin.cases (0 : Fin 2) singletonSmall5137) =
      mixedMoment B node2556 node2556Labels := by
    have ha : raw2166 = raw2167 := by apply Matrix.ext; unfold raw2166 raw2167; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5137 = raw2167Labels := by decide +kernel
    rw [ha, hj, canonical2167 B hB]
  have hc1 : mixedMoment B raw2166 (Fin.cases (1 : Fin 2) singletonSmall5137) =
      mixedMoment B node3521 node3521Labels := by
    have ha : raw2166 = raw2168 := by apply Matrix.ext; unfold raw2166 raw2168; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5137 = raw2168Labels := by decide +kernel
    rw [ha, hj, canonical2168 B hB]
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

theorem singleton5352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5352 node5352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3690 node3690Labels + mixedMoment B node3764 node3764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2394 singletonSmall5352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5352) = raw2394Labels := by decide +kernel
  rw [hl, canonical2394 B hB] at h
  have hc0 : mixedMoment B raw2394 (Fin.cases (0 : Fin 2) singletonSmall5352) =
      mixedMoment B node3690 node3690Labels := by
    have ha : raw2394 = raw2395 := by apply Matrix.ext; unfold raw2394 raw2395; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5352 = raw2395Labels := by decide +kernel
    rw [ha, hj, canonical2395 B hB]
  have hc1 : mixedMoment B raw2394 (Fin.cases (1 : Fin 2) singletonSmall5352) =
      mixedMoment B node3764 node3764Labels := by
    have ha : raw2394 = raw2396 := by apply Matrix.ext; unfold raw2394 raw2396; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5352 = raw2396Labels := by decide +kernel
    rw [ha, hj, canonical2396 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5356 node5356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3694 node3694Labels + mixedMoment B node3773 node3773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2403 singletonSmall5356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5356) = raw2403Labels := by decide +kernel
  rw [hl, canonical2403 B hB] at h
  have hc0 : mixedMoment B raw2403 (Fin.cases (0 : Fin 2) singletonSmall5356) =
      mixedMoment B node3694 node3694Labels := by
    have ha : raw2403 = raw2404 := by apply Matrix.ext; unfold raw2403 raw2404; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5356 = raw2404Labels := by decide +kernel
    rw [ha, hj, canonical2404 B hB]
  have hc1 : mixedMoment B raw2403 (Fin.cases (1 : Fin 2) singletonSmall5356) =
      mixedMoment B node3773 node3773Labels := by
    have ha : raw2403 = raw2405 := by apply Matrix.ext; unfold raw2403 raw2405; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5356 = raw2405Labels := by decide +kernel
    rw [ha, hj, canonical2405 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5368 node5368Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3705 node3705Labels + mixedMoment B node3767 node3767Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2415 singletonSmall5368
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5368) = raw2415Labels := by decide +kernel
  rw [hl, canonical2415 B hB] at h
  have hc0 : mixedMoment B raw2415 (Fin.cases (0 : Fin 2) singletonSmall5368) =
      mixedMoment B node3705 node3705Labels := by
    have ha : raw2415 = raw2416 := by apply Matrix.ext; unfold raw2415 raw2416; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5368 = raw2416Labels := by decide +kernel
    rw [ha, hj, canonical2416 B hB]
  have hc1 : mixedMoment B raw2415 (Fin.cases (1 : Fin 2) singletonSmall5368) =
      mixedMoment B node3767 node3767Labels := by
    have ha : raw2415 = raw2417 := by apply Matrix.ext; unfold raw2415 raw2417; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5368 = raw2417Labels := by decide +kernel
    rw [ha, hj, canonical2417 B hB]
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

theorem sound901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node901 node901Labels = Sparse.eval nodeValue901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 901) = mixedMoment B node901 node901Labels := rfl
  simpa [nodeValue901, Sparse.eval] using hc.symm

theorem sound902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node902 node902Labels = Sparse.eval nodeValue902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 902) = mixedMoment B node902 node902Labels := rfl
  simpa [nodeValue902, Sparse.eval] using hc.symm

theorem sound903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node903 node903Labels = Sparse.eval nodeValue903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 903) = mixedMoment B node903 node903Labels := rfl
  simpa [nodeValue903, Sparse.eval] using hc.symm

theorem sound927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node927 node927Labels = Sparse.eval nodeValue927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 927) = mixedMoment B node927 node927Labels := rfl
  simpa [nodeValue927, Sparse.eval] using hc.symm

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

theorem sound1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1589 node1589Labels = Sparse.eval nodeValue1589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1589) = mixedMoment B node1589 node1589Labels := rfl
  simpa [nodeValue1589, Sparse.eval] using hc.symm

theorem sound1590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1590 node1590Labels = Sparse.eval nodeValue1590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1590) = mixedMoment B node1590 node1590Labels := rfl
  simpa [nodeValue1590, Sparse.eval] using hc.symm

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

theorem sound1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1618 node1618Labels = Sparse.eval nodeValue1618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1618) = mixedMoment B node1618 node1618Labels := rfl
  simpa [nodeValue1618, Sparse.eval] using hc.symm

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

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

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

theorem sound1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1773 node1773Labels = Sparse.eval nodeValue1773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1773) = mixedMoment B node1773 node1773Labels := rfl
  simpa [nodeValue1773, Sparse.eval] using hc.symm

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

theorem sound1841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1841 node1841Labels = Sparse.eval nodeValue1841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1841) = mixedMoment B node1841 node1841Labels := rfl
  simpa [nodeValue1841, Sparse.eval] using hc.symm

theorem sound1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1850 node1850Labels = Sparse.eval nodeValue1850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1850) = mixedMoment B node1850 node1850Labels := rfl
  simpa [nodeValue1850, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2295 node2295Labels = Sparse.eval nodeValue2295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2295) = mixedMoment B node2295 node2295Labels := rfl
  simpa [nodeValue2295, Sparse.eval] using hc.symm

theorem sound2300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2300 node2300Labels = Sparse.eval nodeValue2300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2300) = mixedMoment B node2300 node2300Labels := rfl
  simpa [nodeValue2300, Sparse.eval] using hc.symm

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

theorem sound2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2306 node2306Labels = Sparse.eval nodeValue2306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2306) = mixedMoment B node2306 node2306Labels := rfl
  simpa [nodeValue2306, Sparse.eval] using hc.symm

theorem sound2318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2318 node2318Labels = Sparse.eval nodeValue2318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2318) = mixedMoment B node2318 node2318Labels := rfl
  simpa [nodeValue2318, Sparse.eval] using hc.symm

theorem sound2337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2337 node2337Labels = Sparse.eval nodeValue2337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2337) = mixedMoment B node2337 node2337Labels := rfl
  simpa [nodeValue2337, Sparse.eval] using hc.symm

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

theorem sound2372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2372 node2372Labels = Sparse.eval nodeValue2372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2372) = mixedMoment B node2372 node2372Labels := rfl
  simpa [nodeValue2372, Sparse.eval] using hc.symm

theorem sound2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2388 node2388Labels = Sparse.eval nodeValue2388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2388) = mixedMoment B node2388 node2388Labels := rfl
  simpa [nodeValue2388, Sparse.eval] using hc.symm

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

theorem sound2452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2452 node2452Labels = Sparse.eval nodeValue2452 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2452) = mixedMoment B node2452 node2452Labels := rfl
  simpa [nodeValue2452, Sparse.eval] using hc.symm

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

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3315 node3315Labels = Sparse.eval nodeValue3315 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3315) = mixedMoment B node3315 node3315Labels := rfl
  simpa [nodeValue3315, Sparse.eval] using hc.symm

theorem sound3318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3318 node3318Labels = Sparse.eval nodeValue3318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3318) = mixedMoment B node3318 node3318Labels := rfl
  simpa [nodeValue3318, Sparse.eval] using hc.symm

theorem sound3325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3325 node3325Labels = Sparse.eval nodeValue3325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3325) = mixedMoment B node3325 node3325Labels := rfl
  simpa [nodeValue3325, Sparse.eval] using hc.symm

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

theorem sound3336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3336 node3336Labels = Sparse.eval nodeValue3336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3336) = mixedMoment B node3336 node3336Labels := rfl
  simpa [nodeValue3336, Sparse.eval] using hc.symm

theorem sound3354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3354 node3354Labels = Sparse.eval nodeValue3354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3354) = mixedMoment B node3354 node3354Labels := rfl
  simpa [nodeValue3354, Sparse.eval] using hc.symm

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

theorem sound3400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3400 node3400Labels = Sparse.eval nodeValue3400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3400) = mixedMoment B node3400 node3400Labels := rfl
  simpa [nodeValue3400, Sparse.eval] using hc.symm

theorem sound3412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3412 node3412Labels = Sparse.eval nodeValue3412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3412) = mixedMoment B node3412 node3412Labels := rfl
  simpa [nodeValue3412, Sparse.eval] using hc.symm

theorem sound3433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3433 node3433Labels = Sparse.eval nodeValue3433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3433) = mixedMoment B node3433 node3433Labels := rfl
  simpa [nodeValue3433, Sparse.eval] using hc.symm

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

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

theorem sound3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3705 node3705Labels = Sparse.eval nodeValue3705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3705) = mixedMoment B node3705 node3705Labels := rfl
  simpa [nodeValue3705, Sparse.eval] using hc.symm

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

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

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

theorem sound4323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4323 node4323Labels = Sparse.eval nodeValue4323 (mixedVector B) := by
  have h := singleton4323 B _hB
  rw [sound901 B _hB _hF, sound1589 B _hB _hF] at h
  norm_num [nodeValue4323, nodeValue901, nodeValue1589, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4324 node4324Labels = Sparse.eval nodeValue4324 (mixedVector B) := by
  have h := singleton4324 B _hB
  rw [sound902 B _hB _hF, sound1590 B _hB _hF] at h
  norm_num [nodeValue4324, nodeValue902, nodeValue1590, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4325 node4325Labels = Sparse.eval nodeValue4325 (mixedVector B) := by
  have h := singleton4325 B _hB
  rw [sound903 B _hB _hF, sound1591 B _hB _hF] at h
  norm_num [nodeValue4325, nodeValue903, nodeValue1591, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4349 node4349Labels = Sparse.eval nodeValue4349 (mixedVector B) := by
  have h := singleton4349 B _hB
  rw [sound927 B _hB _hF, sound1675 B _hB _hF] at h
  norm_num [nodeValue4349, nodeValue927, nodeValue1675, Sparse.eval] at h ⊢
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

theorem sound4644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4644 node4644Labels = Sparse.eval nodeValue4644 (mixedVector B) := by
  have h := singleton4644 B _hB
  rw [sound1773 B _hB _hF, sound1841 B _hB _hF] at h
  norm_num [nodeValue4644, nodeValue1773, nodeValue1841, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4902 node4902Labels = Sparse.eval nodeValue4902 (mixedVector B) := by
  have h := singleton4902 B _hB
  rw [sound2295 B _hB _hF, sound3315 B _hB _hF] at h
  norm_num [nodeValue4902, nodeValue2295, nodeValue3315, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4907 node4907Labels = Sparse.eval nodeValue4907 (mixedVector B) := by
  have h := singleton4907 B _hB
  rw [sound2300 B _hB _hF, sound3325 B _hB _hF] at h
  norm_num [nodeValue4907, nodeValue2300, nodeValue3325, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4913 node4913Labels = Sparse.eval nodeValue4913 (mixedVector B) := by
  have h := singleton4913 B _hB
  rw [sound2306 B _hB _hF, sound3318 B _hB _hF] at h
  norm_num [nodeValue4913, nodeValue2306, nodeValue3318, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4928 node4928Labels = Sparse.eval nodeValue4928 (mixedVector B) := by
  have h := singleton4928 B _hB
  rw [sound2318 B _hB _hF, sound3400 B _hB _hF] at h
  norm_num [nodeValue4928, nodeValue2318, nodeValue3400, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4946 node4946Labels = Sparse.eval nodeValue4946 (mixedVector B) := by
  have h := singleton4946 B _hB
  rw [sound2337 B _hB _hF, sound3412 B _hB _hF] at h
  norm_num [nodeValue4946, nodeValue2337, nodeValue3412, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4987 node4987Labels = Sparse.eval nodeValue4987 (mixedVector B) := by
  have h := singleton4987 B _hB
  rw [sound2372 B _hB _hF, sound3336 B _hB _hF] at h
  norm_num [nodeValue4987, nodeValue2372, nodeValue3336, Sparse.eval] at h ⊢
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

theorem sound5003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5003 node5003Labels = Sparse.eval nodeValue5003 (mixedVector B) := by
  have h := singleton5003 B _hB
  rw [sound2388 B _hB _hF, sound3354 B _hB _hF] at h
  norm_num [nodeValue5003, nodeValue2388, nodeValue3354, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5036 node5036Labels = Sparse.eval nodeValue5036 (mixedVector B) := by
  have h := singleton5036 B _hB
  rw [sound2428 B _hB _hF, sound3450 B _hB _hF] at h
  norm_num [nodeValue5036, nodeValue2428, nodeValue3450, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5050 node5050Labels = Sparse.eval nodeValue5050 (mixedVector B) := by
  have h := singleton5050 B _hB
  rw [sound2452 B _hB _hF, sound3433 B _hB _hF] at h
  norm_num [nodeValue5050, nodeValue2452, nodeValue3433, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5137 node5137Labels = Sparse.eval nodeValue5137 (mixedVector B) := by
  have h := singleton5137 B _hB
  rw [sound2556 B _hB _hF, sound3521 B _hB _hF] at h
  norm_num [nodeValue5137, nodeValue2556, nodeValue3521, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5352 node5352Labels = Sparse.eval nodeValue5352 (mixedVector B) := by
  have h := singleton5352 B _hB
  rw [sound3690 B _hB _hF, sound3764 B _hB _hF] at h
  norm_num [nodeValue5352, nodeValue3690, nodeValue3764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5356 node5356Labels = Sparse.eval nodeValue5356 (mixedVector B) := by
  have h := singleton5356 B _hB
  rw [sound3694 B _hB _hF, sound3773 B _hB _hF] at h
  norm_num [nodeValue5356, nodeValue3694, nodeValue3773, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5368 node5368Labels = Sparse.eval nodeValue5368 (mixedVector B) := by
  have h := singleton5368 B _hB
  rw [sound3705 B _hB _hF, sound3767 B _hB _hF] at h
  norm_num [nodeValue5368, nodeValue3705, nodeValue3767, Sparse.eval] at h ⊢
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

theorem sourceEq2197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2197 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 1) (sourceB2197 + difference 1 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 1) (sourceB2197 + difference 1 0) sourceC2197) = raw17096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw17096; decide +kernel
    rw [ha]
    exact (canonical17096 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 2) (sourceB2197 + difference 2 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 2) (sourceB2197 + difference 2 0) sourceC2197) = raw17097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw17097; decide +kernel
    rw [ha]
    exact (canonical17097 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 3) (sourceB2197 + difference 3 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 3) (sourceB2197 + difference 3 0) sourceC2197) = raw17098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw17098; decide +kernel
    rw [ha]
    exact (canonical17098 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 4) (sourceB2197 + difference 4 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 4) (sourceB2197 + difference 4 0) sourceC2197) = raw3145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw3145; decide +kernel
    rw [ha]
    exact (canonical3145 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 5) (sourceB2197 + difference 5 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 5) (sourceB2197 + difference 5 0) sourceC2197) = raw3140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw3140; decide +kernel
    rw [ha]
    exact (canonical3140 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 0) (sourceB2197 + difference 0 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 0) (sourceB2197 + difference 0 1) sourceC2197) = raw9860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9860; decide +kernel
    rw [ha]
    exact (canonical9860 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 2) (sourceB2197 + difference 2 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 2) (sourceB2197 + difference 2 1) sourceC2197) = raw9862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9862; decide +kernel
    rw [ha]
    exact (canonical9862 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 3) (sourceB2197 + difference 3 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 3) (sourceB2197 + difference 3 1) sourceC2197) = raw9863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9863; decide +kernel
    rw [ha]
    exact (canonical9863 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 4) (sourceB2197 + difference 4 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 4) (sourceB2197 + difference 4 1) sourceC2197) = raw3144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw3144; decide +kernel
    rw [ha]
    exact (canonical3144 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 5) (sourceB2197 + difference 5 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 5) (sourceB2197 + difference 5 1) sourceC2197) = raw3139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw3139; decide +kernel
    rw [ha]
    exact (canonical3139 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 0) (sourceB2197 + difference 0 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 0) (sourceB2197 + difference 0 2) sourceC2197) = raw30139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30139; decide +kernel
    rw [ha]
    exact (canonical30139 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 1) (sourceB2197 + difference 1 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 1) (sourceB2197 + difference 1 2) sourceC2197) = raw30140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30140; decide +kernel
    rw [ha]
    exact (canonical30140 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 3) (sourceB2197 + difference 3 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 3) (sourceB2197 + difference 3 2) sourceC2197) = raw30141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30141; decide +kernel
    rw [ha]
    exact (canonical30141 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 4) (sourceB2197 + difference 4 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 4) (sourceB2197 + difference 4 2) sourceC2197) = raw9853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9853; decide +kernel
    rw [ha]
    exact (canonical9853 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 5) (sourceB2197 + difference 5 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 5) (sourceB2197 + difference 5 2) sourceC2197) = raw30142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30142; decide +kernel
    rw [ha]
    exact (canonical30142 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 0) (sourceB2197 + difference 0 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 0) (sourceB2197 + difference 0 3) sourceC2197) = raw30143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30143; decide +kernel
    rw [ha]
    exact (canonical30143 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 1) (sourceB2197 + difference 1 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 1) (sourceB2197 + difference 1 3) sourceC2197) = raw30144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30144; decide +kernel
    rw [ha]
    exact (canonical30144 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 2) (sourceB2197 + difference 2 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 2) (sourceB2197 + difference 2 3) sourceC2197) = raw30145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30145; decide +kernel
    rw [ha]
    exact (canonical30145 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 4) (sourceB2197 + difference 4 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 4) (sourceB2197 + difference 4 3) sourceC2197) = raw9857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9857; decide +kernel
    rw [ha]
    exact (canonical9857 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 5) (sourceB2197 + difference 5 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 5) (sourceB2197 + difference 5 3) sourceC2197) = raw30146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30146; decide +kernel
    rw [ha]
    exact (canonical30146 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 0) (sourceB2197 + difference 0 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 0) (sourceB2197 + difference 0 4) sourceC2197) = raw30147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30147; decide +kernel
    rw [ha]
    exact (canonical30147 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 1) (sourceB2197 + difference 1 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 1) (sourceB2197 + difference 1 4) sourceC2197) = raw30148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30148; decide +kernel
    rw [ha]
    exact (canonical30148 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 2) (sourceB2197 + difference 2 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 2) (sourceB2197 + difference 2 4) sourceC2197) = raw30149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30149; decide +kernel
    rw [ha]
    exact (canonical30149 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 3) (sourceB2197 + difference 3 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 3) (sourceB2197 + difference 3 4) sourceC2197) = raw30150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30150; decide +kernel
    rw [ha]
    exact (canonical30150 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 5) (sourceB2197 + difference 5 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 5) (sourceB2197 + difference 5 4) sourceC2197) = raw30151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30151; decide +kernel
    rw [ha]
    exact (canonical30151 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 0) (sourceB2197 + difference 0 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 0) (sourceB2197 + difference 0 5) sourceC2197) = raw28772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw28772; decide +kernel
    rw [ha]
    exact (canonical28772 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 1) (sourceB2197 + difference 1 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 1) (sourceB2197 + difference 1 5) sourceC2197) = raw28773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw28773; decide +kernel
    rw [ha]
    exact (canonical28773 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 2) (sourceB2197 + difference 2 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 2) (sourceB2197 + difference 2 5) sourceC2197) = raw28774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw28774; decide +kernel
    rw [ha]
    exact (canonical28774 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 3) (sourceB2197 + difference 3 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 3) (sourceB2197 + difference 3 5) sourceC2197) = raw28775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw28775; decide +kernel
    rw [ha]
    exact (canonical28775 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 4) (sourceB2197 + difference 4 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 4) (sourceB2197 + difference 4 5) sourceC2197) = raw9865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9865; decide +kernel
    rw [ha]
    exact (canonical9865 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2197 sourceB2197 sourceC2197
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2197, Integer.Sparse.eval]
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

theorem reindexCheck1822 : Integer.Sparse.reindex keyMap MixedData.row1822 = numericRow1822 := by decide +kernel

theorem numericCheck1822 (x : Master → ℝ) : Integer.Sparse.eval numericRow1822 x =
    (17280 : ℝ) * reducedSource1822 x := by
  norm_num [numericRow1822, reducedSource1822, Integer.Sparse.eval, Sparse.eval, nodeValue4323, nodeValue4324, nodeValue4325, nodeValue4349, nodeValue4404, nodeValue4631, nodeValue4637, nodeValue4644, nodeValue4804, nodeValue4902, nodeValue4907, nodeValue4913, nodeValue4928, nodeValue4946, nodeValue4987, nodeValue5003, nodeValue5036, nodeValue5050, nodeValue5075, nodeValue5134, nodeValue5137, nodeValue5168, nodeValue5169, nodeValue5258, nodeValue5259, nodeValue5352, nodeValue5356, nodeValue5368, nodeValue5434, nodeValue5483] <;> ring

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

theorem reducedZero1822 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1822 (mixedVector B) = 0 := by
  have h4323 : mixedVector B (Sum.inr 4323) = Sparse.eval nodeValue4323 (mixedVector B) := by
    change mixedMoment B node4323 node4323Labels = _
    exact sound4323 B hB hF
  have h4324 : mixedVector B (Sum.inr 4324) = Sparse.eval nodeValue4324 (mixedVector B) := by
    change mixedMoment B node4324 node4324Labels = _
    exact sound4324 B hB hF
  have h4325 : mixedVector B (Sum.inr 4325) = Sparse.eval nodeValue4325 (mixedVector B) := by
    change mixedMoment B node4325 node4325Labels = _
    exact sound4325 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4631 : mixedVector B (Sum.inr 4631) = Sparse.eval nodeValue4631 (mixedVector B) := by
    change mixedMoment B node4631 node4631Labels = _
    exact sound4631 B hB hF
  have h4637 : mixedVector B (Sum.inr 4637) = Sparse.eval nodeValue4637 (mixedVector B) := by
    change mixedMoment B node4637 node4637Labels = _
    exact sound4637 B hB hF
  have h4644 : mixedVector B (Sum.inr 4644) = Sparse.eval nodeValue4644 (mixedVector B) := by
    change mixedMoment B node4644 node4644Labels = _
    exact sound4644 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4902 : mixedVector B (Sum.inr 4902) = Sparse.eval nodeValue4902 (mixedVector B) := by
    change mixedMoment B node4902 node4902Labels = _
    exact sound4902 B hB hF
  have h4907 : mixedVector B (Sum.inr 4907) = Sparse.eval nodeValue4907 (mixedVector B) := by
    change mixedMoment B node4907 node4907Labels = _
    exact sound4907 B hB hF
  have h4913 : mixedVector B (Sum.inr 4913) = Sparse.eval nodeValue4913 (mixedVector B) := by
    change mixedMoment B node4913 node4913Labels = _
    exact sound4913 B hB hF
  have h4928 : mixedVector B (Sum.inr 4928) = Sparse.eval nodeValue4928 (mixedVector B) := by
    change mixedMoment B node4928 node4928Labels = _
    exact sound4928 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h4987 : mixedVector B (Sum.inr 4987) = Sparse.eval nodeValue4987 (mixedVector B) := by
    change mixedMoment B node4987 node4987Labels = _
    exact sound4987 B hB hF
  have h5003 : mixedVector B (Sum.inr 5003) = Sparse.eval nodeValue5003 (mixedVector B) := by
    change mixedMoment B node5003 node5003Labels = _
    exact sound5003 B hB hF
  have h5036 : mixedVector B (Sum.inr 5036) = Sparse.eval nodeValue5036 (mixedVector B) := by
    change mixedMoment B node5036 node5036Labels = _
    exact sound5036 B hB hF
  have h5050 : mixedVector B (Sum.inr 5050) = Sparse.eval nodeValue5050 (mixedVector B) := by
    change mixedMoment B node5050 node5050Labels = _
    exact sound5050 B hB hF
  have h5075 : mixedVector B (Sum.inr 5075) = Sparse.eval nodeValue5075 (mixedVector B) := by
    change mixedMoment B node5075 node5075Labels = _
    exact sound5075 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169_e B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  simpa only [sourceForm2197, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4323, h4324, h4325, h4349, h4404, h4631, h4637, h4644, h4804, h4902, h4907, h4913, h4928, h4946, h4987, h5003, h5036, h5050, h5075, h5134, h5137, h5168, h5169, h5258, h5259, h5352, h5356, h5368, h5434, h5483, reducedSource1822] using sourceEq2197 B hB

theorem rowSound1822_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1822 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1822, numericCheck1822, reducedZero1822 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e_oai
