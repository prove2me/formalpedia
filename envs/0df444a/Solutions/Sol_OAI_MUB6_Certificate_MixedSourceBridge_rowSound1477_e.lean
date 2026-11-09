-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:13:44.420205+00:00
-- url     : https://prove2.me/submissions/b4d01ec9-372d-448b-9fed-cf4e277035cb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5169_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e

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

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

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

theorem transition_reverse (b c : Basis) :
    transition c b = (transition b c).conjTranspose := by
  ext i j
  simp [transition, Matrix.conjTranspose_apply]

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

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem familyAverage_add (B : Fin 7 → Basis) (F G : CMatrix → ℝ) :
    familyAverage B (fun H => F H + G H) = familyAverage B F + familyAverage B G := by
  simp only [familyAverage, average_add]

theorem familyAverage_mul (B : Fin 7 → Basis) (c : ℝ) (F : CMatrix → ℝ) :
    familyAverage B (fun H => c * F H) = c * familyAverage B F := by
  simp only [familyAverage, average_mul]

theorem relativeMatrix_reverse (B : Fin 7 → Basis) (p : Fin 7 × Coord) :
    relativeMatrix B (reversePair p).1 (reversePair p).2 =
      (relativeMatrix B p.1 p.2).conjTranspose := by
  simp only [relativeMatrix, reversePair, Fin.succAbove_succAbove_predAbove]
  exact transition_reverse _ _

theorem familyAverage_transpose (B : Fin 7 → Basis) (F : CMatrix → ℝ)
    (hF : ∀ H, F (fun i j => conj (H i j)) = F H) :
    familyAverage B (fun H => F H.transpose) = familyAverage B F := by
  change (average (fun r : Fin 7 => average (fun s : Coord => F ((relativeMatrix B r s).transpose)))) =
    average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))
  rw [← average_prod (fun p : Fin 7 × Coord => F ((relativeMatrix B p.1 p.2).transpose)),
    ← average_prod (fun p : Fin 7 × Coord => F (relativeMatrix B p.1 p.2))]
  have h (p : Fin 7 × Coord) :
      F ((relativeMatrix B p.1 p.2).transpose) =
        F (relativeMatrix B (reversePair p).1 (reversePair p).2) := by
    rw [relativeMatrix_reverse]
    exact (hF ((relativeMatrix B p.1 p.2).transpose)).symm
  simp_rw [h]
  exact average_equiv reversePairEquiv (fun p => F (relativeMatrix B p.1 p.2))

theorem rowFourier_conjugate {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier (fun i j => conj (H i j)) ρ a = conj (rowFourier H ρ a) := by
  simp only [rowFourier, map_mul, map_sum, map_prod, map_zpow₀, map_inv₀, map_ofNat]

theorem unorientedRowProducts_conjugate {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    unorientedRowProducts (fun i j => conj (H i j)) A = unorientedRowProducts H A := by
  apply average_congr
  intro ρ
  simp only [rowFourier_conjugate, ← map_prod, Complex.conj_re]

theorem averagedRowProducts_split {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    averagedRowProducts H A =
      (1 / 2 : ℝ) * unorientedRowProducts H A +
        (1 / 2 : ℝ) * unorientedRowProducts H.transpose A := by
  have h (ρ : Fin p ↪ Coord) :
      ((∏ j, rowFourier H ρ (fun i => A i j)).re +
        (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (1 / 2 : ℝ) * (∏ j, rowFourier H ρ (fun i => A i j)).re +
        (1 / 2 : ℝ) * (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re := by ring
  simp only [averagedRowProducts, h, average_add, average_mul, unorientedRowProducts]

theorem familyAverage_averagedRowProducts {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    familyAverage B (fun H => averagedRowProducts H A) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  simp only [averagedRowProducts_split, familyAverage_add, familyAverage_mul]
  rw [familyAverage_transpose B (fun H => unorientedRowProducts H A)
    (fun H => unorientedRowProducts_conjugate H A)]
  ring

theorem mixedMoment_single_label {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) :
      average (fun τ : Fin 1 ↪ Coord =>
        (mixedIntegrand B A (fun _ => (0 : Fin 1)) r ρ τ).re) =
      average (fun s : Coord => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re) := by
    exact average_equiv singletonEmbeddingEquiv
      (fun s => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re)
  simp_rw [h]
  exact average_comm _

/-- Single-label mixed moments expand into the manuscript's transpose-averaged
pair moments with the exact falling-factorial weights. -/
theorem mixedMoment_single_label_partition {p n : ℕ} {P : Type*} [Fintype P]
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        familyPairMoment B (groupedColumns A (F.label s)) := by
  rw [mixedMoment_single_label, ← familyAverage_averagedRowProducts]
  unfold familyAverage
  simp_rw [averagedRowProducts_partition (relativeMatrix_isHadamard B hB _ _) A F cover,
    average_sum, average_mul]
  rfl

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

theorem canonical1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1293 raw1293Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw1293 raw1293Labels = mixedMoment B raw1293step0 raw1293step0Labels := by
      have ha : raw1293step0 = (fun i j => raw1293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1293step0 raw1293; decide +kernel
      have hl : raw1293step0Labels = raw1293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1293 raw1293Labels permutation32 permutation4
    mixedMoment B raw1293step0 raw1293step0Labels = mixedMoment B raw1293step1 raw1293step1Labels := by
      have ha : raw1293step1 = raw1293step0 := by apply Matrix.ext; unfold raw1293step1 raw1293step0; decide +kernel
      have hl : raw1293step0Labels = labelEmbedding7 ∘ raw1293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1293step0 raw1293step0Labels raw1293step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1294 raw1294Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw1294 raw1294Labels = mixedMoment B raw1294step0 raw1294step0Labels := by
      have ha : raw1294step0 = (fun i j => raw1294 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1294step0 raw1294; decide +kernel
      have hl : raw1294step0Labels = raw1294Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1294 raw1294Labels permutation32 permutation4
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1295 raw1295Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw1295 raw1295Labels = mixedMoment B raw1295step0 raw1295step0Labels := by
      have ha : raw1295step0 = (fun i j => raw1295 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1295step0 raw1295; decide +kernel
      have hl : raw1295step0Labels = raw1295Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1295 raw1295Labels permutation32 permutation6
    mixedMoment B raw1295step0 raw1295step0Labels = mixedMoment B raw1295step1 raw1295step1Labels := by
      have ha : raw1295step1 = -raw1295step0 := by apply Matrix.ext; change ∀ i j, raw1295step1 i j = -(raw1295step0 i j); unfold raw1295step1 raw1295step0; decide +kernel
      have hl : raw1295step1Labels = raw1295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1295step1 raw1295step1Labels = mixedMoment B raw1295step2 raw1295step2Labels := by
      have ha : raw1295step2 = raw1295step1 := by apply Matrix.ext; unfold raw1295step2 raw1295step1; decide +kernel
      have hl : raw1295step1Labels = labelEmbedding1 ∘ raw1295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1295step1 raw1295step1Labels raw1295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical1299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1299 raw1299Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw1299 raw1299Labels = mixedMoment B raw1299step0 raw1299step0Labels := by
      have ha : raw1299step0 = (fun i j => raw1299 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1299step0 raw1299; decide +kernel
      have hl : raw1299step0Labels = raw1299Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1299 raw1299Labels permutation8 permutation4
    mixedMoment B raw1299step0 raw1299step0Labels = mixedMoment B raw1299step1 raw1299step1Labels := by
      have ha : raw1299step1 = raw1299step0 := by apply Matrix.ext; unfold raw1299step1 raw1299step0; decide +kernel
      have hl : raw1299step0Labels = labelEmbedding7 ∘ raw1299step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1299step0 raw1299step0Labels raw1299step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1300 raw1300Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw1300 raw1300Labels = mixedMoment B raw1300step0 raw1300step0Labels := by
      have ha : raw1300step0 = (fun i j => raw1300 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1300step0 raw1300; decide +kernel
      have hl : raw1300step0Labels = raw1300Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1300 raw1300Labels permutation8 permutation4
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1301 raw1301Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw1301 raw1301Labels = mixedMoment B raw1301step0 raw1301step0Labels := by
      have ha : raw1301step0 = (fun i j => raw1301 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1301step0 raw1301; decide +kernel
      have hl : raw1301step0Labels = raw1301Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1301 raw1301Labels permutation9 permutation6
    mixedMoment B raw1301step0 raw1301step0Labels = mixedMoment B raw1301step1 raw1301step1Labels := by
      have ha : raw1301step1 = -raw1301step0 := by apply Matrix.ext; change ∀ i j, raw1301step1 i j = -(raw1301step0 i j); unfold raw1301step1 raw1301step0; decide +kernel
      have hl : raw1301step1Labels = raw1301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1301step1 raw1301step1Labels = mixedMoment B raw1301step2 raw1301step2Labels := by
      have ha : raw1301step2 = raw1301step1 := by apply Matrix.ext; unfold raw1301step2 raw1301step1; decide +kernel
      have hl : raw1301step1Labels = labelEmbedding1 ∘ raw1301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1301step1 raw1301step1Labels raw1301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17671 raw17671Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw17671 raw17671Labels = mixedMoment B raw17671step0 raw17671step0Labels := by
      have hz : ∀ j, raw17671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17671step0 = (fun i j => raw17671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17671step0 raw17671; decide +kernel
      have hl : raw17671step0Labels = raw17671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17671 raw17671Labels permutation346 hz
    mixedMoment B raw17671step0 raw17671step0Labels = mixedMoment B raw17671step1 raw17671step1Labels := by
      have ha : raw17671step1 = (fun i j => raw17671step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17671step1 raw17671step0; decide +kernel
      have hl : raw17671step1Labels = raw17671step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17671step0 raw17671step0Labels permutation34 permutation3
    mixedMoment B raw17671step1 raw17671step1Labels = mixedMoment B raw17671step2 raw17671step2Labels := by
      have ha : raw17671step2 = raw17671step1 := by apply Matrix.ext; unfold raw17671step2 raw17671step1; decide +kernel
      have hl : raw17671step1Labels = labelEmbedding6 ∘ raw17671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17671step1 raw17671step1Labels raw17671step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

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

theorem canonical2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2094 raw2094Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw2094 raw2094Labels = mixedMoment B raw2094step0 raw2094step0Labels := by
      have ha : raw2094step0 = (fun i j => raw2094 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2094step0 raw2094; decide +kernel
      have hl : raw2094step0Labels = raw2094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2094 raw2094Labels permutation152 permutation4
    mixedMoment B raw2094step0 raw2094step0Labels = mixedMoment B raw2094step1 raw2094step1Labels := by
      have ha : raw2094step1 = raw2094step0 := by apply Matrix.ext; unfold raw2094step1 raw2094step0; decide +kernel
      have hl : raw2094step0Labels = labelEmbedding7 ∘ raw2094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2094step0 raw2094step0Labels raw2094step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical2095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2095 raw2095Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw2095 raw2095Labels = mixedMoment B raw2095step0 raw2095step0Labels := by
      have ha : raw2095step0 = (fun i j => raw2095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2095step0 raw2095; decide +kernel
      have hl : raw2095step0Labels = raw2095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2095 raw2095Labels permutation152 permutation4
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2096 raw2096Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw2096 raw2096Labels = mixedMoment B raw2096step0 raw2096step0Labels := by
      have ha : raw2096step0 = (fun i j => raw2096 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2096step0 raw2096; decide +kernel
      have hl : raw2096step0Labels = raw2096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2096 raw2096Labels permutation158 permutation6
    mixedMoment B raw2096step0 raw2096step0Labels = mixedMoment B raw2096step1 raw2096step1Labels := by
      have ha : raw2096step1 = -raw2096step0 := by apply Matrix.ext; change ∀ i j, raw2096step1 i j = -(raw2096step0 i j); unfold raw2096step1 raw2096step0; decide +kernel
      have hl : raw2096step1Labels = raw2096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2096step1 raw2096step1Labels = mixedMoment B raw2096step2 raw2096step2Labels := by
      have ha : raw2096step2 = raw2096step1 := by apply Matrix.ext; unfold raw2096step2 raw2096step1; decide +kernel
      have hl : raw2096step1Labels = labelEmbedding1 ∘ raw2096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2096step1 raw2096step1Labels raw2096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21481 raw21481Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw21481 raw21481Labels = mixedMoment B raw21481step0 raw21481step0Labels := by
      have hz : ∀ j, raw21481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21481step0 = (fun i j => raw21481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21481step0 raw21481; decide +kernel
      have hl : raw21481step0Labels = raw21481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21481 raw21481Labels permutation434 hz
    mixedMoment B raw21481step0 raw21481step0Labels = mixedMoment B raw21481step1 raw21481step1Labels := by
      have hz : ∀ j, raw21481step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21481step1 = (fun i j => raw21481step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21481step1 raw21481step0; decide +kernel
      have hl : raw21481step1Labels = raw21481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21481step0 raw21481step0Labels permutation80 hz
    mixedMoment B raw21481step1 raw21481step1Labels = mixedMoment B raw21481step2 raw21481step2Labels := by
      have ha : raw21481step2 = (fun i j => raw21481step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21481step2 raw21481step1; decide +kernel
      have hl : raw21481step2Labels = raw21481step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21481step1 raw21481step1Labels permutation10 permutation3
    mixedMoment B raw21481step2 raw21481step2Labels = mixedMoment B raw21481step3 raw21481step3Labels := by
      have ha : raw21481step3 = raw21481step2 := by apply Matrix.ext; unfold raw21481step3 raw21481step2; decide +kernel
      have hl : raw21481step2Labels = labelEmbedding6 ∘ raw21481step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21481step2 raw21481step2Labels raw21481step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical21485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21485 raw21485Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw21485 raw21485Labels = mixedMoment B raw21485step0 raw21485step0Labels := by
      have hz : ∀ j, raw21485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21485step0 = (fun i j => raw21485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21485step0 raw21485; decide +kernel
      have hl : raw21485step0Labels = raw21485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21485 raw21485Labels permutation434 hz
    mixedMoment B raw21485step0 raw21485step0Labels = mixedMoment B raw21485step1 raw21485step1Labels := by
      have ha : raw21485step1 = (fun i j => raw21485step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21485step1 raw21485step0; decide +kernel
      have hl : raw21485step1Labels = raw21485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21485step0 raw21485step0Labels permutation34 permutation3
    mixedMoment B raw21485step1 raw21485step1Labels = mixedMoment B raw21485step2 raw21485step2Labels := by
      have ha : raw21485step2 = raw21485step1 := by apply Matrix.ext; unfold raw21485step2 raw21485step1; decide +kernel
      have hl : raw21485step1Labels = labelEmbedding6 ∘ raw21485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21485step1 raw21485step1Labels raw21485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical21486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21486 raw21486Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw21486 raw21486Labels = mixedMoment B raw21486step0 raw21486step0Labels := by
      have hz : ∀ j, raw21486 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21486step0 = (fun i j => raw21486 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21486step0 raw21486; decide +kernel
      have hl : raw21486step0Labels = raw21486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21486 raw21486Labels permutation346 hz
    mixedMoment B raw21486step0 raw21486step0Labels = mixedMoment B raw21486step1 raw21486step1Labels := by
      have ha : raw21486step1 = (fun i j => raw21486step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21486step1 raw21486step0; decide +kernel
      have hl : raw21486step1Labels = raw21486step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21486step0 raw21486step0Labels permutation34 permutation3
    mixedMoment B raw21486step1 raw21486step1Labels = mixedMoment B raw21486step2 raw21486step2Labels := by
      have ha : raw21486step2 = raw21486step1 := by apply Matrix.ext; unfold raw21486step2 raw21486step1; decide +kernel
      have hl : raw21486step1Labels = labelEmbedding6 ∘ raw21486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21486step1 raw21486step1Labels raw21486step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4101 node4101Labels := by rfl

theorem canonical21487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21487 raw21487Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21487 raw21487Labels = mixedMoment B raw21487step0 raw21487step0Labels := by
      have hz : ∀ j, raw21487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21487step0 = (fun i j => raw21487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21487step0 raw21487; decide +kernel
      have hl : raw21487step0Labels = raw21487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21487 raw21487Labels permutation346 hz
    mixedMoment B raw21487step0 raw21487step0Labels = mixedMoment B raw21487step1 raw21487step1Labels := by
      have ha : raw21487step1 = (fun i j => raw21487step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21487step1 raw21487step0; decide +kernel
      have hl : raw21487step1Labels = raw21487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21487step0 raw21487step0Labels permutation34 permutation3
    mixedMoment B raw21487step1 raw21487step1Labels = mixedMoment B raw21487step2 raw21487step2Labels := by
      have ha : raw21487step2 = raw21487step1 := by apply Matrix.ext; unfold raw21487step2 raw21487step1; decide +kernel
      have hl : raw21487step1Labels = labelEmbedding6 ∘ raw21487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21487step1 raw21487step1Labels raw21487step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical21488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21488 raw21488Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw21488 raw21488Labels = mixedMoment B raw21488step0 raw21488step0Labels := by
      have ha : raw21488step0 = (fun i j => raw21488 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21488step0 raw21488; decide +kernel
      have hl : raw21488step0Labels = raw21488Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21488 raw21488Labels permutation178 permutation3
    mixedMoment B raw21488step0 raw21488step0Labels = mixedMoment B raw21488step1 raw21488step1Labels := by
      have ha : raw21488step1 = raw21488step0 := by apply Matrix.ext; unfold raw21488step1 raw21488step0; decide +kernel
      have hl : raw21488step0Labels = labelEmbedding6 ∘ raw21488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21488step0 raw21488step0Labels raw21488step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

theorem canonical21494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21494 raw21494Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw21494 raw21494Labels = mixedMoment B raw21494step0 raw21494step0Labels := by
      have hz : ∀ j, raw21494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21494step0 = (fun i j => raw21494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21494step0 raw21494; decide +kernel
      have hl : raw21494step0Labels = raw21494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21494 raw21494Labels permutation434 hz
    mixedMoment B raw21494step0 raw21494step0Labels = mixedMoment B raw21494step1 raw21494step1Labels := by
      have hz : ∀ j, raw21494step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21494step1 = (fun i j => raw21494step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21494step1 raw21494step0; decide +kernel
      have hl : raw21494step1Labels = raw21494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21494step0 raw21494step0Labels permutation80 hz
    mixedMoment B raw21494step1 raw21494step1Labels = mixedMoment B raw21494step2 raw21494step2Labels := by
      have ha : raw21494step2 = (fun i j => raw21494step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21494step2 raw21494step1; decide +kernel
      have hl : raw21494step2Labels = raw21494step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21494step1 raw21494step1Labels permutation8 permutation3
    mixedMoment B raw21494step2 raw21494step2Labels = mixedMoment B raw21494step3 raw21494step3Labels := by
      have ha : raw21494step3 = raw21494step2 := by apply Matrix.ext; unfold raw21494step3 raw21494step2; decide +kernel
      have hl : raw21494step2Labels = labelEmbedding6 ∘ raw21494step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21494step2 raw21494step2Labels raw21494step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

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

theorem canonical2301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2301 raw2301Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2301 raw2301Labels = mixedMoment B raw2301step0 raw2301step0Labels := by
      have ha : raw2301step0 = (fun i j => raw2301 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2301step0 raw2301; decide +kernel
      have hl : raw2301step0Labels = raw2301Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2301 raw2301Labels permutation8 permutation4
    mixedMoment B raw2301step0 raw2301step0Labels = mixedMoment B raw2301step1 raw2301step1Labels := by
      have ha : raw2301step1 = raw2301step0 := by apply Matrix.ext; unfold raw2301step1 raw2301step0; decide +kernel
      have hl : raw2301step0Labels = labelEmbedding7 ∘ raw2301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2301step0 raw2301step0Labels raw2301step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical2302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2302 raw2302Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2302 raw2302Labels = mixedMoment B raw2302step0 raw2302step0Labels := by
      have ha : raw2302step0 = (fun i j => raw2302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2302step0 raw2302; decide +kernel
      have hl : raw2302step0Labels = raw2302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2302 raw2302Labels permutation8 permutation4
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical2303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2303 raw2303Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw2303 raw2303Labels = mixedMoment B raw2303step0 raw2303step0Labels := by
      have ha : raw2303step0 = (fun i j => raw2303 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2303step0 raw2303; decide +kernel
      have hl : raw2303step0Labels = raw2303Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2303 raw2303Labels permutation10 permutation6
    mixedMoment B raw2303step0 raw2303step0Labels = mixedMoment B raw2303step1 raw2303step1Labels := by
      have ha : raw2303step1 = -raw2303step0 := by apply Matrix.ext; change ∀ i j, raw2303step1 i j = -(raw2303step0 i j); unfold raw2303step1 raw2303step0; decide +kernel
      have hl : raw2303step1Labels = raw2303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2303step1 raw2303step1Labels = mixedMoment B raw2303step2 raw2303step2Labels := by
      have ha : raw2303step2 = raw2303step1 := by apply Matrix.ext; unfold raw2303step2 raw2303step1; decide +kernel
      have hl : raw2303step1Labels = labelEmbedding1 ∘ raw2303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2303step1 raw2303step1Labels raw2303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3627 node3627Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23230 raw23230Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw23230 raw23230Labels = mixedMoment B raw23230step0 raw23230step0Labels := by
      have hz : ∀ j, raw23230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23230step0 = (fun i j => raw23230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23230step0 raw23230; decide +kernel
      have hl : raw23230step0Labels = raw23230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23230 raw23230Labels permutation346 hz
    mixedMoment B raw23230step0 raw23230step0Labels = mixedMoment B raw23230step1 raw23230step1Labels := by
      have ha : raw23230step1 = (fun i j => raw23230step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23230step1 raw23230step0; decide +kernel
      have hl : raw23230step1Labels = raw23230step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23230step0 raw23230step0Labels permutation32 permutation3
    mixedMoment B raw23230step1 raw23230step1Labels = mixedMoment B raw23230step2 raw23230step2Labels := by
      have ha : raw23230step2 = raw23230step1 := by apply Matrix.ext; unfold raw23230step2 raw23230step1; decide +kernel
      have hl : raw23230step1Labels = labelEmbedding6 ∘ raw23230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23230step1 raw23230step1Labels raw23230step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

theorem canonical23231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23231 raw23231Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23231 raw23231Labels = mixedMoment B raw23231step0 raw23231step0Labels := by
      have hz : ∀ j, raw23231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23231step0 = (fun i j => raw23231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23231step0 raw23231; decide +kernel
      have hl : raw23231step0Labels = raw23231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23231 raw23231Labels permutation346 hz
    mixedMoment B raw23231step0 raw23231step0Labels = mixedMoment B raw23231step1 raw23231step1Labels := by
      have ha : raw23231step1 = (fun i j => raw23231step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23231step1 raw23231step0; decide +kernel
      have hl : raw23231step1Labels = raw23231step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23231step0 raw23231step0Labels permutation32 permutation3
    mixedMoment B raw23231step1 raw23231step1Labels = mixedMoment B raw23231step2 raw23231step2Labels := by
      have ha : raw23231step2 = raw23231step1 := by apply Matrix.ext; unfold raw23231step2 raw23231step1; decide +kernel
      have hl : raw23231step1Labels = labelEmbedding6 ∘ raw23231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23231step1 raw23231step1Labels raw23231step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical23232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23232 raw23232Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw23232 raw23232Labels = mixedMoment B raw23232step0 raw23232step0Labels := by
      have ha : raw23232step0 = (fun i j => raw23232 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23232step0 raw23232; decide +kernel
      have hl : raw23232step0Labels = raw23232Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23232 raw23232Labels permutation176 permutation3
    mixedMoment B raw23232step0 raw23232step0Labels = mixedMoment B raw23232step1 raw23232step1Labels := by
      have ha : raw23232step1 = raw23232step0 := by apply Matrix.ext; unfold raw23232step1 raw23232step0; decide +kernel
      have hl : raw23232step0Labels = labelEmbedding6 ∘ raw23232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23232step0 raw23232step0Labels raw23232step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

theorem canonical23233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23233 raw23233Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23233 raw23233Labels = mixedMoment B raw23233step0 raw23233step0Labels := by
      have hz : ∀ j, raw23233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23233step0 = (fun i j => raw23233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23233step0 raw23233; decide +kernel
      have hl : raw23233step0Labels = raw23233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23233 raw23233Labels permutation346 hz
    mixedMoment B raw23233step0 raw23233step0Labels = mixedMoment B raw23233step1 raw23233step1Labels := by
      have ha : raw23233step1 = (fun i j => raw23233step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23233step1 raw23233step0; decide +kernel
      have hl : raw23233step1Labels = raw23233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23233step0 raw23233step0Labels permutation36 permutation3
    mixedMoment B raw23233step1 raw23233step1Labels = mixedMoment B raw23233step2 raw23233step2Labels := by
      have ha : raw23233step2 = raw23233step1 := by apply Matrix.ext; unfold raw23233step2 raw23233step1; decide +kernel
      have hl : raw23233step1Labels = labelEmbedding6 ∘ raw23233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23233step1 raw23233step1Labels raw23233step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical197
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25241 raw25241Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw25241 raw25241Labels = mixedMoment B raw25241step0 raw25241step0Labels := by
      have ha : raw25241step0 = (fun i j => raw25241 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25241step0 raw25241; decide +kernel
      have hl : raw25241step0Labels = raw25241Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25241 raw25241Labels permutation178 permutation3
    mixedMoment B raw25241step0 raw25241step0Labels = mixedMoment B raw25241step1 raw25241step1Labels := by
      have ha : raw25241step1 = raw25241step0 := by apply Matrix.ext; unfold raw25241step1 raw25241step0; decide +kernel
      have hl : raw25241step0Labels = labelEmbedding6 ∘ raw25241step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25241step0 raw25241step0Labels raw25241step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical25242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25242 raw25242Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw25242 raw25242Labels = mixedMoment B raw25242step0 raw25242step0Labels := by
      have hz : ∀ j, raw25242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25242step0 = (fun i j => raw25242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25242step0 raw25242; decide +kernel
      have hl : raw25242step0Labels = raw25242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25242 raw25242Labels permutation346 hz
    mixedMoment B raw25242step0 raw25242step0Labels = mixedMoment B raw25242step1 raw25242step1Labels := by
      have ha : raw25242step1 = (fun i j => raw25242step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25242step1 raw25242step0; decide +kernel
      have hl : raw25242step1Labels = raw25242step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25242step0 raw25242step0Labels permutation35 permutation3
    mixedMoment B raw25242step1 raw25242step1Labels = mixedMoment B raw25242step2 raw25242step2Labels := by
      have ha : raw25242step2 = raw25242step1 := by apply Matrix.ext; unfold raw25242step2 raw25242step1; decide +kernel
      have hl : raw25242step1Labels = labelEmbedding6 ∘ raw25242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25242step1 raw25242step1Labels raw25242step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical25243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25243 raw25243Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw25243 raw25243Labels = mixedMoment B raw25243step0 raw25243step0Labels := by
      have hz : ∀ j, raw25243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25243step0 = (fun i j => raw25243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25243step0 raw25243; decide +kernel
      have hl : raw25243step0Labels = raw25243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25243 raw25243Labels permutation346 hz
    mixedMoment B raw25243step0 raw25243step0Labels = mixedMoment B raw25243step1 raw25243step1Labels := by
      have ha : raw25243step1 = (fun i j => raw25243step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25243step1 raw25243step0; decide +kernel
      have hl : raw25243step1Labels = raw25243step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25243step0 raw25243step0Labels permutation46 permutation3
    mixedMoment B raw25243step1 raw25243step1Labels = mixedMoment B raw25243step2 raw25243step2Labels := by
      have ha : raw25243step2 = raw25243step1 := by apply Matrix.ext; unfold raw25243step2 raw25243step1; decide +kernel
      have hl : raw25243step1Labels = labelEmbedding6 ∘ raw25243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25243step1 raw25243step1Labels raw25243step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

theorem canonical25244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25244 raw25244Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw25244 raw25244Labels = mixedMoment B raw25244step0 raw25244step0Labels := by
      have ha : raw25244step0 = (fun i j => raw25244 (permutation190 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25244step0 raw25244; decide +kernel
      have hl : raw25244step0Labels = raw25244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25244 raw25244Labels permutation190 permutation3
    mixedMoment B raw25244step0 raw25244step0Labels = mixedMoment B raw25244step1 raw25244step1Labels := by
      have ha : raw25244step1 = raw25244step0 := by apply Matrix.ext; unfold raw25244step1 raw25244step0; decide +kernel
      have hl : raw25244step0Labels = labelEmbedding6 ∘ raw25244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25244step0 raw25244step0Labels raw25244step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

theorem canonical25245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25245 raw25245Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw25245 raw25245Labels = mixedMoment B raw25245step0 raw25245step0Labels := by
      have hz : ∀ j, raw25245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25245step0 = (fun i j => raw25245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25245step0 raw25245; decide +kernel
      have hl : raw25245step0Labels = raw25245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25245 raw25245Labels permutation346 hz
    mixedMoment B raw25245step0 raw25245step0Labels = mixedMoment B raw25245step1 raw25245step1Labels := by
      have ha : raw25245step1 = (fun i j => raw25245step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25245step1 raw25245step0; decide +kernel
      have hl : raw25245step1Labels = raw25245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25245step0 raw25245step0Labels permutation46 permutation3
    mixedMoment B raw25245step1 raw25245step1Labels = mixedMoment B raw25245step2 raw25245step2Labels := by
      have ha : raw25245step2 = raw25245step1 := by apply Matrix.ext; unfold raw25245step2 raw25245step1; decide +kernel
      have hl : raw25245step1Labels = labelEmbedding6 ∘ raw25245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25245step1 raw25245step1Labels raw25245step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

theorem canonical25246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25246 raw25246Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25246 raw25246Labels = mixedMoment B raw25246step0 raw25246step0Labels := by
      have hz : ∀ j, raw25246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25246step0 = (fun i j => raw25246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25246step0 raw25246; decide +kernel
      have hl : raw25246step0Labels = raw25246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25246 raw25246Labels permutation346 hz
    mixedMoment B raw25246step0 raw25246step0Labels = mixedMoment B raw25246step1 raw25246step1Labels := by
      have ha : raw25246step1 = (fun i j => raw25246step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25246step1 raw25246step0; decide +kernel
      have hl : raw25246step1Labels = raw25246step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25246step0 raw25246step0Labels permutation49 permutation3
    mixedMoment B raw25246step1 raw25246step1Labels = mixedMoment B raw25246step2 raw25246step2Labels := by
      have ha : raw25246step2 = raw25246step1 := by apply Matrix.ext; unfold raw25246step2 raw25246step1; decide +kernel
      have hl : raw25246step1Labels = labelEmbedding6 ∘ raw25246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25246step1 raw25246step1Labels raw25246step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical25247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25247 raw25247Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw25247 raw25247Labels = mixedMoment B raw25247step0 raw25247step0Labels := by
      have ha : raw25247step0 = (fun i j => raw25247 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25247step0 raw25247; decide +kernel
      have hl : raw25247step0Labels = raw25247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25247 raw25247Labels permutation164 permutation3
    mixedMoment B raw25247step0 raw25247step0Labels = mixedMoment B raw25247step1 raw25247step1Labels := by
      have ha : raw25247step1 = raw25247step0 := by apply Matrix.ext; unfold raw25247step1 raw25247step0; decide +kernel
      have hl : raw25247step0Labels = labelEmbedding6 ∘ raw25247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25247step0 raw25247step0Labels raw25247step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

theorem canonical25248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25248 raw25248Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw25248 raw25248Labels = mixedMoment B raw25248step0 raw25248step0Labels := by
      have ha : raw25248step0 = (fun i j => raw25248 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25248step0 raw25248; decide +kernel
      have hl : raw25248step0Labels = raw25248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25248 raw25248Labels permutation164 permutation3
    mixedMoment B raw25248step0 raw25248step0Labels = mixedMoment B raw25248step1 raw25248step1Labels := by
      have ha : raw25248step1 = raw25248step0 := by apply Matrix.ext; unfold raw25248step1 raw25248step0; decide +kernel
      have hl : raw25248step0Labels = labelEmbedding6 ∘ raw25248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25248step0 raw25248step0Labels raw25248step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical25249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25249 raw25249Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw25249 raw25249Labels = mixedMoment B raw25249step0 raw25249step0Labels := by
      have ha : raw25249step0 = (fun i j => raw25249 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25249step0 raw25249; decide +kernel
      have hl : raw25249step0Labels = raw25249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25249 raw25249Labels permutation224 permutation3
    mixedMoment B raw25249step0 raw25249step0Labels = mixedMoment B raw25249step1 raw25249step1Labels := by
      have ha : raw25249step1 = raw25249step0 := by apply Matrix.ext; unfold raw25249step1 raw25249step0; decide +kernel
      have hl : raw25249step0Labels = labelEmbedding6 ∘ raw25249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25249step0 raw25249step0Labels raw25249step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical25250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25250 raw25250Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw25250 raw25250Labels = mixedMoment B raw25250step0 raw25250step0Labels := by
      have ha : raw25250step0 = (fun i j => raw25250 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25250step0 raw25250; decide +kernel
      have hl : raw25250step0Labels = raw25250Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25250 raw25250Labels permutation168 permutation3
    mixedMoment B raw25250step0 raw25250step0Labels = mixedMoment B raw25250step1 raw25250step1Labels := by
      have ha : raw25250step1 = raw25250step0 := by apply Matrix.ext; unfold raw25250step1 raw25250step0; decide +kernel
      have hl : raw25250step0Labels = labelEmbedding6 ∘ raw25250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25250step0 raw25250step0Labels raw25250step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical25251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25251 raw25251Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw25251 raw25251Labels = mixedMoment B raw25251step0 raw25251step0Labels := by
      have hz : ∀ j, raw25251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25251step0 = (fun i j => raw25251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25251step0 raw25251; decide +kernel
      have hl : raw25251step0Labels = raw25251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25251 raw25251Labels permutation346 hz
    mixedMoment B raw25251step0 raw25251step0Labels = mixedMoment B raw25251step1 raw25251step1Labels := by
      have ha : raw25251step1 = (fun i j => raw25251step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25251step1 raw25251step0; decide +kernel
      have hl : raw25251step1Labels = raw25251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25251step0 raw25251step0Labels permutation35 permutation3
    mixedMoment B raw25251step1 raw25251step1Labels = mixedMoment B raw25251step2 raw25251step2Labels := by
      have ha : raw25251step2 = raw25251step1 := by apply Matrix.ext; unfold raw25251step2 raw25251step1; decide +kernel
      have hl : raw25251step1Labels = labelEmbedding6 ∘ raw25251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25251step1 raw25251step1Labels raw25251step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

theorem canonical25252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25252 raw25252Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25252 raw25252Labels = mixedMoment B raw25252step0 raw25252step0Labels := by
      have hz : ∀ j, raw25252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25252step0 = (fun i j => raw25252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25252step0 raw25252; decide +kernel
      have hl : raw25252step0Labels = raw25252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25252 raw25252Labels permutation346 hz
    mixedMoment B raw25252step0 raw25252step0Labels = mixedMoment B raw25252step1 raw25252step1Labels := by
      have ha : raw25252step1 = (fun i j => raw25252step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25252step1 raw25252step0; decide +kernel
      have hl : raw25252step1Labels = raw25252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25252step0 raw25252step0Labels permutation35 permutation3
    mixedMoment B raw25252step1 raw25252step1Labels = mixedMoment B raw25252step2 raw25252step2Labels := by
      have ha : raw25252step2 = raw25252step1 := by apply Matrix.ext; unfold raw25252step2 raw25252step1; decide +kernel
      have hl : raw25252step1Labels = labelEmbedding6 ∘ raw25252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25252step1 raw25252step1Labels raw25252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical25253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25253 raw25253Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw25253 raw25253Labels = mixedMoment B raw25253step0 raw25253step0Labels := by
      have ha : raw25253step0 = (fun i j => raw25253 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25253step0 raw25253; decide +kernel
      have hl : raw25253step0Labels = raw25253Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25253 raw25253Labels permutation179 permutation3
    mixedMoment B raw25253step0 raw25253step0Labels = mixedMoment B raw25253step1 raw25253step1Labels := by
      have ha : raw25253step1 = raw25253step0 := by apply Matrix.ext; unfold raw25253step1 raw25253step0; decide +kernel
      have hl : raw25253step0Labels = labelEmbedding6 ∘ raw25253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25253step0 raw25253step0Labels raw25253step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

theorem canonical25254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25254 raw25254Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw25254 raw25254Labels = mixedMoment B raw25254step0 raw25254step0Labels := by
      have hz : ∀ j, raw25254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25254step0 = (fun i j => raw25254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25254step0 raw25254; decide +kernel
      have hl : raw25254step0Labels = raw25254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25254 raw25254Labels permutation346 hz
    mixedMoment B raw25254step0 raw25254step0Labels = mixedMoment B raw25254step1 raw25254step1Labels := by
      have ha : raw25254step1 = (fun i j => raw25254step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25254step1 raw25254step0; decide +kernel
      have hl : raw25254step1Labels = raw25254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25254step0 raw25254step0Labels permutation45 permutation3
    mixedMoment B raw25254step1 raw25254step1Labels = mixedMoment B raw25254step2 raw25254step2Labels := by
      have ha : raw25254step2 = raw25254step1 := by apply Matrix.ext; unfold raw25254step2 raw25254step1; decide +kernel
      have hl : raw25254step1Labels = labelEmbedding6 ∘ raw25254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25254step1 raw25254step1Labels raw25254step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

theorem canonical25255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25255 raw25255Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25255 raw25255Labels = mixedMoment B raw25255step0 raw25255step0Labels := by
      have hz : ∀ j, raw25255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25255step0 = (fun i j => raw25255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25255step0 raw25255; decide +kernel
      have hl : raw25255step0Labels = raw25255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25255 raw25255Labels permutation346 hz
    mixedMoment B raw25255step0 raw25255step0Labels = mixedMoment B raw25255step1 raw25255step1Labels := by
      have ha : raw25255step1 = (fun i j => raw25255step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25255step1 raw25255step0; decide +kernel
      have hl : raw25255step1Labels = raw25255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25255step0 raw25255step0Labels permutation35 permutation3
    mixedMoment B raw25255step1 raw25255step1Labels = mixedMoment B raw25255step2 raw25255step2Labels := by
      have ha : raw25255step2 = raw25255step1 := by apply Matrix.ext; unfold raw25255step2 raw25255step1; decide +kernel
      have hl : raw25255step1Labels = labelEmbedding6 ∘ raw25255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25255step1 raw25255step1Labels raw25255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw270 raw270Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw270 raw270Labels = mixedMoment B raw270step0 raw270step0Labels := by
      have ha : raw270step0 = (fun i j => raw270 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw270step0 raw270; decide +kernel
      have hl : raw270step0Labels = raw270Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw270 raw270Labels permutation8 permutation5
    mixedMoment B raw270step0 raw270step0Labels = mixedMoment B raw270step1 raw270step1Labels := by
      have ha : raw270step1 = raw270step0 := by apply Matrix.ext; unfold raw270step1 raw270step0; decide +kernel
      have hl : raw270step0Labels = labelEmbedding1 ∘ raw270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw270step0 raw270step0Labels raw270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw271 raw271Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw271 raw271Labels = mixedMoment B raw271step0 raw271step0Labels := by
      have ha : raw271step0 = (fun i j => raw271 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw271step0 raw271; decide +kernel
      have hl : raw271step0Labels = raw271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw271 raw271Labels permutation8 permutation5
    _ = mixedMoment B node404 node404Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2766 raw2766Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2766 raw2766Labels = mixedMoment B raw2766step0 raw2766step0Labels := by
      have hz : ∀ j, raw2766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2766step0 = (fun i j => raw2766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2766step0 raw2766; decide +kernel
      have hl : raw2766step0Labels = raw2766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2766 raw2766Labels permutation346 hz
    mixedMoment B raw2766step0 raw2766step0Labels = mixedMoment B raw2766step1 raw2766step1Labels := by
      have ha : raw2766step1 = (fun i j => raw2766step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2766step1 raw2766step0; decide +kernel
      have hl : raw2766step1Labels = raw2766step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2766step0 raw2766step0Labels permutation44 permutation3
    mixedMoment B raw2766step1 raw2766step1Labels = mixedMoment B raw2766step2 raw2766step2Labels := by
      have ha : raw2766step2 = raw2766step1 := by apply Matrix.ext; unfold raw2766step2 raw2766step1; decide +kernel
      have hl : raw2766step1Labels = labelEmbedding6 ∘ raw2766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2766step1 raw2766step1Labels raw2766step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2771 raw2771Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2771 raw2771Labels = mixedMoment B raw2771step0 raw2771step0Labels := by
      have hz : ∀ j, raw2771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2771step0 = (fun i j => raw2771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2771step0 raw2771; decide +kernel
      have hl : raw2771step0Labels = raw2771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2771 raw2771Labels permutation434 hz
    mixedMoment B raw2771step0 raw2771step0Labels = mixedMoment B raw2771step1 raw2771step1Labels := by
      have hz : ∀ j, raw2771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2771step1 = (fun i j => raw2771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2771step1 raw2771step0; decide +kernel
      have hl : raw2771step1Labels = raw2771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2771step0 raw2771step0Labels permutation80 hz
    mixedMoment B raw2771step1 raw2771step1Labels = mixedMoment B raw2771step2 raw2771step2Labels := by
      have ha : raw2771step2 = (fun i j => raw2771step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2771step2 raw2771step1; decide +kernel
      have hl : raw2771step2Labels = raw2771step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2771step1 raw2771step1Labels permutation8 permutation3
    mixedMoment B raw2771step2 raw2771step2Labels = mixedMoment B raw2771step3 raw2771step3Labels := by
      have ha : raw2771step3 = raw2771step2 := by apply Matrix.ext; unfold raw2771step3 raw2771step2; decide +kernel
      have hl : raw2771step2Labels = labelEmbedding6 ∘ raw2771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2771step2 raw2771step2Labels raw2771step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4931 raw4931Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw4931 raw4931Labels = mixedMoment B raw4931step0 raw4931step0Labels := by
      have hz : ∀ j, raw4931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4931step0 = (fun i j => raw4931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4931step0 raw4931; decide +kernel
      have hl : raw4931step0Labels = raw4931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4931 raw4931Labels permutation346 hz
    mixedMoment B raw4931step0 raw4931step0Labels = mixedMoment B raw4931step1 raw4931step1Labels := by
      have ha : raw4931step1 = (fun i j => raw4931step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4931step1 raw4931step0; decide +kernel
      have hl : raw4931step1Labels = raw4931step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4931step0 raw4931step0Labels permutation44 permutation3
    mixedMoment B raw4931step1 raw4931step1Labels = mixedMoment B raw4931step2 raw4931step2Labels := by
      have ha : raw4931step2 = raw4931step1 := by apply Matrix.ext; unfold raw4931step2 raw4931step1; decide +kernel
      have hl : raw4931step1Labels = labelEmbedding6 ∘ raw4931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4931step1 raw4931step1Labels raw4931step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

theorem canonical4935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4935 raw4935Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw4935 raw4935Labels = mixedMoment B raw4935step0 raw4935step0Labels := by
      have hz : ∀ j, raw4935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4935step0 = (fun i j => raw4935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4935step0 raw4935; decide +kernel
      have hl : raw4935step0Labels = raw4935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4935 raw4935Labels permutation434 hz
    mixedMoment B raw4935step0 raw4935step0Labels = mixedMoment B raw4935step1 raw4935step1Labels := by
      have hz : ∀ j, raw4935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4935step1 = (fun i j => raw4935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4935step1 raw4935step0; decide +kernel
      have hl : raw4935step1Labels = raw4935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4935step0 raw4935step0Labels permutation80 hz
    mixedMoment B raw4935step1 raw4935step1Labels = mixedMoment B raw4935step2 raw4935step2Labels := by
      have ha : raw4935step2 = (fun i j => raw4935step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4935step2 raw4935step1; decide +kernel
      have hl : raw4935step2Labels = raw4935step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4935step1 raw4935step1Labels permutation8 permutation3
    mixedMoment B raw4935step2 raw4935step2Labels = mixedMoment B raw4935step3 raw4935step3Labels := by
      have ha : raw4935step3 = raw4935step2 := by apply Matrix.ext; unfold raw4935step3 raw4935step2; decide +kernel
      have hl : raw4935step2Labels = labelEmbedding6 ∘ raw4935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4935step2 raw4935step2Labels raw4935step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

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

theorem canonical675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw675 raw675Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw675 raw675Labels = mixedMoment B raw675step0 raw675step0Labels := by
      have ha : raw675step0 = (fun i j => raw675 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw675step0 raw675; decide +kernel
      have hl : raw675step0Labels = raw675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw675 raw675Labels permutation32 permutation4
    mixedMoment B raw675step0 raw675step0Labels = mixedMoment B raw675step1 raw675step1Labels := by
      have ha : raw675step1 = raw675step0 := by apply Matrix.ext; unfold raw675step1 raw675step0; decide +kernel
      have hl : raw675step0Labels = labelEmbedding7 ∘ raw675step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw675step0 raw675step0Labels raw675step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4101 node4101Labels := by rfl

theorem canonical676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw676 raw676Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw676 raw676Labels = mixedMoment B raw676step0 raw676step0Labels := by
      have ha : raw676step0 = (fun i j => raw676 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw676step0 raw676; decide +kernel
      have hl : raw676step0Labels = raw676Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw676 raw676Labels permutation32 permutation4
    _ = mixedMoment B node538 node538Labels := by rfl

theorem canonical677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw677 raw677Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw677 raw677Labels = mixedMoment B raw677step0 raw677step0Labels := by
      have ha : raw677step0 = (fun i j => raw677 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw677step0 raw677; decide +kernel
      have hl : raw677step0Labels = raw677Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw677 raw677Labels permutation38 permutation6
    mixedMoment B raw677step0 raw677step0Labels = mixedMoment B raw677step1 raw677step1Labels := by
      have ha : raw677step1 = -raw677step0 := by apply Matrix.ext; change ∀ i j, raw677step1 i j = -(raw677step0 i j); unfold raw677step1 raw677step0; decide +kernel
      have hl : raw677step1Labels = raw677step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw677step1 raw677step1Labels = mixedMoment B raw677step2 raw677step2Labels := by
      have ha : raw677step2 = raw677step1 := by apply Matrix.ext; unfold raw677step2 raw677step1; decide +kernel
      have hl : raw677step1Labels = labelEmbedding1 ∘ raw677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw677step1 raw677step1Labels raw677step2Labels labelEmbedding1 hl
    _ = mixedMoment B node663 node663Labels := by rfl

theorem canonical678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw678 raw678Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw678 raw678Labels = mixedMoment B raw678step0 raw678step0Labels := by
      have ha : raw678step0 = (fun i j => raw678 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw678step0 raw678; decide +kernel
      have hl : raw678step0Labels = raw678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw678 raw678Labels permutation32 permutation4
    mixedMoment B raw678step0 raw678step0Labels = mixedMoment B raw678step1 raw678step1Labels := by
      have ha : raw678step1 = raw678step0 := by apply Matrix.ext; unfold raw678step1 raw678step0; decide +kernel
      have hl : raw678step0Labels = labelEmbedding7 ∘ raw678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw678step0 raw678step0Labels raw678step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

theorem canonical679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw679 raw679Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw679 raw679Labels = mixedMoment B raw679step0 raw679step0Labels := by
      have ha : raw679step0 = (fun i j => raw679 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw679step0 raw679; decide +kernel
      have hl : raw679step0Labels = raw679Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw679 raw679Labels permutation32 permutation4
    _ = mixedMoment B node539 node539Labels := by rfl

theorem canonical680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw680 raw680Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw680 raw680Labels = mixedMoment B raw680step0 raw680step0Labels := by
      have ha : raw680step0 = (fun i j => raw680 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw680step0 raw680; decide +kernel
      have hl : raw680step0Labels = raw680Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw680 raw680Labels permutation38 permutation6
    mixedMoment B raw680step0 raw680step0Labels = mixedMoment B raw680step1 raw680step1Labels := by
      have ha : raw680step1 = -raw680step0 := by apply Matrix.ext; change ∀ i j, raw680step1 i j = -(raw680step0 i j); unfold raw680step1 raw680step0; decide +kernel
      have hl : raw680step1Labels = raw680step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw680step1 raw680step1Labels = mixedMoment B raw680step2 raw680step2Labels := by
      have ha : raw680step2 = raw680step1 := by apply Matrix.ext; unfold raw680step2 raw680step1; decide +kernel
      have hl : raw680step1Labels = labelEmbedding1 ∘ raw680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw680step1 raw680step1Labels raw680step2Labels labelEmbedding1 hl
    _ = mixedMoment B node664 node664Labels := by rfl

theorem canonical693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw693 raw693Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw693 raw693Labels = mixedMoment B raw693step0 raw693step0Labels := by
      have ha : raw693step0 = (fun i j => raw693 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw693step0 raw693; decide +kernel
      have hl : raw693step0Labels = raw693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw693 raw693Labels permutation32 permutation4
    mixedMoment B raw693step0 raw693step0Labels = mixedMoment B raw693step1 raw693step1Labels := by
      have ha : raw693step1 = raw693step0 := by apply Matrix.ext; unfold raw693step1 raw693step0; decide +kernel
      have hl : raw693step0Labels = labelEmbedding7 ∘ raw693step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw693step0 raw693step0Labels raw693step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4107 node4107Labels := by rfl

theorem canonical694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw694 raw694Labels = mixedMoment B node544 node544Labels := by
  calc
    mixedMoment B raw694 raw694Labels = mixedMoment B raw694step0 raw694step0Labels := by
      have ha : raw694step0 = (fun i j => raw694 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw694step0 raw694; decide +kernel
      have hl : raw694step0Labels = raw694Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw694 raw694Labels permutation32 permutation4
    _ = mixedMoment B node544 node544Labels := by rfl

theorem canonical695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw695 raw695Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw695 raw695Labels = mixedMoment B raw695step0 raw695step0Labels := by
      have ha : raw695step0 = (fun i j => raw695 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw695step0 raw695; decide +kernel
      have hl : raw695step0Labels = raw695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw695 raw695Labels permutation32 permutation6
    mixedMoment B raw695step0 raw695step0Labels = mixedMoment B raw695step1 raw695step1Labels := by
      have ha : raw695step1 = -raw695step0 := by apply Matrix.ext; change ∀ i j, raw695step1 i j = -(raw695step0 i j); unfold raw695step1 raw695step0; decide +kernel
      have hl : raw695step1Labels = raw695step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw695step1 raw695step1Labels = mixedMoment B raw695step2 raw695step2Labels := by
      have ha : raw695step2 = raw695step1 := by apply Matrix.ext; unfold raw695step2 raw695step1; decide +kernel
      have hl : raw695step1Labels = labelEmbedding1 ∘ raw695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw695step1 raw695step1Labels raw695step2Labels labelEmbedding1 hl
    _ = mixedMoment B node682 node682Labels := by rfl

theorem canonical723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw723 raw723Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw723 raw723Labels = mixedMoment B raw723step0 raw723step0Labels := by
      have ha : raw723step0 = (fun i j => raw723 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw723step0 raw723; decide +kernel
      have hl : raw723step0Labels = raw723Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw723 raw723Labels permutation32 permutation4
    mixedMoment B raw723step0 raw723step0Labels = mixedMoment B raw723step1 raw723step1Labels := by
      have ha : raw723step1 = raw723step0 := by apply Matrix.ext; unfold raw723step1 raw723step0; decide +kernel
      have hl : raw723step0Labels = labelEmbedding7 ∘ raw723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw723step0 raw723step0Labels raw723step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

theorem canonical724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw724 raw724Labels = mixedMoment B node554 node554Labels := by
  calc
    mixedMoment B raw724 raw724Labels = mixedMoment B raw724step0 raw724step0Labels := by
      have ha : raw724step0 = (fun i j => raw724 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw724step0 raw724; decide +kernel
      have hl : raw724step0Labels = raw724Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw724 raw724Labels permutation32 permutation4
    _ = mixedMoment B node554 node554Labels := by rfl

theorem canonical725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw725 raw725Labels = mixedMoment B node668 node668Labels := by
  calc
    mixedMoment B raw725 raw725Labels = mixedMoment B raw725step0 raw725step0Labels := by
      have ha : raw725step0 = (fun i j => raw725 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw725step0 raw725; decide +kernel
      have hl : raw725step0Labels = raw725Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw725 raw725Labels permutation33 permutation6
    mixedMoment B raw725step0 raw725step0Labels = mixedMoment B raw725step1 raw725step1Labels := by
      have ha : raw725step1 = -raw725step0 := by apply Matrix.ext; change ∀ i j, raw725step1 i j = -(raw725step0 i j); unfold raw725step1 raw725step0; decide +kernel
      have hl : raw725step1Labels = raw725step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw725step1 raw725step1Labels = mixedMoment B raw725step2 raw725step2Labels := by
      have ha : raw725step2 = raw725step1 := by apply Matrix.ext; unfold raw725step2 raw725step1; decide +kernel
      have hl : raw725step1Labels = labelEmbedding1 ∘ raw725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw725step1 raw725step1Labels raw725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node668 node668Labels := by rfl

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

theorem canonical1023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1023 raw1023Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw1023 raw1023Labels = mixedMoment B raw1023step0 raw1023step0Labels := by
      have ha : raw1023step0 = (fun i j => raw1023 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1023step0 raw1023; decide +kernel
      have hl : raw1023step0Labels = raw1023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1023 raw1023Labels permutation152 permutation4
    mixedMoment B raw1023step0 raw1023step0Labels = mixedMoment B raw1023step1 raw1023step1Labels := by
      have ha : raw1023step1 = raw1023step0 := by apply Matrix.ext; unfold raw1023step1 raw1023step0; decide +kernel
      have hl : raw1023step0Labels = labelEmbedding7 ∘ raw1023step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1023step0 raw1023step0Labels raw1023step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

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

theorem canonical1024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1024 raw1024Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw1024 raw1024Labels = mixedMoment B raw1024step0 raw1024step0Labels := by
      have ha : raw1024step0 = (fun i j => raw1024 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1024step0 raw1024; decide +kernel
      have hl : raw1024step0Labels = raw1024Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1024 raw1024Labels permutation152 permutation4
    _ = mixedMoment B node865 node865Labels := by rfl

theorem canonical1025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1025 raw1025Labels = mixedMoment B node1553 node1553Labels := by
  calc
    mixedMoment B raw1025 raw1025Labels = mixedMoment B raw1025step0 raw1025step0Labels := by
      have ha : raw1025step0 = (fun i j => raw1025 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1025step0 raw1025; decide +kernel
      have hl : raw1025step0Labels = raw1025Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1025 raw1025Labels permutation158 permutation6
    mixedMoment B raw1025step0 raw1025step0Labels = mixedMoment B raw1025step1 raw1025step1Labels := by
      have ha : raw1025step1 = -raw1025step0 := by apply Matrix.ext; change ∀ i j, raw1025step1 i j = -(raw1025step0 i j); unfold raw1025step1 raw1025step0; decide +kernel
      have hl : raw1025step1Labels = raw1025step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1025step1 raw1025step1Labels = mixedMoment B raw1025step2 raw1025step2Labels := by
      have ha : raw1025step2 = raw1025step1 := by apply Matrix.ext; unfold raw1025step2 raw1025step1; decide +kernel
      have hl : raw1025step1Labels = labelEmbedding1 ∘ raw1025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1025step1 raw1025step1Labels raw1025step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1553 node1553Labels := by rfl

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

theorem canonical1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1038 raw1038Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw1038 raw1038Labels = mixedMoment B raw1038step0 raw1038step0Labels := by
      have ha : raw1038step0 = (fun i j => raw1038 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1038step0 raw1038; decide +kernel
      have hl : raw1038step0Labels = raw1038Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1038 raw1038Labels permutation152 permutation4
    mixedMoment B raw1038step0 raw1038step0Labels = mixedMoment B raw1038step1 raw1038step1Labels := by
      have ha : raw1038step1 = raw1038step0 := by apply Matrix.ext; unfold raw1038step1 raw1038step0; decide +kernel
      have hl : raw1038step0Labels = labelEmbedding7 ∘ raw1038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1038step0 raw1038step0Labels raw1038step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

theorem canonical1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1039 raw1039Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw1039 raw1039Labels = mixedMoment B raw1039step0 raw1039step0Labels := by
      have ha : raw1039step0 = (fun i j => raw1039 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1039step0 raw1039; decide +kernel
      have hl : raw1039step0Labels = raw1039Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1039 raw1039Labels permutation152 permutation4
    _ = mixedMoment B node870 node870Labels := by rfl

theorem canonical1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1040 raw1040Labels = mixedMoment B node1567 node1567Labels := by
  calc
    mixedMoment B raw1040 raw1040Labels = mixedMoment B raw1040step0 raw1040step0Labels := by
      have ha : raw1040step0 = (fun i j => raw1040 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1040step0 raw1040; decide +kernel
      have hl : raw1040step0Labels = raw1040Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1040 raw1040Labels permutation152 permutation6
    mixedMoment B raw1040step0 raw1040step0Labels = mixedMoment B raw1040step1 raw1040step1Labels := by
      have ha : raw1040step1 = -raw1040step0 := by apply Matrix.ext; change ∀ i j, raw1040step1 i j = -(raw1040step0 i j); unfold raw1040step1 raw1040step0; decide +kernel
      have hl : raw1040step1Labels = raw1040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1040step1 raw1040step1Labels = mixedMoment B raw1040step2 raw1040step2Labels := by
      have ha : raw1040step2 = raw1040step1 := by apply Matrix.ext; unfold raw1040step2 raw1040step1; decide +kernel
      have hl : raw1040step1Labels = labelEmbedding1 ∘ raw1040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1040step1 raw1040step1Labels raw1040step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1567 node1567Labels := by rfl

theorem canonical1062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1062 raw1062Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw1062 raw1062Labels = mixedMoment B raw1062step0 raw1062step0Labels := by
      have ha : raw1062step0 = (fun i j => raw1062 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1062step0 raw1062; decide +kernel
      have hl : raw1062step0Labels = raw1062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1062 raw1062Labels permutation152 permutation4
    mixedMoment B raw1062step0 raw1062step0Labels = mixedMoment B raw1062step1 raw1062step1Labels := by
      have ha : raw1062step1 = raw1062step0 := by apply Matrix.ext; unfold raw1062step1 raw1062step0; decide +kernel
      have hl : raw1062step0Labels = labelEmbedding7 ∘ raw1062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1062step0 raw1062step0Labels raw1062step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

theorem canonical1063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1063 raw1063Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw1063 raw1063Labels = mixedMoment B raw1063step0 raw1063step0Labels := by
      have ha : raw1063step0 = (fun i j => raw1063 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1063step0 raw1063; decide +kernel
      have hl : raw1063step0Labels = raw1063Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1063 raw1063Labels permutation152 permutation4
    _ = mixedMoment B node879 node879Labels := by rfl

theorem canonical1064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1064 raw1064Labels = mixedMoment B node1556 node1556Labels := by
  calc
    mixedMoment B raw1064 raw1064Labels = mixedMoment B raw1064step0 raw1064step0Labels := by
      have ha : raw1064step0 = (fun i j => raw1064 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1064step0 raw1064; decide +kernel
      have hl : raw1064step0Labels = raw1064Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1064 raw1064Labels permutation153 permutation6
    mixedMoment B raw1064step0 raw1064step0Labels = mixedMoment B raw1064step1 raw1064step1Labels := by
      have ha : raw1064step1 = -raw1064step0 := by apply Matrix.ext; change ∀ i j, raw1064step1 i j = -(raw1064step0 i j); unfold raw1064step1 raw1064step0; decide +kernel
      have hl : raw1064step1Labels = raw1064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1064step1 raw1064step1Labels = mixedMoment B raw1064step2 raw1064step2Labels := by
      have ha : raw1064step2 = raw1064step1 := by apply Matrix.ext; unfold raw1064step2 raw1064step1; decide +kernel
      have hl : raw1064step1Labels = labelEmbedding1 ∘ raw1064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1064step1 raw1064step1Labels raw1064step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1556 node1556Labels := by rfl

theorem canonical1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1128 raw1128Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw1128 raw1128Labels = mixedMoment B raw1128step0 raw1128step0Labels := by
      have ha : raw1128step0 = (fun i j => raw1128 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1128step0 raw1128; decide +kernel
      have hl : raw1128step0Labels = raw1128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1128 raw1128Labels permutation152 permutation4
    mixedMoment B raw1128step0 raw1128step0Labels = mixedMoment B raw1128step1 raw1128step1Labels := by
      have ha : raw1128step1 = raw1128step0 := by apply Matrix.ext; unfold raw1128step1 raw1128step0; decide +kernel
      have hl : raw1128step0Labels = labelEmbedding7 ∘ raw1128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1128step0 raw1128step0Labels raw1128step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1129 raw1129Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw1129 raw1129Labels = mixedMoment B raw1129step0 raw1129step0Labels := by
      have ha : raw1129step0 = (fun i j => raw1129 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1129step0 raw1129; decide +kernel
      have hl : raw1129step0Labels = raw1129Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1129 raw1129Labels permutation152 permutation4
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1130 raw1130Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw1130 raw1130Labels = mixedMoment B raw1130step0 raw1130step0Labels := by
      have ha : raw1130step0 = (fun i j => raw1130 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1130step0 raw1130; decide +kernel
      have hl : raw1130step0Labels = raw1130Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1130 raw1130Labels permutation152 permutation6
    mixedMoment B raw1130step0 raw1130step0Labels = mixedMoment B raw1130step1 raw1130step1Labels := by
      have ha : raw1130step1 = -raw1130step0 := by apply Matrix.ext; change ∀ i j, raw1130step1 i j = -(raw1130step0 i j); unfold raw1130step1 raw1130step0; decide +kernel
      have hl : raw1130step1Labels = raw1130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1130step1 raw1130step1Labels = mixedMoment B raw1130step2 raw1130step2Labels := by
      have ha : raw1130step2 = raw1130step1 := by apply Matrix.ext; unfold raw1130step2 raw1130step1; decide +kernel
      have hl : raw1130step1Labels = labelEmbedding1 ∘ raw1130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1130step1 raw1130step1Labels raw1130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

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

theorem canonical1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1149 raw1149Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw1149 raw1149Labels = mixedMoment B raw1149step0 raw1149step0Labels := by
      have ha : raw1149step0 = (fun i j => raw1149 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1149step0 raw1149; decide +kernel
      have hl : raw1149step0Labels = raw1149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1149 raw1149Labels permutation32 permutation4
    mixedMoment B raw1149step0 raw1149step0Labels = mixedMoment B raw1149step1 raw1149step1Labels := by
      have ha : raw1149step1 = raw1149step0 := by apply Matrix.ext; unfold raw1149step1 raw1149step0; decide +kernel
      have hl : raw1149step0Labels = labelEmbedding7 ∘ raw1149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1149step0 raw1149step0Labels raw1149step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1150 raw1150Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw1150 raw1150Labels = mixedMoment B raw1150step0 raw1150step0Labels := by
      have ha : raw1150step0 = (fun i j => raw1150 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1150step0 raw1150; decide +kernel
      have hl : raw1150step0Labels = raw1150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1150 raw1150Labels permutation32 permutation4
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1151 raw1151Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw1151 raw1151Labels = mixedMoment B raw1151step0 raw1151step0Labels := by
      have ha : raw1151step0 = (fun i j => raw1151 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1151step0 raw1151; decide +kernel
      have hl : raw1151step0Labels = raw1151Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1151 raw1151Labels permutation32 permutation6
    mixedMoment B raw1151step0 raw1151step0Labels = mixedMoment B raw1151step1 raw1151step1Labels := by
      have ha : raw1151step1 = -raw1151step0 := by apply Matrix.ext; change ∀ i j, raw1151step1 i j = -(raw1151step0 i j); unfold raw1151step1 raw1151step0; decide +kernel
      have hl : raw1151step1Labels = raw1151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1151step1 raw1151step1Labels = mixedMoment B raw1151step2 raw1151step2Labels := by
      have ha : raw1151step2 = raw1151step1 := by apply Matrix.ext; unfold raw1151step2 raw1151step1; decide +kernel
      have hl : raw1151step1Labels = labelEmbedding1 ∘ raw1151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1151step1 raw1151step1Labels raw1151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

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

theorem canonical1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1212 raw1212Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw1212 raw1212Labels = mixedMoment B raw1212step0 raw1212step0Labels := by
      have ha : raw1212step0 = (fun i j => raw1212 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1212step0 raw1212; decide +kernel
      have hl : raw1212step0Labels = raw1212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1212 raw1212Labels permutation152 permutation4
    mixedMoment B raw1212step0 raw1212step0Labels = mixedMoment B raw1212step1 raw1212step1Labels := by
      have ha : raw1212step1 = raw1212step0 := by apply Matrix.ext; unfold raw1212step1 raw1212step0; decide +kernel
      have hl : raw1212step0Labels = labelEmbedding7 ∘ raw1212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1212step0 raw1212step0Labels raw1212step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1213 raw1213Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw1213 raw1213Labels = mixedMoment B raw1213step0 raw1213step0Labels := by
      have ha : raw1213step0 = (fun i j => raw1213 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1213step0 raw1213; decide +kernel
      have hl : raw1213step0Labels = raw1213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1213 raw1213Labels permutation152 permutation4
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical1214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1214 raw1214Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw1214 raw1214Labels = mixedMoment B raw1214step0 raw1214step0Labels := by
      have ha : raw1214step0 = (fun i j => raw1214 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1214step0 raw1214; decide +kernel
      have hl : raw1214step0Labels = raw1214Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1214 raw1214Labels permutation152 permutation6
    mixedMoment B raw1214step0 raw1214step0Labels = mixedMoment B raw1214step1 raw1214step1Labels := by
      have ha : raw1214step1 = -raw1214step0 := by apply Matrix.ext; change ∀ i j, raw1214step1 i j = -(raw1214step0 i j); unfold raw1214step1 raw1214step0; decide +kernel
      have hl : raw1214step1Labels = raw1214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1214step1 raw1214step1Labels = mixedMoment B raw1214step2 raw1214step2Labels := by
      have ha : raw1214step2 = raw1214step1 := by apply Matrix.ext; unfold raw1214step2 raw1214step1; decide +kernel
      have hl : raw1214step1Labels = labelEmbedding1 ∘ raw1214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1214step1 raw1214step1Labels raw1214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1616 node1616Labels := by rfl

theorem canonical1215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1215 raw1215Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw1215 raw1215Labels = mixedMoment B raw1215step0 raw1215step0Labels := by
      have ha : raw1215step0 = (fun i j => raw1215 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1215step0 raw1215; decide +kernel
      have hl : raw1215step0Labels = raw1215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1215 raw1215Labels permutation32 permutation4
    mixedMoment B raw1215step0 raw1215step0Labels = mixedMoment B raw1215step1 raw1215step1Labels := by
      have ha : raw1215step1 = raw1215step0 := by apply Matrix.ext; unfold raw1215step1 raw1215step0; decide +kernel
      have hl : raw1215step0Labels = labelEmbedding7 ∘ raw1215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1215step0 raw1215step0Labels raw1215step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

theorem canonical1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1216 raw1216Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw1216 raw1216Labels = mixedMoment B raw1216step0 raw1216step0Labels := by
      have ha : raw1216step0 = (fun i j => raw1216 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1216step0 raw1216; decide +kernel
      have hl : raw1216step0Labels = raw1216Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1216 raw1216Labels permutation32 permutation4
    _ = mixedMoment B node982 node982Labels := by rfl

theorem canonical1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1217 raw1217Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw1217 raw1217Labels = mixedMoment B raw1217step0 raw1217step0Labels := by
      have ha : raw1217step0 = (fun i j => raw1217 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1217step0 raw1217; decide +kernel
      have hl : raw1217step0Labels = raw1217Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1217 raw1217Labels permutation32 permutation6
    mixedMoment B raw1217step0 raw1217step0Labels = mixedMoment B raw1217step1 raw1217step1Labels := by
      have ha : raw1217step1 = -raw1217step0 := by apply Matrix.ext; change ∀ i j, raw1217step1 i j = -(raw1217step0 i j); unfold raw1217step1 raw1217step0; decide +kernel
      have hl : raw1217step1Labels = raw1217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1217step1 raw1217step1Labels = mixedMoment B raw1217step2 raw1217step2Labels := by
      have ha : raw1217step2 = raw1217step1 := by apply Matrix.ext; unfold raw1217step2 raw1217step1; decide +kernel
      have hl : raw1217step1Labels = labelEmbedding1 ∘ raw1217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1217step1 raw1217step1Labels raw1217step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1617 node1617Labels := by rfl

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

theorem canonical1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1236 raw1236Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw1236 raw1236Labels = mixedMoment B raw1236step0 raw1236step0Labels := by
      have ha : raw1236step0 = (fun i j => raw1236 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1236step0 raw1236; decide +kernel
      have hl : raw1236step0Labels = raw1236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1236 raw1236Labels permutation32 permutation4
    mixedMoment B raw1236step0 raw1236step0Labels = mixedMoment B raw1236step1 raw1236step1Labels := by
      have ha : raw1236step1 = raw1236step0 := by apply Matrix.ext; unfold raw1236step1 raw1236step0; decide +kernel
      have hl : raw1236step0Labels = labelEmbedding7 ∘ raw1236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1236step0 raw1236step0Labels raw1236step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

theorem canonical1237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1237 raw1237Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw1237 raw1237Labels = mixedMoment B raw1237step0 raw1237step0Labels := by
      have ha : raw1237step0 = (fun i j => raw1237 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1237step0 raw1237; decide +kernel
      have hl : raw1237step0Labels = raw1237Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1237 raw1237Labels permutation32 permutation4
    _ = mixedMoment B node1005 node1005Labels := by rfl

theorem canonical1238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1238 raw1238Labels = mixedMoment B node1623 node1623Labels := by
  calc
    mixedMoment B raw1238 raw1238Labels = mixedMoment B raw1238step0 raw1238step0Labels := by
      have ha : raw1238step0 = (fun i j => raw1238 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1238step0 raw1238; decide +kernel
      have hl : raw1238step0Labels = raw1238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1238 raw1238Labels permutation33 permutation6
    mixedMoment B raw1238step0 raw1238step0Labels = mixedMoment B raw1238step1 raw1238step1Labels := by
      have ha : raw1238step1 = -raw1238step0 := by apply Matrix.ext; change ∀ i j, raw1238step1 i j = -(raw1238step0 i j); unfold raw1238step1 raw1238step0; decide +kernel
      have hl : raw1238step1Labels = raw1238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1238step1 raw1238step1Labels = mixedMoment B raw1238step2 raw1238step2Labels := by
      have ha : raw1238step2 = raw1238step1 := by apply Matrix.ext; unfold raw1238step2 raw1238step1; decide +kernel
      have hl : raw1238step1Labels = labelEmbedding1 ∘ raw1238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1238step1 raw1238step1Labels raw1238step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1623 node1623Labels := by rfl

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

theorem canonical1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1257 raw1257Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw1257 raw1257Labels = mixedMoment B raw1257step0 raw1257step0Labels := by
      have ha : raw1257step0 = (fun i j => raw1257 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1257step0 raw1257; decide +kernel
      have hl : raw1257step0Labels = raw1257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1257 raw1257Labels permutation32 permutation4
    mixedMoment B raw1257step0 raw1257step0Labels = mixedMoment B raw1257step1 raw1257step1Labels := by
      have ha : raw1257step1 = raw1257step0 := by apply Matrix.ext; unfold raw1257step1 raw1257step0; decide +kernel
      have hl : raw1257step0Labels = labelEmbedding7 ∘ raw1257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1257step0 raw1257step0Labels raw1257step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1258 raw1258Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw1258 raw1258Labels = mixedMoment B raw1258step0 raw1258step0Labels := by
      have ha : raw1258step0 = (fun i j => raw1258 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1258step0 raw1258; decide +kernel
      have hl : raw1258step0Labels = raw1258Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1258 raw1258Labels permutation32 permutation4
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1259 raw1259Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw1259 raw1259Labels = mixedMoment B raw1259step0 raw1259step0Labels := by
      have ha : raw1259step0 = (fun i j => raw1259 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1259step0 raw1259; decide +kernel
      have hl : raw1259step0Labels = raw1259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1259 raw1259Labels permutation40 permutation6
    mixedMoment B raw1259step0 raw1259step0Labels = mixedMoment B raw1259step1 raw1259step1Labels := by
      have ha : raw1259step1 = -raw1259step0 := by apply Matrix.ext; change ∀ i j, raw1259step1 i j = -(raw1259step0 i j); unfold raw1259step1 raw1259step0; decide +kernel
      have hl : raw1259step1Labels = raw1259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1259step1 raw1259step1Labels = mixedMoment B raw1259step2 raw1259step2Labels := by
      have ha : raw1259step2 = raw1259step1 := by apply Matrix.ext; unfold raw1259step2 raw1259step1; decide +kernel
      have hl : raw1259step1Labels = labelEmbedding1 ∘ raw1259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1259step1 raw1259step1Labels raw1259step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1263 raw1263Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw1263 raw1263Labels = mixedMoment B raw1263step0 raw1263step0Labels := by
      have ha : raw1263step0 = (fun i j => raw1263 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1263step0 raw1263; decide +kernel
      have hl : raw1263step0Labels = raw1263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1263 raw1263Labels permutation8 permutation4
    mixedMoment B raw1263step0 raw1263step0Labels = mixedMoment B raw1263step1 raw1263step1Labels := by
      have ha : raw1263step1 = raw1263step0 := by apply Matrix.ext; unfold raw1263step1 raw1263step0; decide +kernel
      have hl : raw1263step0Labels = labelEmbedding7 ∘ raw1263step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1263step0 raw1263step0Labels raw1263step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1264 raw1264Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw1264 raw1264Labels = mixedMoment B raw1264step0 raw1264step0Labels := by
      have ha : raw1264step0 = (fun i j => raw1264 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1264step0 raw1264; decide +kernel
      have hl : raw1264step0Labels = raw1264Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1264 raw1264Labels permutation8 permutation4
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical1265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1265 raw1265Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw1265 raw1265Labels = mixedMoment B raw1265step0 raw1265step0Labels := by
      have ha : raw1265step0 = (fun i j => raw1265 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1265step0 raw1265; decide +kernel
      have hl : raw1265step0Labels = raw1265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1265 raw1265Labels permutation10 permutation6
    mixedMoment B raw1265step0 raw1265step0Labels = mixedMoment B raw1265step1 raw1265step1Labels := by
      have ha : raw1265step1 = -raw1265step0 := by apply Matrix.ext; change ∀ i j, raw1265step1 i j = -(raw1265step0 i j); unfold raw1265step1 raw1265step0; decide +kernel
      have hl : raw1265step1Labels = raw1265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1265step1 raw1265step1Labels = mixedMoment B raw1265step2 raw1265step2Labels := by
      have ha : raw1265step2 = raw1265step1 := by apply Matrix.ext; unfold raw1265step2 raw1265step1; decide +kernel
      have hl : raw1265step1Labels = labelEmbedding1 ∘ raw1265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1265step1 raw1265step1Labels raw1265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical1275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1275 raw1275Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw1275 raw1275Labels = mixedMoment B raw1275step0 raw1275step0Labels := by
      have ha : raw1275step0 = (fun i j => raw1275 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1275step0 raw1275; decide +kernel
      have hl : raw1275step0Labels = raw1275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1275 raw1275Labels permutation8 permutation4
    mixedMoment B raw1275step0 raw1275step0Labels = mixedMoment B raw1275step1 raw1275step1Labels := by
      have ha : raw1275step1 = raw1275step0 := by apply Matrix.ext; unfold raw1275step1 raw1275step0; decide +kernel
      have hl : raw1275step0Labels = labelEmbedding7 ∘ raw1275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1275step0 raw1275step0Labels raw1275step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1276 raw1276Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw1276 raw1276Labels = mixedMoment B raw1276step0 raw1276step0Labels := by
      have ha : raw1276step0 = (fun i j => raw1276 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1276step0 raw1276; decide +kernel
      have hl : raw1276step0Labels = raw1276Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1276 raw1276Labels permutation8 permutation4
    _ = mixedMoment B node1050 node1050Labels := by rfl

theorem canonical1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1277 raw1277Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw1277 raw1277Labels = mixedMoment B raw1277step0 raw1277step0Labels := by
      have ha : raw1277step0 = (fun i j => raw1277 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1277step0 raw1277; decide +kernel
      have hl : raw1277step0Labels = raw1277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1277 raw1277Labels permutation8 permutation6
    mixedMoment B raw1277step0 raw1277step0Labels = mixedMoment B raw1277step1 raw1277step1Labels := by
      have ha : raw1277step1 = -raw1277step0 := by apply Matrix.ext; change ∀ i j, raw1277step1 i j = -(raw1277step0 i j); unfold raw1277step1 raw1277step0; decide +kernel
      have hl : raw1277step1Labels = raw1277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1277step1 raw1277step1Labels = mixedMoment B raw1277step2 raw1277step2Labels := by
      have ha : raw1277step2 = raw1277step1 := by apply Matrix.ext; unfold raw1277step2 raw1277step1; decide +kernel
      have hl : raw1277step1Labels = labelEmbedding1 ∘ raw1277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1277step1 raw1277step1Labels raw1277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_GroupedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit grouping formulas for the two- and three-column equality
patterns. These discharge the dependent finite-label calculations once,
so concrete certificate rows need only ordinary integer arithmetic. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family3_0 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1 + A i 2) := by
  change groupedColumns A (fun _ : Fin 3 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family3_1 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 1) =
      (fun i => ![A i 0 + A i 1, A i 2]) := by
  change groupedColumns A (![0, 0, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_2 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 2) =
      (fun i => ![A i 0 + A i 2, A i 1]) := by
  change groupedColumns A (![0, 1, 0] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_3 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 3) =
      (fun i => ![A i 0, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_4 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 4) = A := by
  change groupedColumns A (fun j : Fin 3 => j) = _
  ext i b
  simp [groupedColumns, Finset.sum_filter]

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleRules
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

/-- The five equality patterns for three sampled column indices. -/
theorem single_label_three {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 3) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family3 EqualityPatterns.covers3
  rw [sum_fin_five] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3,
    EqualityPatterns.blocks3, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Nat.descFactorial] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw781 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw781 = injectiveMoment H raw781step0 := by
      have heq : raw781step0 = -raw781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw781).symm
    injectiveMoment H raw781step0 = injectiveMoment H raw781step1 := by
      have heq : raw781step1 = (fun i j => raw781step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw781step0 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node404 node404Labels = Sparse.eval singlePairValue404 (familyPairVector B) := by
  have hp := single_label_three B hB node404
  have hl : node404Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node404 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node404 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node404 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node404 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value181 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 4) = PairSemantics.raw781 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node404 PairSemantics.raw781; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical781 hH).trans (PairSemantics.sound181 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue404, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value65, PairSemantics.value181, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2767 node2767Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw270 singletonSmall2767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2767) = raw270Labels := by decide +kernel
  rw [hl, canonical270 B hB] at h
  have hc0 : mixedMoment B raw270 (Fin.cases (0 : Fin 1) singletonSmall2767) =
      mixedMoment B node404 node404Labels := by
    have ha : raw270 = raw271 := by apply Matrix.ext; unfold raw270 raw271; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2767 = raw271Labels := by decide +kernel
    rw [ha, hj, canonical271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4101 node4101Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node538 node538Labels + mixedMoment B node663 node663Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw675 singletonSmall4101
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4101) = raw675Labels := by decide +kernel
  rw [hl, canonical675 B hB] at h
  have hc0 : mixedMoment B raw675 (Fin.cases (0 : Fin 2) singletonSmall4101) =
      mixedMoment B node538 node538Labels := by
    have ha : raw675 = raw676 := by apply Matrix.ext; unfold raw675 raw676; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4101 = raw676Labels := by decide +kernel
    rw [ha, hj, canonical676 B hB]
  have hc1 : mixedMoment B raw675 (Fin.cases (1 : Fin 2) singletonSmall4101) =
      mixedMoment B node663 node663Labels := by
    have ha : raw675 = raw677 := by apply Matrix.ext; unfold raw675 raw677; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4101 = raw677Labels := by decide +kernel
    rw [ha, hj, canonical677 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4102 node4102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node539 node539Labels + mixedMoment B node664 node664Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw678 singletonSmall4102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4102) = raw678Labels := by decide +kernel
  rw [hl, canonical678 B hB] at h
  have hc0 : mixedMoment B raw678 (Fin.cases (0 : Fin 2) singletonSmall4102) =
      mixedMoment B node539 node539Labels := by
    have ha : raw678 = raw679 := by apply Matrix.ext; unfold raw678 raw679; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4102 = raw679Labels := by decide +kernel
    rw [ha, hj, canonical679 B hB]
  have hc1 : mixedMoment B raw678 (Fin.cases (1 : Fin 2) singletonSmall4102) =
      mixedMoment B node664 node664Labels := by
    have ha : raw678 = raw680 := by apply Matrix.ext; unfold raw678 raw680; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4102 = raw680Labels := by decide +kernel
    rw [ha, hj, canonical680 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4107 node4107Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node544 node544Labels + mixedMoment B node682 node682Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw693 singletonSmall4107
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4107) = raw693Labels := by decide +kernel
  rw [hl, canonical693 B hB] at h
  have hc0 : mixedMoment B raw693 (Fin.cases (0 : Fin 2) singletonSmall4107) =
      mixedMoment B node544 node544Labels := by
    have ha : raw693 = raw694 := by apply Matrix.ext; unfold raw693 raw694; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4107 = raw694Labels := by decide +kernel
    rw [ha, hj, canonical694 B hB]
  have hc1 : mixedMoment B raw693 (Fin.cases (1 : Fin 2) singletonSmall4107) =
      mixedMoment B node682 node682Labels := by
    have ha : raw693 = raw695 := by apply Matrix.ext; unfold raw693 raw695; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4107 = raw695Labels := by decide +kernel
    rw [ha, hj, canonical695 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4119 node4119Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node554 node554Labels + mixedMoment B node668 node668Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw723 singletonSmall4119
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4119) = raw723Labels := by decide +kernel
  rw [hl, canonical723 B hB] at h
  have hc0 : mixedMoment B raw723 (Fin.cases (0 : Fin 2) singletonSmall4119) =
      mixedMoment B node554 node554Labels := by
    have ha : raw723 = raw724 := by apply Matrix.ext; unfold raw723 raw724; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4119 = raw724Labels := by decide +kernel
    rw [ha, hj, canonical724 B hB]
  have hc1 : mixedMoment B raw723 (Fin.cases (1 : Fin 2) singletonSmall4119) =
      mixedMoment B node668 node668Labels := by
    have ha : raw723 = raw725 := by apply Matrix.ext; unfold raw723 raw725; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4119 = raw725Labels := by decide +kernel
    rw [ha, hj, canonical725 B hB]
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

theorem singleton4287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4287 node4287Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node865 node865Labels + mixedMoment B node1553 node1553Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1023 singletonSmall4287
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4287) = raw1023Labels := by decide +kernel
  rw [hl, canonical1023 B hB] at h
  have hc0 : mixedMoment B raw1023 (Fin.cases (0 : Fin 2) singletonSmall4287) =
      mixedMoment B node865 node865Labels := by
    have ha : raw1023 = raw1024 := by apply Matrix.ext; unfold raw1023 raw1024; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4287 = raw1024Labels := by decide +kernel
    rw [ha, hj, canonical1024 B hB]
  have hc1 : mixedMoment B raw1023 (Fin.cases (1 : Fin 2) singletonSmall4287) =
      mixedMoment B node1553 node1553Labels := by
    have ha : raw1023 = raw1025 := by apply Matrix.ext; unfold raw1023 raw1025; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4287 = raw1025Labels := by decide +kernel
    rw [ha, hj, canonical1025 B hB]
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

theorem singleton4292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4292 node4292Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node870 node870Labels + mixedMoment B node1567 node1567Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1038 singletonSmall4292
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4292) = raw1038Labels := by decide +kernel
  rw [hl, canonical1038 B hB] at h
  have hc0 : mixedMoment B raw1038 (Fin.cases (0 : Fin 2) singletonSmall4292) =
      mixedMoment B node870 node870Labels := by
    have ha : raw1038 = raw1039 := by apply Matrix.ext; unfold raw1038 raw1039; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4292 = raw1039Labels := by decide +kernel
    rw [ha, hj, canonical1039 B hB]
  have hc1 : mixedMoment B raw1038 (Fin.cases (1 : Fin 2) singletonSmall4292) =
      mixedMoment B node1567 node1567Labels := by
    have ha : raw1038 = raw1040 := by apply Matrix.ext; unfold raw1038 raw1040; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4292 = raw1040Labels := by decide +kernel
    rw [ha, hj, canonical1040 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4301 node4301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node879 node879Labels + mixedMoment B node1556 node1556Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1062 singletonSmall4301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4301) = raw1062Labels := by decide +kernel
  rw [hl, canonical1062 B hB] at h
  have hc0 : mixedMoment B raw1062 (Fin.cases (0 : Fin 2) singletonSmall4301) =
      mixedMoment B node879 node879Labels := by
    have ha : raw1062 = raw1063 := by apply Matrix.ext; unfold raw1062 raw1063; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4301 = raw1063Labels := by decide +kernel
    rw [ha, hj, canonical1063 B hB]
  have hc1 : mixedMoment B raw1062 (Fin.cases (1 : Fin 2) singletonSmall4301) =
      mixedMoment B node1556 node1556Labels := by
    have ha : raw1062 = raw1064 := by apply Matrix.ext; unfold raw1062 raw1064; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4301 = raw1064Labels := by decide +kernel
    rw [ha, hj, canonical1064 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4344 node4344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node922 node922Labels + mixedMoment B node1673 node1673Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1128 singletonSmall4344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4344) = raw1128Labels := by decide +kernel
  rw [hl, canonical1128 B hB] at h
  have hc0 : mixedMoment B raw1128 (Fin.cases (0 : Fin 2) singletonSmall4344) =
      mixedMoment B node922 node922Labels := by
    have ha : raw1128 = raw1129 := by apply Matrix.ext; unfold raw1128 raw1129; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4344 = raw1129Labels := by decide +kernel
    rw [ha, hj, canonical1129 B hB]
  have hc1 : mixedMoment B raw1128 (Fin.cases (1 : Fin 2) singletonSmall4344) =
      mixedMoment B node1673 node1673Labels := by
    have ha : raw1128 = raw1130 := by apply Matrix.ext; unfold raw1128 raw1130; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4344 = raw1130Labels := by decide +kernel
    rw [ha, hj, canonical1130 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4355 node4355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node933 node933Labels + mixedMoment B node1691 node1691Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1149 singletonSmall4355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4355) = raw1149Labels := by decide +kernel
  rw [hl, canonical1149 B hB] at h
  have hc0 : mixedMoment B raw1149 (Fin.cases (0 : Fin 2) singletonSmall4355) =
      mixedMoment B node933 node933Labels := by
    have ha : raw1149 = raw1150 := by apply Matrix.ext; unfold raw1149 raw1150; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4355 = raw1150Labels := by decide +kernel
    rw [ha, hj, canonical1150 B hB]
  have hc1 : mixedMoment B raw1149 (Fin.cases (1 : Fin 2) singletonSmall4355) =
      mixedMoment B node1691 node1691Labels := by
    have ha : raw1149 = raw1151 := by apply Matrix.ext; unfold raw1149 raw1151; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4355 = raw1151Labels := by decide +kernel
    rw [ha, hj, canonical1151 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4399 node4399Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node980 node980Labels + mixedMoment B node1616 node1616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1212 singletonSmall4399
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4399) = raw1212Labels := by decide +kernel
  rw [hl, canonical1212 B hB] at h
  have hc0 : mixedMoment B raw1212 (Fin.cases (0 : Fin 2) singletonSmall4399) =
      mixedMoment B node980 node980Labels := by
    have ha : raw1212 = raw1213 := by apply Matrix.ext; unfold raw1212 raw1213; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4399 = raw1213Labels := by decide +kernel
    rw [ha, hj, canonical1213 B hB]
  have hc1 : mixedMoment B raw1212 (Fin.cases (1 : Fin 2) singletonSmall4399) =
      mixedMoment B node1616 node1616Labels := by
    have ha : raw1212 = raw1214 := by apply Matrix.ext; unfold raw1212 raw1214; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4399 = raw1214Labels := by decide +kernel
    rw [ha, hj, canonical1214 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4401 node4401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node982 node982Labels + mixedMoment B node1617 node1617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1215 singletonSmall4401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4401) = raw1215Labels := by decide +kernel
  rw [hl, canonical1215 B hB] at h
  have hc0 : mixedMoment B raw1215 (Fin.cases (0 : Fin 2) singletonSmall4401) =
      mixedMoment B node982 node982Labels := by
    have ha : raw1215 = raw1216 := by apply Matrix.ext; unfold raw1215 raw1216; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4401 = raw1216Labels := by decide +kernel
    rw [ha, hj, canonical1216 B hB]
  have hc1 : mixedMoment B raw1215 (Fin.cases (1 : Fin 2) singletonSmall4401) =
      mixedMoment B node1617 node1617Labels := by
    have ha : raw1215 = raw1217 := by apply Matrix.ext; unfold raw1215 raw1217; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4401 = raw1217Labels := by decide +kernel
    rw [ha, hj, canonical1217 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4424 node4424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1005 node1005Labels + mixedMoment B node1623 node1623Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1236 singletonSmall4424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4424) = raw1236Labels := by decide +kernel
  rw [hl, canonical1236 B hB] at h
  have hc0 : mixedMoment B raw1236 (Fin.cases (0 : Fin 2) singletonSmall4424) =
      mixedMoment B node1005 node1005Labels := by
    have ha : raw1236 = raw1237 := by apply Matrix.ext; unfold raw1236 raw1237; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4424 = raw1237Labels := by decide +kernel
    rw [ha, hj, canonical1237 B hB]
  have hc1 : mixedMoment B raw1236 (Fin.cases (1 : Fin 2) singletonSmall4424) =
      mixedMoment B node1623 node1623Labels := by
    have ha : raw1236 = raw1238 := by apply Matrix.ext; unfold raw1236 raw1238; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4424 = raw1238Labels := by decide +kernel
    rw [ha, hj, canonical1238 B hB]
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

theorem singleton4457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4457 node4457Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1040 node1040Labels + mixedMoment B node1707 node1707Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1257 singletonSmall4457
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4457) = raw1257Labels := by decide +kernel
  rw [hl, canonical1257 B hB] at h
  have hc0 : mixedMoment B raw1257 (Fin.cases (0 : Fin 2) singletonSmall4457) =
      mixedMoment B node1040 node1040Labels := by
    have ha : raw1257 = raw1258 := by apply Matrix.ext; unfold raw1257 raw1258; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4457 = raw1258Labels := by decide +kernel
    rw [ha, hj, canonical1258 B hB]
  have hc1 : mixedMoment B raw1257 (Fin.cases (1 : Fin 2) singletonSmall4457) =
      mixedMoment B node1707 node1707Labels := by
    have ha : raw1257 = raw1259 := by apply Matrix.ext; unfold raw1257 raw1259; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4457 = raw1259Labels := by decide +kernel
    rw [ha, hj, canonical1259 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4460 node4460Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1043 node1043Labels + mixedMoment B node1725 node1725Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1263 singletonSmall4460
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4460) = raw1263Labels := by decide +kernel
  rw [hl, canonical1263 B hB] at h
  have hc0 : mixedMoment B raw1263 (Fin.cases (0 : Fin 2) singletonSmall4460) =
      mixedMoment B node1043 node1043Labels := by
    have ha : raw1263 = raw1264 := by apply Matrix.ext; unfold raw1263 raw1264; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4460 = raw1264Labels := by decide +kernel
    rw [ha, hj, canonical1264 B hB]
  have hc1 : mixedMoment B raw1263 (Fin.cases (1 : Fin 2) singletonSmall4460) =
      mixedMoment B node1725 node1725Labels := by
    have ha : raw1263 = raw1265 := by apply Matrix.ext; unfold raw1263 raw1265; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4460 = raw1265Labels := by decide +kernel
    rw [ha, hj, canonical1265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4467 node4467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1050 node1050Labels + mixedMoment B node1751 node1751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1275 singletonSmall4467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4467) = raw1275Labels := by decide +kernel
  rw [hl, canonical1275 B hB] at h
  have hc0 : mixedMoment B raw1275 (Fin.cases (0 : Fin 2) singletonSmall4467) =
      mixedMoment B node1050 node1050Labels := by
    have ha : raw1275 = raw1276 := by apply Matrix.ext; unfold raw1275 raw1276; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4467 = raw1276Labels := by decide +kernel
    rw [ha, hj, canonical1276 B hB]
  have hc1 : mixedMoment B raw1275 (Fin.cases (1 : Fin 2) singletonSmall4467) =
      mixedMoment B node1751 node1751Labels := by
    have ha : raw1275 = raw1277 := by apply Matrix.ext; unfold raw1275 raw1277; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4467 = raw1277Labels := by decide +kernel
    rw [ha, hj, canonical1277 B hB]
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

theorem singleton4495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4495 node4495Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1079 node1079Labels + mixedMoment B node1708 node1708Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1293 singletonSmall4495
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4495) = raw1293Labels := by decide +kernel
  rw [hl, canonical1293 B hB] at h
  have hc0 : mixedMoment B raw1293 (Fin.cases (0 : Fin 2) singletonSmall4495) =
      mixedMoment B node1079 node1079Labels := by
    have ha : raw1293 = raw1294 := by apply Matrix.ext; unfold raw1293 raw1294; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4495 = raw1294Labels := by decide +kernel
    rw [ha, hj, canonical1294 B hB]
  have hc1 : mixedMoment B raw1293 (Fin.cases (1 : Fin 2) singletonSmall4495) =
      mixedMoment B node1708 node1708Labels := by
    have ha : raw1293 = raw1295 := by apply Matrix.ext; unfold raw1293 raw1295; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4495 = raw1295Labels := by decide +kernel
    rw [ha, hj, canonical1295 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4499 node4499Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1083 node1083Labels + mixedMoment B node1728 node1728Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1299 singletonSmall4499
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4499) = raw1299Labels := by decide +kernel
  rw [hl, canonical1299 B hB] at h
  have hc0 : mixedMoment B raw1299 (Fin.cases (0 : Fin 2) singletonSmall4499) =
      mixedMoment B node1083 node1083Labels := by
    have ha : raw1299 = raw1300 := by apply Matrix.ext; unfold raw1299 raw1300; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4499 = raw1300Labels := by decide +kernel
    rw [ha, hj, canonical1300 B hB]
  have hc1 : mixedMoment B raw1299 (Fin.cases (1 : Fin 2) singletonSmall4499) =
      mixedMoment B node1728 node1728Labels := by
    have ha : raw1299 = raw1301 := by apply Matrix.ext; unfold raw1299 raw1301; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4499 = raw1301Labels := by decide +kernel
    rw [ha, hj, canonical1301 B hB]
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

theorem singleton5073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5073 node5073Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2480 node2480Labels + mixedMoment B node3467 node3467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2094 singletonSmall5073
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5073) = raw2094Labels := by decide +kernel
  rw [hl, canonical2094 B hB] at h
  have hc0 : mixedMoment B raw2094 (Fin.cases (0 : Fin 2) singletonSmall5073) =
      mixedMoment B node2480 node2480Labels := by
    have ha : raw2094 = raw2095 := by apply Matrix.ext; unfold raw2094 raw2095; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5073 = raw2095Labels := by decide +kernel
    rw [ha, hj, canonical2095 B hB]
  have hc1 : mixedMoment B raw2094 (Fin.cases (1 : Fin 2) singletonSmall5073) =
      mixedMoment B node3467 node3467Labels := by
    have ha : raw2094 = raw2096 := by apply Matrix.ext; unfold raw2094 raw2096; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5073 = raw2096Labels := by decide +kernel
    rw [ha, hj, canonical2096 B hB]
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

theorem singleton5293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5293 node5293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2767 node2767Labels + mixedMoment B node3627 node3627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2301 singletonSmall5293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5293) = raw2301Labels := by decide +kernel
  rw [hl, canonical2301 B hB] at h
  have hc0 : mixedMoment B raw2301 (Fin.cases (0 : Fin 2) singletonSmall5293) =
      mixedMoment B node2767 node2767Labels := by
    have ha : raw2301 = raw2302 := by apply Matrix.ext; unfold raw2301 raw2302; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5293 = raw2302Labels := by decide +kernel
    rw [ha, hj, canonical2302 B hB]
  have hc1 : mixedMoment B raw2301 (Fin.cases (1 : Fin 2) singletonSmall5293) =
      mixedMoment B node3627 node3627Labels := by
    have ha : raw2301 = raw2303 := by apply Matrix.ext; unfold raw2301 raw2303; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5293 = raw2303Labels := by decide +kernel
    rw [ha, hj, canonical2303 B hB]
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

theorem sound663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node663 node663Labels = Sparse.eval nodeValue663 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 663) = mixedMoment B node663 node663Labels := rfl
  simpa [nodeValue663, Sparse.eval] using hc.symm

theorem sound664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node664 node664Labels = Sparse.eval nodeValue664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 664) = mixedMoment B node664 node664Labels := rfl
  simpa [nodeValue664, Sparse.eval] using hc.symm

theorem sound668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node668 node668Labels = Sparse.eval nodeValue668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 668) = mixedMoment B node668 node668Labels := rfl
  simpa [nodeValue668, Sparse.eval] using hc.symm

theorem sound682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node682 node682Labels = Sparse.eval nodeValue682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 682) = mixedMoment B node682 node682Labels := rfl
  simpa [nodeValue682, Sparse.eval] using hc.symm

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

theorem sound865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node865 node865Labels = Sparse.eval nodeValue865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 865) = mixedMoment B node865 node865Labels := rfl
  simpa [nodeValue865, Sparse.eval] using hc.symm

theorem sound866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node866 node866Labels = Sparse.eval nodeValue866 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 866) = mixedMoment B node866 node866Labels := rfl
  simpa [nodeValue866, Sparse.eval] using hc.symm

theorem sound870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node870 node870Labels = Sparse.eval nodeValue870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 870) = mixedMoment B node870 node870Labels := rfl
  simpa [nodeValue870, Sparse.eval] using hc.symm

theorem sound879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node879 node879Labels = Sparse.eval nodeValue879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 879) = mixedMoment B node879 node879Labels := rfl
  simpa [nodeValue879, Sparse.eval] using hc.symm

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

theorem sound922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node922 node922Labels = Sparse.eval nodeValue922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 922) = mixedMoment B node922 node922Labels := rfl
  simpa [nodeValue922, Sparse.eval] using hc.symm

theorem sound924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node924 node924Labels = Sparse.eval nodeValue924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 924) = mixedMoment B node924 node924Labels := rfl
  simpa [nodeValue924, Sparse.eval] using hc.symm

theorem sound927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node927 node927Labels = Sparse.eval nodeValue927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 927) = mixedMoment B node927 node927Labels := rfl
  simpa [nodeValue927, Sparse.eval] using hc.symm

theorem sound933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node933 node933Labels = Sparse.eval nodeValue933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 933) = mixedMoment B node933 node933Labels := rfl
  simpa [nodeValue933, Sparse.eval] using hc.symm

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

theorem sound980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node980 node980Labels = Sparse.eval nodeValue980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 980) = mixedMoment B node980 node980Labels := rfl
  simpa [nodeValue980, Sparse.eval] using hc.symm

theorem sound982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node982 node982Labels = Sparse.eval nodeValue982 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 982) = mixedMoment B node982 node982Labels := rfl
  simpa [nodeValue982, Sparse.eval] using hc.symm

theorem sound985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node985 node985Labels = Sparse.eval nodeValue985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 985) = mixedMoment B node985 node985Labels := rfl
  simpa [nodeValue985, Sparse.eval] using hc.symm

theorem sound1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1005 node1005Labels = Sparse.eval nodeValue1005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1005) = mixedMoment B node1005 node1005Labels := rfl
  simpa [nodeValue1005, Sparse.eval] using hc.symm

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

theorem sound1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1039 node1039Labels = Sparse.eval nodeValue1039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1039) = mixedMoment B node1039 node1039Labels := rfl
  simpa [nodeValue1039, Sparse.eval] using hc.symm

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

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

theorem sound1553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1553 node1553Labels = Sparse.eval nodeValue1553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1553) = mixedMoment B node1553 node1553Labels := rfl
  simpa [nodeValue1553, Sparse.eval] using hc.symm

theorem sound1554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1554 node1554Labels = Sparse.eval nodeValue1554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1554) = mixedMoment B node1554 node1554Labels := rfl
  simpa [nodeValue1554, Sparse.eval] using hc.symm

theorem sound1556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1556 node1556Labels = Sparse.eval nodeValue1556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1556) = mixedMoment B node1556 node1556Labels := rfl
  simpa [nodeValue1556, Sparse.eval] using hc.symm

theorem sound1567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1567 node1567Labels = Sparse.eval nodeValue1567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1567) = mixedMoment B node1567 node1567Labels := rfl
  simpa [nodeValue1567, Sparse.eval] using hc.symm

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

theorem sound1616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1616 node1616Labels = Sparse.eval nodeValue1616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1616) = mixedMoment B node1616 node1616Labels := rfl
  simpa [nodeValue1616, Sparse.eval] using hc.symm

theorem sound1617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1617 node1617Labels = Sparse.eval nodeValue1617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1617) = mixedMoment B node1617 node1617Labels := rfl
  simpa [nodeValue1617, Sparse.eval] using hc.symm

theorem sound1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1618 node1618Labels = Sparse.eval nodeValue1618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1618) = mixedMoment B node1618 node1618Labels := rfl
  simpa [nodeValue1618, Sparse.eval] using hc.symm

theorem sound1623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1623 node1623Labels = Sparse.eval nodeValue1623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1623) = mixedMoment B node1623 node1623Labels := rfl
  simpa [nodeValue1623, Sparse.eval] using hc.symm

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

theorem sound1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1673 node1673Labels = Sparse.eval nodeValue1673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1673) = mixedMoment B node1673 node1673Labels := rfl
  simpa [nodeValue1673, Sparse.eval] using hc.symm

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

theorem sound1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1691 node1691Labels = Sparse.eval nodeValue1691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1691) = mixedMoment B node1691 node1691Labels := rfl
  simpa [nodeValue1691, Sparse.eval] using hc.symm

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

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

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

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

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node404 node404Labels = Sparse.eval nodeValue404 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue404 (familyPairVector B) := singlePair404 B _hB
    _ = _ := by
      norm_num [singlePairValue404, nodeValue404, Sparse.eval, mixedVector]
      ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2767 node2767Labels = Sparse.eval nodeValue2767 (mixedVector B) := by
  have h := singleton2767 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue2767, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

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

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

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

theorem sound538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node538 node538Labels = Sparse.eval nodeValue538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 538) = mixedMoment B node538 node538Labels := rfl
  simpa [nodeValue538, Sparse.eval] using hc.symm

theorem sound539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node539 node539Labels = Sparse.eval nodeValue539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 539) = mixedMoment B node539 node539Labels := rfl
  simpa [nodeValue539, Sparse.eval] using hc.symm

theorem sound544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node544 node544Labels = Sparse.eval nodeValue544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 544) = mixedMoment B node544 node544Labels := rfl
  simpa [nodeValue544, Sparse.eval] using hc.symm

theorem sound554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node554 node554Labels = Sparse.eval nodeValue554 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 554) = mixedMoment B node554 node554Labels := rfl
  simpa [nodeValue554, Sparse.eval] using hc.symm

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

theorem sound4101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4101 node4101Labels = Sparse.eval nodeValue4101 (mixedVector B) := by
  have h := singleton4101 B _hB
  rw [sound538 B _hB _hF, sound663 B _hB _hF] at h
  norm_num [nodeValue4101, nodeValue538, nodeValue663, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4102 node4102Labels = Sparse.eval nodeValue4102 (mixedVector B) := by
  have h := singleton4102 B _hB
  rw [sound539 B _hB _hF, sound664 B _hB _hF] at h
  norm_num [nodeValue4102, nodeValue539, nodeValue664, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4107 node4107Labels = Sparse.eval nodeValue4107 (mixedVector B) := by
  have h := singleton4107 B _hB
  rw [sound544 B _hB _hF, sound682 B _hB _hF] at h
  norm_num [nodeValue4107, nodeValue544, nodeValue682, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4119 node4119Labels = Sparse.eval nodeValue4119 (mixedVector B) := by
  have h := singleton4119 B _hB
  rw [sound554 B _hB _hF, sound668 B _hB _hF] at h
  norm_num [nodeValue4119, nodeValue554, nodeValue668, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4287 node4287Labels = Sparse.eval nodeValue4287 (mixedVector B) := by
  have h := singleton4287 B _hB
  rw [sound865 B _hB _hF, sound1553 B _hB _hF] at h
  norm_num [nodeValue4287, nodeValue865, nodeValue1553, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4292 node4292Labels = Sparse.eval nodeValue4292 (mixedVector B) := by
  have h := singleton4292 B _hB
  rw [sound870 B _hB _hF, sound1567 B _hB _hF] at h
  norm_num [nodeValue4292, nodeValue870, nodeValue1567, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4301 node4301Labels = Sparse.eval nodeValue4301 (mixedVector B) := by
  have h := singleton4301 B _hB
  rw [sound879 B _hB _hF, sound1556 B _hB _hF] at h
  norm_num [nodeValue4301, nodeValue879, nodeValue1556, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4344 node4344Labels = Sparse.eval nodeValue4344 (mixedVector B) := by
  have h := singleton4344 B _hB
  rw [sound922 B _hB _hF, sound1673 B _hB _hF] at h
  norm_num [nodeValue4344, nodeValue922, nodeValue1673, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4346 node4346Labels = Sparse.eval nodeValue4346 (mixedVector B) := by
  have h := singleton4346 B _hB
  rw [sound924 B _hB _hF, sound1674 B _hB _hF] at h
  norm_num [nodeValue4346, nodeValue924, nodeValue1674, Sparse.eval] at h ⊢
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

theorem sound4355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4355 node4355Labels = Sparse.eval nodeValue4355 (mixedVector B) := by
  have h := singleton4355 B _hB
  rw [sound933 B _hB _hF, sound1691 B _hB _hF] at h
  norm_num [nodeValue4355, nodeValue933, nodeValue1691, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4399 node4399Labels = Sparse.eval nodeValue4399 (mixedVector B) := by
  have h := singleton4399 B _hB
  rw [sound980 B _hB _hF, sound1616 B _hB _hF] at h
  norm_num [nodeValue4399, nodeValue980, nodeValue1616, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4401 node4401Labels = Sparse.eval nodeValue4401 (mixedVector B) := by
  have h := singleton4401 B _hB
  rw [sound982 B _hB _hF, sound1617 B _hB _hF] at h
  norm_num [nodeValue4401, nodeValue982, nodeValue1617, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4424 node4424Labels = Sparse.eval nodeValue4424 (mixedVector B) := by
  have h := singleton4424 B _hB
  rw [sound1005 B _hB _hF, sound1623 B _hB _hF] at h
  norm_num [nodeValue4424, nodeValue1005, nodeValue1623, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4456 node4456Labels = Sparse.eval nodeValue4456 (mixedVector B) := by
  have h := singleton4456 B _hB
  rw [sound1039 B _hB _hF, sound1706 B _hB _hF] at h
  norm_num [nodeValue4456, nodeValue1039, nodeValue1706, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4457 node4457Labels = Sparse.eval nodeValue4457 (mixedVector B) := by
  have h := singleton4457 B _hB
  rw [sound1040 B _hB _hF, sound1707 B _hB _hF] at h
  norm_num [nodeValue4457, nodeValue1040, nodeValue1707, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4467 node4467Labels = Sparse.eval nodeValue4467 (mixedVector B) := by
  have h := singleton4467 B _hB
  rw [sound1050 B _hB _hF, sound1751 B _hB _hF] at h
  norm_num [nodeValue4467, nodeValue1050, nodeValue1751, Sparse.eval] at h ⊢
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

theorem sound4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4495 node4495Labels = Sparse.eval nodeValue4495 (mixedVector B) := by
  have h := singleton4495 B _hB
  rw [sound1079 B _hB _hF, sound1708 B _hB _hF] at h
  norm_num [nodeValue4495, nodeValue1079, nodeValue1708, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4499 node4499Labels = Sparse.eval nodeValue4499 (mixedVector B) := by
  have h := singleton4499 B _hB
  rw [sound1083 B _hB _hF, sound1728 B _hB _hF] at h
  norm_num [nodeValue4499, nodeValue1083, nodeValue1728, Sparse.eval] at h ⊢
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

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
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

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5293 node5293Labels = Sparse.eval nodeValue5293 (mixedVector B) := by
  have h := singleton5293 B _hB
  rw [sound2767 B _hB _hF, sound3627 B _hB _hF] at h
  norm_num [nodeValue5293, nodeValue2767, nodeValue3627, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources54
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1730 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 1) (sourceB1730 + difference 1 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 1) (sourceB1730 + difference 1 0) sourceC1730) = raw17671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw17671; decide +kernel
    rw [ha]
    exact (canonical17671 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 2) (sourceB1730 + difference 2 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 2) (sourceB1730 + difference 2 0) sourceC1730) = raw25241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25241; decide +kernel
    rw [ha]
    exact (canonical25241 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 3) (sourceB1730 + difference 3 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 3) (sourceB1730 + difference 3 0) sourceC1730) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 4) (sourceB1730 + difference 4 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 4) (sourceB1730 + difference 4 0) sourceC1730) = raw2766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw2766; decide +kernel
    rw [ha]
    exact (canonical2766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 5) (sourceB1730 + difference 5 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 5) (sourceB1730 + difference 5 0) sourceC1730) = raw25242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25242; decide +kernel
    rw [ha]
    exact (canonical25242 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 0) (sourceB1730 + difference 0 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 0) (sourceB1730 + difference 0 1) sourceC1730) = raw25243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25243; decide +kernel
    rw [ha]
    exact (canonical25243 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 2) (sourceB1730 + difference 2 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 2) (sourceB1730 + difference 2 1) sourceC1730) = raw25244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25244; decide +kernel
    rw [ha]
    exact (canonical25244 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 3) (sourceB1730 + difference 3 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 3) (sourceB1730 + difference 3 1) sourceC1730) = raw21481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21481; decide +kernel
    rw [ha]
    exact (canonical21481 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 4) (sourceB1730 + difference 4 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 4) (sourceB1730 + difference 4 1) sourceC1730) = raw25245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25245; decide +kernel
    rw [ha]
    exact (canonical25245 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 5) (sourceB1730 + difference 5 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 5) (sourceB1730 + difference 5 1) sourceC1730) = raw25246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25246; decide +kernel
    rw [ha]
    exact (canonical25246 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 0) (sourceB1730 + difference 0 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 0) (sourceB1730 + difference 0 2) sourceC1730) = raw25247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25247; decide +kernel
    rw [ha]
    exact (canonical25247 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 1) (sourceB1730 + difference 1 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 1) (sourceB1730 + difference 1 2) sourceC1730) = raw25248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25248; decide +kernel
    rw [ha]
    exact (canonical25248 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 3) (sourceB1730 + difference 3 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 3) (sourceB1730 + difference 3 2) sourceC1730) = raw21485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21485; decide +kernel
    rw [ha]
    exact (canonical21485 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 4) (sourceB1730 + difference 4 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 4) (sourceB1730 + difference 4 2) sourceC1730) = raw25249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25249; decide +kernel
    rw [ha]
    exact (canonical25249 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 5) (sourceB1730 + difference 5 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 5) (sourceB1730 + difference 5 2) sourceC1730) = raw25250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25250; decide +kernel
    rw [ha]
    exact (canonical25250 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 0) (sourceB1730 + difference 0 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 0) (sourceB1730 + difference 0 3) sourceC1730) = raw25251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25251; decide +kernel
    rw [ha]
    exact (canonical25251 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 1) (sourceB1730 + difference 1 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 1) (sourceB1730 + difference 1 3) sourceC1730) = raw25252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25252; decide +kernel
    rw [ha]
    exact (canonical25252 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 2) (sourceB1730 + difference 2 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 2) (sourceB1730 + difference 2 3) sourceC1730) = raw25253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25253; decide +kernel
    rw [ha]
    exact (canonical25253 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 4) (sourceB1730 + difference 4 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 4) (sourceB1730 + difference 4 3) sourceC1730) = raw25254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25254; decide +kernel
    rw [ha]
    exact (canonical25254 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 5) (sourceB1730 + difference 5 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 5) (sourceB1730 + difference 5 3) sourceC1730) = raw25255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25255; decide +kernel
    rw [ha]
    exact (canonical25255 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 0) (sourceB1730 + difference 0 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 0) (sourceB1730 + difference 0 4) sourceC1730) = raw23230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw23230; decide +kernel
    rw [ha]
    exact (canonical23230 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 1) (sourceB1730 + difference 1 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 1) (sourceB1730 + difference 1 4) sourceC1730) = raw23231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw23231; decide +kernel
    rw [ha]
    exact (canonical23231 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 2) (sourceB1730 + difference 2 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4292) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 2) (sourceB1730 + difference 2 4) sourceC1730) = raw23232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw23232; decide +kernel
    rw [ha]
    exact (canonical23232 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 3) (sourceB1730 + difference 3 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 3) (sourceB1730 + difference 3 4) sourceC1730) = raw21494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21494; decide +kernel
    rw [ha]
    exact (canonical21494 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 5) (sourceB1730 + difference 5 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 5) (sourceB1730 + difference 5 4) sourceC1730) = raw23233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw23233; decide +kernel
    rw [ha]
    exact (canonical23233 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 0) (sourceB1730 + difference 0 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 0) (sourceB1730 + difference 0 5) sourceC1730) = raw21486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21486; decide +kernel
    rw [ha]
    exact (canonical21486 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 1) (sourceB1730 + difference 1 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 1) (sourceB1730 + difference 1 5) sourceC1730) = raw21487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21487; decide +kernel
    rw [ha]
    exact (canonical21487 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 2) (sourceB1730 + difference 2 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 2) (sourceB1730 + difference 2 5) sourceC1730) = raw21488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21488; decide +kernel
    rw [ha]
    exact (canonical21488 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 3) (sourceB1730 + difference 3 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 3) (sourceB1730 + difference 3 5) sourceC1730) = raw4935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw4935; decide +kernel
    rw [ha]
    exact (canonical4935 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 4) (sourceB1730 + difference 4 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 4) (sourceB1730 + difference 4 5) sourceC1730) = raw4931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw4931; decide +kernel
    rw [ha]
    exact (canonical4931 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1730 sourceB1730 sourceC1730
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1730, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1477 : Integer.Sparse.reindex keyMap MixedData.row1477 = numericRow1477 := by decide +kernel

theorem numericCheck1477 (x : Master → ℝ) : Integer.Sparse.eval numericRow1477 x =
    (17280 : ℝ) * reducedSource1477 x := by
  norm_num [numericRow1477, reducedSource1477, Integer.Sparse.eval, Sparse.eval, nodeValue4100, nodeValue4101, nodeValue4102, nodeValue4107, nodeValue4119, nodeValue4287, nodeValue4288, nodeValue4292, nodeValue4301, nodeValue4344, nodeValue4346, nodeValue4349, nodeValue4355, nodeValue4399, nodeValue4401, nodeValue4404, nodeValue4424, nodeValue4456, nodeValue4457, nodeValue4458, nodeValue4460, nodeValue4467, nodeValue4495, nodeValue4499, nodeValue5073, nodeValue5169, nodeValue5259, nodeValue5292, nodeValue5293]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1477 (mixedVector B) = 0 := by
  have h4100 : mixedVector B (Sum.inr 4100) = Sparse.eval nodeValue4100 (mixedVector B) := by
    change mixedMoment B node4100 node4100Labels = _
    exact sound4100 B hB hF
  have h4101 : mixedVector B (Sum.inr 4101) = Sparse.eval nodeValue4101 (mixedVector B) := by
    change mixedMoment B node4101 node4101Labels = _
    exact sound4101 B hB hF
  have h4102 : mixedVector B (Sum.inr 4102) = Sparse.eval nodeValue4102 (mixedVector B) := by
    change mixedMoment B node4102 node4102Labels = _
    exact sound4102 B hB hF
  have h4107 : mixedVector B (Sum.inr 4107) = Sparse.eval nodeValue4107 (mixedVector B) := by
    change mixedMoment B node4107 node4107Labels = _
    exact sound4107 B hB hF
  have h4119 : mixedVector B (Sum.inr 4119) = Sparse.eval nodeValue4119 (mixedVector B) := by
    change mixedMoment B node4119 node4119Labels = _
    exact sound4119 B hB hF
  have h4287 : mixedVector B (Sum.inr 4287) = Sparse.eval nodeValue4287 (mixedVector B) := by
    change mixedMoment B node4287 node4287Labels = _
    exact sound4287 B hB hF
  have h4288 : mixedVector B (Sum.inr 4288) = Sparse.eval nodeValue4288 (mixedVector B) := by
    change mixedMoment B node4288 node4288Labels = _
    exact sound4288 B hB hF
  have h4292 : mixedVector B (Sum.inr 4292) = Sparse.eval nodeValue4292 (mixedVector B) := by
    change mixedMoment B node4292 node4292Labels = _
    exact sound4292 B hB hF
  have h4301 : mixedVector B (Sum.inr 4301) = Sparse.eval nodeValue4301 (mixedVector B) := by
    change mixedMoment B node4301 node4301Labels = _
    exact sound4301 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4401 : mixedVector B (Sum.inr 4401) = Sparse.eval nodeValue4401 (mixedVector B) := by
    change mixedMoment B node4401 node4401Labels = _
    exact sound4401 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4424 : mixedVector B (Sum.inr 4424) = Sparse.eval nodeValue4424 (mixedVector B) := by
    change mixedMoment B node4424 node4424Labels = _
    exact sound4424 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169_e B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  simpa only [sourceForm1730, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4100, h4101, h4102, h4107, h4119, h4287, h4288, h4292, h4301, h4344, h4346, h4349, h4355, h4399, h4401, h4404, h4424, h4456, h4457, h4458, h4460, h4467, h4495, h4499, h5073, h5169, h5259, h5292, h5293, reducedSource1477] using sourceEq1730 B hB

theorem rowSound1477_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1477 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1477, numericCheck1477, reducedZero1477 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e_oai
