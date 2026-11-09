-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:43:12.364372+00:00
-- url     : https://prove2.me/submissions/198c439c-af16-470d-878a-12bcab5a0ddc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2593_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2766_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1584_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1587_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1589_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1593_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1595_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1599_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

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

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14290 raw14290Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw14290 raw14290Labels = mixedMoment B raw14290step0 raw14290step0Labels := by
      have ha : raw14290step0 = (fun i j => raw14290 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14290step0 raw14290; decide +kernel
      have hl : raw14290step0Labels = raw14290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14290 raw14290Labels permutation242 permutation7
    mixedMoment B raw14290step0 raw14290step0Labels = mixedMoment B raw14290step1 raw14290step1Labels := by
      have ha : raw14290step1 = -raw14290step0 := by apply Matrix.ext; change ∀ i j, raw14290step1 i j = -(raw14290step0 i j); unfold raw14290step1 raw14290step0; decide +kernel
      have hl : raw14290step1Labels = raw14290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14290step1 raw14290step1Labels = mixedMoment B raw14290step2 raw14290step2Labels := by
      have ha : raw14290step2 = raw14290step1 := by apply Matrix.ext; unfold raw14290step2 raw14290step1; decide +kernel
      have hl : raw14290step1Labels = labelEmbedding1 ∘ raw14290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14290step1 raw14290step1Labels raw14290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical14295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14295 raw14295Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw14295 raw14295Labels = mixedMoment B raw14295step0 raw14295step0Labels := by
      have ha : raw14295step0 = (fun i j => raw14295 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14295step0 raw14295; decide +kernel
      have hl : raw14295step0Labels = raw14295Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14295 raw14295Labels permutation240 permutation7
    mixedMoment B raw14295step0 raw14295step0Labels = mixedMoment B raw14295step1 raw14295step1Labels := by
      have ha : raw14295step1 = -raw14295step0 := by apply Matrix.ext; change ∀ i j, raw14295step1 i j = -(raw14295step0 i j); unfold raw14295step1 raw14295step0; decide +kernel
      have hl : raw14295step1Labels = raw14295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14295step1 raw14295step1Labels = mixedMoment B raw14295step2 raw14295step2Labels := by
      have ha : raw14295step2 = raw14295step1 := by apply Matrix.ext; unfold raw14295step2 raw14295step1; decide +kernel
      have hl : raw14295step1Labels = labelEmbedding1 ∘ raw14295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14295step1 raw14295step1Labels raw14295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical14296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14296 raw14296Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14296 raw14296Labels = mixedMoment B raw14296step0 raw14296step0Labels := by
      have hz : ∀ j, raw14296 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14296step0 = (fun i j => raw14296 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14296step0 raw14296; decide +kernel
      have hl : raw14296step0Labels = raw14296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14296 raw14296Labels permutation520 hz
    mixedMoment B raw14296step0 raw14296step0Labels = mixedMoment B raw14296step1 raw14296step1Labels := by
      have ha : raw14296step1 = (fun i j => raw14296step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14296step1 raw14296step0; decide +kernel
      have hl : raw14296step1Labels = raw14296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14296step0 raw14296step0Labels permutation50 permutation7
    mixedMoment B raw14296step1 raw14296step1Labels = mixedMoment B raw14296step2 raw14296step2Labels := by
      have ha : raw14296step2 = -raw14296step1 := by apply Matrix.ext; change ∀ i j, raw14296step2 i j = -(raw14296step1 i j); unfold raw14296step2 raw14296step1; decide +kernel
      have hl : raw14296step2Labels = raw14296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14296step2 raw14296step2Labels = mixedMoment B raw14296step3 raw14296step3Labels := by
      have ha : raw14296step3 = raw14296step2 := by apply Matrix.ext; unfold raw14296step3 raw14296step2; decide +kernel
      have hl : raw14296step2Labels = labelEmbedding1 ∘ raw14296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14296step2 raw14296step2Labels raw14296step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical14297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14297 raw14297Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14297 raw14297Labels = mixedMoment B raw14297step0 raw14297step0Labels := by
      have hz : ∀ j, raw14297 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14297step0 = (fun i j => raw14297 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14297step0 raw14297; decide +kernel
      have hl : raw14297step0Labels = raw14297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14297 raw14297Labels permutation590 hz
    mixedMoment B raw14297step0 raw14297step0Labels = mixedMoment B raw14297step1 raw14297step1Labels := by
      have ha : raw14297step1 = (fun i j => raw14297step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14297step1 raw14297step0; decide +kernel
      have hl : raw14297step1Labels = raw14297step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14297step0 raw14297step0Labels permutation50 permutation7
    mixedMoment B raw14297step1 raw14297step1Labels = mixedMoment B raw14297step2 raw14297step2Labels := by
      have ha : raw14297step2 = -raw14297step1 := by apply Matrix.ext; change ∀ i j, raw14297step2 i j = -(raw14297step1 i j); unfold raw14297step2 raw14297step1; decide +kernel
      have hl : raw14297step2Labels = raw14297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14297step2 raw14297step2Labels = mixedMoment B raw14297step3 raw14297step3Labels := by
      have ha : raw14297step3 = raw14297step2 := by apply Matrix.ext; unfold raw14297step3 raw14297step2; decide +kernel
      have hl : raw14297step2Labels = labelEmbedding1 ∘ raw14297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14297step2 raw14297step2Labels raw14297step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical14298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14298 raw14298Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw14298 raw14298Labels = mixedMoment B raw14298step0 raw14298step0Labels := by
      have ha : raw14298step0 = (fun i j => raw14298 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14298step0 raw14298; decide +kernel
      have hl : raw14298step0Labels = raw14298Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14298 raw14298Labels permutation240 permutation7
    mixedMoment B raw14298step0 raw14298step0Labels = mixedMoment B raw14298step1 raw14298step1Labels := by
      have ha : raw14298step1 = -raw14298step0 := by apply Matrix.ext; change ∀ i j, raw14298step1 i j = -(raw14298step0 i j); unfold raw14298step1 raw14298step0; decide +kernel
      have hl : raw14298step1Labels = raw14298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14298step1 raw14298step1Labels = mixedMoment B raw14298step2 raw14298step2Labels := by
      have ha : raw14298step2 = raw14298step1 := by apply Matrix.ext; unfold raw14298step2 raw14298step1; decide +kernel
      have hl : raw14298step1Labels = labelEmbedding1 ∘ raw14298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14298step1 raw14298step1Labels raw14298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

theorem canonical14303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14303 raw14303Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw14303 raw14303Labels = mixedMoment B raw14303step0 raw14303step0Labels := by
      have ha : raw14303step0 = (fun i j => raw14303 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14303step0 raw14303; decide +kernel
      have hl : raw14303step0Labels = raw14303Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14303 raw14303Labels permutation260 permutation7
    mixedMoment B raw14303step0 raw14303step0Labels = mixedMoment B raw14303step1 raw14303step1Labels := by
      have ha : raw14303step1 = -raw14303step0 := by apply Matrix.ext; change ∀ i j, raw14303step1 i j = -(raw14303step0 i j); unfold raw14303step1 raw14303step0; decide +kernel
      have hl : raw14303step1Labels = raw14303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14303step1 raw14303step1Labels = mixedMoment B raw14303step2 raw14303step2Labels := by
      have ha : raw14303step2 = raw14303step1 := by apply Matrix.ext; unfold raw14303step2 raw14303step1; decide +kernel
      have hl : raw14303step1Labels = labelEmbedding1 ∘ raw14303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14303step1 raw14303step1Labels raw14303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21506 raw21506Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw21506 raw21506Labels = mixedMoment B raw21506step0 raw21506step0Labels := by
      have hz : ∀ j, raw21506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21506step0 = (fun i j => raw21506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21506step0 raw21506; decide +kernel
      have hl : raw21506step0Labels = raw21506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21506 raw21506Labels permutation434 hz
    mixedMoment B raw21506step0 raw21506step0Labels = mixedMoment B raw21506step1 raw21506step1Labels := by
      have ha : raw21506step1 = (fun i j => raw21506step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21506step1 raw21506step0; decide +kernel
      have hl : raw21506step1Labels = raw21506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21506step0 raw21506step0Labels permutation34 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical21510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21510 raw21510Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw21510 raw21510Labels = mixedMoment B raw21510step0 raw21510step0Labels := by
      have hz : ∀ j, raw21510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21510step0 = (fun i j => raw21510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21510step0 raw21510; decide +kernel
      have hl : raw21510step0Labels = raw21510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21510 raw21510Labels permutation346 hz
    mixedMoment B raw21510step0 raw21510step0Labels = mixedMoment B raw21510step1 raw21510step1Labels := by
      have ha : raw21510step1 = (fun i j => raw21510step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21510step1 raw21510step0; decide +kernel
      have hl : raw21510step1Labels = raw21510step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21510step0 raw21510step0Labels permutation34 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

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

theorem canonical23250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23250 raw23250Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23250 raw23250Labels = mixedMoment B raw23250step0 raw23250step0Labels := by
      have hz : ∀ j, raw23250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23250step0 = (fun i j => raw23250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23250step0 raw23250; decide +kernel
      have hl : raw23250step0Labels = raw23250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23250 raw23250Labels permutation434 hz
    mixedMoment B raw23250step0 raw23250step0Labels = mixedMoment B raw23250step1 raw23250step1Labels := by
      have ha : raw23250step1 = (fun i j => raw23250step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23250step1 raw23250step0; decide +kernel
      have hl : raw23250step1Labels = raw23250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23250step0 raw23250step0Labels permutation36 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical23254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23254 raw23254Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23254 raw23254Labels = mixedMoment B raw23254step0 raw23254step0Labels := by
      have hz : ∀ j, raw23254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23254step0 = (fun i j => raw23254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23254step0 raw23254; decide +kernel
      have hl : raw23254step0Labels = raw23254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23254 raw23254Labels permutation346 hz
    mixedMoment B raw23254step0 raw23254step0Labels = mixedMoment B raw23254step1 raw23254step1Labels := by
      have ha : raw23254step1 = (fun i j => raw23254step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23254step1 raw23254step0; decide +kernel
      have hl : raw23254step1Labels = raw23254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23254step0 raw23254step0Labels permutation36 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

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

theorem canonical25258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25258 raw25258Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw25258 raw25258Labels = mixedMoment B raw25258step0 raw25258step0Labels := by
      have hz : ∀ j, raw25258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25258step0 = (fun i j => raw25258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25258step0 raw25258; decide +kernel
      have hl : raw25258step0Labels = raw25258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25258 raw25258Labels permutation346 hz
    mixedMoment B raw25258step0 raw25258step0Labels = mixedMoment B raw25258step1 raw25258step1Labels := by
      have ha : raw25258step1 = (fun i j => raw25258step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25258step1 raw25258step0; decide +kernel
      have hl : raw25258step1Labels = raw25258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25258step0 raw25258step0Labels permutation35 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

theorem canonical25262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25262 raw25262Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25262 raw25262Labels = mixedMoment B raw25262step0 raw25262step0Labels := by
      have hz : ∀ j, raw25262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25262step0 = (fun i j => raw25262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25262step0 raw25262; decide +kernel
      have hl : raw25262step0Labels = raw25262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25262 raw25262Labels permutation346 hz
    mixedMoment B raw25262step0 raw25262step0Labels = mixedMoment B raw25262step1 raw25262step1Labels := by
      have ha : raw25262step1 = (fun i j => raw25262step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25262step1 raw25262step0; decide +kernel
      have hl : raw25262step1Labels = raw25262step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25262step0 raw25262step0Labels permutation49 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical25263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25263 raw25263Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw25263 raw25263Labels = mixedMoment B raw25263step0 raw25263step0Labels := by
      have ha : raw25263step0 = (fun i j => raw25263 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25263step0 raw25263; decide +kernel
      have hl : raw25263step0Labels = raw25263Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25263 raw25263Labels permutation164 permutation3
    _ = mixedMoment B node537 node537Labels := by rfl

theorem canonical25264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25264 raw25264Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw25264 raw25264Labels = mixedMoment B raw25264step0 raw25264step0Labels := by
      have ha : raw25264step0 = (fun i j => raw25264 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25264step0 raw25264; decide +kernel
      have hl : raw25264step0Labels = raw25264Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25264 raw25264Labels permutation164 permutation3
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical25265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25265 raw25265Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25265 raw25265Labels = mixedMoment B raw25265step0 raw25265step0Labels := by
      have ha : raw25265step0 = (fun i j => raw25265 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25265step0 raw25265; decide +kernel
      have hl : raw25265step0Labels = raw25265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25265 raw25265Labels permutation224 permutation3
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical25271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25271 raw25271Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw25271 raw25271Labels = mixedMoment B raw25271step0 raw25271step0Labels := by
      have hz : ∀ j, raw25271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25271step0 = (fun i j => raw25271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25271step0 raw25271; decide +kernel
      have hl : raw25271step0Labels = raw25271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25271 raw25271Labels permutation346 hz
    mixedMoment B raw25271step0 raw25271step0Labels = mixedMoment B raw25271step1 raw25271step1Labels := by
      have ha : raw25271step1 = (fun i j => raw25271step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25271step1 raw25271step0; decide +kernel
      have hl : raw25271step1Labels = raw25271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25271step0 raw25271step0Labels permutation35 permutation3
    _ = mixedMoment B node1040 node1040Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26946 raw26946Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw26946 raw26946Labels = mixedMoment B raw26946step0 raw26946step0Labels := by
      have ha : raw26946step0 = (fun i j => raw26946 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26946step0 raw26946; decide +kernel
      have hl : raw26946step0Labels = raw26946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26946 raw26946Labels permutation240 permutation7
    mixedMoment B raw26946step0 raw26946step0Labels = mixedMoment B raw26946step1 raw26946step1Labels := by
      have ha : raw26946step1 = -raw26946step0 := by apply Matrix.ext; change ∀ i j, raw26946step1 i j = -(raw26946step0 i j); unfold raw26946step1 raw26946step0; decide +kernel
      have hl : raw26946step1Labels = raw26946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26946step1 raw26946step1Labels = mixedMoment B raw26946step2 raw26946step2Labels := by
      have ha : raw26946step2 = raw26946step1 := by apply Matrix.ext; unfold raw26946step2 raw26946step1; decide +kernel
      have hl : raw26946step1Labels = labelEmbedding1 ∘ raw26946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26946step1 raw26946step1Labels raw26946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1506 node1506Labels := by rfl

theorem canonical26947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26947 raw26947Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26947 raw26947Labels = mixedMoment B raw26947step0 raw26947step0Labels := by
      have ha : raw26947step0 = (fun i j => raw26947 (permutation244 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26947step0 raw26947; decide +kernel
      have hl : raw26947step0Labels = raw26947Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26947 raw26947Labels permutation244 permutation7
    mixedMoment B raw26947step0 raw26947step0Labels = mixedMoment B raw26947step1 raw26947step1Labels := by
      have ha : raw26947step1 = -raw26947step0 := by apply Matrix.ext; change ∀ i j, raw26947step1 i j = -(raw26947step0 i j); unfold raw26947step1 raw26947step0; decide +kernel
      have hl : raw26947step1Labels = raw26947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26947step1 raw26947step1Labels = mixedMoment B raw26947step2 raw26947step2Labels := by
      have ha : raw26947step2 = raw26947step1 := by apply Matrix.ext; unfold raw26947step2 raw26947step1; decide +kernel
      have hl : raw26947step1Labels = labelEmbedding1 ∘ raw26947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26947step1 raw26947step1Labels raw26947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical26948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26948 raw26948Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw26948 raw26948Labels = mixedMoment B raw26948step0 raw26948step0Labels := by
      have hz : ∀ j, raw26948 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26948step0 = (fun i j => raw26948 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26948step0 raw26948; decide +kernel
      have hl : raw26948step0Labels = raw26948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26948 raw26948Labels permutation520 hz
    mixedMoment B raw26948step0 raw26948step0Labels = mixedMoment B raw26948step1 raw26948step1Labels := by
      have ha : raw26948step1 = (fun i j => raw26948step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26948step1 raw26948step0; decide +kernel
      have hl : raw26948step1Labels = raw26948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26948step0 raw26948step0Labels permutation50 permutation7
    mixedMoment B raw26948step1 raw26948step1Labels = mixedMoment B raw26948step2 raw26948step2Labels := by
      have ha : raw26948step2 = -raw26948step1 := by apply Matrix.ext; change ∀ i j, raw26948step2 i j = -(raw26948step1 i j); unfold raw26948step2 raw26948step1; decide +kernel
      have hl : raw26948step2Labels = raw26948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26948step2 raw26948step2Labels = mixedMoment B raw26948step3 raw26948step3Labels := by
      have ha : raw26948step3 = raw26948step2 := by apply Matrix.ext; unfold raw26948step3 raw26948step2; decide +kernel
      have hl : raw26948step2Labels = labelEmbedding1 ∘ raw26948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26948step2 raw26948step2Labels raw26948step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1726 node1726Labels := by rfl

theorem canonical26949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26949 raw26949Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw26949 raw26949Labels = mixedMoment B raw26949step0 raw26949step0Labels := by
      have hz : ∀ j, raw26949 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26949step0 = (fun i j => raw26949 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26949step0 raw26949; decide +kernel
      have hl : raw26949step0Labels = raw26949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26949 raw26949Labels permutation590 hz
    mixedMoment B raw26949step0 raw26949step0Labels = mixedMoment B raw26949step1 raw26949step1Labels := by
      have ha : raw26949step1 = (fun i j => raw26949step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26949step1 raw26949step0; decide +kernel
      have hl : raw26949step1Labels = raw26949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26949step0 raw26949step0Labels permutation50 permutation7
    mixedMoment B raw26949step1 raw26949step1Labels = mixedMoment B raw26949step2 raw26949step2Labels := by
      have ha : raw26949step2 = -raw26949step1 := by apply Matrix.ext; change ∀ i j, raw26949step2 i j = -(raw26949step1 i j); unfold raw26949step2 raw26949step1; decide +kernel
      have hl : raw26949step2Labels = raw26949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26949step2 raw26949step2Labels = mixedMoment B raw26949step3 raw26949step3Labels := by
      have ha : raw26949step3 = raw26949step2 := by apply Matrix.ext; unfold raw26949step3 raw26949step2; decide +kernel
      have hl : raw26949step2Labels = labelEmbedding1 ∘ raw26949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26949step2 raw26949step2Labels raw26949step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1726 node1726Labels := by rfl

theorem canonical26950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26950 raw26950Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26950 raw26950Labels = mixedMoment B raw26950step0 raw26950step0Labels := by
      have ha : raw26950step0 = (fun i j => raw26950 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26950step0 raw26950; decide +kernel
      have hl : raw26950step0Labels = raw26950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26950 raw26950Labels permutation241 permutation7
    mixedMoment B raw26950step0 raw26950step0Labels = mixedMoment B raw26950step1 raw26950step1Labels := by
      have ha : raw26950step1 = -raw26950step0 := by apply Matrix.ext; change ∀ i j, raw26950step1 i j = -(raw26950step0 i j); unfold raw26950step1 raw26950step0; decide +kernel
      have hl : raw26950step1Labels = raw26950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26950step1 raw26950step1Labels = mixedMoment B raw26950step2 raw26950step2Labels := by
      have ha : raw26950step2 = raw26950step1 := by apply Matrix.ext; unfold raw26950step2 raw26950step1; decide +kernel
      have hl : raw26950step1Labels = labelEmbedding1 ∘ raw26950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26950step1 raw26950step1Labels raw26950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical26951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26951 raw26951Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw26951 raw26951Labels = mixedMoment B raw26951step0 raw26951step0Labels := by
      have ha : raw26951step0 = (fun i j => raw26951 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26951step0 raw26951; decide +kernel
      have hl : raw26951step0Labels = raw26951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26951 raw26951Labels permutation241 permutation7
    mixedMoment B raw26951step0 raw26951step0Labels = mixedMoment B raw26951step1 raw26951step1Labels := by
      have ha : raw26951step1 = -raw26951step0 := by apply Matrix.ext; change ∀ i j, raw26951step1 i j = -(raw26951step0 i j); unfold raw26951step1 raw26951step0; decide +kernel
      have hl : raw26951step1Labels = raw26951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26951step1 raw26951step1Labels = mixedMoment B raw26951step2 raw26951step2Labels := by
      have ha : raw26951step2 = raw26951step1 := by apply Matrix.ext; unfold raw26951step2 raw26951step1; decide +kernel
      have hl : raw26951step1Labels = labelEmbedding1 ∘ raw26951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26951step1 raw26951step1Labels raw26951step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

theorem canonical26952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26952 raw26952Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw26952 raw26952Labels = mixedMoment B raw26952step0 raw26952step0Labels := by
      have ha : raw26952step0 = (fun i j => raw26952 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26952step0 raw26952; decide +kernel
      have hl : raw26952step0Labels = raw26952Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26952 raw26952Labels permutation241 permutation7
    mixedMoment B raw26952step0 raw26952step0Labels = mixedMoment B raw26952step1 raw26952step1Labels := by
      have ha : raw26952step1 = -raw26952step0 := by apply Matrix.ext; change ∀ i j, raw26952step1 i j = -(raw26952step0 i j); unfold raw26952step1 raw26952step0; decide +kernel
      have hl : raw26952step1Labels = raw26952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26952step1 raw26952step1Labels = mixedMoment B raw26952step2 raw26952step2Labels := by
      have ha : raw26952step2 = raw26952step1 := by apply Matrix.ext; unfold raw26952step2 raw26952step1; decide +kernel
      have hl : raw26952step1Labels = labelEmbedding1 ∘ raw26952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26952step1 raw26952step1Labels raw26952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

theorem canonical26953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26953 raw26953Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw26953 raw26953Labels = mixedMoment B raw26953step0 raw26953step0Labels := by
      have hz : ∀ j, raw26953 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26953step0 = (fun i j => raw26953 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26953step0 raw26953; decide +kernel
      have hl : raw26953step0Labels = raw26953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26953 raw26953Labels permutation520 hz
    mixedMoment B raw26953step0 raw26953step0Labels = mixedMoment B raw26953step1 raw26953step1Labels := by
      have ha : raw26953step1 = (fun i j => raw26953step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26953step1 raw26953step0; decide +kernel
      have hl : raw26953step1Labels = raw26953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26953step0 raw26953step0Labels permutation51 permutation7
    mixedMoment B raw26953step1 raw26953step1Labels = mixedMoment B raw26953step2 raw26953step2Labels := by
      have ha : raw26953step2 = -raw26953step1 := by apply Matrix.ext; change ∀ i j, raw26953step2 i j = -(raw26953step1 i j); unfold raw26953step2 raw26953step1; decide +kernel
      have hl : raw26953step2Labels = raw26953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26953step2 raw26953step2Labels = mixedMoment B raw26953step3 raw26953step3Labels := by
      have ha : raw26953step3 = raw26953step2 := by apply Matrix.ext; unfold raw26953step3 raw26953step2; decide +kernel
      have hl : raw26953step2Labels = labelEmbedding1 ∘ raw26953step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26953step2 raw26953step2Labels raw26953step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical26954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26954 raw26954Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw26954 raw26954Labels = mixedMoment B raw26954step0 raw26954step0Labels := by
      have hz : ∀ j, raw26954 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26954step0 = (fun i j => raw26954 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26954step0 raw26954; decide +kernel
      have hl : raw26954step0Labels = raw26954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26954 raw26954Labels permutation590 hz
    mixedMoment B raw26954step0 raw26954step0Labels = mixedMoment B raw26954step1 raw26954step1Labels := by
      have ha : raw26954step1 = (fun i j => raw26954step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26954step1 raw26954step0; decide +kernel
      have hl : raw26954step1Labels = raw26954step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26954step0 raw26954step0Labels permutation51 permutation7
    mixedMoment B raw26954step1 raw26954step1Labels = mixedMoment B raw26954step2 raw26954step2Labels := by
      have ha : raw26954step2 = -raw26954step1 := by apply Matrix.ext; change ∀ i j, raw26954step2 i j = -(raw26954step1 i j); unfold raw26954step2 raw26954step1; decide +kernel
      have hl : raw26954step2Labels = raw26954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26954step2 raw26954step2Labels = mixedMoment B raw26954step3 raw26954step3Labels := by
      have ha : raw26954step3 = raw26954step2 := by apply Matrix.ext; unfold raw26954step3 raw26954step2; decide +kernel
      have hl : raw26954step2Labels = labelEmbedding1 ∘ raw26954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26954step2 raw26954step2Labels raw26954step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical26955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26955 raw26955Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw26955 raw26955Labels = mixedMoment B raw26955step0 raw26955step0Labels := by
      have ha : raw26955step0 = (fun i j => raw26955 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26955step0 raw26955; decide +kernel
      have hl : raw26955step0Labels = raw26955Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26955 raw26955Labels permutation240 permutation7
    mixedMoment B raw26955step0 raw26955step0Labels = mixedMoment B raw26955step1 raw26955step1Labels := by
      have ha : raw26955step1 = -raw26955step0 := by apply Matrix.ext; change ∀ i j, raw26955step1 i j = -(raw26955step0 i j); unfold raw26955step1 raw26955step0; decide +kernel
      have hl : raw26955step1Labels = raw26955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26955step1 raw26955step1Labels = mixedMoment B raw26955step2 raw26955step2Labels := by
      have ha : raw26955step2 = raw26955step1 := by apply Matrix.ext; unfold raw26955step2 raw26955step1; decide +kernel
      have hl : raw26955step1Labels = labelEmbedding1 ∘ raw26955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26955step1 raw26955step1Labels raw26955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

theorem canonical26956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26956 raw26956Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw26956 raw26956Labels = mixedMoment B raw26956step0 raw26956step0Labels := by
      have ha : raw26956step0 = (fun i j => raw26956 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26956step0 raw26956; decide +kernel
      have hl : raw26956step0Labels = raw26956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26956 raw26956Labels permutation240 permutation7
    mixedMoment B raw26956step0 raw26956step0Labels = mixedMoment B raw26956step1 raw26956step1Labels := by
      have ha : raw26956step1 = -raw26956step0 := by apply Matrix.ext; change ∀ i j, raw26956step1 i j = -(raw26956step0 i j); unfold raw26956step1 raw26956step0; decide +kernel
      have hl : raw26956step1Labels = raw26956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26956step1 raw26956step1Labels = mixedMoment B raw26956step2 raw26956step2Labels := by
      have ha : raw26956step2 = raw26956step1 := by apply Matrix.ext; unfold raw26956step2 raw26956step1; decide +kernel
      have hl : raw26956step1Labels = labelEmbedding1 ∘ raw26956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26956step1 raw26956step1Labels raw26956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

theorem canonical26957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26957 raw26957Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw26957 raw26957Labels = mixedMoment B raw26957step0 raw26957step0Labels := by
      have hz : ∀ j, raw26957 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26957step0 = (fun i j => raw26957 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26957step0 raw26957; decide +kernel
      have hl : raw26957step0Labels = raw26957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26957 raw26957Labels permutation520 hz
    mixedMoment B raw26957step0 raw26957step0Labels = mixedMoment B raw26957step1 raw26957step1Labels := by
      have ha : raw26957step1 = (fun i j => raw26957step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26957step1 raw26957step0; decide +kernel
      have hl : raw26957step1Labels = raw26957step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26957step0 raw26957step0Labels permutation50 permutation7
    mixedMoment B raw26957step1 raw26957step1Labels = mixedMoment B raw26957step2 raw26957step2Labels := by
      have ha : raw26957step2 = -raw26957step1 := by apply Matrix.ext; change ∀ i j, raw26957step2 i j = -(raw26957step1 i j); unfold raw26957step2 raw26957step1; decide +kernel
      have hl : raw26957step2Labels = raw26957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26957step2 raw26957step2Labels = mixedMoment B raw26957step3 raw26957step3Labels := by
      have ha : raw26957step3 = raw26957step2 := by apply Matrix.ext; unfold raw26957step3 raw26957step2; decide +kernel
      have hl : raw26957step2Labels = labelEmbedding1 ∘ raw26957step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26957step2 raw26957step2Labels raw26957step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical26958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26958 raw26958Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw26958 raw26958Labels = mixedMoment B raw26958step0 raw26958step0Labels := by
      have hz : ∀ j, raw26958 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26958step0 = (fun i j => raw26958 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26958step0 raw26958; decide +kernel
      have hl : raw26958step0Labels = raw26958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26958 raw26958Labels permutation590 hz
    mixedMoment B raw26958step0 raw26958step0Labels = mixedMoment B raw26958step1 raw26958step1Labels := by
      have ha : raw26958step1 = (fun i j => raw26958step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26958step1 raw26958step0; decide +kernel
      have hl : raw26958step1Labels = raw26958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26958step0 raw26958step0Labels permutation50 permutation7
    mixedMoment B raw26958step1 raw26958step1Labels = mixedMoment B raw26958step2 raw26958step2Labels := by
      have ha : raw26958step2 = -raw26958step1 := by apply Matrix.ext; change ∀ i j, raw26958step2 i j = -(raw26958step1 i j); unfold raw26958step2 raw26958step1; decide +kernel
      have hl : raw26958step2Labels = raw26958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26958step2 raw26958step2Labels = mixedMoment B raw26958step3 raw26958step3Labels := by
      have ha : raw26958step3 = raw26958step2 := by apply Matrix.ext; unfold raw26958step3 raw26958step2; decide +kernel
      have hl : raw26958step2Labels = labelEmbedding1 ∘ raw26958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26958step2 raw26958step2Labels raw26958step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical26959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26959 raw26959Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw26959 raw26959Labels = mixedMoment B raw26959step0 raw26959step0Labels := by
      have ha : raw26959step0 = (fun i j => raw26959 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26959step0 raw26959; decide +kernel
      have hl : raw26959step0Labels = raw26959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26959 raw26959Labels permutation260 permutation7
    mixedMoment B raw26959step0 raw26959step0Labels = mixedMoment B raw26959step1 raw26959step1Labels := by
      have ha : raw26959step1 = -raw26959step0 := by apply Matrix.ext; change ∀ i j, raw26959step1 i j = -(raw26959step0 i j); unfold raw26959step1 raw26959step0; decide +kernel
      have hl : raw26959step1Labels = raw26959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26959step1 raw26959step1Labels = mixedMoment B raw26959step2 raw26959step2Labels := by
      have ha : raw26959step2 = raw26959step1 := by apply Matrix.ext; unfold raw26959step2 raw26959step1; decide +kernel
      have hl : raw26959step1Labels = labelEmbedding1 ∘ raw26959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26959step1 raw26959step1Labels raw26959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

theorem canonical26960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26960 raw26960Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw26960 raw26960Labels = mixedMoment B raw26960step0 raw26960step0Labels := by
      have ha : raw26960step0 = (fun i j => raw26960 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26960step0 raw26960; decide +kernel
      have hl : raw26960step0Labels = raw26960Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26960 raw26960Labels permutation260 permutation7
    mixedMoment B raw26960step0 raw26960step0Labels = mixedMoment B raw26960step1 raw26960step1Labels := by
      have ha : raw26960step1 = -raw26960step0 := by apply Matrix.ext; change ∀ i j, raw26960step1 i j = -(raw26960step0 i j); unfold raw26960step1 raw26960step0; decide +kernel
      have hl : raw26960step1Labels = raw26960step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26960step1 raw26960step1Labels = mixedMoment B raw26960step2 raw26960step2Labels := by
      have ha : raw26960step2 = raw26960step1 := by apply Matrix.ext; unfold raw26960step2 raw26960step1; decide +kernel
      have hl : raw26960step1Labels = labelEmbedding1 ∘ raw26960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26960step1 raw26960step1Labels raw26960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

theorem canonical26961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26961 raw26961Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw26961 raw26961Labels = mixedMoment B raw26961step0 raw26961step0Labels := by
      have ha : raw26961step0 = (fun i j => raw26961 (permutation261 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26961step0 raw26961; decide +kernel
      have hl : raw26961step0Labels = raw26961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26961 raw26961Labels permutation261 permutation7
    mixedMoment B raw26961step0 raw26961step0Labels = mixedMoment B raw26961step1 raw26961step1Labels := by
      have ha : raw26961step1 = -raw26961step0 := by apply Matrix.ext; change ∀ i j, raw26961step1 i j = -(raw26961step0 i j); unfold raw26961step1 raw26961step0; decide +kernel
      have hl : raw26961step1Labels = raw26961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26961step1 raw26961step1Labels = mixedMoment B raw26961step2 raw26961step2Labels := by
      have ha : raw26961step2 = raw26961step1 := by apply Matrix.ext; unfold raw26961step2 raw26961step1; decide +kernel
      have hl : raw26961step1Labels = labelEmbedding1 ∘ raw26961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26961step1 raw26961step1Labels raw26961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical26962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26962 raw26962Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw26962 raw26962Labels = mixedMoment B raw26962step0 raw26962step0Labels := by
      have hz : ∀ j, raw26962 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26962step0 = (fun i j => raw26962 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26962step0 raw26962; decide +kernel
      have hl : raw26962step0Labels = raw26962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26962 raw26962Labels permutation590 hz
    mixedMoment B raw26962step0 raw26962step0Labels = mixedMoment B raw26962step1 raw26962step1Labels := by
      have ha : raw26962step1 = (fun i j => raw26962step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26962step1 raw26962step0; decide +kernel
      have hl : raw26962step1Labels = raw26962step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26962step0 raw26962step0Labels permutation50 permutation7
    mixedMoment B raw26962step1 raw26962step1Labels = mixedMoment B raw26962step2 raw26962step2Labels := by
      have ha : raw26962step2 = -raw26962step1 := by apply Matrix.ext; change ∀ i j, raw26962step2 i j = -(raw26962step1 i j); unfold raw26962step2 raw26962step1; decide +kernel
      have hl : raw26962step2Labels = raw26962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26962step2 raw26962step2Labels = mixedMoment B raw26962step3 raw26962step3Labels := by
      have ha : raw26962step3 = raw26962step2 := by apply Matrix.ext; unfold raw26962step3 raw26962step2; decide +kernel
      have hl : raw26962step2Labels = labelEmbedding1 ∘ raw26962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26962step2 raw26962step2Labels raw26962step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical26963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26963 raw26963Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw26963 raw26963Labels = mixedMoment B raw26963step0 raw26963step0Labels := by
      have ha : raw26963step0 = (fun i j => raw26963 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26963step0 raw26963; decide +kernel
      have hl : raw26963step0Labels = raw26963Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26963 raw26963Labels permutation240 permutation7
    mixedMoment B raw26963step0 raw26963step0Labels = mixedMoment B raw26963step1 raw26963step1Labels := by
      have ha : raw26963step1 = -raw26963step0 := by apply Matrix.ext; change ∀ i j, raw26963step1 i j = -(raw26963step0 i j); unfold raw26963step1 raw26963step0; decide +kernel
      have hl : raw26963step1Labels = raw26963step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26963step1 raw26963step1Labels = mixedMoment B raw26963step2 raw26963step2Labels := by
      have ha : raw26963step2 = raw26963step1 := by apply Matrix.ext; unfold raw26963step2 raw26963step1; decide +kernel
      have hl : raw26963step1Labels = labelEmbedding1 ∘ raw26963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26963step1 raw26963step1Labels raw26963step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

theorem canonical26964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26964 raw26964Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw26964 raw26964Labels = mixedMoment B raw26964step0 raw26964step0Labels := by
      have ha : raw26964step0 = (fun i j => raw26964 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26964step0 raw26964; decide +kernel
      have hl : raw26964step0Labels = raw26964Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26964 raw26964Labels permutation240 permutation7
    mixedMoment B raw26964step0 raw26964step0Labels = mixedMoment B raw26964step1 raw26964step1Labels := by
      have ha : raw26964step1 = -raw26964step0 := by apply Matrix.ext; change ∀ i j, raw26964step1 i j = -(raw26964step0 i j); unfold raw26964step1 raw26964step0; decide +kernel
      have hl : raw26964step1Labels = raw26964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26964step1 raw26964step1Labels = mixedMoment B raw26964step2 raw26964step2Labels := by
      have ha : raw26964step2 = raw26964step1 := by apply Matrix.ext; unfold raw26964step2 raw26964step1; decide +kernel
      have hl : raw26964step1Labels = labelEmbedding1 ∘ raw26964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26964step1 raw26964step1Labels raw26964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

theorem canonical26965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26965 raw26965Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw26965 raw26965Labels = mixedMoment B raw26965step0 raw26965step0Labels := by
      have hz : ∀ j, raw26965 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26965step0 = (fun i j => raw26965 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26965step0 raw26965; decide +kernel
      have hl : raw26965step0Labels = raw26965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26965 raw26965Labels permutation520 hz
    mixedMoment B raw26965step0 raw26965step0Labels = mixedMoment B raw26965step1 raw26965step1Labels := by
      have ha : raw26965step1 = (fun i j => raw26965step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26965step1 raw26965step0; decide +kernel
      have hl : raw26965step1Labels = raw26965step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26965step0 raw26965step0Labels permutation50 permutation7
    mixedMoment B raw26965step1 raw26965step1Labels = mixedMoment B raw26965step2 raw26965step2Labels := by
      have ha : raw26965step2 = -raw26965step1 := by apply Matrix.ext; change ∀ i j, raw26965step2 i j = -(raw26965step1 i j); unfold raw26965step2 raw26965step1; decide +kernel
      have hl : raw26965step2Labels = raw26965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26965step2 raw26965step2Labels = mixedMoment B raw26965step3 raw26965step3Labels := by
      have ha : raw26965step3 = raw26965step2 := by apply Matrix.ext; unfold raw26965step3 raw26965step2; decide +kernel
      have hl : raw26965step2Labels = labelEmbedding1 ∘ raw26965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26965step2 raw26965step2Labels raw26965step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical26966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26966 raw26966Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw26966 raw26966Labels = mixedMoment B raw26966step0 raw26966step0Labels := by
      have ha : raw26966step0 = (fun i j => raw26966 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26966step0 raw26966; decide +kernel
      have hl : raw26966step0Labels = raw26966Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26966 raw26966Labels permutation240 permutation2
    _ = mixedMoment B node599 node599Labels := by rfl

theorem canonical26967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26967 raw26967Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw26967 raw26967Labels = mixedMoment B raw26967step0 raw26967step0Labels := by
      have ha : raw26967step0 = (fun i j => raw26967 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26967step0 raw26967; decide +kernel
      have hl : raw26967step0Labels = raw26967Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26967 raw26967Labels permutation168 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical26968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26968 raw26968Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw26968 raw26968Labels = mixedMoment B raw26968step0 raw26968step0Labels := by
      have ha : raw26968step0 = (fun i j => raw26968 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26968step0 raw26968; decide +kernel
      have hl : raw26968step0Labels = raw26968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26968 raw26968Labels permutation192 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical26969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26969 raw26969Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw26969 raw26969Labels = mixedMoment B raw26969step0 raw26969step0Labels := by
      have ha : raw26969step0 = (fun i j => raw26969 (permutation216 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26969step0 raw26969; decide +kernel
      have hl : raw26969step0Labels = raw26969Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26969 raw26969Labels permutation216 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical26970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26970 raw26970Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw26970 raw26970Labels = mixedMoment B raw26970step0 raw26970step0Labels := by
      have hz : ∀ j, raw26970 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26970step0 = (fun i j => raw26970 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26970step0 raw26970; decide +kernel
      have hl : raw26970step0Labels = raw26970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26970 raw26970Labels permutation520 hz
    mixedMoment B raw26970step0 raw26970step0Labels = mixedMoment B raw26970step1 raw26970step1Labels := by
      have ha : raw26970step1 = (fun i j => raw26970step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26970step1 raw26970step0; decide +kernel
      have hl : raw26970step1Labels = raw26970step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26970step0 raw26970step0Labels permutation50 permutation2
    _ = mixedMoment B node1081 node1081Labels := by rfl

theorem canonical26971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26971 raw26971Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw26971 raw26971Labels = mixedMoment B raw26971step0 raw26971step0Labels := by
      have hz : ∀ j, raw26971 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26971step0 = (fun i j => raw26971 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26971step0 raw26971; decide +kernel
      have hl : raw26971step0Labels = raw26971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26971 raw26971Labels permutation590 hz
    mixedMoment B raw26971step0 raw26971step0Labels = mixedMoment B raw26971step1 raw26971step1Labels := by
      have ha : raw26971step1 = (fun i j => raw26971step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26971step1 raw26971step0; decide +kernel
      have hl : raw26971step1Labels = raw26971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26971step0 raw26971step0Labels permutation50 permutation2
    _ = mixedMoment B node1081 node1081Labels := by rfl

theorem canonical26992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26992 raw26992Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw26992 raw26992Labels = mixedMoment B raw26992step0 raw26992step0Labels := by
      have ha : raw26992step0 = (fun i j => raw26992 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26992step0 raw26992; decide +kernel
      have hl : raw26992step0Labels = raw26992Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26992 raw26992Labels permutation168 permutation3
    _ = mixedMoment B node2593 node2593Labels := by rfl

theorem canonical26993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26993 raw26993Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw26993 raw26993Labels = mixedMoment B raw26993step0 raw26993step0Labels := by
      have hz : ∀ j, raw26993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26993step0 = (fun i j => raw26993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26993step0 raw26993; decide +kernel
      have hl : raw26993step0Labels = raw26993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26993 raw26993Labels permutation434 hz
    mixedMoment B raw26993step0 raw26993step0Labels = mixedMoment B raw26993step1 raw26993step1Labels := by
      have ha : raw26993step1 = (fun i j => raw26993step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26993step1 raw26993step0; decide +kernel
      have hl : raw26993step1Labels = raw26993step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26993step0 raw26993step0Labels permutation35 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

theorem canonical26994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26994 raw26994Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw26994 raw26994Labels = mixedMoment B raw26994step0 raw26994step0Labels := by
      have ha : raw26994step0 = (fun i j => raw26994 (permutation228 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26994step0 raw26994; decide +kernel
      have hl : raw26994step0Labels = raw26994Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26994 raw26994Labels permutation228 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical26995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26995 raw26995Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw26995 raw26995Labels = mixedMoment B raw26995step0 raw26995step0Labels := by
      have ha : raw26995step0 = (fun i j => raw26995 (permutation250 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26995step0 raw26995; decide +kernel
      have hl : raw26995step0Labels = raw26995Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26995 raw26995Labels permutation250 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical26996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26996 raw26996Labels = mixedMoment B node550 node550Labels := by
  calc
    mixedMoment B raw26996 raw26996Labels = mixedMoment B raw26996step0 raw26996step0Labels := by
      have ha : raw26996step0 = (fun i j => raw26996 (permutation243 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26996step0 raw26996; decide +kernel
      have hl : raw26996step0Labels = raw26996Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26996 raw26996Labels permutation243 permutation3
    _ = mixedMoment B node550 node550Labels := by rfl

theorem canonical26997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26997 raw26997Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26997 raw26997Labels = mixedMoment B raw26997step0 raw26997step0Labels := by
      have hz : ∀ j, raw26997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26997step0 = (fun i j => raw26997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26997step0 raw26997; decide +kernel
      have hl : raw26997step0Labels = raw26997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26997 raw26997Labels permutation434 hz
    mixedMoment B raw26997step0 raw26997step0Labels = mixedMoment B raw26997step1 raw26997step1Labels := by
      have ha : raw26997step1 = (fun i j => raw26997step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26997step1 raw26997step0; decide +kernel
      have hl : raw26997step1Labels = raw26997step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26997step0 raw26997step0Labels permutation49 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical26998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26998 raw26998Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw26998 raw26998Labels = mixedMoment B raw26998step0 raw26998step0Labels := by
      have ha : raw26998step0 = (fun i j => raw26998 (permutation243 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26998step0 raw26998; decide +kernel
      have hl : raw26998step0Labels = raw26998Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26998 raw26998Labels permutation243 permutation3
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical26999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26999 raw26999Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw26999 raw26999Labels = mixedMoment B raw26999step0 raw26999step0Labels := by
      have ha : raw26999step0 = (fun i j => raw26999 (permutation263 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26999step0 raw26999; decide +kernel
      have hl : raw26999step0Labels = raw26999Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26999 raw26999Labels permutation263 permutation3
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical27000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27000 raw27000Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw27000 raw27000Labels = mixedMoment B raw27000step0 raw27000step0Labels := by
      have ha : raw27000step0 = (fun i j => raw27000 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27000step0 raw27000; decide +kernel
      have hl : raw27000step0Labels = raw27000Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27000 raw27000Labels permutation169 permutation3
    _ = mixedMoment B node535 node535Labels := by rfl

theorem canonical27001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27001 raw27001Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw27001 raw27001Labels = mixedMoment B raw27001step0 raw27001step0Labels := by
      have ha : raw27001step0 = (fun i j => raw27001 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27001step0 raw27001; decide +kernel
      have hl : raw27001step0Labels = raw27001Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27001 raw27001Labels permutation169 permutation3
    _ = mixedMoment B node919 node919Labels := by rfl

theorem canonical27002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27002 raw27002Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw27002 raw27002Labels = mixedMoment B raw27002step0 raw27002step0Labels := by
      have hz : ∀ j, raw27002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27002step0 = (fun i j => raw27002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27002step0 raw27002; decide +kernel
      have hl : raw27002step0Labels = raw27002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27002 raw27002Labels permutation434 hz
    mixedMoment B raw27002step0 raw27002step0Labels = mixedMoment B raw27002step1 raw27002step1Labels := by
      have ha : raw27002step1 = (fun i j => raw27002step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27002step1 raw27002step0; decide +kernel
      have hl : raw27002step1Labels = raw27002step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27002step0 raw27002step0Labels permutation35 permutation3
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical27003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27003 raw27003Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw27003 raw27003Labels = mixedMoment B raw27003step0 raw27003step0Labels := by
      have ha : raw27003step0 = (fun i j => raw27003 (permutation229 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27003step0 raw27003; decide +kernel
      have hl : raw27003step0Labels = raw27003Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27003 raw27003Labels permutation229 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical27004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27004 raw27004Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw27004 raw27004Labels = mixedMoment B raw27004step0 raw27004step0Labels := by
      have ha : raw27004step0 = (fun i j => raw27004 (permutation251 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27004step0 raw27004; decide +kernel
      have hl : raw27004step0Labels = raw27004Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27004 raw27004Labels permutation251 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical27005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27005 raw27005Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw27005 raw27005Labels = mixedMoment B raw27005step0 raw27005step0Labels := by
      have ha : raw27005step0 = (fun i j => raw27005 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27005step0 raw27005; decide +kernel
      have hl : raw27005step0Labels = raw27005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27005 raw27005Labels permutation168 permutation3
    _ = mixedMoment B node535 node535Labels := by rfl

theorem canonical27006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27006 raw27006Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw27006 raw27006Labels = mixedMoment B raw27006step0 raw27006step0Labels := by
      have ha : raw27006step0 = (fun i j => raw27006 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27006step0 raw27006; decide +kernel
      have hl : raw27006step0Labels = raw27006Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27006 raw27006Labels permutation168 permutation3
    _ = mixedMoment B node919 node919Labels := by rfl

theorem canonical27007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27007 raw27007Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw27007 raw27007Labels = mixedMoment B raw27007step0 raw27007step0Labels := by
      have ha : raw27007step0 = (fun i j => raw27007 (permutation228 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27007step0 raw27007; decide +kernel
      have hl : raw27007step0Labels = raw27007Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27007 raw27007Labels permutation228 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical211
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27008 raw27008Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw27008 raw27008Labels = mixedMoment B raw27008step0 raw27008step0Labels := by
      have ha : raw27008step0 = (fun i j => raw27008 (permutation250 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27008step0 raw27008; decide +kernel
      have hl : raw27008step0Labels = raw27008Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27008 raw27008Labels permutation250 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

theorem canonical27009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27009 raw27009Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw27009 raw27009Labels = mixedMoment B raw27009step0 raw27009step0Labels := by
      have ha : raw27009step0 = (fun i j => raw27009 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27009step0 raw27009; decide +kernel
      have hl : raw27009step0Labels = raw27009Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27009 raw27009Labels permutation170 permutation3
    _ = mixedMoment B node537 node537Labels := by rfl

theorem canonical27010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27010 raw27010Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw27010 raw27010Labels = mixedMoment B raw27010step0 raw27010step0Labels := by
      have ha : raw27010step0 = (fun i j => raw27010 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27010step0 raw27010; decide +kernel
      have hl : raw27010step0Labels = raw27010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27010 raw27010Labels permutation170 permutation3
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical27011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27011 raw27011Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw27011 raw27011Labels = mixedMoment B raw27011step0 raw27011step0Labels := by
      have ha : raw27011step0 = (fun i j => raw27011 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27011step0 raw27011; decide +kernel
      have hl : raw27011step0Labels = raw27011Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27011 raw27011Labels permutation246 permutation3
    _ = mixedMoment B node980 node980Labels := by rfl

theorem canonical27040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27040 raw27040Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw27040 raw27040Labels = mixedMoment B raw27040step0 raw27040step0Labels := by
      have hz : ∀ j, raw27040 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27040step0 = (fun i j => raw27040 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27040step0 raw27040; decide +kernel
      have hl : raw27040step0Labels = raw27040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27040 raw27040Labels permutation265 hz
    mixedMoment B raw27040step0 raw27040step0Labels = mixedMoment B raw27040step1 raw27040step1Labels := by
      have ha : raw27040step1 = (fun i j => raw27040step0 (permutation55 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27040step1 raw27040step0; decide +kernel
      have hl : raw27040step1Labels = raw27040step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27040step0 raw27040step0Labels permutation55 permutation2
    _ = mixedMoment B node1070 node1070Labels := by rfl

theorem canonical27041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27041 raw27041Labels = mixedMoment B node2043 node2043Labels := by
  calc
    mixedMoment B raw27041 raw27041Labels = mixedMoment B raw27041step0 raw27041step0Labels := by
      have ha : raw27041step0 = (fun i j => raw27041 (permutation175 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27041step0 raw27041; decide +kernel
      have hl : raw27041step0Labels = raw27041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27041 raw27041Labels permutation175 permutation2
    _ = mixedMoment B node2043 node2043Labels := by rfl

theorem canonical27042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27042 raw27042Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw27042 raw27042Labels = mixedMoment B raw27042step0 raw27042step0Labels := by
      have hz : ∀ j, raw27042 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27042step0 = (fun i j => raw27042 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27042step0 raw27042; decide +kernel
      have hl : raw27042step0Labels = raw27042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27042 raw27042Labels permutation265 hz
    mixedMoment B raw27042step0 raw27042step0Labels = mixedMoment B raw27042step1 raw27042step1Labels := by
      have ha : raw27042step1 = (fun i j => raw27042step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27042step1 raw27042step0; decide +kernel
      have hl : raw27042step1Labels = raw27042step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27042step0 raw27042step0Labels permutation62 permutation4
    mixedMoment B raw27042step1 raw27042step1Labels = mixedMoment B raw27042step2 raw27042step2Labels := by
      have ha : raw27042step2 = -raw27042step1 := by apply Matrix.ext; change ∀ i j, raw27042step2 i j = -(raw27042step1 i j); unfold raw27042step2 raw27042step1; decide +kernel
      have hl : raw27042step2Labels = raw27042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical27043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27043 raw27043Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27043 raw27043Labels = mixedMoment B raw27043step0 raw27043step0Labels := by
      have hz : ∀ j, raw27043 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27043step0 = (fun i j => raw27043 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27043step0 raw27043; decide +kernel
      have hl : raw27043step0Labels = raw27043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27043 raw27043Labels permutation265 hz
    mixedMoment B raw27043step0 raw27043step0Labels = mixedMoment B raw27043step1 raw27043step1Labels := by
      have ha : raw27043step1 = (fun i j => raw27043step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27043step1 raw27043step0; decide +kernel
      have hl : raw27043step1Labels = raw27043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27043step0 raw27043step0Labels permutation43 permutation2
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical27044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27044 raw27044Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw27044 raw27044Labels = mixedMoment B raw27044step0 raw27044step0Labels := by
      have hz : ∀ j, raw27044 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27044step0 = (fun i j => raw27044 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27044step0 raw27044; decide +kernel
      have hl : raw27044step0Labels = raw27044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27044 raw27044Labels permutation520 hz
    mixedMoment B raw27044step0 raw27044step0Labels = mixedMoment B raw27044step1 raw27044step1Labels := by
      have hz : ∀ j, raw27044step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27044step1 = (fun i j => raw27044step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27044step1 raw27044step0; decide +kernel
      have hl : raw27044step1Labels = raw27044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27044step0 raw27044step0Labels permutation56 hz
    mixedMoment B raw27044step1 raw27044step1Labels = mixedMoment B raw27044step2 raw27044step2Labels := by
      have ha : raw27044step2 = (fun i j => raw27044step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27044step2 raw27044step1; decide +kernel
      have hl : raw27044step2Labels = raw27044step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27044step1 raw27044step1Labels permutation13 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical27045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27045 raw27045Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27045 raw27045Labels = mixedMoment B raw27045step0 raw27045step0Labels := by
      have hz : ∀ j, raw27045 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27045step0 = (fun i j => raw27045 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27045step0 raw27045; decide +kernel
      have hl : raw27045step0Labels = raw27045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27045 raw27045Labels permutation265 hz
    mixedMoment B raw27045step0 raw27045step0Labels = mixedMoment B raw27045step1 raw27045step1Labels := by
      have ha : raw27045step1 = (fun i j => raw27045step0 (permutation55 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27045step1 raw27045step0; decide +kernel
      have hl : raw27045step1Labels = raw27045step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27045step0 raw27045step0Labels permutation55 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical27046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27046 raw27046Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27046 raw27046Labels = mixedMoment B raw27046step0 raw27046step0Labels := by
      have hz : ∀ j, raw27046 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27046step0 = (fun i j => raw27046 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27046step0 raw27046; decide +kernel
      have hl : raw27046step0Labels = raw27046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27046 raw27046Labels permutation520 hz
    mixedMoment B raw27046step0 raw27046step0Labels = mixedMoment B raw27046step1 raw27046step1Labels := by
      have hz : ∀ j, raw27046step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27046step1 = (fun i j => raw27046step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27046step1 raw27046step0; decide +kernel
      have hl : raw27046step1Labels = raw27046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27046step0 raw27046step0Labels permutation56 hz
    mixedMoment B raw27046step1 raw27046step1Labels = mixedMoment B raw27046step2 raw27046step2Labels := by
      have ha : raw27046step2 = (fun i j => raw27046step1 (permutation13 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27046step2 raw27046step1; decide +kernel
      have hl : raw27046step2Labels = raw27046step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27046step1 raw27046step1Labels permutation13 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical27047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27047 raw27047Labels = mixedMoment B node1071 node1071Labels := by
  calc
    mixedMoment B raw27047 raw27047Labels = mixedMoment B raw27047step0 raw27047step0Labels := by
      have hz : ∀ j, raw27047 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27047step0 = (fun i j => raw27047 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27047step0 raw27047; decide +kernel
      have hl : raw27047step0Labels = raw27047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27047 raw27047Labels permutation265 hz
    mixedMoment B raw27047step0 raw27047step0Labels = mixedMoment B raw27047step1 raw27047step1Labels := by
      have ha : raw27047step1 = (fun i j => raw27047step0 (permutation54 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27047step1 raw27047step0; decide +kernel
      have hl : raw27047step1Labels = raw27047step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27047step0 raw27047step0Labels permutation54 permutation2
    _ = mixedMoment B node1071 node1071Labels := by rfl

theorem canonical27048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27048 raw27048Labels = mixedMoment B node2044 node2044Labels := by
  calc
    mixedMoment B raw27048 raw27048Labels = mixedMoment B raw27048step0 raw27048step0Labels := by
      have ha : raw27048step0 = (fun i j => raw27048 (permutation174 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27048step0 raw27048; decide +kernel
      have hl : raw27048step0Labels = raw27048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27048 raw27048Labels permutation174 permutation2
    _ = mixedMoment B node2044 node2044Labels := by rfl

theorem canonical27049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27049 raw27049Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw27049 raw27049Labels = mixedMoment B raw27049step0 raw27049step0Labels := by
      have hz : ∀ j, raw27049 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27049step0 = (fun i j => raw27049 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27049step0 raw27049; decide +kernel
      have hl : raw27049step0Labels = raw27049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27049 raw27049Labels permutation265 hz
    mixedMoment B raw27049step0 raw27049step0Labels = mixedMoment B raw27049step1 raw27049step1Labels := by
      have ha : raw27049step1 = (fun i j => raw27049step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27049step1 raw27049step0; decide +kernel
      have hl : raw27049step1Labels = raw27049step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27049step0 raw27049step0Labels permutation37 permutation2
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical27050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27050 raw27050Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw27050 raw27050Labels = mixedMoment B raw27050step0 raw27050step0Labels := by
      have hz : ∀ j, raw27050 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27050step0 = (fun i j => raw27050 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27050step0 raw27050; decide +kernel
      have hl : raw27050step0Labels = raw27050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27050 raw27050Labels permutation265 hz
    mixedMoment B raw27050step0 raw27050step0Labels = mixedMoment B raw27050step1 raw27050step1Labels := by
      have ha : raw27050step1 = (fun i j => raw27050step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27050step1 raw27050step0; decide +kernel
      have hl : raw27050step1Labels = raw27050step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27050step0 raw27050step0Labels permutation43 permutation2
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical27051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27051 raw27051Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw27051 raw27051Labels = mixedMoment B raw27051step0 raw27051step0Labels := by
      have hz : ∀ j, raw27051 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27051step0 = (fun i j => raw27051 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27051step0 raw27051; decide +kernel
      have hl : raw27051step0Labels = raw27051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27051 raw27051Labels permutation520 hz
    mixedMoment B raw27051step0 raw27051step0Labels = mixedMoment B raw27051step1 raw27051step1Labels := by
      have hz : ∀ j, raw27051step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27051step1 = (fun i j => raw27051step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27051step1 raw27051step0; decide +kernel
      have hl : raw27051step1Labels = raw27051step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27051step0 raw27051step0Labels permutation56 hz
    mixedMoment B raw27051step1 raw27051step1Labels = mixedMoment B raw27051step2 raw27051step2Labels := by
      have ha : raw27051step2 = (fun i j => raw27051step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27051step2 raw27051step1; decide +kernel
      have hl : raw27051step2Labels = raw27051step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27051step1 raw27051step1Labels permutation12 permutation2
    _ = mixedMoment B node2288 node2288Labels := by rfl

theorem canonical27052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27052 raw27052Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw27052 raw27052Labels = mixedMoment B raw27052step0 raw27052step0Labels := by
      have hz : ∀ j, raw27052 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27052step0 = (fun i j => raw27052 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27052step0 raw27052; decide +kernel
      have hl : raw27052step0Labels = raw27052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27052 raw27052Labels permutation265 hz
    mixedMoment B raw27052step0 raw27052step0Labels = mixedMoment B raw27052step1 raw27052step1Labels := by
      have ha : raw27052step1 = (fun i j => raw27052step0 (permutation54 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27052step1 raw27052step0; decide +kernel
      have hl : raw27052step1Labels = raw27052step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27052step0 raw27052step0Labels permutation54 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical27053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27053 raw27053Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw27053 raw27053Labels = mixedMoment B raw27053step0 raw27053step0Labels := by
      have hz : ∀ j, raw27053 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27053step0 = (fun i j => raw27053 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27053step0 raw27053; decide +kernel
      have hl : raw27053step0Labels = raw27053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27053 raw27053Labels permutation520 hz
    mixedMoment B raw27053step0 raw27053step0Labels = mixedMoment B raw27053step1 raw27053step1Labels := by
      have hz : ∀ j, raw27053step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27053step1 = (fun i j => raw27053step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27053step1 raw27053step0; decide +kernel
      have hl : raw27053step1Labels = raw27053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27053step0 raw27053step0Labels permutation56 hz
    mixedMoment B raw27053step1 raw27053step1Labels = mixedMoment B raw27053step2 raw27053step2Labels := by
      have ha : raw27053step2 = (fun i j => raw27053step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27053step2 raw27053step1; decide +kernel
      have hl : raw27053step2Labels = raw27053step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27053step1 raw27053step1Labels permutation12 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical27054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27054 raw27054Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw27054 raw27054Labels = mixedMoment B raw27054step0 raw27054step0Labels := by
      have hz : ∀ j, raw27054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27054step0 = (fun i j => raw27054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27054step0 raw27054; decide +kernel
      have hl : raw27054step0Labels = raw27054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27054 raw27054Labels permutation265 hz
    mixedMoment B raw27054step0 raw27054step0Labels = mixedMoment B raw27054step1 raw27054step1Labels := by
      have ha : raw27054step1 = (fun i j => raw27054step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27054step1 raw27054step0; decide +kernel
      have hl : raw27054step1Labels = raw27054step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27054step0 raw27054step0Labels permutation53 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

theorem canonical27055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27055 raw27055Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw27055 raw27055Labels = mixedMoment B raw27055step0 raw27055step0Labels := by
      have ha : raw27055step0 = (fun i j => raw27055 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27055step0 raw27055; decide +kernel
      have hl : raw27055step0Labels = raw27055Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27055 raw27055Labels permutation173 permutation2
    _ = mixedMoment B node2046 node2046Labels := by rfl

theorem canonical27056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27056 raw27056Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw27056 raw27056Labels = mixedMoment B raw27056step0 raw27056step0Labels := by
      have hz : ∀ j, raw27056 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27056step0 = (fun i j => raw27056 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27056step0 raw27056; decide +kernel
      have hl : raw27056step0Labels = raw27056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27056 raw27056Labels permutation265 hz
    mixedMoment B raw27056step0 raw27056step0Labels = mixedMoment B raw27056step1 raw27056step1Labels := by
      have ha : raw27056step1 = (fun i j => raw27056step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27056step1 raw27056step0; decide +kernel
      have hl : raw27056step1Labels = raw27056step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27056step0 raw27056step0Labels permutation36 permutation2
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical27057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27057 raw27057Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw27057 raw27057Labels = mixedMoment B raw27057step0 raw27057step0Labels := by
      have hz : ∀ j, raw27057 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27057step0 = (fun i j => raw27057 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27057step0 raw27057; decide +kernel
      have hl : raw27057step0Labels = raw27057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27057 raw27057Labels permutation265 hz
    mixedMoment B raw27057step0 raw27057step0Labels = mixedMoment B raw27057step1 raw27057step1Labels := by
      have ha : raw27057step1 = (fun i j => raw27057step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27057step1 raw27057step0; decide +kernel
      have hl : raw27057step1Labels = raw27057step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27057step0 raw27057step0Labels permutation43 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical27058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27058 raw27058Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw27058 raw27058Labels = mixedMoment B raw27058step0 raw27058step0Labels := by
      have hz : ∀ j, raw27058 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27058step0 = (fun i j => raw27058 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27058step0 raw27058; decide +kernel
      have hl : raw27058step0Labels = raw27058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27058 raw27058Labels permutation265 hz
    mixedMoment B raw27058step0 raw27058step0Labels = mixedMoment B raw27058step1 raw27058step1Labels := by
      have ha : raw27058step1 = (fun i j => raw27058step0 (permutation49 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27058step1 raw27058step0; decide +kernel
      have hl : raw27058step1Labels = raw27058step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27058step0 raw27058step0Labels permutation49 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical27059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27059 raw27059Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw27059 raw27059Labels = mixedMoment B raw27059step0 raw27059step0Labels := by
      have hz : ∀ j, raw27059 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27059step0 = (fun i j => raw27059 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27059step0 raw27059; decide +kernel
      have hl : raw27059step0Labels = raw27059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27059 raw27059Labels permutation265 hz
    mixedMoment B raw27059step0 raw27059step0Labels = mixedMoment B raw27059step1 raw27059step1Labels := by
      have ha : raw27059step1 = (fun i j => raw27059step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27059step1 raw27059step0; decide +kernel
      have hl : raw27059step1Labels = raw27059step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27059step0 raw27059step0Labels permutation53 permutation2
    _ = mixedMoment B node2227 node2227Labels := by rfl

theorem canonical27060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27060 raw27060Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw27060 raw27060Labels = mixedMoment B raw27060step0 raw27060step0Labels := by
      have hz : ∀ j, raw27060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27060step0 = (fun i j => raw27060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27060step0 raw27060; decide +kernel
      have hl : raw27060step0Labels = raw27060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27060 raw27060Labels permutation265 hz
    mixedMoment B raw27060step0 raw27060step0Labels = mixedMoment B raw27060step1 raw27060step1Labels := by
      have ha : raw27060step1 = (fun i j => raw27060step0 (permutation53 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27060step1 raw27060step0; decide +kernel
      have hl : raw27060step1Labels = raw27060step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27060step0 raw27060step0Labels permutation53 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical27091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27091 raw27091Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw27091 raw27091Labels = mixedMoment B raw27091step0 raw27091step0Labels := by
      have ha : raw27091step0 = (fun i j => raw27091 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27091step0 raw27091; decide +kernel
      have hl : raw27091step0Labels = raw27091Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27091 raw27091Labels permutation169 permutation7
    mixedMoment B raw27091step0 raw27091step0Labels = mixedMoment B raw27091step1 raw27091step1Labels := by
      have ha : raw27091step1 = -raw27091step0 := by apply Matrix.ext; change ∀ i j, raw27091step1 i j = -(raw27091step0 i j); unfold raw27091step1 raw27091step0; decide +kernel
      have hl : raw27091step1Labels = raw27091step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27091step1 raw27091step1Labels = mixedMoment B raw27091step2 raw27091step2Labels := by
      have ha : raw27091step2 = raw27091step1 := by apply Matrix.ext; unfold raw27091step2 raw27091step1; decide +kernel
      have hl : raw27091step1Labels = labelEmbedding1 ∘ raw27091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27091step1 raw27091step1Labels raw27091step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical27092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27092 raw27092Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw27092 raw27092Labels = mixedMoment B raw27092step0 raw27092step0Labels := by
      have hz : ∀ j, raw27092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27092step0 = (fun i j => raw27092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27092step0 raw27092; decide +kernel
      have hl : raw27092step0Labels = raw27092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27092 raw27092Labels permutation265 hz
    mixedMoment B raw27092step0 raw27092step0Labels = mixedMoment B raw27092step1 raw27092step1Labels := by
      have ha : raw27092step1 = (fun i j => raw27092step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27092step1 raw27092step0; decide +kernel
      have hl : raw27092step1Labels = raw27092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27092step0 raw27092step0Labels permutation49 permutation7
    mixedMoment B raw27092step1 raw27092step1Labels = mixedMoment B raw27092step2 raw27092step2Labels := by
      have ha : raw27092step2 = -raw27092step1 := by apply Matrix.ext; change ∀ i j, raw27092step2 i j = -(raw27092step1 i j); unfold raw27092step2 raw27092step1; decide +kernel
      have hl : raw27092step2Labels = raw27092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27092step2 raw27092step2Labels = mixedMoment B raw27092step3 raw27092step3Labels := by
      have ha : raw27092step3 = raw27092step2 := by apply Matrix.ext; unfold raw27092step3 raw27092step2; decide +kernel
      have hl : raw27092step2Labels = labelEmbedding1 ∘ raw27092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27092step2 raw27092step2Labels raw27092step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical27093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27093 raw27093Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw27093 raw27093Labels = mixedMoment B raw27093step0 raw27093step0Labels := by
      have hz : ∀ j, raw27093 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27093step0 = (fun i j => raw27093 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27093step0 raw27093; decide +kernel
      have hl : raw27093step0Labels = raw27093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27093 raw27093Labels permutation265 hz
    mixedMoment B raw27093step0 raw27093step0Labels = mixedMoment B raw27093step1 raw27093step1Labels := by
      have ha : raw27093step1 = (fun i j => raw27093step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27093step1 raw27093step0; decide +kernel
      have hl : raw27093step1Labels = raw27093step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27093step0 raw27093step0Labels permutation49 permutation7
    mixedMoment B raw27093step1 raw27093step1Labels = mixedMoment B raw27093step2 raw27093step2Labels := by
      have ha : raw27093step2 = -raw27093step1 := by apply Matrix.ext; change ∀ i j, raw27093step2 i j = -(raw27093step1 i j); unfold raw27093step2 raw27093step1; decide +kernel
      have hl : raw27093step2Labels = raw27093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27093step2 raw27093step2Labels = mixedMoment B raw27093step3 raw27093step3Labels := by
      have ha : raw27093step3 = raw27093step2 := by apply Matrix.ext; unfold raw27093step3 raw27093step2; decide +kernel
      have hl : raw27093step2Labels = labelEmbedding1 ∘ raw27093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27093step2 raw27093step2Labels raw27093step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical27094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27094 raw27094Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw27094 raw27094Labels = mixedMoment B raw27094step0 raw27094step0Labels := by
      have hz : ∀ j, raw27094 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27094step0 = (fun i j => raw27094 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27094step0 raw27094; decide +kernel
      have hl : raw27094step0Labels = raw27094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27094 raw27094Labels permutation520 hz
    mixedMoment B raw27094step0 raw27094step0Labels = mixedMoment B raw27094step1 raw27094step1Labels := by
      have hz : ∀ j, raw27094step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27094step1 = (fun i j => raw27094step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27094step1 raw27094step0; decide +kernel
      have hl : raw27094step1Labels = raw27094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27094step0 raw27094step0Labels permutation56 hz
    mixedMoment B raw27094step1 raw27094step1Labels = mixedMoment B raw27094step2 raw27094step2Labels := by
      have ha : raw27094step2 = (fun i j => raw27094step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27094step2 raw27094step1; decide +kernel
      have hl : raw27094step2Labels = raw27094step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27094step1 raw27094step1Labels permutation13 permutation7
    mixedMoment B raw27094step2 raw27094step2Labels = mixedMoment B raw27094step3 raw27094step3Labels := by
      have ha : raw27094step3 = -raw27094step2 := by apply Matrix.ext; change ∀ i j, raw27094step3 i j = -(raw27094step2 i j); unfold raw27094step3 raw27094step2; decide +kernel
      have hl : raw27094step3Labels = raw27094step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27094step3 raw27094step3Labels = mixedMoment B raw27094step4 raw27094step4Labels := by
      have ha : raw27094step4 = raw27094step3 := by apply Matrix.ext; unfold raw27094step4 raw27094step3; decide +kernel
      have hl : raw27094step3Labels = labelEmbedding1 ∘ raw27094step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27094step3 raw27094step3Labels raw27094step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical27095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27095 raw27095Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw27095 raw27095Labels = mixedMoment B raw27095step0 raw27095step0Labels := by
      have hz : ∀ j, raw27095 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27095step0 = (fun i j => raw27095 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27095step0 raw27095; decide +kernel
      have hl : raw27095step0Labels = raw27095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27095 raw27095Labels permutation590 hz
    mixedMoment B raw27095step0 raw27095step0Labels = mixedMoment B raw27095step1 raw27095step1Labels := by
      have hz : ∀ j, raw27095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27095step1 = (fun i j => raw27095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27095step1 raw27095step0; decide +kernel
      have hl : raw27095step1Labels = raw27095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27095step0 raw27095step0Labels permutation56 hz
    mixedMoment B raw27095step1 raw27095step1Labels = mixedMoment B raw27095step2 raw27095step2Labels := by
      have ha : raw27095step2 = (fun i j => raw27095step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27095step2 raw27095step1; decide +kernel
      have hl : raw27095step2Labels = raw27095step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27095step1 raw27095step1Labels permutation13 permutation7
    mixedMoment B raw27095step2 raw27095step2Labels = mixedMoment B raw27095step3 raw27095step3Labels := by
      have ha : raw27095step3 = -raw27095step2 := by apply Matrix.ext; change ∀ i j, raw27095step3 i j = -(raw27095step2 i j); unfold raw27095step3 raw27095step2; decide +kernel
      have hl : raw27095step3Labels = raw27095step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27095step3 raw27095step3Labels = mixedMoment B raw27095step4 raw27095step4Labels := by
      have ha : raw27095step4 = raw27095step3 := by apply Matrix.ext; unfold raw27095step4 raw27095step3; decide +kernel
      have hl : raw27095step3Labels = labelEmbedding1 ∘ raw27095step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27095step3 raw27095step3Labels raw27095step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical27096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27096 raw27096Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw27096 raw27096Labels = mixedMoment B raw27096step0 raw27096step0Labels := by
      have ha : raw27096step0 = (fun i j => raw27096 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27096step0 raw27096; decide +kernel
      have hl : raw27096step0Labels = raw27096Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27096 raw27096Labels permutation169 permutation7
    mixedMoment B raw27096step0 raw27096step0Labels = mixedMoment B raw27096step1 raw27096step1Labels := by
      have ha : raw27096step1 = -raw27096step0 := by apply Matrix.ext; change ∀ i j, raw27096step1 i j = -(raw27096step0 i j); unfold raw27096step1 raw27096step0; decide +kernel
      have hl : raw27096step1Labels = raw27096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27096step1 raw27096step1Labels = mixedMoment B raw27096step2 raw27096step2Labels := by
      have ha : raw27096step2 = raw27096step1 := by apply Matrix.ext; unfold raw27096step2 raw27096step1; decide +kernel
      have hl : raw27096step1Labels = labelEmbedding1 ∘ raw27096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27096step1 raw27096step1Labels raw27096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1502 node1502Labels := by rfl

theorem canonical27097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27097 raw27097Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw27097 raw27097Labels = mixedMoment B raw27097step0 raw27097step0Labels := by
      have ha : raw27097step0 = (fun i j => raw27097 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27097step0 raw27097; decide +kernel
      have hl : raw27097step0Labels = raw27097Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27097 raw27097Labels permutation169 permutation7
    mixedMoment B raw27097step0 raw27097step0Labels = mixedMoment B raw27097step1 raw27097step1Labels := by
      have ha : raw27097step1 = -raw27097step0 := by apply Matrix.ext; change ∀ i j, raw27097step1 i j = -(raw27097step0 i j); unfold raw27097step1 raw27097step0; decide +kernel
      have hl : raw27097step1Labels = raw27097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27097step1 raw27097step1Labels = mixedMoment B raw27097step2 raw27097step2Labels := by
      have ha : raw27097step2 = raw27097step1 := by apply Matrix.ext; unfold raw27097step2 raw27097step1; decide +kernel
      have hl : raw27097step1Labels = labelEmbedding1 ∘ raw27097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27097step1 raw27097step1Labels raw27097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1699 node1699Labels := by rfl

theorem canonical27098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27098 raw27098Labels = mixedMoment B node1698 node1698Labels := by
  calc
    mixedMoment B raw27098 raw27098Labels = mixedMoment B raw27098step0 raw27098step0Labels := by
      have ha : raw27098step0 = (fun i j => raw27098 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27098step0 raw27098; decide +kernel
      have hl : raw27098step0Labels = raw27098Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27098 raw27098Labels permutation169 permutation7
    mixedMoment B raw27098step0 raw27098step0Labels = mixedMoment B raw27098step1 raw27098step1Labels := by
      have ha : raw27098step1 = -raw27098step0 := by apply Matrix.ext; change ∀ i j, raw27098step1 i j = -(raw27098step0 i j); unfold raw27098step1 raw27098step0; decide +kernel
      have hl : raw27098step1Labels = raw27098step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27098step1 raw27098step1Labels = mixedMoment B raw27098step2 raw27098step2Labels := by
      have ha : raw27098step2 = raw27098step1 := by apply Matrix.ext; unfold raw27098step2 raw27098step1; decide +kernel
      have hl : raw27098step1Labels = labelEmbedding1 ∘ raw27098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27098step1 raw27098step1Labels raw27098step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1698 node1698Labels := by rfl

theorem canonical27099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27099 raw27099Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw27099 raw27099Labels = mixedMoment B raw27099step0 raw27099step0Labels := by
      have hz : ∀ j, raw27099 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27099step0 = (fun i j => raw27099 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27099step0 raw27099; decide +kernel
      have hl : raw27099step0Labels = raw27099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27099 raw27099Labels permutation520 hz
    mixedMoment B raw27099step0 raw27099step0Labels = mixedMoment B raw27099step1 raw27099step1Labels := by
      have ha : raw27099step1 = (fun i j => raw27099step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27099step1 raw27099step0; decide +kernel
      have hl : raw27099step1Labels = raw27099step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27099step0 raw27099step0Labels permutation37 permutation7
    mixedMoment B raw27099step1 raw27099step1Labels = mixedMoment B raw27099step2 raw27099step2Labels := by
      have ha : raw27099step2 = -raw27099step1 := by apply Matrix.ext; change ∀ i j, raw27099step2 i j = -(raw27099step1 i j); unfold raw27099step2 raw27099step1; decide +kernel
      have hl : raw27099step2Labels = raw27099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27099step2 raw27099step2Labels = mixedMoment B raw27099step3 raw27099step3Labels := by
      have ha : raw27099step3 = raw27099step2 := by apply Matrix.ext; unfold raw27099step3 raw27099step2; decide +kernel
      have hl : raw27099step2Labels = labelEmbedding1 ∘ raw27099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27099step2 raw27099step2Labels raw27099step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical27100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27100 raw27100Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw27100 raw27100Labels = mixedMoment B raw27100step0 raw27100step0Labels := by
      have hz : ∀ j, raw27100 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27100step0 = (fun i j => raw27100 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27100step0 raw27100; decide +kernel
      have hl : raw27100step0Labels = raw27100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27100 raw27100Labels permutation590 hz
    mixedMoment B raw27100step0 raw27100step0Labels = mixedMoment B raw27100step1 raw27100step1Labels := by
      have ha : raw27100step1 = (fun i j => raw27100step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27100step1 raw27100step0; decide +kernel
      have hl : raw27100step1Labels = raw27100step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27100step0 raw27100step0Labels permutation37 permutation7
    mixedMoment B raw27100step1 raw27100step1Labels = mixedMoment B raw27100step2 raw27100step2Labels := by
      have ha : raw27100step2 = -raw27100step1 := by apply Matrix.ext; change ∀ i j, raw27100step2 i j = -(raw27100step1 i j); unfold raw27100step2 raw27100step1; decide +kernel
      have hl : raw27100step2Labels = raw27100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27100step2 raw27100step2Labels = mixedMoment B raw27100step3 raw27100step3Labels := by
      have ha : raw27100step3 = raw27100step2 := by apply Matrix.ext; unfold raw27100step3 raw27100step2; decide +kernel
      have hl : raw27100step2Labels = labelEmbedding1 ∘ raw27100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27100step2 raw27100step2Labels raw27100step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

theorem canonical27101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27101 raw27101Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw27101 raw27101Labels = mixedMoment B raw27101step0 raw27101step0Labels := by
      have hz : ∀ j, raw27101 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27101step0 = (fun i j => raw27101 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27101step0 raw27101; decide +kernel
      have hl : raw27101step0Labels = raw27101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27101 raw27101Labels permutation265 hz
    mixedMoment B raw27101step0 raw27101step0Labels = mixedMoment B raw27101step1 raw27101step1Labels := by
      have ha : raw27101step1 = (fun i j => raw27101step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27101step1 raw27101step0; decide +kernel
      have hl : raw27101step1Labels = raw27101step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27101step0 raw27101step0Labels permutation49 permutation7
    mixedMoment B raw27101step1 raw27101step1Labels = mixedMoment B raw27101step2 raw27101step2Labels := by
      have ha : raw27101step2 = -raw27101step1 := by apply Matrix.ext; change ∀ i j, raw27101step2 i j = -(raw27101step1 i j); unfold raw27101step2 raw27101step1; decide +kernel
      have hl : raw27101step2Labels = raw27101step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27101step2 raw27101step2Labels = mixedMoment B raw27101step3 raw27101step3Labels := by
      have ha : raw27101step3 = raw27101step2 := by apply Matrix.ext; unfold raw27101step3 raw27101step2; decide +kernel
      have hl : raw27101step2Labels = labelEmbedding1 ∘ raw27101step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27101step2 raw27101step2Labels raw27101step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

theorem canonical27102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27102 raw27102Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw27102 raw27102Labels = mixedMoment B raw27102step0 raw27102step0Labels := by
      have ha : raw27102step0 = (fun i j => raw27102 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27102step0 raw27102; decide +kernel
      have hl : raw27102step0Labels = raw27102Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27102 raw27102Labels permutation169 permutation7
    mixedMoment B raw27102step0 raw27102step0Labels = mixedMoment B raw27102step1 raw27102step1Labels := by
      have ha : raw27102step1 = -raw27102step0 := by apply Matrix.ext; change ∀ i j, raw27102step1 i j = -(raw27102step0 i j); unfold raw27102step1 raw27102step0; decide +kernel
      have hl : raw27102step1Labels = raw27102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27102step1 raw27102step1Labels = mixedMoment B raw27102step2 raw27102step2Labels := by
      have ha : raw27102step2 = raw27102step1 := by apply Matrix.ext; unfold raw27102step2 raw27102step1; decide +kernel
      have hl : raw27102step1Labels = labelEmbedding1 ∘ raw27102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27102step1 raw27102step1Labels raw27102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

theorem canonical27103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27103 raw27103Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw27103 raw27103Labels = mixedMoment B raw27103step0 raw27103step0Labels := by
      have hz : ∀ j, raw27103 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27103step0 = (fun i j => raw27103 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27103step0 raw27103; decide +kernel
      have hl : raw27103step0Labels = raw27103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27103 raw27103Labels permutation265 hz
    mixedMoment B raw27103step0 raw27103step0Labels = mixedMoment B raw27103step1 raw27103step1Labels := by
      have ha : raw27103step1 = (fun i j => raw27103step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27103step1 raw27103step0; decide +kernel
      have hl : raw27103step1Labels = raw27103step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27103step0 raw27103step0Labels permutation49 permutation7
    mixedMoment B raw27103step1 raw27103step1Labels = mixedMoment B raw27103step2 raw27103step2Labels := by
      have ha : raw27103step2 = -raw27103step1 := by apply Matrix.ext; change ∀ i j, raw27103step2 i j = -(raw27103step1 i j); unfold raw27103step2 raw27103step1; decide +kernel
      have hl : raw27103step2Labels = raw27103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27103step2 raw27103step2Labels = mixedMoment B raw27103step3 raw27103step3Labels := by
      have ha : raw27103step3 = raw27103step2 := by apply Matrix.ext; unfold raw27103step3 raw27103step2; decide +kernel
      have hl : raw27103step2Labels = labelEmbedding1 ∘ raw27103step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27103step2 raw27103step2Labels raw27103step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical27104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27104 raw27104Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw27104 raw27104Labels = mixedMoment B raw27104step0 raw27104step0Labels := by
      have hz : ∀ j, raw27104 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27104step0 = (fun i j => raw27104 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27104step0 raw27104; decide +kernel
      have hl : raw27104step0Labels = raw27104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27104 raw27104Labels permutation520 hz
    mixedMoment B raw27104step0 raw27104step0Labels = mixedMoment B raw27104step1 raw27104step1Labels := by
      have hz : ∀ j, raw27104step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27104step1 = (fun i j => raw27104step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27104step1 raw27104step0; decide +kernel
      have hl : raw27104step1Labels = raw27104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27104step0 raw27104step0Labels permutation56 hz
    mixedMoment B raw27104step1 raw27104step1Labels = mixedMoment B raw27104step2 raw27104step2Labels := by
      have ha : raw27104step2 = (fun i j => raw27104step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27104step2 raw27104step1; decide +kernel
      have hl : raw27104step2Labels = raw27104step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27104step1 raw27104step1Labels permutation13 permutation7
    mixedMoment B raw27104step2 raw27104step2Labels = mixedMoment B raw27104step3 raw27104step3Labels := by
      have ha : raw27104step3 = -raw27104step2 := by apply Matrix.ext; change ∀ i j, raw27104step3 i j = -(raw27104step2 i j); unfold raw27104step3 raw27104step2; decide +kernel
      have hl : raw27104step3Labels = raw27104step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27104step3 raw27104step3Labels = mixedMoment B raw27104step4 raw27104step4Labels := by
      have ha : raw27104step4 = raw27104step3 := by apply Matrix.ext; unfold raw27104step4 raw27104step3; decide +kernel
      have hl : raw27104step3Labels = labelEmbedding1 ∘ raw27104step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27104step3 raw27104step3Labels raw27104step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical27105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27105 raw27105Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw27105 raw27105Labels = mixedMoment B raw27105step0 raw27105step0Labels := by
      have hz : ∀ j, raw27105 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27105step0 = (fun i j => raw27105 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27105step0 raw27105; decide +kernel
      have hl : raw27105step0Labels = raw27105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27105 raw27105Labels permutation590 hz
    mixedMoment B raw27105step0 raw27105step0Labels = mixedMoment B raw27105step1 raw27105step1Labels := by
      have hz : ∀ j, raw27105step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27105step1 = (fun i j => raw27105step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27105step1 raw27105step0; decide +kernel
      have hl : raw27105step1Labels = raw27105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27105step0 raw27105step0Labels permutation56 hz
    mixedMoment B raw27105step1 raw27105step1Labels = mixedMoment B raw27105step2 raw27105step2Labels := by
      have ha : raw27105step2 = (fun i j => raw27105step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27105step2 raw27105step1; decide +kernel
      have hl : raw27105step2Labels = raw27105step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27105step1 raw27105step1Labels permutation13 permutation7
    mixedMoment B raw27105step2 raw27105step2Labels = mixedMoment B raw27105step3 raw27105step3Labels := by
      have ha : raw27105step3 = -raw27105step2 := by apply Matrix.ext; change ∀ i j, raw27105step3 i j = -(raw27105step2 i j); unfold raw27105step3 raw27105step2; decide +kernel
      have hl : raw27105step3Labels = raw27105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27105step3 raw27105step3Labels = mixedMoment B raw27105step4 raw27105step4Labels := by
      have ha : raw27105step4 = raw27105step3 := by apply Matrix.ext; unfold raw27105step4 raw27105step3; decide +kernel
      have hl : raw27105step3Labels = labelEmbedding1 ∘ raw27105step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27105step3 raw27105step3Labels raw27105step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

theorem canonical27106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27106 raw27106Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw27106 raw27106Labels = mixedMoment B raw27106step0 raw27106step0Labels := by
      have hz : ∀ j, raw27106 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27106step0 = (fun i j => raw27106 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27106step0 raw27106; decide +kernel
      have hl : raw27106step0Labels = raw27106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27106 raw27106Labels permutation265 hz
    mixedMoment B raw27106step0 raw27106step0Labels = mixedMoment B raw27106step1 raw27106step1Labels := by
      have ha : raw27106step1 = (fun i j => raw27106step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27106step1 raw27106step0; decide +kernel
      have hl : raw27106step1Labels = raw27106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27106step0 raw27106step0Labels permutation49 permutation7
    mixedMoment B raw27106step1 raw27106step1Labels = mixedMoment B raw27106step2 raw27106step2Labels := by
      have ha : raw27106step2 = -raw27106step1 := by apply Matrix.ext; change ∀ i j, raw27106step2 i j = -(raw27106step1 i j); unfold raw27106step2 raw27106step1; decide +kernel
      have hl : raw27106step2Labels = raw27106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27106step2 raw27106step2Labels = mixedMoment B raw27106step3 raw27106step3Labels := by
      have ha : raw27106step3 = raw27106step2 := by apply Matrix.ext; unfold raw27106step3 raw27106step2; decide +kernel
      have hl : raw27106step2Labels = labelEmbedding1 ∘ raw27106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27106step2 raw27106step2Labels raw27106step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

theorem canonical27107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27107 raw27107Labels = mixedMoment B node1665 node1665Labels := by
  calc
    mixedMoment B raw27107 raw27107Labels = mixedMoment B raw27107step0 raw27107step0Labels := by
      have ha : raw27107step0 = (fun i j => raw27107 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27107step0 raw27107; decide +kernel
      have hl : raw27107step0Labels = raw27107Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27107 raw27107Labels permutation169 permutation7
    mixedMoment B raw27107step0 raw27107step0Labels = mixedMoment B raw27107step1 raw27107step1Labels := by
      have ha : raw27107step1 = -raw27107step0 := by apply Matrix.ext; change ∀ i j, raw27107step1 i j = -(raw27107step0 i j); unfold raw27107step1 raw27107step0; decide +kernel
      have hl : raw27107step1Labels = raw27107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27107step1 raw27107step1Labels = mixedMoment B raw27107step2 raw27107step2Labels := by
      have ha : raw27107step2 = raw27107step1 := by apply Matrix.ext; unfold raw27107step2 raw27107step1; decide +kernel
      have hl : raw27107step1Labels = labelEmbedding1 ∘ raw27107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27107step1 raw27107step1Labels raw27107step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1665 node1665Labels := by rfl

theorem canonical27108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27108 raw27108Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw27108 raw27108Labels = mixedMoment B raw27108step0 raw27108step0Labels := by
      have hz : ∀ j, raw27108 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27108step0 = (fun i j => raw27108 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27108step0 raw27108; decide +kernel
      have hl : raw27108step0Labels = raw27108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27108 raw27108Labels permutation265 hz
    mixedMoment B raw27108step0 raw27108step0Labels = mixedMoment B raw27108step1 raw27108step1Labels := by
      have ha : raw27108step1 = (fun i j => raw27108step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27108step1 raw27108step0; decide +kernel
      have hl : raw27108step1Labels = raw27108step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27108step0 raw27108step0Labels permutation49 permutation7
    mixedMoment B raw27108step1 raw27108step1Labels = mixedMoment B raw27108step2 raw27108step2Labels := by
      have ha : raw27108step2 = -raw27108step1 := by apply Matrix.ext; change ∀ i j, raw27108step2 i j = -(raw27108step1 i j); unfold raw27108step2 raw27108step1; decide +kernel
      have hl : raw27108step2Labels = raw27108step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27108step2 raw27108step2Labels = mixedMoment B raw27108step3 raw27108step3Labels := by
      have ha : raw27108step3 = raw27108step2 := by apply Matrix.ext; unfold raw27108step3 raw27108step2; decide +kernel
      have hl : raw27108step2Labels = labelEmbedding1 ∘ raw27108step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27108step2 raw27108step2Labels raw27108step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

theorem canonical27109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27109 raw27109Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw27109 raw27109Labels = mixedMoment B raw27109step0 raw27109step0Labels := by
      have hz : ∀ j, raw27109 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27109step0 = (fun i j => raw27109 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27109step0 raw27109; decide +kernel
      have hl : raw27109step0Labels = raw27109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27109 raw27109Labels permutation520 hz
    mixedMoment B raw27109step0 raw27109step0Labels = mixedMoment B raw27109step1 raw27109step1Labels := by
      have hz : ∀ j, raw27109step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27109step1 = (fun i j => raw27109step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27109step1 raw27109step0; decide +kernel
      have hl : raw27109step1Labels = raw27109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27109step0 raw27109step0Labels permutation56 hz
    mixedMoment B raw27109step1 raw27109step1Labels = mixedMoment B raw27109step2 raw27109step2Labels := by
      have ha : raw27109step2 = (fun i j => raw27109step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27109step2 raw27109step1; decide +kernel
      have hl : raw27109step2Labels = raw27109step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27109step1 raw27109step1Labels permutation13 permutation7
    mixedMoment B raw27109step2 raw27109step2Labels = mixedMoment B raw27109step3 raw27109step3Labels := by
      have ha : raw27109step3 = -raw27109step2 := by apply Matrix.ext; change ∀ i j, raw27109step3 i j = -(raw27109step2 i j); unfold raw27109step3 raw27109step2; decide +kernel
      have hl : raw27109step3Labels = raw27109step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27109step3 raw27109step3Labels = mixedMoment B raw27109step4 raw27109step4Labels := by
      have ha : raw27109step4 = raw27109step3 := by apply Matrix.ext; unfold raw27109step4 raw27109step3; decide +kernel
      have hl : raw27109step3Labels = labelEmbedding1 ∘ raw27109step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27109step3 raw27109step3Labels raw27109step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical27110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27110 raw27110Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw27110 raw27110Labels = mixedMoment B raw27110step0 raw27110step0Labels := by
      have hz : ∀ j, raw27110 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27110step0 = (fun i j => raw27110 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27110step0 raw27110; decide +kernel
      have hl : raw27110step0Labels = raw27110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27110 raw27110Labels permutation590 hz
    mixedMoment B raw27110step0 raw27110step0Labels = mixedMoment B raw27110step1 raw27110step1Labels := by
      have hz : ∀ j, raw27110step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27110step1 = (fun i j => raw27110step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27110step1 raw27110step0; decide +kernel
      have hl : raw27110step1Labels = raw27110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27110step0 raw27110step0Labels permutation56 hz
    mixedMoment B raw27110step1 raw27110step1Labels = mixedMoment B raw27110step2 raw27110step2Labels := by
      have ha : raw27110step2 = (fun i j => raw27110step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27110step2 raw27110step1; decide +kernel
      have hl : raw27110step2Labels = raw27110step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27110step1 raw27110step1Labels permutation13 permutation7
    mixedMoment B raw27110step2 raw27110step2Labels = mixedMoment B raw27110step3 raw27110step3Labels := by
      have ha : raw27110step3 = -raw27110step2 := by apply Matrix.ext; change ∀ i j, raw27110step3 i j = -(raw27110step2 i j); unfold raw27110step3 raw27110step2; decide +kernel
      have hl : raw27110step3Labels = raw27110step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27110step3 raw27110step3Labels = mixedMoment B raw27110step4 raw27110step4Labels := by
      have ha : raw27110step4 = raw27110step3 := by apply Matrix.ext; unfold raw27110step4 raw27110step3; decide +kernel
      have hl : raw27110step3Labels = labelEmbedding1 ∘ raw27110step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27110step3 raw27110step3Labels raw27110step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical27111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27111 raw27111Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw27111 raw27111Labels = mixedMoment B raw27111step0 raw27111step0Labels := by
      have hz : ∀ j, raw27111 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27111step0 = (fun i j => raw27111 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27111step0 raw27111; decide +kernel
      have hl : raw27111step0Labels = raw27111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27111 raw27111Labels permutation265 hz
    mixedMoment B raw27111step0 raw27111step0Labels = mixedMoment B raw27111step1 raw27111step1Labels := by
      have ha : raw27111step1 = (fun i j => raw27111step0 (permutation55 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27111step1 raw27111step0; decide +kernel
      have hl : raw27111step1Labels = raw27111step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27111step0 raw27111step0Labels permutation55 permutation7
    mixedMoment B raw27111step1 raw27111step1Labels = mixedMoment B raw27111step2 raw27111step2Labels := by
      have ha : raw27111step2 = -raw27111step1 := by apply Matrix.ext; change ∀ i j, raw27111step2 i j = -(raw27111step1 i j); unfold raw27111step2 raw27111step1; decide +kernel
      have hl : raw27111step2Labels = raw27111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27111step2 raw27111step2Labels = mixedMoment B raw27111step3 raw27111step3Labels := by
      have ha : raw27111step3 = raw27111step2 := by apply Matrix.ext; unfold raw27111step3 raw27111step2; decide +kernel
      have hl : raw27111step2Labels = labelEmbedding1 ∘ raw27111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27111step2 raw27111step2Labels raw27111step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical27112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27112 raw27112Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw27112 raw27112Labels = mixedMoment B raw27112step0 raw27112step0Labels := by
      have ha : raw27112step0 = (fun i j => raw27112 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27112step0 raw27112; decide +kernel
      have hl : raw27112step0Labels = raw27112Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27112 raw27112Labels permutation175 permutation7
    mixedMoment B raw27112step0 raw27112step0Labels = mixedMoment B raw27112step1 raw27112step1Labels := by
      have ha : raw27112step1 = -raw27112step0 := by apply Matrix.ext; change ∀ i j, raw27112step1 i j = -(raw27112step0 i j); unfold raw27112step1 raw27112step0; decide +kernel
      have hl : raw27112step1Labels = raw27112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27112step1 raw27112step1Labels = mixedMoment B raw27112step2 raw27112step2Labels := by
      have ha : raw27112step2 = raw27112step1 := by apply Matrix.ext; unfold raw27112step2 raw27112step1; decide +kernel
      have hl : raw27112step1Labels = labelEmbedding1 ∘ raw27112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27112step1 raw27112step1Labels raw27112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

theorem canonical27113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27113 raw27113Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw27113 raw27113Labels = mixedMoment B raw27113step0 raw27113step0Labels := by
      have hz : ∀ j, raw27113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27113step0 = (fun i j => raw27113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27113step0 raw27113; decide +kernel
      have hl : raw27113step0Labels = raw27113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27113 raw27113Labels permutation265 hz
    mixedMoment B raw27113step0 raw27113step0Labels = mixedMoment B raw27113step1 raw27113step1Labels := by
      have ha : raw27113step1 = (fun i j => raw27113step0 (permutation55 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27113step1 raw27113step0; decide +kernel
      have hl : raw27113step1Labels = raw27113step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27113step0 raw27113step0Labels permutation55 permutation7
    mixedMoment B raw27113step1 raw27113step1Labels = mixedMoment B raw27113step2 raw27113step2Labels := by
      have ha : raw27113step2 = -raw27113step1 := by apply Matrix.ext; change ∀ i j, raw27113step2 i j = -(raw27113step1 i j); unfold raw27113step2 raw27113step1; decide +kernel
      have hl : raw27113step2Labels = raw27113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27113step2 raw27113step2Labels = mixedMoment B raw27113step3 raw27113step3Labels := by
      have ha : raw27113step3 = raw27113step2 := by apply Matrix.ext; unfold raw27113step3 raw27113step2; decide +kernel
      have hl : raw27113step2Labels = labelEmbedding1 ∘ raw27113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27113step2 raw27113step2Labels raw27113step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical27114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27114 raw27114Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw27114 raw27114Labels = mixedMoment B raw27114step0 raw27114step0Labels := by
      have hz : ∀ j, raw27114 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27114step0 = (fun i j => raw27114 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27114step0 raw27114; decide +kernel
      have hl : raw27114step0Labels = raw27114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27114 raw27114Labels permutation265 hz
    mixedMoment B raw27114step0 raw27114step0Labels = mixedMoment B raw27114step1 raw27114step1Labels := by
      have ha : raw27114step1 = (fun i j => raw27114step0 (permutation55 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27114step1 raw27114step0; decide +kernel
      have hl : raw27114step1Labels = raw27114step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27114step0 raw27114step0Labels permutation55 permutation7
    mixedMoment B raw27114step1 raw27114step1Labels = mixedMoment B raw27114step2 raw27114step2Labels := by
      have ha : raw27114step2 = -raw27114step1 := by apply Matrix.ext; change ∀ i j, raw27114step2 i j = -(raw27114step1 i j); unfold raw27114step2 raw27114step1; decide +kernel
      have hl : raw27114step2Labels = raw27114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27114step2 raw27114step2Labels = mixedMoment B raw27114step3 raw27114step3Labels := by
      have ha : raw27114step3 = raw27114step2 := by apply Matrix.ext; unfold raw27114step3 raw27114step2; decide +kernel
      have hl : raw27114step2Labels = labelEmbedding1 ∘ raw27114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27114step2 raw27114step2Labels raw27114step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical27115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27115 raw27115Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw27115 raw27115Labels = mixedMoment B raw27115step0 raw27115step0Labels := by
      have hz : ∀ j, raw27115 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27115step0 = (fun i j => raw27115 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27115step0 raw27115; decide +kernel
      have hl : raw27115step0Labels = raw27115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27115 raw27115Labels permutation590 hz
    mixedMoment B raw27115step0 raw27115step0Labels = mixedMoment B raw27115step1 raw27115step1Labels := by
      have hz : ∀ j, raw27115step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27115step1 = (fun i j => raw27115step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27115step1 raw27115step0; decide +kernel
      have hl : raw27115step1Labels = raw27115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27115step0 raw27115step0Labels permutation56 hz
    mixedMoment B raw27115step1 raw27115step1Labels = mixedMoment B raw27115step2 raw27115step2Labels := by
      have ha : raw27115step2 = (fun i j => raw27115step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27115step2 raw27115step1; decide +kernel
      have hl : raw27115step2Labels = raw27115step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27115step1 raw27115step1Labels permutation13 permutation7
    mixedMoment B raw27115step2 raw27115step2Labels = mixedMoment B raw27115step3 raw27115step3Labels := by
      have ha : raw27115step3 = -raw27115step2 := by apply Matrix.ext; change ∀ i j, raw27115step3 i j = -(raw27115step2 i j); unfold raw27115step3 raw27115step2; decide +kernel
      have hl : raw27115step3Labels = raw27115step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27115step3 raw27115step3Labels = mixedMoment B raw27115step4 raw27115step4Labels := by
      have ha : raw27115step4 = raw27115step3 := by apply Matrix.ext; unfold raw27115step4 raw27115step3; decide +kernel
      have hl : raw27115step3Labels = labelEmbedding1 ∘ raw27115step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27115step3 raw27115step3Labels raw27115step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical27116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27116 raw27116Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw27116 raw27116Labels = mixedMoment B raw27116step0 raw27116step0Labels := by
      have hz : ∀ j, raw27116 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27116step0 = (fun i j => raw27116 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27116step0 raw27116; decide +kernel
      have hl : raw27116step0Labels = raw27116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27116 raw27116Labels permutation265 hz
    mixedMoment B raw27116step0 raw27116step0Labels = mixedMoment B raw27116step1 raw27116step1Labels := by
      have ha : raw27116step1 = (fun i j => raw27116step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27116step1 raw27116step0; decide +kernel
      have hl : raw27116step1Labels = raw27116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27116step0 raw27116step0Labels permutation49 permutation7
    mixedMoment B raw27116step1 raw27116step1Labels = mixedMoment B raw27116step2 raw27116step2Labels := by
      have ha : raw27116step2 = -raw27116step1 := by apply Matrix.ext; change ∀ i j, raw27116step2 i j = -(raw27116step1 i j); unfold raw27116step2 raw27116step1; decide +kernel
      have hl : raw27116step2Labels = raw27116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27116step2 raw27116step2Labels = mixedMoment B raw27116step3 raw27116step3Labels := by
      have ha : raw27116step3 = raw27116step2 := by apply Matrix.ext; unfold raw27116step3 raw27116step2; decide +kernel
      have hl : raw27116step2Labels = labelEmbedding1 ∘ raw27116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27116step2 raw27116step2Labels raw27116step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical27117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27117 raw27117Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw27117 raw27117Labels = mixedMoment B raw27117step0 raw27117step0Labels := by
      have ha : raw27117step0 = (fun i j => raw27117 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27117step0 raw27117; decide +kernel
      have hl : raw27117step0Labels = raw27117Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27117 raw27117Labels permutation169 permutation7
    mixedMoment B raw27117step0 raw27117step0Labels = mixedMoment B raw27117step1 raw27117step1Labels := by
      have ha : raw27117step1 = -raw27117step0 := by apply Matrix.ext; change ∀ i j, raw27117step1 i j = -(raw27117step0 i j); unfold raw27117step1 raw27117step0; decide +kernel
      have hl : raw27117step1Labels = raw27117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27117step1 raw27117step1Labels = mixedMoment B raw27117step2 raw27117step2Labels := by
      have ha : raw27117step2 = raw27117step1 := by apply Matrix.ext; unfold raw27117step2 raw27117step1; decide +kernel
      have hl : raw27117step1Labels = labelEmbedding1 ∘ raw27117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27117step1 raw27117step1Labels raw27117step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

theorem canonical27118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27118 raw27118Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw27118 raw27118Labels = mixedMoment B raw27118step0 raw27118step0Labels := by
      have hz : ∀ j, raw27118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27118step0 = (fun i j => raw27118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27118step0 raw27118; decide +kernel
      have hl : raw27118step0Labels = raw27118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27118 raw27118Labels permutation265 hz
    mixedMoment B raw27118step0 raw27118step0Labels = mixedMoment B raw27118step1 raw27118step1Labels := by
      have ha : raw27118step1 = (fun i j => raw27118step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27118step1 raw27118step0; decide +kernel
      have hl : raw27118step1Labels = raw27118step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27118step0 raw27118step0Labels permutation49 permutation7
    mixedMoment B raw27118step1 raw27118step1Labels = mixedMoment B raw27118step2 raw27118step2Labels := by
      have ha : raw27118step2 = -raw27118step1 := by apply Matrix.ext; change ∀ i j, raw27118step2 i j = -(raw27118step1 i j); unfold raw27118step2 raw27118step1; decide +kernel
      have hl : raw27118step2Labels = raw27118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27118step2 raw27118step2Labels = mixedMoment B raw27118step3 raw27118step3Labels := by
      have ha : raw27118step3 = raw27118step2 := by apply Matrix.ext; unfold raw27118step3 raw27118step2; decide +kernel
      have hl : raw27118step2Labels = labelEmbedding1 ∘ raw27118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27118step2 raw27118step2Labels raw27118step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical27119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27119 raw27119Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw27119 raw27119Labels = mixedMoment B raw27119step0 raw27119step0Labels := by
      have hz : ∀ j, raw27119 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27119step0 = (fun i j => raw27119 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27119step0 raw27119; decide +kernel
      have hl : raw27119step0Labels = raw27119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27119 raw27119Labels permutation265 hz
    mixedMoment B raw27119step0 raw27119step0Labels = mixedMoment B raw27119step1 raw27119step1Labels := by
      have ha : raw27119step1 = (fun i j => raw27119step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27119step1 raw27119step0; decide +kernel
      have hl : raw27119step1Labels = raw27119step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27119step0 raw27119step0Labels permutation49 permutation7
    mixedMoment B raw27119step1 raw27119step1Labels = mixedMoment B raw27119step2 raw27119step2Labels := by
      have ha : raw27119step2 = -raw27119step1 := by apply Matrix.ext; change ∀ i j, raw27119step2 i j = -(raw27119step1 i j); unfold raw27119step2 raw27119step1; decide +kernel
      have hl : raw27119step2Labels = raw27119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27119step2 raw27119step2Labels = mixedMoment B raw27119step3 raw27119step3Labels := by
      have ha : raw27119step3 = raw27119step2 := by apply Matrix.ext; unfold raw27119step3 raw27119step2; decide +kernel
      have hl : raw27119step2Labels = labelEmbedding1 ∘ raw27119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27119step2 raw27119step2Labels raw27119step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical27120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27120 raw27120Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw27120 raw27120Labels = mixedMoment B raw27120step0 raw27120step0Labels := by
      have hz : ∀ j, raw27120 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27120step0 = (fun i j => raw27120 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27120step0 raw27120; decide +kernel
      have hl : raw27120step0Labels = raw27120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27120 raw27120Labels permutation520 hz
    mixedMoment B raw27120step0 raw27120step0Labels = mixedMoment B raw27120step1 raw27120step1Labels := by
      have hz : ∀ j, raw27120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27120step1 = (fun i j => raw27120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27120step1 raw27120step0; decide +kernel
      have hl : raw27120step1Labels = raw27120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27120step0 raw27120step0Labels permutation56 hz
    mixedMoment B raw27120step1 raw27120step1Labels = mixedMoment B raw27120step2 raw27120step2Labels := by
      have ha : raw27120step2 = (fun i j => raw27120step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27120step2 raw27120step1; decide +kernel
      have hl : raw27120step2Labels = raw27120step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27120step1 raw27120step1Labels permutation13 permutation7
    mixedMoment B raw27120step2 raw27120step2Labels = mixedMoment B raw27120step3 raw27120step3Labels := by
      have ha : raw27120step3 = -raw27120step2 := by apply Matrix.ext; change ∀ i j, raw27120step3 i j = -(raw27120step2 i j); unfold raw27120step3 raw27120step2; decide +kernel
      have hl : raw27120step3Labels = raw27120step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27120step3 raw27120step3Labels = mixedMoment B raw27120step4 raw27120step4Labels := by
      have ha : raw27120step4 = raw27120step3 := by apply Matrix.ext; unfold raw27120step4 raw27120step3; decide +kernel
      have hl : raw27120step3Labels = labelEmbedding1 ∘ raw27120step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27120step3 raw27120step3Labels raw27120step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27201 raw27201Labels = mixedMoment B node995 node995Labels := by
  calc
    mixedMoment B raw27201 raw27201Labels = mixedMoment B raw27201step0 raw27201step0Labels := by
      have ha : raw27201step0 = (fun i j => raw27201 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27201step0 raw27201; decide +kernel
      have hl : raw27201step0Labels = raw27201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27201 raw27201Labels permutation169 permutation2
    _ = mixedMoment B node995 node995Labels := by rfl

theorem canonical27202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27202 raw27202Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw27202 raw27202Labels = mixedMoment B raw27202step0 raw27202step0Labels := by
      have ha : raw27202step0 = (fun i j => raw27202 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27202step0 raw27202; decide +kernel
      have hl : raw27202step0Labels = raw27202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27202 raw27202Labels permutation169 permutation2
    _ = mixedMoment B node1940 node1940Labels := by rfl

theorem canonical27203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27203 raw27203Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw27203 raw27203Labels = mixedMoment B raw27203step0 raw27203step0Labels := by
      have ha : raw27203step0 = (fun i j => raw27203 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27203step0 raw27203; decide +kernel
      have hl : raw27203step0Labels = raw27203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27203 raw27203Labels permutation155 permutation2
    _ = mixedMoment B node2219 node2219Labels := by rfl

theorem canonical27204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27204 raw27204Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw27204 raw27204Labels = mixedMoment B raw27204step0 raw27204step0Labels := by
      have ha : raw27204step0 = (fun i j => raw27204 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27204step0 raw27204; decide +kernel
      have hl : raw27204step0Labels = raw27204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27204 raw27204Labels permutation161 permutation2
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical27205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27205 raw27205Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27205 raw27205Labels = mixedMoment B raw27205step0 raw27205step0Labels := by
      have hz : ∀ j, raw27205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27205step0 = (fun i j => raw27205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27205step0 raw27205; decide +kernel
      have hl : raw27205step0Labels = raw27205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27205 raw27205Labels permutation520 hz
    mixedMoment B raw27205step0 raw27205step0Labels = mixedMoment B raw27205step1 raw27205step1Labels := by
      have ha : raw27205step1 = (fun i j => raw27205step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27205step1 raw27205step0; decide +kernel
      have hl : raw27205step1Labels = raw27205step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27205step0 raw27205step0Labels permutation37 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical27206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27206 raw27206Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27206 raw27206Labels = mixedMoment B raw27206step0 raw27206step0Labels := by
      have hz : ∀ j, raw27206 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27206step0 = (fun i j => raw27206 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27206step0 raw27206; decide +kernel
      have hl : raw27206step0Labels = raw27206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27206 raw27206Labels permutation590 hz
    mixedMoment B raw27206step0 raw27206step0Labels = mixedMoment B raw27206step1 raw27206step1Labels := by
      have ha : raw27206step1 = (fun i j => raw27206step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27206step1 raw27206step0; decide +kernel
      have hl : raw27206step1Labels = raw27206step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27206step0 raw27206step0Labels permutation37 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical27207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27207 raw27207Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27207 raw27207Labels = mixedMoment B raw27207step0 raw27207step0Labels := by
      have hz : ∀ j, raw27207 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27207step0 = (fun i j => raw27207 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27207step0 raw27207; decide +kernel
      have hl : raw27207step0Labels = raw27207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27207 raw27207Labels permutation590 hz
    mixedMoment B raw27207step0 raw27207step0Labels = mixedMoment B raw27207step1 raw27207step1Labels := by
      have hz : ∀ j, raw27207step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw27207step1 = (fun i j => raw27207step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw27207step1 raw27207step0; decide +kernel
      have hl : raw27207step1Labels = raw27207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27207step0 raw27207step0Labels permutation128 hz
    mixedMoment B raw27207step1 raw27207step1Labels = mixedMoment B raw27207step2 raw27207step2Labels := by
      have ha : raw27207step2 = (fun i j => raw27207step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27207step2 raw27207step1; decide +kernel
      have hl : raw27207step2Labels = raw27207step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27207step1 raw27207step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical27208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27208 raw27208Labels = mixedMoment B node996 node996Labels := by
  calc
    mixedMoment B raw27208 raw27208Labels = mixedMoment B raw27208step0 raw27208step0Labels := by
      have ha : raw27208step0 = (fun i j => raw27208 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27208step0 raw27208; decide +kernel
      have hl : raw27208step0Labels = raw27208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27208 raw27208Labels permutation168 permutation2
    _ = mixedMoment B node996 node996Labels := by rfl

theorem canonical27209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27209 raw27209Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw27209 raw27209Labels = mixedMoment B raw27209step0 raw27209step0Labels := by
      have ha : raw27209step0 = (fun i j => raw27209 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27209step0 raw27209; decide +kernel
      have hl : raw27209step0Labels = raw27209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27209 raw27209Labels permutation168 permutation2
    _ = mixedMoment B node1941 node1941Labels := by rfl

theorem canonical27210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27210 raw27210Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw27210 raw27210Labels = mixedMoment B raw27210step0 raw27210step0Labels := by
      have ha : raw27210step0 = (fun i j => raw27210 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27210step0 raw27210; decide +kernel
      have hl : raw27210step0Labels = raw27210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27210 raw27210Labels permutation155 permutation2
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical27211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27211 raw27211Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw27211 raw27211Labels = mixedMoment B raw27211step0 raw27211step0Labels := by
      have ha : raw27211step0 = (fun i j => raw27211 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27211step0 raw27211; decide +kernel
      have hl : raw27211step0Labels = raw27211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27211 raw27211Labels permutation161 permutation2
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical27212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27212 raw27212Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw27212 raw27212Labels = mixedMoment B raw27212step0 raw27212step0Labels := by
      have hz : ∀ j, raw27212 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27212step0 = (fun i j => raw27212 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27212step0 raw27212; decide +kernel
      have hl : raw27212step0Labels = raw27212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27212 raw27212Labels permutation520 hz
    mixedMoment B raw27212step0 raw27212step0Labels = mixedMoment B raw27212step1 raw27212step1Labels := by
      have ha : raw27212step1 = (fun i j => raw27212step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27212step1 raw27212step0; decide +kernel
      have hl : raw27212step1Labels = raw27212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27212step0 raw27212step0Labels permutation36 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical27213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27213 raw27213Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw27213 raw27213Labels = mixedMoment B raw27213step0 raw27213step0Labels := by
      have hz : ∀ j, raw27213 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27213step0 = (fun i j => raw27213 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27213step0 raw27213; decide +kernel
      have hl : raw27213step0Labels = raw27213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27213 raw27213Labels permutation590 hz
    mixedMoment B raw27213step0 raw27213step0Labels = mixedMoment B raw27213step1 raw27213step1Labels := by
      have ha : raw27213step1 = (fun i j => raw27213step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27213step1 raw27213step0; decide +kernel
      have hl : raw27213step1Labels = raw27213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27213step0 raw27213step0Labels permutation36 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical27214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27214 raw27214Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw27214 raw27214Labels = mixedMoment B raw27214step0 raw27214step0Labels := by
      have hz : ∀ j, raw27214 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27214step0 = (fun i j => raw27214 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27214step0 raw27214; decide +kernel
      have hl : raw27214step0Labels = raw27214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27214 raw27214Labels permutation590 hz
    mixedMoment B raw27214step0 raw27214step0Labels = mixedMoment B raw27214step1 raw27214step1Labels := by
      have hz : ∀ j, raw27214step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw27214step1 = (fun i j => raw27214step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw27214step1 raw27214step0; decide +kernel
      have hl : raw27214step1Labels = raw27214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27214step0 raw27214step0Labels permutation128 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical27215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27215 raw27215Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw27215 raw27215Labels = mixedMoment B raw27215step0 raw27215step0Labels := by
      have hz : ∀ i, raw27215 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw27215step0 = (fun i j => raw27215 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw27215step0 raw27215; decide +kernel
      have hl : raw27215step0Labels = (fun j => raw27215Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27215 raw27215Labels permutation4 hz
    mixedMoment B raw27215step0 raw27215step0Labels = mixedMoment B raw27215step1 raw27215step1Labels := by
      have ha : raw27215step1 = raw27215step0 := by apply Matrix.ext; unfold raw27215step1 raw27215step0; decide +kernel
      have hl : raw27215step0Labels = labelEmbedding2 ∘ raw27215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27215step0 raw27215step0Labels raw27215step1Labels labelEmbedding2 hl
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical27216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27216 raw27216Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27216 raw27216Labels = mixedMoment B raw27216step0 raw27216step0Labels := by
      have ha : raw27216step0 = (fun i j => raw27216 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27216step0 raw27216; decide +kernel
      have hl : raw27216step0Labels = raw27216Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27216 raw27216Labels permutation152 permutation7
    mixedMoment B raw27216step0 raw27216step0Labels = mixedMoment B raw27216step1 raw27216step1Labels := by
      have ha : raw27216step1 = -raw27216step0 := by apply Matrix.ext; change ∀ i j, raw27216step1 i j = -(raw27216step0 i j); unfold raw27216step1 raw27216step0; decide +kernel
      have hl : raw27216step1Labels = raw27216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27216step1 raw27216step1Labels = mixedMoment B raw27216step2 raw27216step2Labels := by
      have ha : raw27216step2 = raw27216step1 := by apply Matrix.ext; unfold raw27216step2 raw27216step1; decide +kernel
      have hl : raw27216step1Labels = labelEmbedding10 ∘ raw27216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27216step1 raw27216step1Labels raw27216step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

theorem canonical27217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27217 raw27217Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27217 raw27217Labels = mixedMoment B raw27217step0 raw27217step0Labels := by
      have ha : raw27217step0 = (fun i j => raw27217 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27217step0 raw27217; decide +kernel
      have hl : raw27217step0Labels = raw27217Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27217 raw27217Labels permutation158 permutation7
    mixedMoment B raw27217step0 raw27217step0Labels = mixedMoment B raw27217step1 raw27217step1Labels := by
      have ha : raw27217step1 = -raw27217step0 := by apply Matrix.ext; change ∀ i j, raw27217step1 i j = -(raw27217step0 i j); unfold raw27217step1 raw27217step0; decide +kernel
      have hl : raw27217step1Labels = raw27217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27217step1 raw27217step1Labels = mixedMoment B raw27217step2 raw27217step2Labels := by
      have ha : raw27217step2 = raw27217step1 := by apply Matrix.ext; unfold raw27217step2 raw27217step1; decide +kernel
      have hl : raw27217step1Labels = labelEmbedding10 ∘ raw27217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27217step1 raw27217step1Labels raw27217step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

theorem canonical27218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27218 raw27218Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27218 raw27218Labels = mixedMoment B raw27218step0 raw27218step0Labels := by
      have ha : raw27218step0 = (fun i j => raw27218 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27218step0 raw27218; decide +kernel
      have hl : raw27218step0Labels = raw27218Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27218 raw27218Labels permutation164 permutation7
    mixedMoment B raw27218step0 raw27218step0Labels = mixedMoment B raw27218step1 raw27218step1Labels := by
      have ha : raw27218step1 = -raw27218step0 := by apply Matrix.ext; change ∀ i j, raw27218step1 i j = -(raw27218step0 i j); unfold raw27218step1 raw27218step0; decide +kernel
      have hl : raw27218step1Labels = raw27218step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27218step1 raw27218step1Labels = mixedMoment B raw27218step2 raw27218step2Labels := by
      have ha : raw27218step2 = raw27218step1 := by apply Matrix.ext; unfold raw27218step2 raw27218step1; decide +kernel
      have hl : raw27218step1Labels = labelEmbedding10 ∘ raw27218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27218step1 raw27218step1Labels raw27218step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

theorem canonical27219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27219 raw27219Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27219 raw27219Labels = mixedMoment B raw27219step0 raw27219step0Labels := by
      have ha : raw27219step0 = (fun i j => raw27219 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27219step0 raw27219; decide +kernel
      have hl : raw27219step0Labels = raw27219Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27219 raw27219Labels permutation170 permutation7
    mixedMoment B raw27219step0 raw27219step0Labels = mixedMoment B raw27219step1 raw27219step1Labels := by
      have ha : raw27219step1 = -raw27219step0 := by apply Matrix.ext; change ∀ i j, raw27219step1 i j = -(raw27219step0 i j); unfold raw27219step1 raw27219step0; decide +kernel
      have hl : raw27219step1Labels = raw27219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27219step1 raw27219step1Labels = mixedMoment B raw27219step2 raw27219step2Labels := by
      have ha : raw27219step2 = raw27219step1 := by apply Matrix.ext; unfold raw27219step2 raw27219step1; decide +kernel
      have hl : raw27219step1Labels = labelEmbedding10 ∘ raw27219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27219step1 raw27219step1Labels raw27219step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

theorem canonical27220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27220 raw27220Labels = mixedMoment B node4164 node4164Labels := by
  calc
    _ = mixedMoment B node4164 node4164Labels := by rfl

theorem canonical27221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27221 raw27221Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27221 raw27221Labels = mixedMoment B raw27221step0 raw27221step0Labels := by
      have ha : raw27221step0 = (fun i j => raw27221 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27221step0 raw27221; decide +kernel
      have hl : raw27221step0Labels = raw27221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27221 raw27221Labels permutation176 permutation2
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical27222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27222 raw27222Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27222 raw27222Labels = mixedMoment B raw27222step0 raw27222step0Labels := by
      have ha : raw27222step0 = (fun i j => raw27222 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27222step0 raw27222; decide +kernel
      have hl : raw27222step0Labels = raw27222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27222 raw27222Labels permutation200 permutation2
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical27223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27223 raw27223Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27223 raw27223Labels = mixedMoment B raw27223step0 raw27223step0Labels := by
      have ha : raw27223step0 = (fun i j => raw27223 (permutation224 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27223step0 raw27223; decide +kernel
      have hl : raw27223step0Labels = raw27223Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27223 raw27223Labels permutation224 permutation2
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical27224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27224 raw27224Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27224 raw27224Labels = mixedMoment B raw27224step0 raw27224step0Labels := by
      have ha : raw27224step0 = (fun i j => raw27224 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27224step0 raw27224; decide +kernel
      have hl : raw27224step0Labels = raw27224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27224 raw27224Labels permutation246 permutation2
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical27225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27225 raw27225Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw27225 raw27225Labels = mixedMoment B raw27225step0 raw27225step0Labels := by
      have ha : raw27225step0 = (fun i j => raw27225 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27225step0 raw27225; decide +kernel
      have hl : raw27225step0Labels = raw27225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27225 raw27225Labels permutation161 permutation2
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical27226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27226 raw27226Labels = mixedMoment B node4306 node4306Labels := by
  calc
    mixedMoment B raw27226 raw27226Labels = mixedMoment B raw27226step0 raw27226step0Labels := by
      have ha : raw27226step0 = (fun i j => raw27226 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27226step0 raw27226; decide +kernel
      have hl : raw27226step0Labels = raw27226Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27226 raw27226Labels permutation161 permutation2
    _ = mixedMoment B node4306 node4306Labels := by rfl

theorem canonical27227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27227 raw27227Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27227 raw27227Labels = mixedMoment B raw27227step0 raw27227step0Labels := by
      have ha : raw27227step0 = (fun i j => raw27227 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27227step0 raw27227; decide +kernel
      have hl : raw27227step0Labels = raw27227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27227 raw27227Labels permutation161 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27228 raw27228Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27228 raw27228Labels = mixedMoment B raw27228step0 raw27228step0Labels := by
      have ha : raw27228step0 = (fun i j => raw27228 (permutation167 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27228step0 raw27228; decide +kernel
      have hl : raw27228step0Labels = raw27228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27228 raw27228Labels permutation167 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27229 raw27229Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27229 raw27229Labels = mixedMoment B raw27229step0 raw27229step0Labels := by
      have ha : raw27229step0 = (fun i j => raw27229 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27229step0 raw27229; decide +kernel
      have hl : raw27229step0Labels = raw27229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27229 raw27229Labels permutation173 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27230 raw27230Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw27230 raw27230Labels = mixedMoment B raw27230step0 raw27230step0Labels := by
      have ha : raw27230step0 = (fun i j => raw27230 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27230step0 raw27230; decide +kernel
      have hl : raw27230step0Labels = raw27230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27230 raw27230Labels permutation155 permutation2
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical27231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27231 raw27231Labels = mixedMoment B node4306 node4306Labels := by
  calc
    mixedMoment B raw27231 raw27231Labels = mixedMoment B raw27231step0 raw27231step0Labels := by
      have ha : raw27231step0 = (fun i j => raw27231 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27231step0 raw27231; decide +kernel
      have hl : raw27231step0Labels = raw27231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27231 raw27231Labels permutation155 permutation2
    _ = mixedMoment B node4306 node4306Labels := by rfl

theorem canonical27232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27232 raw27232Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27232 raw27232Labels = mixedMoment B raw27232step0 raw27232step0Labels := by
      have ha : raw27232step0 = (fun i j => raw27232 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27232step0 raw27232; decide +kernel
      have hl : raw27232step0Labels = raw27232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27232 raw27232Labels permutation155 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27233 raw27233Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27233 raw27233Labels = mixedMoment B raw27233step0 raw27233step0Labels := by
      have ha : raw27233step0 = (fun i j => raw27233 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27233step0 raw27233; decide +kernel
      have hl : raw27233step0Labels = raw27233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27233 raw27233Labels permutation165 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27234 raw27234Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27234 raw27234Labels = mixedMoment B raw27234step0 raw27234step0Labels := by
      have ha : raw27234step0 = (fun i j => raw27234 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27234step0 raw27234; decide +kernel
      have hl : raw27234step0Labels = raw27234Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27234 raw27234Labels permutation171 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27235 raw27235Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw27235 raw27235Labels = mixedMoment B raw27235step0 raw27235step0Labels := by
      have ha : raw27235step0 = (fun i j => raw27235 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27235step0 raw27235; decide +kernel
      have hl : raw27235step0Labels = raw27235Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27235 raw27235Labels permutation153 permutation2
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical27236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27236 raw27236Labels = mixedMoment B node4306 node4306Labels := by
  calc
    mixedMoment B raw27236 raw27236Labels = mixedMoment B raw27236step0 raw27236step0Labels := by
      have ha : raw27236step0 = (fun i j => raw27236 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27236step0 raw27236; decide +kernel
      have hl : raw27236step0Labels = raw27236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27236 raw27236Labels permutation153 permutation2
    _ = mixedMoment B node4306 node4306Labels := by rfl

theorem canonical27237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27237 raw27237Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27237 raw27237Labels = mixedMoment B raw27237step0 raw27237step0Labels := by
      have ha : raw27237step0 = (fun i j => raw27237 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27237step0 raw27237; decide +kernel
      have hl : raw27237step0Labels = raw27237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27237 raw27237Labels permutation153 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27238 raw27238Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27238 raw27238Labels = mixedMoment B raw27238step0 raw27238step0Labels := by
      have ha : raw27238step0 = (fun i j => raw27238 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27238step0 raw27238; decide +kernel
      have hl : raw27238step0Labels = raw27238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27238 raw27238Labels permutation159 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27239 raw27239Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27239 raw27239Labels = mixedMoment B raw27239step0 raw27239step0Labels := by
      have ha : raw27239step0 = (fun i j => raw27239 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27239step0 raw27239; decide +kernel
      have hl : raw27239step0Labels = raw27239Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27239 raw27239Labels permutation170 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27240 raw27240Labels = mixedMoment B node4143 node4143Labels := by
  calc
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical27241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27241 raw27241Labels = mixedMoment B node4306 node4306Labels := by
  calc
    _ = mixedMoment B node4306 node4306Labels := by rfl

theorem canonical27242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27242 raw27242Labels = mixedMoment B node4399 node4399Labels := by
  calc
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27243 raw27243Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27243 raw27243Labels = mixedMoment B raw27243step0 raw27243step0Labels := by
      have ha : raw27243step0 = (fun i j => raw27243 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27243step0 raw27243; decide +kernel
      have hl : raw27243step0Labels = raw27243Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27243 raw27243Labels permutation158 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

theorem canonical27244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27244 raw27244Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw27244 raw27244Labels = mixedMoment B raw27244step0 raw27244step0Labels := by
      have ha : raw27244step0 = (fun i j => raw27244 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27244step0 raw27244; decide +kernel
      have hl : raw27244step0Labels = raw27244Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27244 raw27244Labels permutation164 permutation2
    _ = mixedMoment B node4399 node4399Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5497 raw5497Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw5497 raw5497Labels = mixedMoment B raw5497step0 raw5497step0Labels := by
      have ha : raw5497step0 = (fun i j => raw5497 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5497step0 raw5497; decide +kernel
      have hl : raw5497step0Labels = raw5497Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5497 raw5497Labels permutation241 permutation7
    mixedMoment B raw5497step0 raw5497step0Labels = mixedMoment B raw5497step1 raw5497step1Labels := by
      have ha : raw5497step1 = -raw5497step0 := by apply Matrix.ext; change ∀ i j, raw5497step1 i j = -(raw5497step0 i j); unfold raw5497step1 raw5497step0; decide +kernel
      have hl : raw5497step1Labels = raw5497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5497step1 raw5497step1Labels = mixedMoment B raw5497step2 raw5497step2Labels := by
      have ha : raw5497step2 = raw5497step1 := by apply Matrix.ext; unfold raw5497step2 raw5497step1; decide +kernel
      have hl : raw5497step1Labels = labelEmbedding1 ∘ raw5497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5497step1 raw5497step1Labels raw5497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical5501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5501 raw5501Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5501 raw5501Labels = mixedMoment B raw5501step0 raw5501step0Labels := by
      have ha : raw5501step0 = (fun i j => raw5501 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5501step0 raw5501; decide +kernel
      have hl : raw5501step0Labels = raw5501Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5501 raw5501Labels permutation241 permutation7
    mixedMoment B raw5501step0 raw5501step0Labels = mixedMoment B raw5501step1 raw5501step1Labels := by
      have ha : raw5501step1 = -raw5501step0 := by apply Matrix.ext; change ∀ i j, raw5501step1 i j = -(raw5501step0 i j); unfold raw5501step1 raw5501step0; decide +kernel
      have hl : raw5501step1Labels = raw5501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5501step1 raw5501step1Labels = mixedMoment B raw5501step2 raw5501step2Labels := by
      have ha : raw5501step2 = raw5501step1 := by apply Matrix.ext; unfold raw5501step2 raw5501step1; decide +kernel
      have hl : raw5501step1Labels = labelEmbedding1 ∘ raw5501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5501step1 raw5501step1Labels raw5501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical5502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5502 raw5502Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw5502 raw5502Labels = mixedMoment B raw5502step0 raw5502step0Labels := by
      have ha : raw5502step0 = (fun i j => raw5502 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5502step0 raw5502; decide +kernel
      have hl : raw5502step0Labels = raw5502Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5502 raw5502Labels permutation240 permutation7
    mixedMoment B raw5502step0 raw5502step0Labels = mixedMoment B raw5502step1 raw5502step1Labels := by
      have ha : raw5502step1 = -raw5502step0 := by apply Matrix.ext; change ∀ i j, raw5502step1 i j = -(raw5502step0 i j); unfold raw5502step1 raw5502step0; decide +kernel
      have hl : raw5502step1Labels = raw5502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5502step1 raw5502step1Labels = mixedMoment B raw5502step2 raw5502step2Labels := by
      have ha : raw5502step2 = raw5502step1 := by apply Matrix.ext; unfold raw5502step2 raw5502step1; decide +kernel
      have hl : raw5502step1Labels = labelEmbedding1 ∘ raw5502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5502step1 raw5502step1Labels raw5502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5506 raw5506Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5506 raw5506Labels = mixedMoment B raw5506step0 raw5506step0Labels := by
      have ha : raw5506step0 = (fun i j => raw5506 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5506step0 raw5506; decide +kernel
      have hl : raw5506step0Labels = raw5506Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5506 raw5506Labels permutation240 permutation7
    mixedMoment B raw5506step0 raw5506step0Labels = mixedMoment B raw5506step1 raw5506step1Labels := by
      have ha : raw5506step1 = -raw5506step0 := by apply Matrix.ext; change ∀ i j, raw5506step1 i j = -(raw5506step0 i j); unfold raw5506step1 raw5506step0; decide +kernel
      have hl : raw5506step1Labels = raw5506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5506step1 raw5506step1Labels = mixedMoment B raw5506step2 raw5506step2Labels := by
      have ha : raw5506step2 = raw5506step1 := by apply Matrix.ext; unfold raw5506step2 raw5506step1; decide +kernel
      have hl : raw5506step1Labels = labelEmbedding1 ∘ raw5506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5506step1 raw5506step1Labels raw5506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical5523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5523 raw5523Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw5523 raw5523Labels = mixedMoment B raw5523step0 raw5523step0Labels := by
      have hz : ∀ j, raw5523 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5523step0 = (fun i j => raw5523 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5523step0 raw5523; decide +kernel
      have hl : raw5523step0Labels = raw5523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5523 raw5523Labels permutation590 hz
    mixedMoment B raw5523step0 raw5523step0Labels = mixedMoment B raw5523step1 raw5523step1Labels := by
      have hz : ∀ j, raw5523step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw5523step1 = (fun i j => raw5523step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw5523step1 raw5523step0; decide +kernel
      have hl : raw5523step1Labels = raw5523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5523step0 raw5523step0Labels permutation128 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

theorem canonical768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw768 raw768Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw768 raw768Labels = mixedMoment B raw768step0 raw768step0Labels := by
      have ha : raw768step0 = (fun i j => raw768 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw768step0 raw768; decide +kernel
      have hl : raw768step0Labels = raw768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw768 raw768Labels permutation152 permutation4
    mixedMoment B raw768step0 raw768step0Labels = mixedMoment B raw768step1 raw768step1Labels := by
      have ha : raw768step1 = raw768step0 := by apply Matrix.ext; unfold raw768step1 raw768step0; decide +kernel
      have hl : raw768step0Labels = labelEmbedding7 ∘ raw768step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw768step0 raw768step0Labels raw768step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw769 raw769Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw769 raw769Labels = mixedMoment B raw769step0 raw769step0Labels := by
      have ha : raw769step0 = (fun i j => raw769 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw769step0 raw769; decide +kernel
      have hl : raw769step0Labels = raw769Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw769 raw769Labels permutation152 permutation4
    _ = mixedMoment B node571 node571Labels := by rfl

theorem canonical770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw770 raw770Labels = mixedMoment B node1491 node1491Labels := by
  calc
    mixedMoment B raw770 raw770Labels = mixedMoment B raw770step0 raw770step0Labels := by
      have ha : raw770step0 = (fun i j => raw770 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw770step0 raw770; decide +kernel
      have hl : raw770step0Labels = raw770Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw770 raw770Labels permutation152 permutation6
    mixedMoment B raw770step0 raw770step0Labels = mixedMoment B raw770step1 raw770step1Labels := by
      have ha : raw770step1 = -raw770step0 := by apply Matrix.ext; change ∀ i j, raw770step1 i j = -(raw770step0 i j); unfold raw770step1 raw770step0; decide +kernel
      have hl : raw770step1Labels = raw770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw770step1 raw770step1Labels = mixedMoment B raw770step2 raw770step2Labels := by
      have ha : raw770step2 = raw770step1 := by apply Matrix.ext; unfold raw770step2 raw770step1; decide +kernel
      have hl : raw770step1Labels = labelEmbedding1 ∘ raw770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw770step1 raw770step1Labels raw770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1491 node1491Labels := by rfl

theorem canonical786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw786 raw786Labels = mixedMoment B node4164 node4164Labels := by
  calc
    mixedMoment B raw786 raw786Labels = mixedMoment B raw786step0 raw786step0Labels := by
      have ha : raw786step0 = (fun i j => raw786 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw786step0 raw786; decide +kernel
      have hl : raw786step0Labels = raw786Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw786 raw786Labels permutation152 permutation4
    mixedMoment B raw786step0 raw786step0Labels = mixedMoment B raw786step1 raw786step1Labels := by
      have ha : raw786step1 = raw786step0 := by apply Matrix.ext; unfold raw786step1 raw786step0; decide +kernel
      have hl : raw786step0Labels = labelEmbedding7 ∘ raw786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw786step0 raw786step0Labels raw786step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4164 node4164Labels := by rfl

theorem canonical787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw787 raw787Labels = mixedMoment B node592 node592Labels := by
  calc
    mixedMoment B raw787 raw787Labels = mixedMoment B raw787step0 raw787step0Labels := by
      have ha : raw787step0 = (fun i j => raw787 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw787step0 raw787; decide +kernel
      have hl : raw787step0Labels = raw787Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw787 raw787Labels permutation152 permutation4
    _ = mixedMoment B node592 node592Labels := by rfl

theorem canonical788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw788 raw788Labels = mixedMoment B node1497 node1497Labels := by
  calc
    mixedMoment B raw788 raw788Labels = mixedMoment B raw788step0 raw788step0Labels := by
      have ha : raw788step0 = (fun i j => raw788 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw788step0 raw788; decide +kernel
      have hl : raw788step0Labels = raw788Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw788 raw788Labels permutation152 permutation6
    mixedMoment B raw788step0 raw788step0Labels = mixedMoment B raw788step1 raw788step1Labels := by
      have ha : raw788step1 = -raw788step0 := by apply Matrix.ext; change ∀ i j, raw788step1 i j = -(raw788step0 i j); unfold raw788step1 raw788step0; decide +kernel
      have hl : raw788step1Labels = raw788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw788step1 raw788step1Labels = mixedMoment B raw788step2 raw788step2Labels := by
      have ha : raw788step2 = raw788step1 := by apply Matrix.ext; unfold raw788step2 raw788step1; decide +kernel
      have hl : raw788step1Labels = labelEmbedding1 ∘ raw788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw788step1 raw788step1Labels raw788step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1497 node1497Labels := by rfl

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

theorem canonical1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1245 raw1245Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw1245 raw1245Labels = mixedMoment B raw1245step0 raw1245step0Labels := by
      have ha : raw1245step0 = (fun i j => raw1245 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1245step0 raw1245; decide +kernel
      have hl : raw1245step0Labels = raw1245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1245 raw1245Labels permutation152 permutation4
    mixedMoment B raw1245step0 raw1245step0Labels = mixedMoment B raw1245step1 raw1245step1Labels := by
      have ha : raw1245step1 = raw1245step0 := by apply Matrix.ext; unfold raw1245step1 raw1245step0; decide +kernel
      have hl : raw1245step0Labels = labelEmbedding7 ∘ raw1245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1245step0 raw1245step0Labels raw1245step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

theorem canonical1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1246 raw1246Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw1246 raw1246Labels = mixedMoment B raw1246step0 raw1246step0Labels := by
      have ha : raw1246step0 = (fun i j => raw1246 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1246step0 raw1246; decide +kernel
      have hl : raw1246step0Labels = raw1246Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1246 raw1246Labels permutation152 permutation4
    _ = mixedMoment B node1034 node1034Labels := by rfl

theorem canonical1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1247 raw1247Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw1247 raw1247Labels = mixedMoment B raw1247step0 raw1247step0Labels := by
      have ha : raw1247step0 = (fun i j => raw1247 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1247step0 raw1247; decide +kernel
      have hl : raw1247step0Labels = raw1247Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1247 raw1247Labels permutation176 permutation6
    mixedMoment B raw1247step0 raw1247step0Labels = mixedMoment B raw1247step1 raw1247step1Labels := by
      have ha : raw1247step1 = -raw1247step0 := by apply Matrix.ext; change ∀ i j, raw1247step1 i j = -(raw1247step0 i j); unfold raw1247step1 raw1247step0; decide +kernel
      have hl : raw1247step1Labels = raw1247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1247step1 raw1247step1Labels = mixedMoment B raw1247step2 raw1247step2Labels := by
      have ha : raw1247step2 = raw1247step1 := by apply Matrix.ext; unfold raw1247step2 raw1247step1; decide +kernel
      have hl : raw1247step1Labels = labelEmbedding1 ∘ raw1247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1247step1 raw1247step1Labels raw1247step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1644 node1644Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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

theorem singleton4143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4143 node4143Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node571 node571Labels + mixedMoment B node1491 node1491Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw768 singletonSmall4143
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4143) = raw768Labels := by decide +kernel
  rw [hl, canonical768 B hB] at h
  have hc0 : mixedMoment B raw768 (Fin.cases (0 : Fin 2) singletonSmall4143) =
      mixedMoment B node571 node571Labels := by
    have ha : raw768 = raw769 := by apply Matrix.ext; unfold raw768 raw769; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4143 = raw769Labels := by decide +kernel
    rw [ha, hj, canonical769 B hB]
  have hc1 : mixedMoment B raw768 (Fin.cases (1 : Fin 2) singletonSmall4143) =
      mixedMoment B node1491 node1491Labels := by
    have ha : raw768 = raw770 := by apply Matrix.ext; unfold raw768 raw770; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4143 = raw770Labels := by decide +kernel
    rw [ha, hj, canonical770 B hB]
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

theorem singleton4164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4164 node4164Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node592 node592Labels + mixedMoment B node1497 node1497Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw786 singletonSmall4164
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4164) = raw786Labels := by decide +kernel
  rw [hl, canonical786 B hB] at h
  have hc0 : mixedMoment B raw786 (Fin.cases (0 : Fin 2) singletonSmall4164) =
      mixedMoment B node592 node592Labels := by
    have ha : raw786 = raw787 := by apply Matrix.ext; unfold raw786 raw787; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4164 = raw787Labels := by decide +kernel
    rw [ha, hj, canonical787 B hB]
  have hc1 : mixedMoment B raw786 (Fin.cases (1 : Fin 2) singletonSmall4164) =
      mixedMoment B node1497 node1497Labels := by
    have ha : raw786 = raw788 := by apply Matrix.ext; unfold raw786 raw788; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4164 = raw788Labels := by decide +kernel
    rw [ha, hj, canonical788 B hB]
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

theorem singleton4451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4451 node4451Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1034 node1034Labels + mixedMoment B node1644 node1644Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1245 singletonSmall4451
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4451) = raw1245Labels := by decide +kernel
  rw [hl, canonical1245 B hB] at h
  have hc0 : mixedMoment B raw1245 (Fin.cases (0 : Fin 2) singletonSmall4451) =
      mixedMoment B node1034 node1034Labels := by
    have ha : raw1245 = raw1246 := by apply Matrix.ext; unfold raw1245 raw1246; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4451 = raw1246Labels := by decide +kernel
    rw [ha, hj, canonical1246 B hB]
  have hc1 : mixedMoment B raw1245 (Fin.cases (1 : Fin 2) singletonSmall4451) =
      mixedMoment B node1644 node1644Labels := by
    have ha : raw1245 = raw1247 := by apply Matrix.ext; unfold raw1245 raw1247; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4451 = raw1247Labels := by decide +kernel
    rw [ha, hj, canonical1247 B hB]
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

theorem sound919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node919 node919Labels = Sparse.eval nodeValue919 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 919) = mixedMoment B node919 node919Labels := rfl
  simpa [nodeValue919, Sparse.eval] using hc.symm

theorem sound922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node922 node922Labels = Sparse.eval nodeValue922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 922) = mixedMoment B node922 node922Labels := rfl
  simpa [nodeValue922, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node996 node996Labels = 0 := by
  exact mixedMoment_alpha B hF node996 node996Labels 1 permutation216
    (by decide +kernel)

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

theorem sound977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node977 node977Labels = Sparse.eval nodeValue977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 977) = mixedMoment B node977 node977Labels := rfl
  simpa [nodeValue977, Sparse.eval] using hc.symm

theorem sound980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node980 node980Labels = Sparse.eval nodeValue980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 980) = mixedMoment B node980 node980Labels := rfl
  simpa [nodeValue980, Sparse.eval] using hc.symm

theorem sound995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node995 node995Labels = Sparse.eval nodeValue995 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 995) = mixedMoment B node995 node995Labels := rfl
  simpa [nodeValue995, Sparse.eval] using hc.symm

theorem sound996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node996 node996Labels = Sparse.eval nodeValue996 (mixedVector B) := by
  simpa only [nodeValue996, Sparse.eval_nil] using zero996 B _hB _hF

theorem sound998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node998 node998Labels = Sparse.eval nodeValue998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 998) = mixedMoment B node998 node998Labels := rfl
  simpa [nodeValue998, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = 0 := by
  exact mixedMoment_order_one B hB node1081 node1081Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1034 node1034Labels = Sparse.eval nodeValue1034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1034) = mixedMoment B node1034 node1034Labels := rfl
  simpa [nodeValue1034, Sparse.eval] using hc.symm

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

theorem sound1070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1070 node1070Labels = Sparse.eval nodeValue1070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1070) = mixedMoment B node1070 node1070Labels := rfl
  simpa [nodeValue1070, Sparse.eval] using hc.symm

theorem sound1071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1071 node1071Labels = Sparse.eval nodeValue1071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1071) = mixedMoment B node1071 node1071Labels := rfl
  simpa [nodeValue1071, Sparse.eval] using hc.symm

theorem sound1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1073 node1073Labels = Sparse.eval nodeValue1073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1073) = mixedMoment B node1073 node1073Labels := rfl
  simpa [nodeValue1073, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

theorem sound1081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1081 node1081Labels = Sparse.eval nodeValue1081 (mixedVector B) := by
  simpa only [nodeValue1081, Sparse.eval_nil] using zero1081 B _hB _hF

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

theorem sound1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1491 node1491Labels = Sparse.eval nodeValue1491 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1491) = mixedMoment B node1491 node1491Labels := rfl
  simpa [nodeValue1491, Sparse.eval] using hc.symm

theorem sound1497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1497 node1497Labels = Sparse.eval nodeValue1497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1497) = mixedMoment B node1497 node1497Labels := rfl
  simpa [nodeValue1497, Sparse.eval] using hc.symm

theorem sound1502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1502 node1502Labels = Sparse.eval nodeValue1502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1502) = mixedMoment B node1502 node1502Labels := rfl
  simpa [nodeValue1502, Sparse.eval] using hc.symm

theorem sound1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1504 node1504Labels = Sparse.eval nodeValue1504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1504) = mixedMoment B node1504 node1504Labels := rfl
  simpa [nodeValue1504, Sparse.eval] using hc.symm

theorem sound1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1506 node1506Labels = Sparse.eval nodeValue1506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1506) = mixedMoment B node1506 node1506Labels := rfl
  simpa [nodeValue1506, Sparse.eval] using hc.symm

theorem sound1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1507 node1507Labels = Sparse.eval nodeValue1507 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1507) = mixedMoment B node1507 node1507Labels := rfl
  simpa [nodeValue1507, Sparse.eval] using hc.symm

theorem sound1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1508 node1508Labels = Sparse.eval nodeValue1508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1508) = mixedMoment B node1508 node1508Labels := rfl
  simpa [nodeValue1508, Sparse.eval] using hc.symm

theorem sound1510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1510 node1510Labels = Sparse.eval nodeValue1510 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1510) = mixedMoment B node1510 node1510Labels := rfl
  simpa [nodeValue1510, Sparse.eval] using hc.symm

theorem sound1512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1512 node1512Labels = Sparse.eval nodeValue1512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1512) = mixedMoment B node1512 node1512Labels := rfl
  simpa [nodeValue1512, Sparse.eval] using hc.symm

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

theorem sound1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1644 node1644Labels = Sparse.eval nodeValue1644 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1644) = mixedMoment B node1644 node1644Labels := rfl
  simpa [nodeValue1644, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1665 node1665Labels = 0 := by
  exact mixedMoment_alpha B hF node1665 node1665Labels 1 permutation484
    (by decide +kernel)

theorem zero1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = 0 := by
  exact mixedMoment_alpha B hF node1698 node1698Labels 1 permutation434
    (by decide +kernel)

theorem zero1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = 0 := by
  exact mixedMoment_alpha B hF node1705 node1705Labels 1 permutation437
    (by decide +kernel)

theorem zero1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1726 node1726Labels = 0 := by
  exact mixedMoment_order_one B hB node1726 node1726Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = 0 := by
  exact mixedMoment_order_one B hB node1727 node1727Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1664 node1664Labels = Sparse.eval nodeValue1664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1664) = mixedMoment B node1664 node1664Labels := rfl
  simpa [nodeValue1664, Sparse.eval] using hc.symm

theorem sound1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1665 node1665Labels = Sparse.eval nodeValue1665 (mixedVector B) := by
  simpa only [nodeValue1665, Sparse.eval_nil] using zero1665 B _hB _hF

theorem sound1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1668 node1668Labels = Sparse.eval nodeValue1668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1668) = mixedMoment B node1668 node1668Labels := rfl
  simpa [nodeValue1668, Sparse.eval] using hc.symm

theorem sound1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1698 node1698Labels = Sparse.eval nodeValue1698 (mixedVector B) := by
  simpa only [nodeValue1698, Sparse.eval_nil] using zero1698 B _hB _hF

theorem sound1699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1699 node1699Labels = Sparse.eval nodeValue1699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1699) = mixedMoment B node1699 node1699Labels := rfl
  simpa [nodeValue1699, Sparse.eval] using hc.symm

theorem sound1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1703 node1703Labels = Sparse.eval nodeValue1703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1703) = mixedMoment B node1703 node1703Labels := rfl
  simpa [nodeValue1703, Sparse.eval] using hc.symm

theorem sound1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = Sparse.eval nodeValue1705 (mixedVector B) := by
  simpa only [nodeValue1705, Sparse.eval_nil] using zero1705 B _hB _hF

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

theorem sound1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1709 node1709Labels = Sparse.eval nodeValue1709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1709) = mixedMoment B node1709 node1709Labels := rfl
  simpa [nodeValue1709, Sparse.eval] using hc.symm

theorem sound1711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1711 node1711Labels = Sparse.eval nodeValue1711 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1711) = mixedMoment B node1711 node1711Labels := rfl
  simpa [nodeValue1711, Sparse.eval] using hc.symm

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

theorem sound1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1714 node1714Labels = Sparse.eval nodeValue1714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1714) = mixedMoment B node1714 node1714Labels := rfl
  simpa [nodeValue1714, Sparse.eval] using hc.symm

theorem sound1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1715 node1715Labels = Sparse.eval nodeValue1715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1715) = mixedMoment B node1715 node1715Labels := rfl
  simpa [nodeValue1715, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

theorem sound1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1726 node1726Labels = Sparse.eval nodeValue1726 (mixedVector B) := by
  simpa only [nodeValue1726, Sparse.eval_nil] using zero1726 B _hB _hF

theorem sound1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1727 node1727Labels = Sparse.eval nodeValue1727 (mixedVector B) := by
  simpa only [nodeValue1727, Sparse.eval_nil] using zero1727 B _hB _hF

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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

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

theorem sound1940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1940 node1940Labels = Sparse.eval nodeValue1940 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1940) = mixedMoment B node1940 node1940Labels := rfl
  simpa [nodeValue1940, Sparse.eval] using hc.symm

theorem sound1941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1941 node1941Labels = Sparse.eval nodeValue1941 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1941) = mixedMoment B node1941 node1941Labels := rfl
  simpa [nodeValue1941, Sparse.eval] using hc.symm

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

theorem sound2043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2043 node2043Labels = Sparse.eval nodeValue2043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2043) = mixedMoment B node2043 node2043Labels := rfl
  simpa [nodeValue2043, Sparse.eval] using hc.symm

theorem sound2044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2044 node2044Labels = Sparse.eval nodeValue2044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2044) = mixedMoment B node2044 node2044Labels := rfl
  simpa [nodeValue2044, Sparse.eval] using hc.symm

theorem sound2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2046 node2046Labels = Sparse.eval nodeValue2046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2046) = mixedMoment B node2046 node2046Labels := rfl
  simpa [nodeValue2046, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = 0 := by
  exact mixedMoment_order_one B hB node2227 node2227Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2201 node2201Labels = Sparse.eval nodeValue2201 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2201) = mixedMoment B node2201 node2201Labels := rfl
  simpa [nodeValue2201, Sparse.eval] using hc.symm

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

theorem sound2219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2219 node2219Labels = Sparse.eval nodeValue2219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2219) = mixedMoment B node2219 node2219Labels := rfl
  simpa [nodeValue2219, Sparse.eval] using hc.symm

theorem sound2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2220 node2220Labels = Sparse.eval nodeValue2220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2220) = mixedMoment B node2220 node2220Labels := rfl
  simpa [nodeValue2220, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

theorem sound2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = Sparse.eval nodeValue2227 (mixedVector B) := by
  simpa only [nodeValue2227, Sparse.eval_nil] using zero2227 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = 0 := by
  exact mixedMoment_order_one B hB node2263 node2263Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = 0 := by
  exact mixedMoment_order_one B hB node2265 node2265Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2241 node2241Labels = Sparse.eval nodeValue2241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2241) = mixedMoment B node2241 node2241Labels := rfl
  simpa [nodeValue2241, Sparse.eval] using hc.symm

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2259 node2259Labels = Sparse.eval nodeValue2259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2259) = mixedMoment B node2259 node2259Labels := rfl
  simpa [nodeValue2259, Sparse.eval] using hc.symm

theorem sound2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2260 node2260Labels = Sparse.eval nodeValue2260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2260) = mixedMoment B node2260 node2260Labels := rfl
  simpa [nodeValue2260, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = Sparse.eval nodeValue2265 (mixedVector B) := by
  simpa only [nodeValue2265, Sparse.eval_nil] using zero2265 B _hB _hF

theorem sound2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2274 node2274Labels = Sparse.eval nodeValue2274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2274) = mixedMoment B node2274 node2274Labels := rfl
  simpa [nodeValue2274, Sparse.eval] using hc.symm

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2288 node2288Labels = Sparse.eval nodeValue2288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2288) = mixedMoment B node2288 node2288Labels := rfl
  simpa [nodeValue2288, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node535 node535Labels = Sparse.eval nodeValue535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 535) = mixedMoment B node535 node535Labels := rfl
  simpa [nodeValue535, Sparse.eval] using hc.symm

theorem sound537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node537 node537Labels = Sparse.eval nodeValue537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 537) = mixedMoment B node537 node537Labels := rfl
  simpa [nodeValue537, Sparse.eval] using hc.symm

theorem sound550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node550 node550Labels = Sparse.eval nodeValue550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 550) = mixedMoment B node550 node550Labels := rfl
  simpa [nodeValue550, Sparse.eval] using hc.symm

theorem sound571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node571 node571Labels = Sparse.eval nodeValue571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 571) = mixedMoment B node571 node571Labels := rfl
  simpa [nodeValue571, Sparse.eval] using hc.symm

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

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

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

theorem sound592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node592 node592Labels = Sparse.eval nodeValue592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 592) = mixedMoment B node592 node592Labels := rfl
  simpa [nodeValue592, Sparse.eval] using hc.symm

theorem sound599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node599 node599Labels = Sparse.eval nodeValue599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 599) = mixedMoment B node599 node599Labels := rfl
  simpa [nodeValue599, Sparse.eval] using hc.symm

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

theorem sound4143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4143 node4143Labels = Sparse.eval nodeValue4143 (mixedVector B) := by
  have h := singleton4143 B _hB
  rw [sound571 B _hB _hF, sound1491 B _hB _hF] at h
  norm_num [nodeValue4143, nodeValue571, nodeValue1491, Sparse.eval] at h ⊢
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

theorem sound4164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4164 node4164Labels = Sparse.eval nodeValue4164 (mixedVector B) := by
  have h := singleton4164 B _hB
  rw [sound592 B _hB _hF, sound1497 B _hB _hF] at h
  norm_num [nodeValue4164, nodeValue592, nodeValue1497, Sparse.eval] at h ⊢
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

theorem zero4306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4306 node4306Labels = 0 := by
  exact mixedMoment_order_one B hB node4306 node4306Labels 1
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

theorem sound4306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4306 node4306Labels = Sparse.eval nodeValue4306 (mixedVector B) := by
  simpa only [nodeValue4306, Sparse.eval_nil] using zero4306 B _hB _hF

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

theorem sound4399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4399 node4399Labels = Sparse.eval nodeValue4399 (mixedVector B) := by
  have h := singleton4399 B _hB
  rw [sound980 B _hB _hF, sound1616 B _hB _hF] at h
  norm_num [nodeValue4399, nodeValue980, nodeValue1616, Sparse.eval] at h ⊢
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

theorem sound4451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4451 node4451Labels = Sparse.eval nodeValue4451 (mixedVector B) := by
  have h := singleton4451 B _hB
  rw [sound1034 B _hB _hF, sound1644 B _hB _hF] at h
  norm_num [nodeValue4451, nodeValue1034, nodeValue1644, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources58
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1872 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 1) (sourceB1872 + difference 1 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 1) (sourceB1872 + difference 1 0) sourceC1872) = raw14295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14295; decide +kernel
    rw [ha]
    exact (canonical14295 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 2) (sourceB1872 + difference 2 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 2) (sourceB1872 + difference 2 0) sourceC1872) = raw5506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw5506; decide +kernel
    rw [ha]
    exact (canonical5506 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 3) (sourceB1872 + difference 3 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 3) (sourceB1872 + difference 3 0) sourceC1872) = raw5501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw5501; decide +kernel
    rw [ha]
    exact (canonical5501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 4) (sourceB1872 + difference 4 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 4) (sourceB1872 + difference 4 0) sourceC1872) = raw14296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14296; decide +kernel
    rw [ha]
    exact (canonical14296 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 5) (sourceB1872 + difference 5 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 5) (sourceB1872 + difference 5 0) sourceC1872) = raw14297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14297; decide +kernel
    rw [ha]
    exact (canonical14297 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 0) (sourceB1872 + difference 0 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 0) (sourceB1872 + difference 0 1) sourceC1872) = raw26946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26946; decide +kernel
    rw [ha]
    exact (canonical26946 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 2) (sourceB1872 + difference 2 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 2) (sourceB1872 + difference 2 1) sourceC1872) = raw14290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14290; decide +kernel
    rw [ha]
    exact (canonical14290 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 3) (sourceB1872 + difference 3 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 3) (sourceB1872 + difference 3 1) sourceC1872) = raw26947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26947; decide +kernel
    rw [ha]
    exact (canonical26947 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 4) (sourceB1872 + difference 4 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 4) (sourceB1872 + difference 4 1) sourceC1872) = raw26948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26948; decide +kernel
    rw [ha]
    exact (canonical26948 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 5) (sourceB1872 + difference 5 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 5) (sourceB1872 + difference 5 1) sourceC1872) = raw26949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26949; decide +kernel
    rw [ha]
    exact (canonical26949 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 0) (sourceB1872 + difference 0 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 0) (sourceB1872 + difference 0 2) sourceC1872) = raw26950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26950; decide +kernel
    rw [ha]
    exact (canonical26950 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 1) (sourceB1872 + difference 1 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 1) (sourceB1872 + difference 1 2) sourceC1872) = raw26951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26951; decide +kernel
    rw [ha]
    exact (canonical26951 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 3) (sourceB1872 + difference 3 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 3) (sourceB1872 + difference 3 2) sourceC1872) = raw26952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26952; decide +kernel
    rw [ha]
    exact (canonical26952 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 4) (sourceB1872 + difference 4 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 4) (sourceB1872 + difference 4 2) sourceC1872) = raw26953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26953; decide +kernel
    rw [ha]
    exact (canonical26953 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 5) (sourceB1872 + difference 5 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 5) (sourceB1872 + difference 5 2) sourceC1872) = raw26954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26954; decide +kernel
    rw [ha]
    exact (canonical26954 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 0) (sourceB1872 + difference 0 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 0) (sourceB1872 + difference 0 3) sourceC1872) = raw26955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26955; decide +kernel
    rw [ha]
    exact (canonical26955 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 1) (sourceB1872 + difference 1 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 1) (sourceB1872 + difference 1 3) sourceC1872) = raw26956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26956; decide +kernel
    rw [ha]
    exact (canonical26956 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 2) (sourceB1872 + difference 2 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 2) (sourceB1872 + difference 2 3) sourceC1872) = raw14298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14298; decide +kernel
    rw [ha]
    exact (canonical14298 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 4) (sourceB1872 + difference 4 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 4) (sourceB1872 + difference 4 3) sourceC1872) = raw26957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26957; decide +kernel
    rw [ha]
    exact (canonical26957 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 5) (sourceB1872 + difference 5 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 5) (sourceB1872 + difference 5 3) sourceC1872) = raw26958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26958; decide +kernel
    rw [ha]
    exact (canonical26958 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 0) (sourceB1872 + difference 0 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 0) (sourceB1872 + difference 0 4) sourceC1872) = raw26959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26959; decide +kernel
    rw [ha]
    exact (canonical26959 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 1) (sourceB1872 + difference 1 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 1) (sourceB1872 + difference 1 4) sourceC1872) = raw26960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26960; decide +kernel
    rw [ha]
    exact (canonical26960 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 2) (sourceB1872 + difference 2 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 2) (sourceB1872 + difference 2 4) sourceC1872) = raw14303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14303; decide +kernel
    rw [ha]
    exact (canonical14303 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 3) (sourceB1872 + difference 3 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 3) (sourceB1872 + difference 3 4) sourceC1872) = raw26961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26961; decide +kernel
    rw [ha]
    exact (canonical26961 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 5) (sourceB1872 + difference 5 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 5) (sourceB1872 + difference 5 4) sourceC1872) = raw26962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26962; decide +kernel
    rw [ha]
    exact (canonical26962 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 0) (sourceB1872 + difference 0 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 0) (sourceB1872 + difference 0 5) sourceC1872) = raw26963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26963; decide +kernel
    rw [ha]
    exact (canonical26963 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 1) (sourceB1872 + difference 1 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 1) (sourceB1872 + difference 1 5) sourceC1872) = raw26964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26964; decide +kernel
    rw [ha]
    exact (canonical26964 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 2) (sourceB1872 + difference 2 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 2) (sourceB1872 + difference 2 5) sourceC1872) = raw5502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw5502; decide +kernel
    rw [ha]
    exact (canonical5502 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 3) (sourceB1872 + difference 3 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 3) (sourceB1872 + difference 3 5) sourceC1872) = raw5497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw5497; decide +kernel
    rw [ha]
    exact (canonical5497 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 4) (sourceB1872 + difference 4 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 4) (sourceB1872 + difference 4 5) sourceC1872) = raw26965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26965; decide +kernel
    rw [ha]
    exact (canonical26965 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1872 sourceB1872 sourceC1872
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1872, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1873 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 0) (sourceB1873 + difference 0 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 599) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 0) (sourceB1873 + difference 0 1) sourceC1873) = raw26966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26966; decide +kernel
    rw [ha]
    exact (canonical26966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 1) (sourceB1873 + difference 1 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 1) (sourceB1873 + difference 1 1) sourceC1873) = raw26967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26967; decide +kernel
    rw [ha]
    exact (canonical26967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 2) (sourceB1873 + difference 2 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 2) (sourceB1873 + difference 2 1) sourceC1873) = raw26968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26968; decide +kernel
    rw [ha]
    exact (canonical26968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 3) (sourceB1873 + difference 3 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 3) (sourceB1873 + difference 3 1) sourceC1873) = raw26969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26969; decide +kernel
    rw [ha]
    exact (canonical26969 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 4) (sourceB1873 + difference 4 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 4) (sourceB1873 + difference 4 1) sourceC1873) = raw26970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26970; decide +kernel
    rw [ha]
    exact (canonical26970 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 5) (sourceB1873 + difference 5 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 5) (sourceB1873 + difference 5 1) sourceC1873) = raw26971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26971; decide +kernel
    rw [ha]
    exact (canonical26971 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1873 + sourceB1873) sourceC1873) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1873 + sourceB1873) sourceC1873) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA1873 sourceB1873 sourceC1873 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1873 sourceB1873 sourceC1873
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1873, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1875 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 1) (sourceB1875 + difference 1 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2593) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 1) (sourceB1875 + difference 1 0) sourceC1875) = raw26992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26992; decide +kernel
    rw [ha]
    exact (canonical26992 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 2) (sourceB1875 + difference 2 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 2) (sourceB1875 + difference 2 0) sourceC1875) = raw25258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25258; decide +kernel
    rw [ha]
    exact (canonical25258 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 3) (sourceB1875 + difference 3 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 3) (sourceB1875 + difference 3 0) sourceC1875) = raw26993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26993; decide +kernel
    rw [ha]
    exact (canonical26993 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 4) (sourceB1875 + difference 4 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 4) (sourceB1875 + difference 4 0) sourceC1875) = raw26994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26994; decide +kernel
    rw [ha]
    exact (canonical26994 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 5) (sourceB1875 + difference 5 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 5) (sourceB1875 + difference 5 0) sourceC1875) = raw26995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26995; decide +kernel
    rw [ha]
    exact (canonical26995 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 0) (sourceB1875 + difference 0 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 550) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 0) (sourceB1875 + difference 0 1) sourceC1875) = raw26996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26996; decide +kernel
    rw [ha]
    exact (canonical26996 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 2) (sourceB1875 + difference 2 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 2) (sourceB1875 + difference 2 1) sourceC1875) = raw25262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25262; decide +kernel
    rw [ha]
    exact (canonical25262 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 3) (sourceB1875 + difference 3 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 3) (sourceB1875 + difference 3 1) sourceC1875) = raw26997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26997; decide +kernel
    rw [ha]
    exact (canonical26997 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 4) (sourceB1875 + difference 4 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 4) (sourceB1875 + difference 4 1) sourceC1875) = raw26998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26998; decide +kernel
    rw [ha]
    exact (canonical26998 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 5) (sourceB1875 + difference 5 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 5) (sourceB1875 + difference 5 1) sourceC1875) = raw26999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26999; decide +kernel
    rw [ha]
    exact (canonical26999 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 0) (sourceB1875 + difference 0 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 535) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 0) (sourceB1875 + difference 0 2) sourceC1875) = raw27000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27000; decide +kernel
    rw [ha]
    exact (canonical27000 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 1) (sourceB1875 + difference 1 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 1) (sourceB1875 + difference 1 2) sourceC1875) = raw27001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27001; decide +kernel
    rw [ha]
    exact (canonical27001 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 3) (sourceB1875 + difference 3 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 3) (sourceB1875 + difference 3 2) sourceC1875) = raw27002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27002; decide +kernel
    rw [ha]
    exact (canonical27002 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 4) (sourceB1875 + difference 4 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 4) (sourceB1875 + difference 4 2) sourceC1875) = raw27003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27003; decide +kernel
    rw [ha]
    exact (canonical27003 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 5) (sourceB1875 + difference 5 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 5) (sourceB1875 + difference 5 2) sourceC1875) = raw27004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27004; decide +kernel
    rw [ha]
    exact (canonical27004 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 0) (sourceB1875 + difference 0 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 535) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 0) (sourceB1875 + difference 0 3) sourceC1875) = raw27005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27005; decide +kernel
    rw [ha]
    exact (canonical27005 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 1) (sourceB1875 + difference 1 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 1) (sourceB1875 + difference 1 3) sourceC1875) = raw27006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27006; decide +kernel
    rw [ha]
    exact (canonical27006 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 2) (sourceB1875 + difference 2 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 2) (sourceB1875 + difference 2 3) sourceC1875) = raw25271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25271; decide +kernel
    rw [ha]
    exact (canonical25271 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 4) (sourceB1875 + difference 4 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 4) (sourceB1875 + difference 4 3) sourceC1875) = raw27007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27007; decide +kernel
    rw [ha]
    exact (canonical27007 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 5) (sourceB1875 + difference 5 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 5) (sourceB1875 + difference 5 3) sourceC1875) = raw27008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27008; decide +kernel
    rw [ha]
    exact (canonical27008 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 0) (sourceB1875 + difference 0 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 537) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 0) (sourceB1875 + difference 0 4) sourceC1875) = raw27009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27009; decide +kernel
    rw [ha]
    exact (canonical27009 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 1) (sourceB1875 + difference 1 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 922) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 1) (sourceB1875 + difference 1 4) sourceC1875) = raw27010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27010; decide +kernel
    rw [ha]
    exact (canonical27010 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 2) (sourceB1875 + difference 2 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 2) (sourceB1875 + difference 2 4) sourceC1875) = raw23254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw23254; decide +kernel
    rw [ha]
    exact (canonical23254 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 3) (sourceB1875 + difference 3 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 3) (sourceB1875 + difference 3 4) sourceC1875) = raw23250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw23250; decide +kernel
    rw [ha]
    exact (canonical23250 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 5) (sourceB1875 + difference 5 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 5) (sourceB1875 + difference 5 4) sourceC1875) = raw27011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27011; decide +kernel
    rw [ha]
    exact (canonical27011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 0) (sourceB1875 + difference 0 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 537) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 0) (sourceB1875 + difference 0 5) sourceC1875) = raw25263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25263; decide +kernel
    rw [ha]
    exact (canonical25263 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 1) (sourceB1875 + difference 1 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 922) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 1) (sourceB1875 + difference 1 5) sourceC1875) = raw25264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25264; decide +kernel
    rw [ha]
    exact (canonical25264 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 2) (sourceB1875 + difference 2 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 2) (sourceB1875 + difference 2 5) sourceC1875) = raw21510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw21510; decide +kernel
    rw [ha]
    exact (canonical21510 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 3) (sourceB1875 + difference 3 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 3) (sourceB1875 + difference 3 5) sourceC1875) = raw21506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw21506; decide +kernel
    rw [ha]
    exact (canonical21506 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 4) (sourceB1875 + difference 4 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 4) (sourceB1875 + difference 4 5) sourceC1875) = raw25265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25265; decide +kernel
    rw [ha]
    exact (canonical25265 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1875 sourceB1875 sourceC1875
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1875, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1877 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 0) (sourceB1877 + difference 0 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 0) (sourceB1877 + difference 0 0) sourceC1877) = raw27040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27040; decide +kernel
    rw [ha]
    exact (canonical27040 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 1) (sourceB1877 + difference 1 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2043) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 1) (sourceB1877 + difference 1 0) sourceC1877) = raw27041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27041; decide +kernel
    rw [ha]
    exact (canonical27041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 2) (sourceB1877 + difference 2 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 2) (sourceB1877 + difference 2 0) sourceC1877) = raw27042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27042; decide +kernel
    rw [ha]
    exact (canonical27042 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 3) (sourceB1877 + difference 3 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 3) (sourceB1877 + difference 3 0) sourceC1877) = raw27043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27043; decide +kernel
    rw [ha]
    exact (canonical27043 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 4) (sourceB1877 + difference 4 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 4) (sourceB1877 + difference 4 0) sourceC1877) = raw27044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27044; decide +kernel
    rw [ha]
    exact (canonical27044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 5) (sourceB1877 + difference 5 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 5) (sourceB1877 + difference 5 0) sourceC1877) = raw27045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27045; decide +kernel
    rw [ha]
    exact (canonical27045 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1877 + sourceB1877) sourceC1877) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1877 + sourceB1877) sourceC1877) = raw27046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1877 sourceB1877 sourceC1877 raw27046; decide +kernel
    rw [ha]
    exact (canonical27046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1877 sourceB1877 sourceC1877
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1877, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1878 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 0) (sourceB1878 + difference 0 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1071) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 0) (sourceB1878 + difference 0 0) sourceC1878) = raw27047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27047; decide +kernel
    rw [ha]
    exact (canonical27047 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 1) (sourceB1878 + difference 1 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2044) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 1) (sourceB1878 + difference 1 0) sourceC1878) = raw27048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27048; decide +kernel
    rw [ha]
    exact (canonical27048 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 2) (sourceB1878 + difference 2 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 2) (sourceB1878 + difference 2 0) sourceC1878) = raw27049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27049; decide +kernel
    rw [ha]
    exact (canonical27049 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 3) (sourceB1878 + difference 3 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 3) (sourceB1878 + difference 3 0) sourceC1878) = raw27050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27050; decide +kernel
    rw [ha]
    exact (canonical27050 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 4) (sourceB1878 + difference 4 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 4) (sourceB1878 + difference 4 0) sourceC1878) = raw27051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27051; decide +kernel
    rw [ha]
    exact (canonical27051 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 5) (sourceB1878 + difference 5 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 5) (sourceB1878 + difference 5 0) sourceC1878) = raw27052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27052; decide +kernel
    rw [ha]
    exact (canonical27052 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1878 + sourceB1878) sourceC1878) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1878 + sourceB1878) sourceC1878) = raw27053 := by
      apply Matrix.ext; unfold doubleCharges sourceA1878 sourceB1878 sourceC1878 raw27053; decide +kernel
    rw [ha]
    exact (canonical27053 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1878 sourceB1878 sourceC1878
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1878, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1879 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 0) (sourceB1879 + difference 0 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 0) (sourceB1879 + difference 0 0) sourceC1879) = raw27054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27054; decide +kernel
    rw [ha]
    exact (canonical27054 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 1) (sourceB1879 + difference 1 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2046) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 1) (sourceB1879 + difference 1 0) sourceC1879) = raw27055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27055; decide +kernel
    rw [ha]
    exact (canonical27055 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 2) (sourceB1879 + difference 2 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 2) (sourceB1879 + difference 2 0) sourceC1879) = raw27056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27056; decide +kernel
    rw [ha]
    exact (canonical27056 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 3) (sourceB1879 + difference 3 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 3) (sourceB1879 + difference 3 0) sourceC1879) = raw27057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27057; decide +kernel
    rw [ha]
    exact (canonical27057 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 4) (sourceB1879 + difference 4 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 4) (sourceB1879 + difference 4 0) sourceC1879) = raw27058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27058; decide +kernel
    rw [ha]
    exact (canonical27058 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 5) (sourceB1879 + difference 5 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 5) (sourceB1879 + difference 5 0) sourceC1879) = raw27059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27059; decide +kernel
    rw [ha]
    exact (canonical27059 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1879 + sourceB1879) sourceC1879) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1879 + sourceB1879) sourceC1879) = raw27060 := by
      apply Matrix.ext; unfold doubleCharges sourceA1879 sourceB1879 sourceC1879 raw27060; decide +kernel
    rw [ha]
    exact (canonical27060 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1879 sourceB1879 sourceC1879
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1879, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1881 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 1) (sourceB1881 + difference 1 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 1) (sourceB1881 + difference 1 0) sourceC1881) = raw27091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27091; decide +kernel
    rw [ha]
    exact (canonical27091 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 2) (sourceB1881 + difference 2 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 2) (sourceB1881 + difference 2 0) sourceC1881) = raw27092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27092; decide +kernel
    rw [ha]
    exact (canonical27092 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 3) (sourceB1881 + difference 3 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 3) (sourceB1881 + difference 3 0) sourceC1881) = raw27093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27093; decide +kernel
    rw [ha]
    exact (canonical27093 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 4) (sourceB1881 + difference 4 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 4) (sourceB1881 + difference 4 0) sourceC1881) = raw27094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27094; decide +kernel
    rw [ha]
    exact (canonical27094 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 5) (sourceB1881 + difference 5 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 5) (sourceB1881 + difference 5 0) sourceC1881) = raw27095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27095; decide +kernel
    rw [ha]
    exact (canonical27095 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 0) (sourceB1881 + difference 0 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 0) (sourceB1881 + difference 0 1) sourceC1881) = raw27096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27096; decide +kernel
    rw [ha]
    exact (canonical27096 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 2) (sourceB1881 + difference 2 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 2) (sourceB1881 + difference 2 1) sourceC1881) = raw27097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27097; decide +kernel
    rw [ha]
    exact (canonical27097 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 3) (sourceB1881 + difference 3 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 3) (sourceB1881 + difference 3 1) sourceC1881) = raw27098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27098; decide +kernel
    rw [ha]
    exact (canonical27098 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 4) (sourceB1881 + difference 4 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 4) (sourceB1881 + difference 4 1) sourceC1881) = raw27099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27099; decide +kernel
    rw [ha]
    exact (canonical27099 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 5) (sourceB1881 + difference 5 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 5) (sourceB1881 + difference 5 1) sourceC1881) = raw27100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27100; decide +kernel
    rw [ha]
    exact (canonical27100 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 0) (sourceB1881 + difference 0 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 0) (sourceB1881 + difference 0 2) sourceC1881) = raw27101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27101; decide +kernel
    rw [ha]
    exact (canonical27101 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 1) (sourceB1881 + difference 1 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1664) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 1) (sourceB1881 + difference 1 2) sourceC1881) = raw27102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27102; decide +kernel
    rw [ha]
    exact (canonical27102 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 3) (sourceB1881 + difference 3 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 3) (sourceB1881 + difference 3 2) sourceC1881) = raw27103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27103; decide +kernel
    rw [ha]
    exact (canonical27103 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 4) (sourceB1881 + difference 4 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 4) (sourceB1881 + difference 4 2) sourceC1881) = raw27104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27104; decide +kernel
    rw [ha]
    exact (canonical27104 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 5) (sourceB1881 + difference 5 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 5) (sourceB1881 + difference 5 2) sourceC1881) = raw27105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27105; decide +kernel
    rw [ha]
    exact (canonical27105 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 0) (sourceB1881 + difference 0 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 0) (sourceB1881 + difference 0 3) sourceC1881) = raw27106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27106; decide +kernel
    rw [ha]
    exact (canonical27106 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 1) (sourceB1881 + difference 1 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 1) (sourceB1881 + difference 1 3) sourceC1881) = raw27107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27107; decide +kernel
    rw [ha]
    exact (canonical27107 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 2) (sourceB1881 + difference 2 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 2) (sourceB1881 + difference 2 3) sourceC1881) = raw27108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27108; decide +kernel
    rw [ha]
    exact (canonical27108 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 4) (sourceB1881 + difference 4 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 4) (sourceB1881 + difference 4 3) sourceC1881) = raw27109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27109; decide +kernel
    rw [ha]
    exact (canonical27109 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 5) (sourceB1881 + difference 5 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 5) (sourceB1881 + difference 5 3) sourceC1881) = raw27110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27110; decide +kernel
    rw [ha]
    exact (canonical27110 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 0) (sourceB1881 + difference 0 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 0) (sourceB1881 + difference 0 4) sourceC1881) = raw27111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27111; decide +kernel
    rw [ha]
    exact (canonical27111 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 1) (sourceB1881 + difference 1 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 1) (sourceB1881 + difference 1 4) sourceC1881) = raw27112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27112; decide +kernel
    rw [ha]
    exact (canonical27112 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 2) (sourceB1881 + difference 2 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 2) (sourceB1881 + difference 2 4) sourceC1881) = raw27113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27113; decide +kernel
    rw [ha]
    exact (canonical27113 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 3) (sourceB1881 + difference 3 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 3) (sourceB1881 + difference 3 4) sourceC1881) = raw27114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27114; decide +kernel
    rw [ha]
    exact (canonical27114 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 5) (sourceB1881 + difference 5 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 5) (sourceB1881 + difference 5 4) sourceC1881) = raw27115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27115; decide +kernel
    rw [ha]
    exact (canonical27115 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 0) (sourceB1881 + difference 0 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 0) (sourceB1881 + difference 0 5) sourceC1881) = raw27116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27116; decide +kernel
    rw [ha]
    exact (canonical27116 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 1) (sourceB1881 + difference 1 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 1) (sourceB1881 + difference 1 5) sourceC1881) = raw27117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27117; decide +kernel
    rw [ha]
    exact (canonical27117 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 2) (sourceB1881 + difference 2 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 2) (sourceB1881 + difference 2 5) sourceC1881) = raw27118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27118; decide +kernel
    rw [ha]
    exact (canonical27118 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 3) (sourceB1881 + difference 3 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 3) (sourceB1881 + difference 3 5) sourceC1881) = raw27119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27119; decide +kernel
    rw [ha]
    exact (canonical27119 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 4) (sourceB1881 + difference 4 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 4) (sourceB1881 + difference 4 5) sourceC1881) = raw27120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27120; decide +kernel
    rw [ha]
    exact (canonical27120 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1881 sourceB1881 sourceC1881
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1881, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1885 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 0) (sourceB1885 + difference 0 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 995) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 0) (sourceB1885 + difference 0 0) sourceC1885) = raw27201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27201; decide +kernel
    rw [ha]
    exact (canonical27201 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 1) (sourceB1885 + difference 1 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1940) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 1) (sourceB1885 + difference 1 0) sourceC1885) = raw27202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27202; decide +kernel
    rw [ha]
    exact (canonical27202 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 2) (sourceB1885 + difference 2 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 2) (sourceB1885 + difference 2 0) sourceC1885) = raw27203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27203; decide +kernel
    rw [ha]
    exact (canonical27203 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 3) (sourceB1885 + difference 3 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 3) (sourceB1885 + difference 3 0) sourceC1885) = raw27204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27204; decide +kernel
    rw [ha]
    exact (canonical27204 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 4) (sourceB1885 + difference 4 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 4) (sourceB1885 + difference 4 0) sourceC1885) = raw27205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27205; decide +kernel
    rw [ha]
    exact (canonical27205 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 5) (sourceB1885 + difference 5 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 5) (sourceB1885 + difference 5 0) sourceC1885) = raw27206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27206; decide +kernel
    rw [ha]
    exact (canonical27206 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1885 + sourceB1885) sourceC1885) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1885 + sourceB1885) sourceC1885) = raw27207 := by
      apply Matrix.ext; unfold doubleCharges sourceA1885 sourceB1885 sourceC1885 raw27207; decide +kernel
    rw [ha]
    exact (canonical27207 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1885 sourceB1885 sourceC1885
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1885, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1886 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1886 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 0) (sourceB1886 + difference 0 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 996) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 0) (sourceB1886 + difference 0 0) sourceC1886) = raw27208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27208; decide +kernel
    rw [ha]
    exact (canonical27208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 1) (sourceB1886 + difference 1 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1941) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 1) (sourceB1886 + difference 1 0) sourceC1886) = raw27209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27209; decide +kernel
    rw [ha]
    exact (canonical27209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 2) (sourceB1886 + difference 2 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 2) (sourceB1886 + difference 2 0) sourceC1886) = raw27210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27210; decide +kernel
    rw [ha]
    exact (canonical27210 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 3) (sourceB1886 + difference 3 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 3) (sourceB1886 + difference 3 0) sourceC1886) = raw27211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27211; decide +kernel
    rw [ha]
    exact (canonical27211 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 4) (sourceB1886 + difference 4 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 4) (sourceB1886 + difference 4 0) sourceC1886) = raw27212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27212; decide +kernel
    rw [ha]
    exact (canonical27212 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 5) (sourceB1886 + difference 5 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 5) (sourceB1886 + difference 5 0) sourceC1886) = raw27213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27213; decide +kernel
    rw [ha]
    exact (canonical27213 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1886 + sourceB1886) sourceC1886) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1886 + sourceB1886) sourceC1886) = raw27214 := by
      apply Matrix.ext; unfold doubleCharges sourceA1886 sourceB1886 sourceC1886 raw27214; decide +kernel
    rw [ha]
    exact (canonical27214 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1886 sourceB1886 sourceC1886
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1886, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1887 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 1) (sourceB1887 + difference 1 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 1) (sourceB1887 + difference 1 0) sourceC1887) = raw27215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27215; decide +kernel
    rw [ha]
    exact (canonical27215 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 2) (sourceB1887 + difference 2 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 2) (sourceB1887 + difference 2 0) sourceC1887) = raw27216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27216; decide +kernel
    rw [ha]
    exact (canonical27216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 3) (sourceB1887 + difference 3 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 3) (sourceB1887 + difference 3 0) sourceC1887) = raw27217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27217; decide +kernel
    rw [ha]
    exact (canonical27217 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 4) (sourceB1887 + difference 4 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 4) (sourceB1887 + difference 4 0) sourceC1887) = raw27218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27218; decide +kernel
    rw [ha]
    exact (canonical27218 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 5) (sourceB1887 + difference 5 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 5) (sourceB1887 + difference 5 0) sourceC1887) = raw27219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27219; decide +kernel
    rw [ha]
    exact (canonical27219 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 0) (sourceB1887 + difference 0 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4164) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 0) (sourceB1887 + difference 0 1) sourceC1887) = raw27220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27220; decide +kernel
    rw [ha]
    exact (canonical27220 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 2) (sourceB1887 + difference 2 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 2) (sourceB1887 + difference 2 1) sourceC1887) = raw27221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27221; decide +kernel
    rw [ha]
    exact (canonical27221 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 3) (sourceB1887 + difference 3 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 3) (sourceB1887 + difference 3 1) sourceC1887) = raw27222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27222; decide +kernel
    rw [ha]
    exact (canonical27222 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 4) (sourceB1887 + difference 4 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 4) (sourceB1887 + difference 4 1) sourceC1887) = raw27223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27223; decide +kernel
    rw [ha]
    exact (canonical27223 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 5) (sourceB1887 + difference 5 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 5) (sourceB1887 + difference 5 1) sourceC1887) = raw27224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27224; decide +kernel
    rw [ha]
    exact (canonical27224 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 0) (sourceB1887 + difference 0 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 0) (sourceB1887 + difference 0 2) sourceC1887) = raw27225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27225; decide +kernel
    rw [ha]
    exact (canonical27225 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 1) (sourceB1887 + difference 1 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4306) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 1) (sourceB1887 + difference 1 2) sourceC1887) = raw27226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27226; decide +kernel
    rw [ha]
    exact (canonical27226 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 3) (sourceB1887 + difference 3 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 3) (sourceB1887 + difference 3 2) sourceC1887) = raw27227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27227; decide +kernel
    rw [ha]
    exact (canonical27227 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 4) (sourceB1887 + difference 4 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 4) (sourceB1887 + difference 4 2) sourceC1887) = raw27228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27228; decide +kernel
    rw [ha]
    exact (canonical27228 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 5) (sourceB1887 + difference 5 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 5) (sourceB1887 + difference 5 2) sourceC1887) = raw27229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27229; decide +kernel
    rw [ha]
    exact (canonical27229 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 0) (sourceB1887 + difference 0 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 0) (sourceB1887 + difference 0 3) sourceC1887) = raw27230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27230; decide +kernel
    rw [ha]
    exact (canonical27230 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 1) (sourceB1887 + difference 1 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4306) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 1) (sourceB1887 + difference 1 3) sourceC1887) = raw27231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27231; decide +kernel
    rw [ha]
    exact (canonical27231 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 2) (sourceB1887 + difference 2 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 2) (sourceB1887 + difference 2 3) sourceC1887) = raw27232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27232; decide +kernel
    rw [ha]
    exact (canonical27232 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 4) (sourceB1887 + difference 4 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 4) (sourceB1887 + difference 4 3) sourceC1887) = raw27233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27233; decide +kernel
    rw [ha]
    exact (canonical27233 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 5) (sourceB1887 + difference 5 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 5) (sourceB1887 + difference 5 3) sourceC1887) = raw27234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27234; decide +kernel
    rw [ha]
    exact (canonical27234 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 0) (sourceB1887 + difference 0 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 0) (sourceB1887 + difference 0 4) sourceC1887) = raw27235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27235; decide +kernel
    rw [ha]
    exact (canonical27235 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 1) (sourceB1887 + difference 1 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4306) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 1) (sourceB1887 + difference 1 4) sourceC1887) = raw27236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27236; decide +kernel
    rw [ha]
    exact (canonical27236 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 2) (sourceB1887 + difference 2 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 2) (sourceB1887 + difference 2 4) sourceC1887) = raw27237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27237; decide +kernel
    rw [ha]
    exact (canonical27237 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 3) (sourceB1887 + difference 3 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 3) (sourceB1887 + difference 3 4) sourceC1887) = raw27238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27238; decide +kernel
    rw [ha]
    exact (canonical27238 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 5) (sourceB1887 + difference 5 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 5) (sourceB1887 + difference 5 4) sourceC1887) = raw27239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27239; decide +kernel
    rw [ha]
    exact (canonical27239 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 0) (sourceB1887 + difference 0 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 0) (sourceB1887 + difference 0 5) sourceC1887) = raw27240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27240; decide +kernel
    rw [ha]
    exact (canonical27240 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 1) (sourceB1887 + difference 1 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4306) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 1) (sourceB1887 + difference 1 5) sourceC1887) = raw27241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27241; decide +kernel
    rw [ha]
    exact (canonical27241 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 2) (sourceB1887 + difference 2 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 2) (sourceB1887 + difference 2 5) sourceC1887) = raw27242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27242; decide +kernel
    rw [ha]
    exact (canonical27242 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 3) (sourceB1887 + difference 3 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 3) (sourceB1887 + difference 3 5) sourceC1887) = raw27243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27243; decide +kernel
    rw [ha]
    exact (canonical27243 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 4) (sourceB1887 + difference 4 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 4) (sourceB1887 + difference 4 5) sourceC1887) = raw27244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27244; decide +kernel
    rw [ha]
    exact (canonical27244 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1887 sourceB1887 sourceC1887
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1887, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1585 : Integer.Sparse.reindex keyMap MixedData.row1585 = numericRow1585 := by decide +kernel

theorem numericCheck1585 (x : Master → ℝ) : Integer.Sparse.eval numericRow1585 x =
    (1 : ℝ) * reducedSource1585 x := by
  norm_num [numericRow1585, reducedSource1585, Integer.Sparse.eval, Sparse.eval, nodeValue1504, nodeValue1506, nodeValue1510, nodeValue1703, nodeValue1705, nodeValue1706, nodeValue1711, nodeValue1713, nodeValue1724, nodeValue1726, nodeValue1737, nodeValue2241, nodeValue2243, nodeValue2263]

theorem reindexCheck1586 : Integer.Sparse.reindex keyMap MixedData.row1586 = numericRow1586 := by decide +kernel

theorem numericCheck1586 (x : Master → ℝ) : Integer.Sparse.eval numericRow1586 x =
    (1 : ℝ) * reducedSource1586 x := by
  norm_num [numericRow1586, reducedSource1586, Integer.Sparse.eval, Sparse.eval, nodeValue599, nodeValue1039, nodeValue1081, nodeValue4083]

theorem reindexCheck1588 : Integer.Sparse.reindex keyMap MixedData.row1588 = numericRow1588 := by decide +kernel

theorem numericCheck1588 (x : Master → ℝ) : Integer.Sparse.eval numericRow1588 x =
    (4320 : ℝ) * reducedSource1588 x := by
  norm_num [numericRow1588, reducedSource1588, Integer.Sparse.eval, Sparse.eval, nodeValue535, nodeValue537, nodeValue550, nodeValue919, nodeValue922, nodeValue977, nodeValue980, nodeValue998, nodeValue1040, nodeValue1041, nodeValue1079, nodeValue2593, nodeValue2721, nodeValue2766]
  ring

theorem reindexCheck1590 : Integer.Sparse.reindex keyMap MixedData.row1590 = numericRow1590 := by decide +kernel

theorem numericCheck1590 (x : Master → ℝ) : Integer.Sparse.eval numericRow1590 x =
    (1 : ℝ) * reducedSource1590 x := by
  norm_num [numericRow1590, reducedSource1590, Integer.Sparse.eval, Sparse.eval, nodeValue1070, nodeValue2043, nodeValue2220, nodeValue2224, nodeValue2259, nodeValue2287, nodeValue4081]

theorem reindexCheck1591 : Integer.Sparse.reindex keyMap MixedData.row1591 = numericRow1591 := by decide +kernel

theorem numericCheck1591 (x : Master → ℝ) : Integer.Sparse.eval numericRow1591 x =
    (1 : ℝ) * reducedSource1591 x := by
  norm_num [numericRow1591, reducedSource1591, Integer.Sparse.eval, Sparse.eval, nodeValue1071, nodeValue2044, nodeValue2225, nodeValue2274, nodeValue2288, nodeValue4082]

theorem reindexCheck1592 : Integer.Sparse.reindex keyMap MixedData.row1592 = numericRow1592 := by decide +kernel

theorem numericCheck1592 (x : Master → ℝ) : Integer.Sparse.eval numericRow1592 x =
    (1 : ℝ) * reducedSource1592 x := by
  norm_num [numericRow1592, reducedSource1592, Integer.Sparse.eval, Sparse.eval, nodeValue1073, nodeValue2046, nodeValue2227, nodeValue2260, nodeValue2275, nodeValue4080]

theorem reindexCheck1594 : Integer.Sparse.reindex keyMap MixedData.row1594 = numericRow1594 := by decide +kernel

theorem numericCheck1594 (x : Master → ℝ) : Integer.Sparse.eval numericRow1594 x =
    (1 : ℝ) * reducedSource1594 x := by
  norm_num [numericRow1594, reducedSource1594, Integer.Sparse.eval, Sparse.eval, nodeValue1502, nodeValue1507, nodeValue1508, nodeValue1512, nodeValue1664, nodeValue1665, nodeValue1668, nodeValue1698, nodeValue1699, nodeValue1707, nodeValue1708, nodeValue1709, nodeValue1714, nodeValue1715, nodeValue1727, nodeValue1728, nodeValue1739, nodeValue2191, nodeValue2244, nodeValue2245, nodeValue2265]

theorem reindexCheck1596 : Integer.Sparse.reindex keyMap MixedData.row1596 = numericRow1596 := by decide +kernel

theorem numericCheck1596 (x : Master → ℝ) : Integer.Sparse.eval numericRow1596 x =
    (1 : ℝ) * reducedSource1596 x := by
  norm_num [numericRow1596, reducedSource1596, Integer.Sparse.eval, Sparse.eval, nodeValue995, nodeValue1940, nodeValue2201, nodeValue2219, nodeValue2224, nodeValue4081]

theorem reindexCheck1597 : Integer.Sparse.reindex keyMap MixedData.row1597 = numericRow1597 := by decide +kernel

theorem numericCheck1597 (x : Master → ℝ) : Integer.Sparse.eval numericRow1597 x =
    (1 : ℝ) * reducedSource1597 x := by
  norm_num [numericRow1597, reducedSource1597, Integer.Sparse.eval, Sparse.eval, nodeValue996, nodeValue1941, nodeValue2213, nodeValue2225, nodeValue4082]

theorem reindexCheck1598 : Integer.Sparse.reindex keyMap MixedData.row1598 = numericRow1598 := by decide +kernel

theorem numericCheck1598 (x : Master → ℝ) : Integer.Sparse.eval numericRow1598 x =
    (4 : ℝ) * reducedSource1598 x := by
  norm_num [numericRow1598, reducedSource1598, Integer.Sparse.eval, Sparse.eval, nodeValue4079, nodeValue4143, nodeValue4164, nodeValue4306, nodeValue4399, nodeValue4451, nodeValue4833]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows99
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1585 (mixedVector B) = 0 := by
  have h1504 : mixedVector B (Sum.inr 1504) = Sparse.eval nodeValue1504 (mixedVector B) := by
    change mixedMoment B node1504 node1504Labels = _
    exact sound1504 B hB hF
  have h1506 : mixedVector B (Sum.inr 1506) = Sparse.eval nodeValue1506 (mixedVector B) := by
    change mixedMoment B node1506 node1506Labels = _
    exact sound1506 B hB hF
  have h1510 : mixedVector B (Sum.inr 1510) = Sparse.eval nodeValue1510 (mixedVector B) := by
    change mixedMoment B node1510 node1510Labels = _
    exact sound1510 B hB hF
  have h1703 : mixedVector B (Sum.inr 1703) = Sparse.eval nodeValue1703 (mixedVector B) := by
    change mixedMoment B node1703 node1703Labels = _
    exact sound1703 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1711 : mixedVector B (Sum.inr 1711) = Sparse.eval nodeValue1711 (mixedVector B) := by
    change mixedMoment B node1711 node1711Labels = _
    exact sound1711 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1726 : mixedVector B (Sum.inr 1726) = Sparse.eval nodeValue1726 (mixedVector B) := by
    change mixedMoment B node1726 node1726Labels = _
    exact sound1726 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  simpa only [sourceForm1872, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1504, h1506, h1510, h1703, h1705, h1706, h1711, h1713, h1724, h1726, h1737, h2241, h2243, h2263, reducedSource1585] using sourceEq1872 B hB

theorem rowSound1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1585 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1585, numericCheck1585, reducedZero1585 B hB hF, mul_zero]

theorem reducedZero1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1586 (mixedVector B) = 0 := by
  have h599 : mixedVector B (Sum.inr 599) = Sparse.eval nodeValue599 (mixedVector B) := by
    change mixedMoment B node599 node599Labels = _
    exact sound599 B hB hF
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1081 : mixedVector B (Sum.inr 1081) = Sparse.eval nodeValue1081 (mixedVector B) := by
    change mixedMoment B node1081 node1081Labels = _
    exact sound1081 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1873, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h599, h1039, h1081, h4083, reducedSource1586] using sourceEq1873 B hB

theorem rowSound1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1586 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1586, numericCheck1586, reducedZero1586 B hB hF, mul_zero]

theorem reducedZero1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1588 (mixedVector B) = 0 := by
  have h535 : mixedVector B (Sum.inr 535) = Sparse.eval nodeValue535 (mixedVector B) := by
    change mixedMoment B node535 node535Labels = _
    exact sound535 B hB hF
  have h537 : mixedVector B (Sum.inr 537) = Sparse.eval nodeValue537 (mixedVector B) := by
    change mixedMoment B node537 node537Labels = _
    exact sound537 B hB hF
  have h550 : mixedVector B (Sum.inr 550) = Sparse.eval nodeValue550 (mixedVector B) := by
    change mixedMoment B node550 node550Labels = _
    exact sound550 B hB hF
  have h919 : mixedVector B (Sum.inr 919) = Sparse.eval nodeValue919 (mixedVector B) := by
    change mixedMoment B node919 node919Labels = _
    exact sound919 B hB hF
  have h922 : mixedVector B (Sum.inr 922) = Sparse.eval nodeValue922 (mixedVector B) := by
    change mixedMoment B node922 node922Labels = _
    exact sound922 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h2593 : mixedVector B (Sum.inr 2593) = Sparse.eval nodeValue2593 (mixedVector B) := by
    change mixedMoment B node2593 node2593Labels = _
    exact sound2593_e B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766_e B hB hF
  simpa only [sourceForm1875, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h535, h537, h550, h919, h922, h977, h980, h998, h1040, h1041, h1079, h2593, h2721, h2766, reducedSource1588] using sourceEq1875 B hB

theorem rowSound1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1588 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1588, numericCheck1588, reducedZero1588 B hB hF, mul_zero]

theorem reducedZero1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1590 (mixedVector B) = 0 := by
  have h1070 : mixedVector B (Sum.inr 1070) = Sparse.eval nodeValue1070 (mixedVector B) := by
    change mixedMoment B node1070 node1070Labels = _
    exact sound1070 B hB hF
  have h2043 : mixedVector B (Sum.inr 2043) = Sparse.eval nodeValue2043 (mixedVector B) := by
    change mixedMoment B node2043 node2043Labels = _
    exact sound2043 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1877, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1070, h2043, h2220, h2224, h2259, h2287, h4081, reducedSource1590] using sourceEq1877 B hB

theorem rowSound1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1590 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1590, numericCheck1590, reducedZero1590 B hB hF, mul_zero]

theorem reducedZero1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1591 (mixedVector B) = 0 := by
  have h1071 : mixedVector B (Sum.inr 1071) = Sparse.eval nodeValue1071 (mixedVector B) := by
    change mixedMoment B node1071 node1071Labels = _
    exact sound1071 B hB hF
  have h2044 : mixedVector B (Sum.inr 2044) = Sparse.eval nodeValue2044 (mixedVector B) := by
    change mixedMoment B node2044 node2044Labels = _
    exact sound2044 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1878, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1071, h2044, h2225, h2274, h2288, h4082, reducedSource1591] using sourceEq1878 B hB

theorem rowSound1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1591 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1591, numericCheck1591, reducedZero1591 B hB hF, mul_zero]

theorem reducedZero1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1592 (mixedVector B) = 0 := by
  have h1073 : mixedVector B (Sum.inr 1073) = Sparse.eval nodeValue1073 (mixedVector B) := by
    change mixedMoment B node1073 node1073Labels = _
    exact sound1073 B hB hF
  have h2046 : mixedVector B (Sum.inr 2046) = Sparse.eval nodeValue2046 (mixedVector B) := by
    change mixedMoment B node2046 node2046Labels = _
    exact sound2046 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1879, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1073, h2046, h2227, h2260, h2275, h4080, reducedSource1592] using sourceEq1879 B hB

theorem rowSound1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1592 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1592, numericCheck1592, reducedZero1592 B hB hF, mul_zero]

theorem reducedZero1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1594 (mixedVector B) = 0 := by
  have h1502 : mixedVector B (Sum.inr 1502) = Sparse.eval nodeValue1502 (mixedVector B) := by
    change mixedMoment B node1502 node1502Labels = _
    exact sound1502 B hB hF
  have h1507 : mixedVector B (Sum.inr 1507) = Sparse.eval nodeValue1507 (mixedVector B) := by
    change mixedMoment B node1507 node1507Labels = _
    exact sound1507 B hB hF
  have h1508 : mixedVector B (Sum.inr 1508) = Sparse.eval nodeValue1508 (mixedVector B) := by
    change mixedMoment B node1508 node1508Labels = _
    exact sound1508 B hB hF
  have h1512 : mixedVector B (Sum.inr 1512) = Sparse.eval nodeValue1512 (mixedVector B) := by
    change mixedMoment B node1512 node1512Labels = _
    exact sound1512 B hB hF
  have h1664 : mixedVector B (Sum.inr 1664) = Sparse.eval nodeValue1664 (mixedVector B) := by
    change mixedMoment B node1664 node1664Labels = _
    exact sound1664 B hB hF
  have h1665 : mixedVector B (Sum.inr 1665) = Sparse.eval nodeValue1665 (mixedVector B) := by
    change mixedMoment B node1665 node1665Labels = _
    exact sound1665 B hB hF
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1698 : mixedVector B (Sum.inr 1698) = Sparse.eval nodeValue1698 (mixedVector B) := by
    change mixedMoment B node1698 node1698Labels = _
    exact sound1698 B hB hF
  have h1699 : mixedVector B (Sum.inr 1699) = Sparse.eval nodeValue1699 (mixedVector B) := by
    change mixedMoment B node1699 node1699Labels = _
    exact sound1699 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  simpa only [sourceForm1881, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1502, h1507, h1508, h1512, h1664, h1665, h1668, h1698, h1699, h1707, h1708, h1709, h1714, h1715, h1727, h1728, h1739, h2191, h2244, h2245, h2265, reducedSource1594] using sourceEq1881 B hB

theorem rowSound1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1594 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1594, numericCheck1594, reducedZero1594 B hB hF, mul_zero]

theorem reducedZero1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1596 (mixedVector B) = 0 := by
  have h995 : mixedVector B (Sum.inr 995) = Sparse.eval nodeValue995 (mixedVector B) := by
    change mixedMoment B node995 node995Labels = _
    exact sound995 B hB hF
  have h1940 : mixedVector B (Sum.inr 1940) = Sparse.eval nodeValue1940 (mixedVector B) := by
    change mixedMoment B node1940 node1940Labels = _
    exact sound1940 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2219 : mixedVector B (Sum.inr 2219) = Sparse.eval nodeValue2219 (mixedVector B) := by
    change mixedMoment B node2219 node2219Labels = _
    exact sound2219 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1885, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h995, h1940, h2201, h2219, h2224, h4081, reducedSource1596] using sourceEq1885 B hB

theorem rowSound1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1596 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1596, numericCheck1596, reducedZero1596 B hB hF, mul_zero]

theorem reducedZero1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1597 (mixedVector B) = 0 := by
  have h996 : mixedVector B (Sum.inr 996) = Sparse.eval nodeValue996 (mixedVector B) := by
    change mixedMoment B node996 node996Labels = _
    exact sound996 B hB hF
  have h1941 : mixedVector B (Sum.inr 1941) = Sparse.eval nodeValue1941 (mixedVector B) := by
    change mixedMoment B node1941 node1941Labels = _
    exact sound1941 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1886, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h996, h1941, h2213, h2225, h4082, reducedSource1597] using sourceEq1886 B hB

theorem rowSound1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1597 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1597, numericCheck1597, reducedZero1597 B hB hF, mul_zero]

theorem reducedZero1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1598 (mixedVector B) = 0 := by
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  have h4143 : mixedVector B (Sum.inr 4143) = Sparse.eval nodeValue4143 (mixedVector B) := by
    change mixedMoment B node4143 node4143Labels = _
    exact sound4143 B hB hF
  have h4164 : mixedVector B (Sum.inr 4164) = Sparse.eval nodeValue4164 (mixedVector B) := by
    change mixedMoment B node4164 node4164Labels = _
    exact sound4164 B hB hF
  have h4306 : mixedVector B (Sum.inr 4306) = Sparse.eval nodeValue4306 (mixedVector B) := by
    change mixedMoment B node4306 node4306Labels = _
    exact sound4306 B hB hF
  have h4399 : mixedVector B (Sum.inr 4399) = Sparse.eval nodeValue4399 (mixedVector B) := by
    change mixedMoment B node4399 node4399Labels = _
    exact sound4399 B hB hF
  have h4451 : mixedVector B (Sum.inr 4451) = Sparse.eval nodeValue4451 (mixedVector B) := by
    change mixedMoment B node4451 node4451Labels = _
    exact sound4451 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  simpa only [sourceForm1887, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4079, h4143, h4164, h4306, h4399, h4451, h4833, reducedSource1598] using sourceEq1887 B hB

theorem rowSound1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1598 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1598, numericCheck1598, reducedZero1598 B hB hF, mul_zero]

theorem sourceRowsAt1584 : MixedData.sourceRows (1584 : Fin 2425) =
    MixedData.row1584 := by decide +kernel

theorem sourceRowsAt1585 : MixedData.sourceRows (1585 : Fin 2425) =
    MixedData.row1585 := by decide +kernel

theorem sourceRowsAt1586 : MixedData.sourceRows (1586 : Fin 2425) =
    MixedData.row1586 := by decide +kernel

theorem sourceRowsAt1587 : MixedData.sourceRows (1587 : Fin 2425) =
    MixedData.row1587 := by decide +kernel

theorem sourceRowsAt1588 : MixedData.sourceRows (1588 : Fin 2425) =
    MixedData.row1588 := by decide +kernel

theorem sourceRowsAt1589 : MixedData.sourceRows (1589 : Fin 2425) =
    MixedData.row1589 := by decide +kernel

theorem sourceRowsAt1590 : MixedData.sourceRows (1590 : Fin 2425) =
    MixedData.row1590 := by decide +kernel

theorem sourceRowsAt1591 : MixedData.sourceRows (1591 : Fin 2425) =
    MixedData.row1591 := by decide +kernel

theorem sourceRowsAt1592 : MixedData.sourceRows (1592 : Fin 2425) =
    MixedData.row1592 := by decide +kernel

theorem sourceRowsAt1593 : MixedData.sourceRows (1593 : Fin 2425) =
    MixedData.row1593 := by decide +kernel

theorem sourceRowsAt1594 : MixedData.sourceRows (1594 : Fin 2425) =
    MixedData.row1594 := by decide +kernel

theorem sourceRowsAt1595 : MixedData.sourceRows (1595 : Fin 2425) =
    MixedData.row1595 := by decide +kernel

theorem sourceRowsAt1596 : MixedData.sourceRows (1596 : Fin 2425) =
    MixedData.row1596 := by decide +kernel

theorem sourceRowsAt1597 : MixedData.sourceRows (1597 : Fin 2425) =
    MixedData.row1597 := by decide +kernel

theorem sourceRowsAt1598 : MixedData.sourceRows (1598 : Fin 2425) =
    MixedData.row1598 := by decide +kernel

theorem sourceRowsAt1599 : MixedData.sourceRows (1599 : Fin 2425) =
    MixedData.row1599 := by decide +kernel

theorem chunkSound99_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 99) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1584 ∨ k.val = 1585 ∨ k.val = 1586 ∨ k.val = 1587 ∨ k.val = 1588 ∨ k.val = 1589 ∨ k.val = 1590 ∨ k.val = 1591 ∨ k.val = 1592 ∨ k.val = 1593 ∨ k.val = 1594 ∨ k.val = 1595 ∨ k.val = 1596 ∨ k.val = 1597 ∨ k.val = 1598 ∨ k.val = 1599 := by omega
  rcases heq with h1584 | h1585 | h1586 | h1587 | h1588 | h1589 | h1590 | h1591 | h1592 | h1593 | h1594 | h1595 | h1596 | h1597 | h1598 | h1599
  · have he : k = (1584 : Fin 2425) := Fin.ext h1584
    subst k
    rw [sourceRowsAt1584]
    exact rowSound1584_e B hB hF
  · have he : k = (1585 : Fin 2425) := Fin.ext h1585
    subst k
    rw [sourceRowsAt1585]
    exact rowSound1585 B hB hF
  · have he : k = (1586 : Fin 2425) := Fin.ext h1586
    subst k
    rw [sourceRowsAt1586]
    exact rowSound1586 B hB hF
  · have he : k = (1587 : Fin 2425) := Fin.ext h1587
    subst k
    rw [sourceRowsAt1587]
    exact rowSound1587_e B hB hF
  · have he : k = (1588 : Fin 2425) := Fin.ext h1588
    subst k
    rw [sourceRowsAt1588]
    exact rowSound1588 B hB hF
  · have he : k = (1589 : Fin 2425) := Fin.ext h1589
    subst k
    rw [sourceRowsAt1589]
    exact rowSound1589_e B hB hF
  · have he : k = (1590 : Fin 2425) := Fin.ext h1590
    subst k
    rw [sourceRowsAt1590]
    exact rowSound1590 B hB hF
  · have he : k = (1591 : Fin 2425) := Fin.ext h1591
    subst k
    rw [sourceRowsAt1591]
    exact rowSound1591 B hB hF
  · have he : k = (1592 : Fin 2425) := Fin.ext h1592
    subst k
    rw [sourceRowsAt1592]
    exact rowSound1592 B hB hF
  · have he : k = (1593 : Fin 2425) := Fin.ext h1593
    subst k
    rw [sourceRowsAt1593]
    exact rowSound1593_e B hB hF
  · have he : k = (1594 : Fin 2425) := Fin.ext h1594
    subst k
    rw [sourceRowsAt1594]
    exact rowSound1594 B hB hF
  · have he : k = (1595 : Fin 2425) := Fin.ext h1595
    subst k
    rw [sourceRowsAt1595]
    exact rowSound1595_e B hB hF
  · have he : k = (1596 : Fin 2425) := Fin.ext h1596
    subst k
    rw [sourceRowsAt1596]
    exact rowSound1596 B hB hF
  · have he : k = (1597 : Fin 2425) := Fin.ext h1597
    subst k
    rw [sourceRowsAt1597]
    exact rowSound1597 B hB hF
  · have he : k = (1598 : Fin 2425) := Fin.ext h1598
    subst k
    rw [sourceRowsAt1598]
    exact rowSound1598 B hB hF
  · have he : k = (1599 : Fin 2425) := Fin.ext h1599
    subst k
    rw [sourceRowsAt1599]
    exact rowSound1599_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e_oai
