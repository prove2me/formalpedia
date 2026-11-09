-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:21:47.767231+00:00
-- url     : https://prove2.me/submissions/4bd46f87-2d50-49aa-8b67-db5c05748b72

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound852_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound853_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound857_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound858_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound859_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound863_e

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

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14797 raw14797Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14797 raw14797Labels = mixedMoment B raw14797step0 raw14797step0Labels := by
      have hz : ∀ j, raw14797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14797step0 = (fun i j => raw14797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14797step0 raw14797; decide +kernel
      have hl : raw14797step0Labels = raw14797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797 raw14797Labels permutation434 hz
    mixedMoment B raw14797step0 raw14797step0Labels = mixedMoment B raw14797step1 raw14797step1Labels := by
      have hz : ∀ j, raw14797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14797step1 = (fun i j => raw14797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14797step1 raw14797step0; decide +kernel
      have hl : raw14797step1Labels = raw14797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797step0 raw14797step0Labels permutation80 hz
    mixedMoment B raw14797step1 raw14797step1Labels = mixedMoment B raw14797step2 raw14797step2Labels := by
      have ha : raw14797step2 = (fun i j => raw14797step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14797step2 raw14797step1; decide +kernel
      have hl : raw14797step2Labels = raw14797step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14797step1 raw14797step1Labels permutation31 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15744 raw15744Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15744 raw15744Labels = mixedMoment B raw15744step0 raw15744step0Labels := by
      have hz : ∀ j, raw15744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15744step0 = (fun i j => raw15744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15744step0 raw15744; decide +kernel
      have hl : raw15744step0Labels = raw15744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15744 raw15744Labels permutation346 hz
    mixedMoment B raw15744step0 raw15744step0Labels = mixedMoment B raw15744step1 raw15744step1Labels := by
      have ha : raw15744step1 = (fun i j => raw15744step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15744step1 raw15744step0; decide +kernel
      have hl : raw15744step1Labels = raw15744step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15744step0 raw15744step0Labels permutation44 permutation4
    mixedMoment B raw15744step1 raw15744step1Labels = mixedMoment B raw15744step2 raw15744step2Labels := by
      have ha : raw15744step2 = -raw15744step1 := by apply Matrix.ext; change ∀ i j, raw15744step2 i j = -(raw15744step1 i j); unfold raw15744step2 raw15744step1; decide +kernel
      have hl : raw15744step2Labels = raw15744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16003 raw16003Labels = mixedMoment B node3871 node3871Labels := by
  calc
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical16004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16004 raw16004Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw16004 raw16004Labels = mixedMoment B raw16004step0 raw16004step0Labels := by
      have ha : raw16004step0 = (fun i j => raw16004 (permutation321 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16004step0 raw16004; decide +kernel
      have hl : raw16004step0Labels = raw16004Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16004 raw16004Labels permutation321 permutation4
    mixedMoment B raw16004step0 raw16004step0Labels = mixedMoment B raw16004step1 raw16004step1Labels := by
      have ha : raw16004step1 = -raw16004step0 := by apply Matrix.ext; change ∀ i j, raw16004step1 i j = -(raw16004step0 i j); unfold raw16004step1 raw16004step0; decide +kernel
      have hl : raw16004step1Labels = raw16004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2951 node2951Labels := by rfl

theorem canonical16005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16005 raw16005Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16005 raw16005Labels = mixedMoment B raw16005step0 raw16005step0Labels := by
      have ha : raw16005step0 = (fun i j => raw16005 (permutation312 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16005step0 raw16005; decide +kernel
      have hl : raw16005step0Labels = raw16005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16005 raw16005Labels permutation312 permutation4
    mixedMoment B raw16005step0 raw16005step0Labels = mixedMoment B raw16005step1 raw16005step1Labels := by
      have ha : raw16005step1 = -raw16005step0 := by apply Matrix.ext; change ∀ i j, raw16005step1 i j = -(raw16005step0 i j); unfold raw16005step1 raw16005step0; decide +kernel
      have hl : raw16005step1Labels = raw16005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

theorem canonical16006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16006 raw16006Labels = mixedMoment B node3927 node3927Labels := by
  calc
    mixedMoment B raw16006 raw16006Labels = mixedMoment B raw16006step0 raw16006step0Labels := by
      have ha : raw16006step0 = (fun i j => raw16006 (permutation321 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16006step0 raw16006; decide +kernel
      have hl : raw16006step0Labels = raw16006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16006 raw16006Labels permutation321 permutation4
    mixedMoment B raw16006step0 raw16006step0Labels = mixedMoment B raw16006step1 raw16006step1Labels := by
      have ha : raw16006step1 = -raw16006step0 := by apply Matrix.ext; change ∀ i j, raw16006step1 i j = -(raw16006step0 i j); unfold raw16006step1 raw16006step0; decide +kernel
      have hl : raw16006step1Labels = raw16006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3927 node3927Labels := by rfl

theorem canonical16007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16007 raw16007Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw16007 raw16007Labels = mixedMoment B raw16007step0 raw16007step0Labels := by
      have hz : ∀ j, raw16007 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16007step0 = (fun i j => raw16007 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16007step0 raw16007; decide +kernel
      have hl : raw16007step0Labels = raw16007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16007 raw16007Labels permutation520 hz
    mixedMoment B raw16007step0 raw16007step0Labels = mixedMoment B raw16007step1 raw16007step1Labels := by
      have ha : raw16007step1 = (fun i j => raw16007step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16007step1 raw16007step0; decide +kernel
      have hl : raw16007step1Labels = raw16007step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16007step0 raw16007step0Labels permutation73 permutation4
    mixedMoment B raw16007step1 raw16007step1Labels = mixedMoment B raw16007step2 raw16007step2Labels := by
      have ha : raw16007step2 = -raw16007step1 := by apply Matrix.ext; change ∀ i j, raw16007step2 i j = -(raw16007step1 i j); unfold raw16007step2 raw16007step1; decide +kernel
      have hl : raw16007step2Labels = raw16007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical16008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16008 raw16008Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw16008 raw16008Labels = mixedMoment B raw16008step0 raw16008step0Labels := by
      have ha : raw16008step0 = (fun i j => raw16008 (permutation321 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16008step0 raw16008; decide +kernel
      have hl : raw16008step0Labels = raw16008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16008 raw16008Labels permutation321 permutation4
    mixedMoment B raw16008step0 raw16008step0Labels = mixedMoment B raw16008step1 raw16008step1Labels := by
      have ha : raw16008step1 = -raw16008step0 := by apply Matrix.ext; change ∀ i j, raw16008step1 i j = -(raw16008step0 i j); unfold raw16008step1 raw16008step0; decide +kernel
      have hl : raw16008step1Labels = raw16008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical16009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16009 raw16009Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16009 raw16009Labels = mixedMoment B raw16009step0 raw16009step0Labels := by
      have hz : ∀ j, raw16009 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16009step0 = (fun i j => raw16009 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16009step0 raw16009; decide +kernel
      have hl : raw16009step0Labels = raw16009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16009 raw16009Labels permutation520 hz
    mixedMoment B raw16009step0 raw16009step0Labels = mixedMoment B raw16009step1 raw16009step1Labels := by
      have ha : raw16009step1 = (fun i j => raw16009step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16009step1 raw16009step0; decide +kernel
      have hl : raw16009step1Labels = raw16009step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16009step0 raw16009step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical16011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16011 raw16011Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw16011 raw16011Labels = mixedMoment B raw16011step0 raw16011step0Labels := by
      have ha : raw16011step0 = (fun i j => raw16011 (permutation310 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16011step0 raw16011; decide +kernel
      have hl : raw16011step0Labels = raw16011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16011 raw16011Labels permutation310 permutation4
    mixedMoment B raw16011step0 raw16011step0Labels = mixedMoment B raw16011step1 raw16011step1Labels := by
      have ha : raw16011step1 = -raw16011step0 := by apply Matrix.ext; change ∀ i j, raw16011step1 i j = -(raw16011step0 i j); unfold raw16011step1 raw16011step0; decide +kernel
      have hl : raw16011step1Labels = raw16011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3091 node3091Labels := by rfl

theorem canonical16018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16018 raw16018Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw16018 raw16018Labels = mixedMoment B raw16018step0 raw16018step0Labels := by
      have ha : raw16018step0 = (fun i j => raw16018 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16018step0 raw16018; decide +kernel
      have hl : raw16018step0Labels = raw16018Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16018 raw16018Labels permutation176 permutation2
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical16019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16019 raw16019Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw16019 raw16019Labels = mixedMoment B raw16019step0 raw16019step0Labels := by
      have ha : raw16019step0 = (fun i j => raw16019 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16019step0 raw16019; decide +kernel
      have hl : raw16019step0Labels = raw16019Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16019 raw16019Labels permutation178 permutation2
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical16020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16020 raw16020Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw16020 raw16020Labels = mixedMoment B raw16020step0 raw16020step0Labels := by
      have ha : raw16020step0 = (fun i j => raw16020 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16020step0 raw16020; decide +kernel
      have hl : raw16020step0Labels = raw16020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16020 raw16020Labels permutation176 permutation2
    _ = mixedMoment B node3783 node3783Labels := by rfl

theorem canonical16021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16021 raw16021Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw16021 raw16021Labels = mixedMoment B raw16021step0 raw16021step0Labels := by
      have ha : raw16021step0 = (fun i j => raw16021 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16021step0 raw16021; decide +kernel
      have hl : raw16021step0Labels = raw16021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16021 raw16021Labels permutation686 permutation2
    mixedMoment B raw16021step0 raw16021step0Labels = mixedMoment B raw16021step1 raw16021step1Labels := by
      have ha : raw16021step1 = -raw16021step0 := by apply Matrix.ext; change ∀ i j, raw16021step1 i j = -(raw16021step0 i j); unfold raw16021step1 raw16021step0; decide +kernel
      have hl : raw16021step1Labels = raw16021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2984 node2984Labels := by rfl

theorem canonical16022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16022 raw16022Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw16022 raw16022Labels = mixedMoment B raw16022step0 raw16022step0Labels := by
      have ha : raw16022step0 = (fun i j => raw16022 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16022step0 raw16022; decide +kernel
      have hl : raw16022step0Labels = raw16022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16022 raw16022Labels permutation154 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

theorem canonical16023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16023 raw16023Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16023 raw16023Labels = mixedMoment B raw16023step0 raw16023step0Labels := by
      have hz : ∀ j, raw16023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16023step0 = (fun i j => raw16023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16023step0 raw16023; decide +kernel
      have hl : raw16023step0Labels = raw16023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16023 raw16023Labels permutation520 hz
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical16024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16024 raw16024Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw16024 raw16024Labels = mixedMoment B raw16024step0 raw16024step0Labels := by
      have ha : raw16024step0 = (fun i j => raw16024 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16024step0 raw16024; decide +kernel
      have hl : raw16024step0Labels = raw16024Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16024 raw16024Labels permutation154 permutation2
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical16025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16025 raw16025Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw16025 raw16025Labels = mixedMoment B raw16025step0 raw16025step0Labels := by
      have ha : raw16025step0 = (fun i j => raw16025 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16025step0 raw16025; decide +kernel
      have hl : raw16025step0Labels = raw16025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16025 raw16025Labels permutation271 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical16026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16026 raw16026Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw16026 raw16026Labels = mixedMoment B raw16026step0 raw16026step0Labels := by
      have ha : raw16026step0 = (fun i j => raw16026 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16026step0 raw16026; decide +kernel
      have hl : raw16026step0Labels = raw16026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16026 raw16026Labels permutation687 permutation2
    mixedMoment B raw16026step0 raw16026step0Labels = mixedMoment B raw16026step1 raw16026step1Labels := by
      have ha : raw16026step1 = -raw16026step0 := by apply Matrix.ext; change ∀ i j, raw16026step1 i j = -(raw16026step0 i j); unfold raw16026step1 raw16026step0; decide +kernel
      have hl : raw16026step1Labels = raw16026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical16027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16027 raw16027Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw16027 raw16027Labels = mixedMoment B raw16027step0 raw16027step0Labels := by
      have ha : raw16027step0 = (fun i j => raw16027 (permutation678 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16027step0 raw16027; decide +kernel
      have hl : raw16027step0Labels = raw16027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16027 raw16027Labels permutation678 permutation2
    mixedMoment B raw16027step0 raw16027step0Labels = mixedMoment B raw16027step1 raw16027step1Labels := by
      have ha : raw16027step1 = -raw16027step0 := by apply Matrix.ext; change ∀ i j, raw16027step1 i j = -(raw16027step0 i j); unfold raw16027step1 raw16027step0; decide +kernel
      have hl : raw16027step1Labels = raw16027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical16028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16028 raw16028Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw16028 raw16028Labels = mixedMoment B raw16028step0 raw16028step0Labels := by
      have ha : raw16028step0 = (fun i j => raw16028 (permutation309 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16028step0 raw16028; decide +kernel
      have hl : raw16028step0Labels = raw16028Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16028 raw16028Labels permutation309 permutation6
    mixedMoment B raw16028step0 raw16028step0Labels = mixedMoment B raw16028step1 raw16028step1Labels := by
      have ha : raw16028step1 = -raw16028step0 := by apply Matrix.ext; change ∀ i j, raw16028step1 i j = -(raw16028step0 i j); unfold raw16028step1 raw16028step0; decide +kernel
      have hl : raw16028step1Labels = raw16028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16028step1 raw16028step1Labels = mixedMoment B raw16028step2 raw16028step2Labels := by
      have ha : raw16028step2 = raw16028step1 := by apply Matrix.ext; unfold raw16028step2 raw16028step1; decide +kernel
      have hl : raw16028step1Labels = labelEmbedding9 ∘ raw16028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16028step1 raw16028step1Labels raw16028step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical16029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16029 raw16029Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw16029 raw16029Labels = mixedMoment B raw16029step0 raw16029step0Labels := by
      have ha : raw16029step0 = (fun i j => raw16029 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16029step0 raw16029; decide +kernel
      have hl : raw16029step0Labels = raw16029Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16029 raw16029Labels permutation308 permutation6
    mixedMoment B raw16029step0 raw16029step0Labels = mixedMoment B raw16029step1 raw16029step1Labels := by
      have ha : raw16029step1 = -raw16029step0 := by apply Matrix.ext; change ∀ i j, raw16029step1 i j = -(raw16029step0 i j); unfold raw16029step1 raw16029step0; decide +kernel
      have hl : raw16029step1Labels = raw16029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16029step1 raw16029step1Labels = mixedMoment B raw16029step2 raw16029step2Labels := by
      have ha : raw16029step2 = raw16029step1 := by apply Matrix.ext; unfold raw16029step2 raw16029step1; decide +kernel
      have hl : raw16029step1Labels = labelEmbedding9 ∘ raw16029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16029step1 raw16029step1Labels raw16029step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical16030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16030 raw16030Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw16030 raw16030Labels = mixedMoment B raw16030step0 raw16030step0Labels := by
      have ha : raw16030step0 = (fun i j => raw16030 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16030step0 raw16030; decide +kernel
      have hl : raw16030step0Labels = raw16030Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16030 raw16030Labels permutation191 permutation5
    mixedMoment B raw16030step0 raw16030step0Labels = mixedMoment B raw16030step1 raw16030step1Labels := by
      have ha : raw16030step1 = -raw16030step0 := by apply Matrix.ext; change ∀ i j, raw16030step1 i j = -(raw16030step0 i j); unfold raw16030step1 raw16030step0; decide +kernel
      have hl : raw16030step1Labels = raw16030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16030step1 raw16030step1Labels = mixedMoment B raw16030step2 raw16030step2Labels := by
      have ha : raw16030step2 = raw16030step1 := by apply Matrix.ext; unfold raw16030step2 raw16030step1; decide +kernel
      have hl : raw16030step1Labels = labelEmbedding8 ∘ raw16030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16030step1 raw16030step1Labels raw16030step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

theorem canonical16031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16031 raw16031Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw16031 raw16031Labels = mixedMoment B raw16031step0 raw16031step0Labels := by
      have ha : raw16031step0 = (fun i j => raw16031 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16031step0 raw16031; decide +kernel
      have hl : raw16031step0Labels = raw16031Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16031 raw16031Labels permutation191 permutation5
    mixedMoment B raw16031step0 raw16031step0Labels = mixedMoment B raw16031step1 raw16031step1Labels := by
      have ha : raw16031step1 = -raw16031step0 := by apply Matrix.ext; change ∀ i j, raw16031step1 i j = -(raw16031step0 i j); unfold raw16031step1 raw16031step0; decide +kernel
      have hl : raw16031step1Labels = raw16031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16031step1 raw16031step1Labels = mixedMoment B raw16031step2 raw16031step2Labels := by
      have ha : raw16031step2 = raw16031step1 := by apply Matrix.ext; unfold raw16031step2 raw16031step1; decide +kernel
      have hl : raw16031step1Labels = labelEmbedding8 ∘ raw16031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16031step1 raw16031step1Labels raw16031step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical16032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16032 raw16032Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw16032 raw16032Labels = mixedMoment B raw16032step0 raw16032step0Labels := by
      have ha : raw16032step0 = (fun i j => raw16032 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16032step0 raw16032; decide +kernel
      have hl : raw16032step0Labels = raw16032Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16032 raw16032Labels permutation185 permutation5
    mixedMoment B raw16032step0 raw16032step0Labels = mixedMoment B raw16032step1 raw16032step1Labels := by
      have ha : raw16032step1 = -raw16032step0 := by apply Matrix.ext; change ∀ i j, raw16032step1 i j = -(raw16032step0 i j); unfold raw16032step1 raw16032step0; decide +kernel
      have hl : raw16032step1Labels = raw16032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16032step1 raw16032step1Labels = mixedMoment B raw16032step2 raw16032step2Labels := by
      have ha : raw16032step2 = raw16032step1 := by apply Matrix.ext; unfold raw16032step2 raw16032step1; decide +kernel
      have hl : raw16032step1Labels = labelEmbedding8 ∘ raw16032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16032step1 raw16032step1Labels raw16032step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical16033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16033 raw16033Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw16033 raw16033Labels = mixedMoment B raw16033step0 raw16033step0Labels := by
      have ha : raw16033step0 = (fun i j => raw16033 (permutation319 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16033step0 raw16033; decide +kernel
      have hl : raw16033step0Labels = raw16033Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16033 raw16033Labels permutation319 permutation4
    mixedMoment B raw16033step0 raw16033step0Labels = mixedMoment B raw16033step1 raw16033step1Labels := by
      have ha : raw16033step1 = raw16033step0 := by apply Matrix.ext; unfold raw16033step1 raw16033step0; decide +kernel
      have hl : raw16033step0Labels = labelEmbedding7 ∘ raw16033step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16033step0 raw16033step0Labels raw16033step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

theorem canonical16034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16034 raw16034Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw16034 raw16034Labels = mixedMoment B raw16034step0 raw16034step0Labels := by
      have ha : raw16034step0 = (fun i j => raw16034 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16034step0 raw16034; decide +kernel
      have hl : raw16034step0Labels = raw16034Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16034 raw16034Labels permutation317 permutation4
    mixedMoment B raw16034step0 raw16034step0Labels = mixedMoment B raw16034step1 raw16034step1Labels := by
      have ha : raw16034step1 = raw16034step0 := by apply Matrix.ext; unfold raw16034step1 raw16034step0; decide +kernel
      have hl : raw16034step0Labels = labelEmbedding7 ∘ raw16034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16034step0 raw16034step0Labels raw16034step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical16035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16035 raw16035Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw16035 raw16035Labels = mixedMoment B raw16035step0 raw16035step0Labels := by
      have ha : raw16035step0 = (fun i j => raw16035 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16035step0 raw16035; decide +kernel
      have hl : raw16035step0Labels = raw16035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16035 raw16035Labels permutation158 permutation3
    mixedMoment B raw16035step0 raw16035step0Labels = mixedMoment B raw16035step1 raw16035step1Labels := by
      have ha : raw16035step1 = raw16035step0 := by apply Matrix.ext; unfold raw16035step1 raw16035step0; decide +kernel
      have hl : raw16035step0Labels = labelEmbedding6 ∘ raw16035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16035step0 raw16035step0Labels raw16035step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical16036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16036 raw16036Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw16036 raw16036Labels = mixedMoment B raw16036step0 raw16036step0Labels := by
      have ha : raw16036step0 = (fun i j => raw16036 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16036step0 raw16036; decide +kernel
      have hl : raw16036step0Labels = raw16036Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16036 raw16036Labels permutation271 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical16037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16037 raw16037Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw16037 raw16037Labels = mixedMoment B raw16037step0 raw16037step0Labels := by
      have ha : raw16037step0 = (fun i j => raw16037 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16037step0 raw16037; decide +kernel
      have hl : raw16037step0Labels = raw16037Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16037 raw16037Labels permutation200 permutation3
    mixedMoment B raw16037step0 raw16037step0Labels = mixedMoment B raw16037step1 raw16037step1Labels := by
      have ha : raw16037step1 = raw16037step0 := by apply Matrix.ext; unfold raw16037step1 raw16037step0; decide +kernel
      have hl : raw16037step0Labels = labelEmbedding6 ∘ raw16037step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16037step0 raw16037step0Labels raw16037step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical16038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16038 raw16038Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw16038 raw16038Labels = mixedMoment B raw16038step0 raw16038step0Labels := by
      have ha : raw16038step0 = (fun i j => raw16038 (permutation230 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16038step0 raw16038; decide +kernel
      have hl : raw16038step0Labels = raw16038Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16038 raw16038Labels permutation230 permutation5
    mixedMoment B raw16038step0 raw16038step0Labels = mixedMoment B raw16038step1 raw16038step1Labels := by
      have ha : raw16038step1 = -raw16038step0 := by apply Matrix.ext; change ∀ i j, raw16038step1 i j = -(raw16038step0 i j); unfold raw16038step1 raw16038step0; decide +kernel
      have hl : raw16038step1Labels = raw16038step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16038step1 raw16038step1Labels = mixedMoment B raw16038step2 raw16038step2Labels := by
      have ha : raw16038step2 = raw16038step1 := by apply Matrix.ext; unfold raw16038step2 raw16038step1; decide +kernel
      have hl : raw16038step1Labels = labelEmbedding8 ∘ raw16038step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16038step1 raw16038step1Labels raw16038step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical16039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16039 raw16039Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw16039 raw16039Labels = mixedMoment B raw16039step0 raw16039step0Labels := by
      have ha : raw16039step0 = (fun i j => raw16039 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16039step0 raw16039; decide +kernel
      have hl : raw16039step0Labels = raw16039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16039 raw16039Labels permutation158 permutation3
    mixedMoment B raw16039step0 raw16039step0Labels = mixedMoment B raw16039step1 raw16039step1Labels := by
      have ha : raw16039step1 = raw16039step0 := by apply Matrix.ext; unfold raw16039step1 raw16039step0; decide +kernel
      have hl : raw16039step0Labels = labelEmbedding6 ∘ raw16039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16039step0 raw16039step0Labels raw16039step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical16040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16040 raw16040Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw16040 raw16040Labels = mixedMoment B raw16040step0 raw16040step0Labels := by
      have ha : raw16040step0 = (fun i j => raw16040 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16040step0 raw16040; decide +kernel
      have hl : raw16040step0Labels = raw16040Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16040 raw16040Labels permutation189 permutation5
    mixedMoment B raw16040step0 raw16040step0Labels = mixedMoment B raw16040step1 raw16040step1Labels := by
      have ha : raw16040step1 = -raw16040step0 := by apply Matrix.ext; change ∀ i j, raw16040step1 i j = -(raw16040step0 i j); unfold raw16040step1 raw16040step0; decide +kernel
      have hl : raw16040step1Labels = raw16040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16040step1 raw16040step1Labels = mixedMoment B raw16040step2 raw16040step2Labels := by
      have ha : raw16040step2 = raw16040step1 := by apply Matrix.ext; unfold raw16040step2 raw16040step1; decide +kernel
      have hl : raw16040step1Labels = labelEmbedding8 ∘ raw16040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16040step1 raw16040step1Labels raw16040step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

theorem canonical16041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16041 raw16041Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw16041 raw16041Labels = mixedMoment B raw16041step0 raw16041step0Labels := by
      have ha : raw16041step0 = (fun i j => raw16041 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16041step0 raw16041; decide +kernel
      have hl : raw16041step0Labels = raw16041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16041 raw16041Labels permutation154 permutation3
    mixedMoment B raw16041step0 raw16041step0Labels = mixedMoment B raw16041step1 raw16041step1Labels := by
      have ha : raw16041step1 = raw16041step0 := by apply Matrix.ext; unfold raw16041step1 raw16041step0; decide +kernel
      have hl : raw16041step0Labels = labelEmbedding6 ∘ raw16041step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16041step0 raw16041step0Labels raw16041step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical16042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16042 raw16042Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw16042 raw16042Labels = mixedMoment B raw16042step0 raw16042step0Labels := by
      have ha : raw16042step0 = (fun i j => raw16042 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16042step0 raw16042; decide +kernel
      have hl : raw16042step0Labels = raw16042Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16042 raw16042Labels permutation189 permutation5
    mixedMoment B raw16042step0 raw16042step0Labels = mixedMoment B raw16042step1 raw16042step1Labels := by
      have ha : raw16042step1 = -raw16042step0 := by apply Matrix.ext; change ∀ i j, raw16042step1 i j = -(raw16042step0 i j); unfold raw16042step1 raw16042step0; decide +kernel
      have hl : raw16042step1Labels = raw16042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16042step1 raw16042step1Labels = mixedMoment B raw16042step2 raw16042step2Labels := by
      have ha : raw16042step2 = raw16042step1 := by apply Matrix.ext; unfold raw16042step2 raw16042step1; decide +kernel
      have hl : raw16042step1Labels = labelEmbedding8 ∘ raw16042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16042step1 raw16042step1Labels raw16042step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

theorem canonical16043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16043 raw16043Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw16043 raw16043Labels = mixedMoment B raw16043step0 raw16043step0Labels := by
      have ha : raw16043step0 = (fun i j => raw16043 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16043step0 raw16043; decide +kernel
      have hl : raw16043step0Labels = raw16043Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16043 raw16043Labels permutation189 permutation5
    mixedMoment B raw16043step0 raw16043step0Labels = mixedMoment B raw16043step1 raw16043step1Labels := by
      have ha : raw16043step1 = -raw16043step0 := by apply Matrix.ext; change ∀ i j, raw16043step1 i j = -(raw16043step0 i j); unfold raw16043step1 raw16043step0; decide +kernel
      have hl : raw16043step1Labels = raw16043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16043step1 raw16043step1Labels = mixedMoment B raw16043step2 raw16043step2Labels := by
      have ha : raw16043step2 = raw16043step1 := by apply Matrix.ext; unfold raw16043step2 raw16043step1; decide +kernel
      have hl : raw16043step1Labels = labelEmbedding8 ∘ raw16043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16043step1 raw16043step1Labels raw16043step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

theorem canonical16044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16044 raw16044Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw16044 raw16044Labels = mixedMoment B raw16044step0 raw16044step0Labels := by
      have ha : raw16044step0 = (fun i j => raw16044 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16044step0 raw16044; decide +kernel
      have hl : raw16044step0Labels = raw16044Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16044 raw16044Labels permutation192 permutation5
    mixedMoment B raw16044step0 raw16044step0Labels = mixedMoment B raw16044step1 raw16044step1Labels := by
      have ha : raw16044step1 = -raw16044step0 := by apply Matrix.ext; change ∀ i j, raw16044step1 i j = -(raw16044step0 i j); unfold raw16044step1 raw16044step0; decide +kernel
      have hl : raw16044step1Labels = raw16044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16044step1 raw16044step1Labels = mixedMoment B raw16044step2 raw16044step2Labels := by
      have ha : raw16044step2 = raw16044step1 := by apply Matrix.ext; unfold raw16044step2 raw16044step1; decide +kernel
      have hl : raw16044step1Labels = labelEmbedding8 ∘ raw16044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16044step1 raw16044step1Labels raw16044step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical16045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16045 raw16045Labels = mixedMoment B node4825 node4825Labels := by
  calc
    mixedMoment B raw16045 raw16045Labels = mixedMoment B raw16045step0 raw16045step0Labels := by
      have ha : raw16045step0 = (fun i j => raw16045 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16045step0 raw16045; decide +kernel
      have hl : raw16045step0Labels = raw16045Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16045 raw16045Labels permutation176 permutation5
    mixedMoment B raw16045step0 raw16045step0Labels = mixedMoment B raw16045step1 raw16045step1Labels := by
      have ha : raw16045step1 = -raw16045step0 := by apply Matrix.ext; change ∀ i j, raw16045step1 i j = -(raw16045step0 i j); unfold raw16045step1 raw16045step0; decide +kernel
      have hl : raw16045step1Labels = raw16045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16045step1 raw16045step1Labels = mixedMoment B raw16045step2 raw16045step2Labels := by
      have ha : raw16045step2 = raw16045step1 := by apply Matrix.ext; unfold raw16045step2 raw16045step1; decide +kernel
      have hl : raw16045step1Labels = labelEmbedding8 ∘ raw16045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16045step1 raw16045step1Labels raw16045step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4825 node4825Labels := by rfl

theorem canonical16046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16046 raw16046Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw16046 raw16046Labels = mixedMoment B raw16046step0 raw16046step0Labels := by
      have ha : raw16046step0 = (fun i j => raw16046 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16046step0 raw16046; decide +kernel
      have hl : raw16046step0Labels = raw16046Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16046 raw16046Labels permutation271 permutation2
    _ = mixedMoment B node5377 node5377Labels := by rfl

theorem canonical16047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16047 raw16047Labels = mixedMoment B node5362 node5362Labels := by
  calc
    mixedMoment B raw16047 raw16047Labels = mixedMoment B raw16047step0 raw16047step0Labels := by
      have ha : raw16047step0 = (fun i j => raw16047 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16047step0 raw16047; decide +kernel
      have hl : raw16047step0Labels = raw16047Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16047 raw16047Labels permutation176 permutation5
    mixedMoment B raw16047step0 raw16047step0Labels = mixedMoment B raw16047step1 raw16047step1Labels := by
      have ha : raw16047step1 = -raw16047step0 := by apply Matrix.ext; change ∀ i j, raw16047step1 i j = -(raw16047step0 i j); unfold raw16047step1 raw16047step0; decide +kernel
      have hl : raw16047step1Labels = raw16047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16047step1 raw16047step1Labels = mixedMoment B raw16047step2 raw16047step2Labels := by
      have ha : raw16047step2 = raw16047step1 := by apply Matrix.ext; unfold raw16047step2 raw16047step1; decide +kernel
      have hl : raw16047step1Labels = labelEmbedding8 ∘ raw16047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16047step1 raw16047step1Labels raw16047step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5362 node5362Labels := by rfl

theorem canonical16048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16048 raw16048Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw16048 raw16048Labels = mixedMoment B raw16048step0 raw16048step0Labels := by
      have ha : raw16048step0 = (fun i j => raw16048 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16048step0 raw16048; decide +kernel
      have hl : raw16048step0Labels = raw16048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16048 raw16048Labels permutation200 permutation3
    mixedMoment B raw16048step0 raw16048step0Labels = mixedMoment B raw16048step1 raw16048step1Labels := by
      have ha : raw16048step1 = raw16048step0 := by apply Matrix.ext; unfold raw16048step1 raw16048step0; decide +kernel
      have hl : raw16048step0Labels = labelEmbedding6 ∘ raw16048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16048step0 raw16048step0Labels raw16048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

theorem canonical16049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16049 raw16049Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw16049 raw16049Labels = mixedMoment B raw16049step0 raw16049step0Labels := by
      have ha : raw16049step0 = (fun i j => raw16049 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16049step0 raw16049; decide +kernel
      have hl : raw16049step0Labels = raw16049Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16049 raw16049Labels permutation194 permutation5
    mixedMoment B raw16049step0 raw16049step0Labels = mixedMoment B raw16049step1 raw16049step1Labels := by
      have ha : raw16049step1 = -raw16049step0 := by apply Matrix.ext; change ∀ i j, raw16049step1 i j = -(raw16049step0 i j); unfold raw16049step1 raw16049step0; decide +kernel
      have hl : raw16049step1Labels = raw16049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16049step1 raw16049step1Labels = mixedMoment B raw16049step2 raw16049step2Labels := by
      have ha : raw16049step2 = raw16049step1 := by apply Matrix.ext; unfold raw16049step2 raw16049step1; decide +kernel
      have hl : raw16049step1Labels = labelEmbedding8 ∘ raw16049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16049step1 raw16049step1Labels raw16049step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical16050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16050 raw16050Labels = mixedMoment B node4797 node4797Labels := by
  calc
    mixedMoment B raw16050 raw16050Labels = mixedMoment B raw16050step0 raw16050step0Labels := by
      have ha : raw16050step0 = (fun i j => raw16050 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16050step0 raw16050; decide +kernel
      have hl : raw16050step0Labels = raw16050Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16050 raw16050Labels permutation188 permutation5
    mixedMoment B raw16050step0 raw16050step0Labels = mixedMoment B raw16050step1 raw16050step1Labels := by
      have ha : raw16050step1 = -raw16050step0 := by apply Matrix.ext; change ∀ i j, raw16050step1 i j = -(raw16050step0 i j); unfold raw16050step1 raw16050step0; decide +kernel
      have hl : raw16050step1Labels = raw16050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16050step1 raw16050step1Labels = mixedMoment B raw16050step2 raw16050step2Labels := by
      have ha : raw16050step2 = raw16050step1 := by apply Matrix.ext; unfold raw16050step2 raw16050step1; decide +kernel
      have hl : raw16050step1Labels = labelEmbedding8 ∘ raw16050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16050step1 raw16050step1Labels raw16050step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4797 node4797Labels := by rfl

theorem canonical16051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16051 raw16051Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw16051 raw16051Labels = mixedMoment B raw16051step0 raw16051step0Labels := by
      have ha : raw16051step0 = (fun i j => raw16051 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16051step0 raw16051; decide +kernel
      have hl : raw16051step0Labels = raw16051Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16051 raw16051Labels permutation688 permutation3
    mixedMoment B raw16051step0 raw16051step0Labels = mixedMoment B raw16051step1 raw16051step1Labels := by
      have ha : raw16051step1 = -raw16051step0 := by apply Matrix.ext; change ∀ i j, raw16051step1 i j = -(raw16051step0 i j); unfold raw16051step1 raw16051step0; decide +kernel
      have hl : raw16051step1Labels = raw16051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16051step1 raw16051step1Labels = mixedMoment B raw16051step2 raw16051step2Labels := by
      have ha : raw16051step2 = raw16051step1 := by apply Matrix.ext; unfold raw16051step2 raw16051step1; decide +kernel
      have hl : raw16051step1Labels = labelEmbedding6 ∘ raw16051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16051step1 raw16051step1Labels raw16051step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical16052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16052 raw16052Labels = mixedMoment B node5132 node5132Labels := by
  calc
    mixedMoment B raw16052 raw16052Labels = mixedMoment B raw16052step0 raw16052step0Labels := by
      have ha : raw16052step0 = (fun i j => raw16052 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16052step0 raw16052; decide +kernel
      have hl : raw16052step0Labels = raw16052Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16052 raw16052Labels permutation686 permutation3
    mixedMoment B raw16052step0 raw16052step0Labels = mixedMoment B raw16052step1 raw16052step1Labels := by
      have ha : raw16052step1 = -raw16052step0 := by apply Matrix.ext; change ∀ i j, raw16052step1 i j = -(raw16052step0 i j); unfold raw16052step1 raw16052step0; decide +kernel
      have hl : raw16052step1Labels = raw16052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16052step1 raw16052step1Labels = mixedMoment B raw16052step2 raw16052step2Labels := by
      have ha : raw16052step2 = raw16052step1 := by apply Matrix.ext; unfold raw16052step2 raw16052step1; decide +kernel
      have hl : raw16052step1Labels = labelEmbedding6 ∘ raw16052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16052step1 raw16052step1Labels raw16052step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5132 node5132Labels := by rfl

theorem canonical16053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16053 raw16053Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw16053 raw16053Labels = mixedMoment B raw16053step0 raw16053step0Labels := by
      have ha : raw16053step0 = (fun i j => raw16053 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16053step0 raw16053; decide +kernel
      have hl : raw16053step0Labels = raw16053Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16053 raw16053Labels permutation680 permutation3
    mixedMoment B raw16053step0 raw16053step0Labels = mixedMoment B raw16053step1 raw16053step1Labels := by
      have ha : raw16053step1 = -raw16053step0 := by apply Matrix.ext; change ∀ i j, raw16053step1 i j = -(raw16053step0 i j); unfold raw16053step1 raw16053step0; decide +kernel
      have hl : raw16053step1Labels = raw16053step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16053step1 raw16053step1Labels = mixedMoment B raw16053step2 raw16053step2Labels := by
      have ha : raw16053step2 = raw16053step1 := by apply Matrix.ext; unfold raw16053step2 raw16053step1; decide +kernel
      have hl : raw16053step1Labels = labelEmbedding6 ∘ raw16053step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16053step1 raw16053step1Labels raw16053step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical16054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16054 raw16054Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw16054 raw16054Labels = mixedMoment B raw16054step0 raw16054step0Labels := by
      have ha : raw16054step0 = (fun i j => raw16054 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16054step0 raw16054; decide +kernel
      have hl : raw16054step0Labels = raw16054Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16054 raw16054Labels permutation658 permutation3
    mixedMoment B raw16054step0 raw16054step0Labels = mixedMoment B raw16054step1 raw16054step1Labels := by
      have ha : raw16054step1 = -raw16054step0 := by apply Matrix.ext; change ∀ i j, raw16054step1 i j = -(raw16054step0 i j); unfold raw16054step1 raw16054step0; decide +kernel
      have hl : raw16054step1Labels = raw16054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16054step1 raw16054step1Labels = mixedMoment B raw16054step2 raw16054step2Labels := by
      have ha : raw16054step2 = raw16054step1 := by apply Matrix.ext; unfold raw16054step2 raw16054step1; decide +kernel
      have hl : raw16054step1Labels = labelEmbedding6 ∘ raw16054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16054step1 raw16054step1Labels raw16054step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

theorem canonical16115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16115 raw16115Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw16115 raw16115Labels = mixedMoment B raw16115step0 raw16115step0Labels := by
      have ha : raw16115step0 = (fun i j => raw16115 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16115step0 raw16115; decide +kernel
      have hl : raw16115step0Labels = raw16115Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16115 raw16115Labels permutation682 permutation2
    mixedMoment B raw16115step0 raw16115step0Labels = mixedMoment B raw16115step1 raw16115step1Labels := by
      have ha : raw16115step1 = -raw16115step0 := by apply Matrix.ext; change ∀ i j, raw16115step1 i j = -(raw16115step0 i j); unfold raw16115step1 raw16115step0; decide +kernel
      have hl : raw16115step1Labels = raw16115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical16117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16117 raw16117Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw16117 raw16117Labels = mixedMoment B raw16117step0 raw16117step0Labels := by
      have ha : raw16117step0 = (fun i j => raw16117 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16117step0 raw16117; decide +kernel
      have hl : raw16117step0Labels = raw16117Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16117 raw16117Labels permutation158 permutation2
    _ = mixedMoment B node3172 node3172Labels := by rfl

theorem canonical16121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16121 raw16121Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16121 raw16121Labels = mixedMoment B raw16121step0 raw16121step0Labels := by
      have hz : ∀ j, raw16121 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw16121step0 = (fun i j => raw16121 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw16121step0 raw16121; decide +kernel
      have hl : raw16121step0Labels = raw16121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16121 raw16121Labels permutation152 hz
    mixedMoment B raw16121step0 raw16121step0Labels = mixedMoment B raw16121step1 raw16121step1Labels := by
      have ha : raw16121step1 = (fun i j => raw16121step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16121step1 raw16121step0; decide +kernel
      have hl : raw16121step1Labels = raw16121step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16121step0 raw16121step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical16122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16122 raw16122Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw16122 raw16122Labels = mixedMoment B raw16122step0 raw16122step0Labels := by
      have ha : raw16122step0 = (fun i j => raw16122 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16122step0 raw16122; decide +kernel
      have hl : raw16122step0Labels = raw16122Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16122 raw16122Labels permutation271 permutation2
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical16123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16123 raw16123Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw16123 raw16123Labels = mixedMoment B raw16123step0 raw16123step0Labels := by
      have ha : raw16123step0 = (fun i j => raw16123 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16123step0 raw16123; decide +kernel
      have hl : raw16123step0Labels = raw16123Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16123 raw16123Labels permutation271 permutation2
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical16124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16124 raw16124Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw16124 raw16124Labels = mixedMoment B raw16124step0 raw16124step0Labels := by
      have ha : raw16124step0 = (fun i j => raw16124 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16124step0 raw16124; decide +kernel
      have hl : raw16124step0Labels = raw16124Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16124 raw16124Labels permutation265 permutation2
    _ = mixedMoment B node3724 node3724Labels := by rfl

theorem canonical16125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16125 raw16125Labels = mixedMoment B node3716 node3716Labels := by
  calc
    mixedMoment B raw16125 raw16125Labels = mixedMoment B raw16125step0 raw16125step0Labels := by
      have ha : raw16125step0 = (fun i j => raw16125 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16125step0 raw16125; decide +kernel
      have hl : raw16125step0Labels = raw16125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16125 raw16125Labels permutation271 permutation2
    _ = mixedMoment B node3716 node3716Labels := by rfl

theorem canonical16126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16126 raw16126Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw16126 raw16126Labels = mixedMoment B raw16126step0 raw16126step0Labels := by
      have ha : raw16126step0 = (fun i j => raw16126 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16126step0 raw16126; decide +kernel
      have hl : raw16126step0Labels = raw16126Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16126 raw16126Labels permutation681 permutation2
    mixedMoment B raw16126step0 raw16126step0Labels = mixedMoment B raw16126step1 raw16126step1Labels := by
      have ha : raw16126step1 = -raw16126step0 := by apply Matrix.ext; change ∀ i j, raw16126step1 i j = -(raw16126step0 i j); unfold raw16126step1 raw16126step0; decide +kernel
      have hl : raw16126step1Labels = raw16126step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2916 node2916Labels := by rfl

theorem canonical16127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16127 raw16127Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw16127 raw16127Labels = mixedMoment B raw16127step0 raw16127step0Labels := by
      have ha : raw16127step0 = (fun i j => raw16127 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16127step0 raw16127; decide +kernel
      have hl : raw16127step0Labels = raw16127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16127 raw16127Labels permutation646 permutation2
    mixedMoment B raw16127step0 raw16127step0Labels = mixedMoment B raw16127step1 raw16127step1Labels := by
      have ha : raw16127step1 = -raw16127step0 := by apply Matrix.ext; change ∀ i j, raw16127step1 i j = -(raw16127step0 i j); unfold raw16127step1 raw16127step0; decide +kernel
      have hl : raw16127step1Labels = raw16127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16128 raw16128Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw16128 raw16128Labels = mixedMoment B raw16128step0 raw16128step0Labels := by
      have ha : raw16128step0 = (fun i j => raw16128 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16128step0 raw16128; decide +kernel
      have hl : raw16128step0Labels = raw16128Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16128 raw16128Labels permutation646 permutation2
    mixedMoment B raw16128step0 raw16128step0Labels = mixedMoment B raw16128step1 raw16128step1Labels := by
      have ha : raw16128step1 = -raw16128step0 := by apply Matrix.ext; change ∀ i j, raw16128step1 i j = -(raw16128step0 i j); unfold raw16128step1 raw16128step0; decide +kernel
      have hl : raw16128step1Labels = raw16128step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical16129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16129 raw16129Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw16129 raw16129Labels = mixedMoment B raw16129step0 raw16129step0Labels := by
      have ha : raw16129step0 = (fun i j => raw16129 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16129step0 raw16129; decide +kernel
      have hl : raw16129step0Labels = raw16129Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16129 raw16129Labels permutation158 permutation2
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical16137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16137 raw16137Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw16137 raw16137Labels = mixedMoment B raw16137step0 raw16137step0Labels := by
      have ha : raw16137step0 = (fun i j => raw16137 (permutation645 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16137step0 raw16137; decide +kernel
      have hl : raw16137step0Labels = raw16137Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16137 raw16137Labels permutation645 permutation2
    mixedMoment B raw16137step0 raw16137step0Labels = mixedMoment B raw16137step1 raw16137step1Labels := by
      have ha : raw16137step1 = -raw16137step0 := by apply Matrix.ext; change ∀ i j, raw16137step1 i j = -(raw16137step0 i j); unfold raw16137step1 raw16137step0; decide +kernel
      have hl : raw16137step1Labels = raw16137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4008 node4008Labels := by rfl

theorem canonical16138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16138 raw16138Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw16138 raw16138Labels = mixedMoment B raw16138step0 raw16138step0Labels := by
      have ha : raw16138step0 = (fun i j => raw16138 (permutation319 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16138step0 raw16138; decide +kernel
      have hl : raw16138step0Labels = raw16138Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16138 raw16138Labels permutation319 permutation4
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical16139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16139 raw16139Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw16139 raw16139Labels = mixedMoment B raw16139step0 raw16139step0Labels := by
      have ha : raw16139step0 = (fun i j => raw16139 (permutation465 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16139step0 raw16139; decide +kernel
      have hl : raw16139step0Labels = raw16139Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16139 raw16139Labels permutation465 permutation4
    _ = mixedMoment B node3949 node3949Labels := by rfl

theorem canonical16140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16140 raw16140Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw16140 raw16140Labels = mixedMoment B raw16140step0 raw16140step0Labels := by
      have ha : raw16140step0 = (fun i j => raw16140 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16140step0 raw16140; decide +kernel
      have hl : raw16140step0Labels = raw16140Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16140 raw16140Labels permutation646 permutation2
    mixedMoment B raw16140step0 raw16140step0Labels = mixedMoment B raw16140step1 raw16140step1Labels := by
      have ha : raw16140step1 = -raw16140step0 := by apply Matrix.ext; change ∀ i j, raw16140step1 i j = -(raw16140step0 i j); unfold raw16140step1 raw16140step0; decide +kernel
      have hl : raw16140step1Labels = raw16140step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3066 node3066Labels := by rfl

theorem canonical16206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16206 raw16206Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw16206 raw16206Labels = mixedMoment B raw16206step0 raw16206step0Labels := by
      have ha : raw16206step0 = (fun i j => raw16206 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16206step0 raw16206; decide +kernel
      have hl : raw16206step0Labels = raw16206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16206 raw16206Labels permutation188 permutation4
    mixedMoment B raw16206step0 raw16206step0Labels = mixedMoment B raw16206step1 raw16206step1Labels := by
      have ha : raw16206step1 = -raw16206step0 := by apply Matrix.ext; change ∀ i j, raw16206step1 i j = -(raw16206step0 i j); unfold raw16206step1 raw16206step0; decide +kernel
      have hl : raw16206step1Labels = raw16206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical16207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16207 raw16207Labels = mixedMoment B node4044 node4044Labels := by
  calc
    mixedMoment B raw16207 raw16207Labels = mixedMoment B raw16207step0 raw16207step0Labels := by
      have ha : raw16207step0 = (fun i j => raw16207 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16207step0 raw16207; decide +kernel
      have hl : raw16207step0Labels = raw16207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16207 raw16207Labels permutation682 permutation2
    _ = mixedMoment B node4044 node4044Labels := by rfl

theorem canonical16208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16208 raw16208Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw16208 raw16208Labels = mixedMoment B raw16208step0 raw16208step0Labels := by
      have ha : raw16208step0 = (fun i j => raw16208 (permutation274 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16208step0 raw16208; decide +kernel
      have hl : raw16208step0Labels = raw16208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16208 raw16208Labels permutation274 permutation2
    mixedMoment B raw16208step0 raw16208step0Labels = mixedMoment B raw16208step1 raw16208step1Labels := by
      have ha : raw16208step1 = -raw16208step0 := by apply Matrix.ext; change ∀ i j, raw16208step1 i j = -(raw16208step0 i j); unfold raw16208step1 raw16208step0; decide +kernel
      have hl : raw16208step1Labels = raw16208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

theorem canonical16209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16209 raw16209Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw16209 raw16209Labels = mixedMoment B raw16209step0 raw16209step0Labels := by
      have hz : ∀ j, raw16209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16209step0 = (fun i j => raw16209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16209step0 raw16209; decide +kernel
      have hl : raw16209step0Labels = raw16209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16209 raw16209Labels permutation434 hz
    mixedMoment B raw16209step0 raw16209step0Labels = mixedMoment B raw16209step1 raw16209step1Labels := by
      have ha : raw16209step1 = (fun i j => raw16209step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16209step1 raw16209step0; decide +kernel
      have hl : raw16209step1Labels = raw16209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16209step0 raw16209step0Labels permutation56 permutation2
    mixedMoment B raw16209step1 raw16209step1Labels = mixedMoment B raw16209step2 raw16209step2Labels := by
      have ha : raw16209step2 = -raw16209step1 := by apply Matrix.ext; change ∀ i j, raw16209step2 i j = -(raw16209step1 i j); unfold raw16209step2 raw16209step1; decide +kernel
      have hl : raw16209step2Labels = raw16209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical16210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16210 raw16210Labels = mixedMoment B node3944 node3944Labels := by
  calc
    mixedMoment B raw16210 raw16210Labels = mixedMoment B raw16210step0 raw16210step0Labels := by
      have ha : raw16210step0 = (fun i j => raw16210 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16210step0 raw16210; decide +kernel
      have hl : raw16210step0Labels = raw16210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16210 raw16210Labels permutation583 permutation2
    _ = mixedMoment B node3944 node3944Labels := by rfl

theorem canonical16211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16211 raw16211Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw16211 raw16211Labels = mixedMoment B raw16211step0 raw16211step0Labels := by
      have ha : raw16211step0 = (fun i j => raw16211 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16211step0 raw16211; decide +kernel
      have hl : raw16211step0Labels = raw16211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16211 raw16211Labels permutation681 permutation2
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical16212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16212 raw16212Labels = mixedMoment B node2977 node2977Labels := by
  calc
    mixedMoment B raw16212 raw16212Labels = mixedMoment B raw16212step0 raw16212step0Labels := by
      have ha : raw16212step0 = (fun i j => raw16212 (permutation308 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16212step0 raw16212; decide +kernel
      have hl : raw16212step0Labels = raw16212Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16212 raw16212Labels permutation308 permutation2
    mixedMoment B raw16212step0 raw16212step0Labels = mixedMoment B raw16212step1 raw16212step1Labels := by
      have ha : raw16212step1 = -raw16212step0 := by apply Matrix.ext; change ∀ i j, raw16212step1 i j = -(raw16212step0 i j); unfold raw16212step1 raw16212step0; decide +kernel
      have hl : raw16212step1Labels = raw16212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2977 node2977Labels := by rfl

theorem canonical16213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16213 raw16213Labels = mixedMoment B node3725 node3725Labels := by
  calc
    mixedMoment B raw16213 raw16213Labels = mixedMoment B raw16213step0 raw16213step0Labels := by
      have ha : raw16213step0 = (fun i j => raw16213 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16213step0 raw16213; decide +kernel
      have hl : raw16213step0Labels = raw16213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16213 raw16213Labels permutation189 permutation4
    mixedMoment B raw16213step0 raw16213step0Labels = mixedMoment B raw16213step1 raw16213step1Labels := by
      have ha : raw16213step1 = -raw16213step0 := by apply Matrix.ext; change ∀ i j, raw16213step1 i j = -(raw16213step0 i j); unfold raw16213step1 raw16213step0; decide +kernel
      have hl : raw16213step1Labels = raw16213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3725 node3725Labels := by rfl

theorem canonical16214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16214 raw16214Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw16214 raw16214Labels = mixedMoment B raw16214step0 raw16214step0Labels := by
      have ha : raw16214step0 = (fun i j => raw16214 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16214step0 raw16214; decide +kernel
      have hl : raw16214step0Labels = raw16214Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16214 raw16214Labels permutation176 permutation4
    mixedMoment B raw16214step0 raw16214step0Labels = mixedMoment B raw16214step1 raw16214step1Labels := by
      have ha : raw16214step1 = -raw16214step0 := by apply Matrix.ext; change ∀ i j, raw16214step1 i j = -(raw16214step0 i j); unfold raw16214step1 raw16214step0; decide +kernel
      have hl : raw16214step1Labels = raw16214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3730 node3730Labels := by rfl

theorem canonical16215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16215 raw16215Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw16215 raw16215Labels = mixedMoment B raw16215step0 raw16215step0Labels := by
      have ha : raw16215step0 = (fun i j => raw16215 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16215step0 raw16215; decide +kernel
      have hl : raw16215step0Labels = raw16215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16215 raw16215Labels permutation188 permutation4
    mixedMoment B raw16215step0 raw16215step0Labels = mixedMoment B raw16215step1 raw16215step1Labels := by
      have ha : raw16215step1 = -raw16215step0 := by apply Matrix.ext; change ∀ i j, raw16215step1 i j = -(raw16215step0 i j); unfold raw16215step1 raw16215step0; decide +kernel
      have hl : raw16215step1Labels = raw16215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

theorem canonical16216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16216 raw16216Labels = mixedMoment B node2975 node2975Labels := by
  calc
    mixedMoment B raw16216 raw16216Labels = mixedMoment B raw16216step0 raw16216step0Labels := by
      have ha : raw16216step0 = (fun i j => raw16216 (permutation306 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16216step0 raw16216; decide +kernel
      have hl : raw16216step0Labels = raw16216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16216 raw16216Labels permutation306 permutation2
    mixedMoment B raw16216step0 raw16216step0Labels = mixedMoment B raw16216step1 raw16216step1Labels := by
      have ha : raw16216step1 = -raw16216step0 := by apply Matrix.ext; change ∀ i j, raw16216step1 i j = -(raw16216step0 i j); unfold raw16216step1 raw16216step0; decide +kernel
      have hl : raw16216step1Labels = raw16216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2975 node2975Labels := by rfl

theorem canonical16217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16217 raw16217Labels = mixedMoment B node3828 node3828Labels := by
  calc
    mixedMoment B raw16217 raw16217Labels = mixedMoment B raw16217step0 raw16217step0Labels := by
      have ha : raw16217step0 = (fun i j => raw16217 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16217step0 raw16217; decide +kernel
      have hl : raw16217step0Labels = raw16217Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16217 raw16217Labels permutation189 permutation4
    mixedMoment B raw16217step0 raw16217step0Labels = mixedMoment B raw16217step1 raw16217step1Labels := by
      have ha : raw16217step1 = -raw16217step0 := by apply Matrix.ext; change ∀ i j, raw16217step1 i j = -(raw16217step0 i j); unfold raw16217step1 raw16217step0; decide +kernel
      have hl : raw16217step1Labels = raw16217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3828 node3828Labels := by rfl

theorem canonical16218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16218 raw16218Labels = mixedMoment B node3826 node3826Labels := by
  calc
    mixedMoment B raw16218 raw16218Labels = mixedMoment B raw16218step0 raw16218step0Labels := by
      have ha : raw16218step0 = (fun i j => raw16218 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16218step0 raw16218; decide +kernel
      have hl : raw16218step0Labels = raw16218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16218 raw16218Labels permutation654 permutation4
    _ = mixedMoment B node3826 node3826Labels := by rfl

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

theorem canonical2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2433 raw2433Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw2433 raw2433Labels = mixedMoment B raw2433step0 raw2433step0Labels := by
      have ha : raw2433step0 = (fun i j => raw2433 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2433step0 raw2433; decide +kernel
      have hl : raw2433step0Labels = raw2433Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2433 raw2433Labels permutation152 permutation4
    mixedMoment B raw2433step0 raw2433step0Labels = mixedMoment B raw2433step1 raw2433step1Labels := by
      have ha : raw2433step1 = raw2433step0 := by apply Matrix.ext; unfold raw2433step1 raw2433step0; decide +kernel
      have hl : raw2433step0Labels = labelEmbedding7 ∘ raw2433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2433step0 raw2433step0Labels raw2433step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2434 raw2434Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw2434 raw2434Labels = mixedMoment B raw2434step0 raw2434step0Labels := by
      have ha : raw2434step0 = (fun i j => raw2434 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2434step0 raw2434; decide +kernel
      have hl : raw2434step0Labels = raw2434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2434 raw2434Labels permutation152 permutation4
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2435 raw2435Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw2435 raw2435Labels = mixedMoment B raw2435step0 raw2435step0Labels := by
      have ha : raw2435step0 = (fun i j => raw2435 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2435step0 raw2435; decide +kernel
      have hl : raw2435step0Labels = raw2435Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2435 raw2435Labels permutation176 permutation6
    mixedMoment B raw2435step0 raw2435step0Labels = mixedMoment B raw2435step1 raw2435step1Labels := by
      have ha : raw2435step1 = -raw2435step0 := by apply Matrix.ext; change ∀ i j, raw2435step1 i j = -(raw2435step0 i j); unfold raw2435step1 raw2435step0; decide +kernel
      have hl : raw2435step1Labels = raw2435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2435step1 raw2435step1Labels = mixedMoment B raw2435step2 raw2435step2Labels := by
      have ha : raw2435step2 = raw2435step1 := by apply Matrix.ext; unfold raw2435step2 raw2435step1; decide +kernel
      have hl : raw2435step1Labels = labelEmbedding1 ∘ raw2435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2435step1 raw2435step1Labels raw2435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

theorem canonical2478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2478 raw2478Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw2478 raw2478Labels = mixedMoment B raw2478step0 raw2478step0Labels := by
      have ha : raw2478step0 = (fun i j => raw2478 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2478step0 raw2478; decide +kernel
      have hl : raw2478step0Labels = raw2478Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2478 raw2478Labels permutation152 permutation4
    mixedMoment B raw2478step0 raw2478step0Labels = mixedMoment B raw2478step1 raw2478step1Labels := by
      have ha : raw2478step1 = raw2478step0 := by apply Matrix.ext; unfold raw2478step1 raw2478step0; decide +kernel
      have hl : raw2478step0Labels = labelEmbedding7 ∘ raw2478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2478step0 raw2478step0Labels raw2478step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

theorem canonical2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2479 raw2479Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw2479 raw2479Labels = mixedMoment B raw2479step0 raw2479step0Labels := by
      have ha : raw2479step0 = (fun i j => raw2479 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2479step0 raw2479; decide +kernel
      have hl : raw2479step0Labels = raw2479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2479 raw2479Labels permutation152 permutation4
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2480 raw2480Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw2480 raw2480Labels = mixedMoment B raw2480step0 raw2480step0Labels := by
      have ha : raw2480step0 = (fun i j => raw2480 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2480step0 raw2480; decide +kernel
      have hl : raw2480step0Labels = raw2480Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2480 raw2480Labels permutation170 permutation6
    mixedMoment B raw2480step0 raw2480step0Labels = mixedMoment B raw2480step1 raw2480step1Labels := by
      have ha : raw2480step1 = -raw2480step0 := by apply Matrix.ext; change ∀ i j, raw2480step1 i j = -(raw2480step0 i j); unfold raw2480step1 raw2480step0; decide +kernel
      have hl : raw2480step1Labels = raw2480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2480step1 raw2480step1Labels = mixedMoment B raw2480step2 raw2480step2Labels := by
      have ha : raw2480step2 = raw2480step1 := by apply Matrix.ext; unfold raw2480step2 raw2480step1; decide +kernel
      have hl : raw2480step1Labels = labelEmbedding1 ∘ raw2480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2480step1 raw2480step1Labels raw2480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

theorem canonical2487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2487 raw2487Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2487 raw2487Labels = mixedMoment B raw2487step0 raw2487step0Labels := by
      have ha : raw2487step0 = (fun i j => raw2487 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2487step0 raw2487; decide +kernel
      have hl : raw2487step0Labels = raw2487Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2487 raw2487Labels permutation152 permutation4
    mixedMoment B raw2487step0 raw2487step0Labels = mixedMoment B raw2487step1 raw2487step1Labels := by
      have ha : raw2487step1 = raw2487step0 := by apply Matrix.ext; unfold raw2487step1 raw2487step0; decide +kernel
      have hl : raw2487step0Labels = labelEmbedding7 ∘ raw2487step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2487step0 raw2487step0Labels raw2487step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2488 raw2488Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2488 raw2488Labels = mixedMoment B raw2488step0 raw2488step0Labels := by
      have ha : raw2488step0 = (fun i j => raw2488 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2488step0 raw2488; decide +kernel
      have hl : raw2488step0Labels = raw2488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2488 raw2488Labels permutation152 permutation4
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2489 raw2489Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw2489 raw2489Labels = mixedMoment B raw2489step0 raw2489step0Labels := by
      have ha : raw2489step0 = (fun i j => raw2489 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2489step0 raw2489; decide +kernel
      have hl : raw2489step0Labels = raw2489Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2489 raw2489Labels permutation170 permutation6
    mixedMoment B raw2489step0 raw2489step0Labels = mixedMoment B raw2489step1 raw2489step1Labels := by
      have ha : raw2489step1 = -raw2489step0 := by apply Matrix.ext; change ∀ i j, raw2489step1 i j = -(raw2489step0 i j); unfold raw2489step1 raw2489step0; decide +kernel
      have hl : raw2489step1Labels = raw2489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2489step1 raw2489step1Labels = mixedMoment B raw2489step2 raw2489step2Labels := by
      have ha : raw2489step2 = raw2489step1 := by apply Matrix.ext; unfold raw2489step2 raw2489step1; decide +kernel
      have hl : raw2489step1Labels = labelEmbedding1 ∘ raw2489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2489step1 raw2489step1Labels raw2489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2508 raw2508Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw2508 raw2508Labels = mixedMoment B raw2508step0 raw2508step0Labels := by
      have ha : raw2508step0 = (fun i j => raw2508 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2508step0 raw2508; decide +kernel
      have hl : raw2508step0Labels = raw2508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2508 raw2508Labels permutation152 permutation5
    mixedMoment B raw2508step0 raw2508step0Labels = mixedMoment B raw2508step1 raw2508step1Labels := by
      have ha : raw2508step1 = raw2508step0 := by apply Matrix.ext; unfold raw2508step1 raw2508step0; decide +kernel
      have hl : raw2508step0Labels = labelEmbedding8 ∘ raw2508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2508step0 raw2508step0Labels raw2508step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2509 raw2509Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw2509 raw2509Labels = mixedMoment B raw2509step0 raw2509step0Labels := by
      have ha : raw2509step0 = (fun i j => raw2509 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2509step0 raw2509; decide +kernel
      have hl : raw2509step0Labels = raw2509Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2509 raw2509Labels permutation662 permutation4
    mixedMoment B raw2509step0 raw2509step0Labels = mixedMoment B raw2509step1 raw2509step1Labels := by
      have ha : raw2509step1 = -raw2509step0 := by apply Matrix.ext; change ∀ i j, raw2509step1 i j = -(raw2509step0 i j); unfold raw2509step1 raw2509step0; decide +kernel
      have hl : raw2509step1Labels = raw2509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical2510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2510 raw2510Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw2510 raw2510Labels = mixedMoment B raw2510step0 raw2510step0Labels := by
      have ha : raw2510step0 = (fun i j => raw2510 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2510step0 raw2510; decide +kernel
      have hl : raw2510step0Labels = raw2510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2510 raw2510Labels permutation160 permutation3
    mixedMoment B raw2510step0 raw2510step0Labels = mixedMoment B raw2510step1 raw2510step1Labels := by
      have ha : raw2510step1 = -raw2510step0 := by apply Matrix.ext; change ∀ i j, raw2510step1 i j = -(raw2510step0 i j); unfold raw2510step1 raw2510step0; decide +kernel
      have hl : raw2510step1Labels = raw2510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2510step1 raw2510step1Labels = mixedMoment B raw2510step2 raw2510step2Labels := by
      have ha : raw2510step2 = raw2510step1 := by apply Matrix.ext; unfold raw2510step2 raw2510step1; decide +kernel
      have hl : raw2510step1Labels = labelEmbedding1 ∘ raw2510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2510step1 raw2510step1Labels raw2510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

theorem canonical2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2514 raw2514Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw2514 raw2514Labels = mixedMoment B raw2514step0 raw2514step0Labels := by
      have ha : raw2514step0 = (fun i j => raw2514 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2514step0 raw2514; decide +kernel
      have hl : raw2514step0Labels = raw2514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2514 raw2514Labels permutation152 permutation4
    mixedMoment B raw2514step0 raw2514step0Labels = mixedMoment B raw2514step1 raw2514step1Labels := by
      have ha : raw2514step1 = raw2514step0 := by apply Matrix.ext; unfold raw2514step1 raw2514step0; decide +kernel
      have hl : raw2514step0Labels = labelEmbedding7 ∘ raw2514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2514step0 raw2514step0Labels raw2514step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2515 raw2515Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw2515 raw2515Labels = mixedMoment B raw2515step0 raw2515step0Labels := by
      have ha : raw2515step0 = (fun i j => raw2515 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2515step0 raw2515; decide +kernel
      have hl : raw2515step0Labels = raw2515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2515 raw2515Labels permutation152 permutation4
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2516 raw2516Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw2516 raw2516Labels = mixedMoment B raw2516step0 raw2516step0Labels := by
      have ha : raw2516step0 = (fun i j => raw2516 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2516step0 raw2516; decide +kernel
      have hl : raw2516step0Labels = raw2516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2516 raw2516Labels permutation176 permutation6
    mixedMoment B raw2516step0 raw2516step0Labels = mixedMoment B raw2516step1 raw2516step1Labels := by
      have ha : raw2516step1 = -raw2516step0 := by apply Matrix.ext; change ∀ i j, raw2516step1 i j = -(raw2516step0 i j); unfold raw2516step1 raw2516step0; decide +kernel
      have hl : raw2516step1Labels = raw2516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2516step1 raw2516step1Labels = mixedMoment B raw2516step2 raw2516step2Labels := by
      have ha : raw2516step2 = raw2516step1 := by apply Matrix.ext; unfold raw2516step2 raw2516step1; decide +kernel
      have hl : raw2516step1Labels = labelEmbedding1 ∘ raw2516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2516step1 raw2516step1Labels raw2516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2547 raw2547Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2547 raw2547Labels = mixedMoment B raw2547step0 raw2547step0Labels := by
      have ha : raw2547step0 = (fun i j => raw2547 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2547step0 raw2547; decide +kernel
      have hl : raw2547step0Labels = raw2547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2547 raw2547Labels permutation152 permutation5
    mixedMoment B raw2547step0 raw2547step0Labels = mixedMoment B raw2547step1 raw2547step1Labels := by
      have ha : raw2547step1 = raw2547step0 := by apply Matrix.ext; unfold raw2547step1 raw2547step0; decide +kernel
      have hl : raw2547step0Labels = labelEmbedding8 ∘ raw2547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2547step0 raw2547step0Labels raw2547step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical2548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2548 raw2548Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2548 raw2548Labels = mixedMoment B raw2548step0 raw2548step0Labels := by
      have ha : raw2548step0 = (fun i j => raw2548 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2548step0 raw2548; decide +kernel
      have hl : raw2548step0Labels = raw2548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2548 raw2548Labels permutation152 permutation4
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2549 raw2549Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw2549 raw2549Labels = mixedMoment B raw2549step0 raw2549step0Labels := by
      have ha : raw2549step0 = (fun i j => raw2549 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2549step0 raw2549; decide +kernel
      have hl : raw2549step0Labels = raw2549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2549 raw2549Labels permutation216 permutation3
    mixedMoment B raw2549step0 raw2549step0Labels = mixedMoment B raw2549step1 raw2549step1Labels := by
      have ha : raw2549step1 = -raw2549step0 := by apply Matrix.ext; change ∀ i j, raw2549step1 i j = -(raw2549step0 i j); unfold raw2549step1 raw2549step0; decide +kernel
      have hl : raw2549step1Labels = raw2549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2549step1 raw2549step1Labels = mixedMoment B raw2549step2 raw2549step2Labels := by
      have ha : raw2549step2 = raw2549step1 := by apply Matrix.ext; unfold raw2549step2 raw2549step1; decide +kernel
      have hl : raw2549step1Labels = labelEmbedding1 ∘ raw2549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2549step1 raw2549step1Labels raw2549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2598 raw2598Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw2598 raw2598Labels = mixedMoment B raw2598step0 raw2598step0Labels := by
      have ha : raw2598step0 = (fun i j => raw2598 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2598step0 raw2598; decide +kernel
      have hl : raw2598step0Labels = raw2598Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2598 raw2598Labels permutation152 permutation4
    mixedMoment B raw2598step0 raw2598step0Labels = mixedMoment B raw2598step1 raw2598step1Labels := by
      have ha : raw2598step1 = raw2598step0 := by apply Matrix.ext; unfold raw2598step1 raw2598step0; decide +kernel
      have hl : raw2598step0Labels = labelEmbedding7 ∘ raw2598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2598step0 raw2598step0Labels raw2598step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical2599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2599 raw2599Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2599 raw2599Labels = mixedMoment B raw2599step0 raw2599step0Labels := by
      have ha : raw2599step0 = (fun i j => raw2599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2599step0 raw2599; decide +kernel
      have hl : raw2599step0Labels = raw2599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2599 raw2599Labels permutation152 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2600 raw2600Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2600 raw2600Labels = mixedMoment B raw2600step0 raw2600step0Labels := by
      have ha : raw2600step0 = (fun i j => raw2600 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2600step0 raw2600; decide +kernel
      have hl : raw2600step0Labels = raw2600Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2600 raw2600Labels permutation688 permutation6
    mixedMoment B raw2600step0 raw2600step0Labels = mixedMoment B raw2600step1 raw2600step1Labels := by
      have ha : raw2600step1 = raw2600step0 := by apply Matrix.ext; unfold raw2600step1 raw2600step0; decide +kernel
      have hl : raw2600step0Labels = labelEmbedding1 ∘ raw2600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2600step0 raw2600step0Labels raw2600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5380 node5380Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3721 node3721Labels + mixedMoment B node3836 node3836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2433 singletonSmall5380
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5380) = raw2433Labels := by decide +kernel
  rw [hl, canonical2433 B hB] at h
  have hc0 : mixedMoment B raw2433 (Fin.cases (0 : Fin 2) singletonSmall5380) =
      mixedMoment B node3721 node3721Labels := by
    have ha : raw2433 = raw2434 := by apply Matrix.ext; unfold raw2433 raw2434; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5380 = raw2434Labels := by decide +kernel
    rw [ha, hj, canonical2434 B hB]
  have hc1 : mixedMoment B raw2433 (Fin.cases (1 : Fin 2) singletonSmall5380) =
      mixedMoment B node3836 node3836Labels := by
    have ha : raw2433 = raw2435 := by apply Matrix.ext; unfold raw2433 raw2435; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5380 = raw2435Labels := by decide +kernel
    rw [ha, hj, canonical2435 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5403 node5403Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3789 node3789Labels + mixedMoment B node3810 node3810Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2478 singletonSmall5403
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5403) = raw2478Labels := by decide +kernel
  rw [hl, canonical2478 B hB] at h
  have hc0 : mixedMoment B raw2478 (Fin.cases (0 : Fin 2) singletonSmall5403) =
      mixedMoment B node3789 node3789Labels := by
    have ha : raw2478 = raw2479 := by apply Matrix.ext; unfold raw2478 raw2479; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5403 = raw2479Labels := by decide +kernel
    rw [ha, hj, canonical2479 B hB]
  have hc1 : mixedMoment B raw2478 (Fin.cases (1 : Fin 2) singletonSmall5403) =
      mixedMoment B node3810 node3810Labels := by
    have ha : raw2478 = raw2480 := by apply Matrix.ext; unfold raw2478 raw2480; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5403 = raw2480Labels := by decide +kernel
    rw [ha, hj, canonical2480 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5406 node5406Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3801 node3801Labels + mixedMoment B node3812 node3812Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2487 singletonSmall5406
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5406) = raw2487Labels := by decide +kernel
  rw [hl, canonical2487 B hB] at h
  have hc0 : mixedMoment B raw2487 (Fin.cases (0 : Fin 2) singletonSmall5406) =
      mixedMoment B node3801 node3801Labels := by
    have ha : raw2487 = raw2488 := by apply Matrix.ext; unfold raw2487 raw2488; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5406 = raw2488Labels := by decide +kernel
    rw [ha, hj, canonical2488 B hB]
  have hc1 : mixedMoment B raw2487 (Fin.cases (1 : Fin 2) singletonSmall5406) =
      mixedMoment B node3812 node3812Labels := by
    have ha : raw2487 = raw2489 := by apply Matrix.ext; unfold raw2487 raw2489; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5406 = raw2489Labels := by decide +kernel
    rw [ha, hj, canonical2489 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5422 node5422Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3964 node3964Labels + mixedMoment B node3900 node3900Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2508 singletonSmall5422
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5422) = raw2508Labels := by decide +kernel
  rw [hl, canonical2508 B hB] at h
  have hc0 : mixedMoment B raw2508 (Fin.cases (0 : Fin 2) singletonSmall5422) =
      mixedMoment B node3964 node3964Labels := by
    have ha : raw2508 = raw2509 := by apply Matrix.ext; unfold raw2508 raw2509; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5422 = raw2509Labels := by decide +kernel
    rw [ha, hj, canonical2509 B hB]
  have hc1 : mixedMoment B raw2508 (Fin.cases (1 : Fin 2) singletonSmall5422) =
      mixedMoment B node3900 node3900Labels := by
    have ha : raw2508 = raw2510 := by apply Matrix.ext; unfold raw2508 raw2510; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5422 = raw2510Labels := by decide +kernel
    rw [ha, hj, canonical2510 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5424 node5424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3838 node3838Labels + mixedMoment B node3843 node3843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2514 singletonSmall5424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5424) = raw2514Labels := by decide +kernel
  rw [hl, canonical2514 B hB] at h
  have hc0 : mixedMoment B raw2514 (Fin.cases (0 : Fin 2) singletonSmall5424) =
      mixedMoment B node3838 node3838Labels := by
    have ha : raw2514 = raw2515 := by apply Matrix.ext; unfold raw2514 raw2515; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5424 = raw2515Labels := by decide +kernel
    rw [ha, hj, canonical2515 B hB]
  have hc1 : mixedMoment B raw2514 (Fin.cases (1 : Fin 2) singletonSmall5424) =
      mixedMoment B node3843 node3843Labels := by
    have ha : raw2514 = raw2516 := by apply Matrix.ext; unfold raw2514 raw2516; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5424 = raw2516Labels := by decide +kernel
    rw [ha, hj, canonical2516 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5447 node5447Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4025 node4025Labels + mixedMoment B node3909 node3909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2547 singletonSmall5447
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5447) = raw2547Labels := by decide +kernel
  rw [hl, canonical2547 B hB] at h
  have hc0 : mixedMoment B raw2547 (Fin.cases (0 : Fin 2) singletonSmall5447) =
      mixedMoment B node4025 node4025Labels := by
    have ha : raw2547 = raw2548 := by apply Matrix.ext; unfold raw2547 raw2548; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5447 = raw2548Labels := by decide +kernel
    rw [ha, hj, canonical2548 B hB]
  have hc1 : mixedMoment B raw2547 (Fin.cases (1 : Fin 2) singletonSmall5447) =
      mixedMoment B node3909 node3909Labels := by
    have ha : raw2547 = raw2549 := by apply Matrix.ext; unfold raw2547 raw2549; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5447 = raw2549Labels := by decide +kernel
    rw [ha, hj, canonical2549 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5478 node5478Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3974 node3974Labels + mixedMoment B node3974 node3974Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2598 singletonSmall5478
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5478) = raw2598Labels := by decide +kernel
  rw [hl, canonical2598 B hB] at h
  have hc0 : mixedMoment B raw2598 (Fin.cases (0 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2599 := by apply Matrix.ext; unfold raw2598 raw2599; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5478 = raw2599Labels := by decide +kernel
    rw [ha, hj, canonical2599 B hB]
  have hc1 : mixedMoment B raw2598 (Fin.cases (1 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2600 := by apply Matrix.ext; unfold raw2598 raw2600; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5478 = raw2600Labels := by decide +kernel
    rw [ha, hj, canonical2600 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = 0 := by
  exact mixedMoment_alpha B hF node5481 node5481Labels 2 permutation158
    (by decide +kernel)

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

theorem sound2615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2615 node2615Labels = Sparse.eval nodeValue2615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2615) = mixedMoment B node2615 node2615Labels := rfl
  simpa [nodeValue2615, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2916 node2916Labels = Sparse.eval nodeValue2916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2916) = mixedMoment B node2916 node2916Labels := rfl
  simpa [nodeValue2916, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2951 node2951Labels = Sparse.eval nodeValue2951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2951) = mixedMoment B node2951 node2951Labels := rfl
  simpa [nodeValue2951, Sparse.eval] using hc.symm

theorem sound2975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2975 node2975Labels = Sparse.eval nodeValue2975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2975) = mixedMoment B node2975 node2975Labels := rfl
  simpa [nodeValue2975, Sparse.eval] using hc.symm

theorem sound2977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2977 node2977Labels = Sparse.eval nodeValue2977 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2977) = mixedMoment B node2977 node2977Labels := rfl
  simpa [nodeValue2977, Sparse.eval] using hc.symm

theorem sound2984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2984 node2984Labels = Sparse.eval nodeValue2984 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2984) = mixedMoment B node2984 node2984Labels := rfl
  simpa [nodeValue2984, Sparse.eval] using hc.symm

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

theorem sound3066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3066 node3066Labels = Sparse.eval nodeValue3066 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3066) = mixedMoment B node3066 node3066Labels := rfl
  simpa [nodeValue3066, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3091 node3091Labels = Sparse.eval nodeValue3091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3091) = mixedMoment B node3091 node3091Labels := rfl
  simpa [nodeValue3091, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3172 node3172Labels = Sparse.eval nodeValue3172 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3172) = mixedMoment B node3172 node3172Labels := rfl
  simpa [nodeValue3172, Sparse.eval] using hc.symm

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

theorem sound3716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3716 node3716Labels = Sparse.eval nodeValue3716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3716) = mixedMoment B node3716 node3716Labels := rfl
  simpa [nodeValue3716, Sparse.eval] using hc.symm

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3723 node3723Labels = Sparse.eval nodeValue3723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3723) = mixedMoment B node3723 node3723Labels := rfl
  simpa [nodeValue3723, Sparse.eval] using hc.symm

theorem sound3724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3724 node3724Labels = Sparse.eval nodeValue3724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3724) = mixedMoment B node3724 node3724Labels := rfl
  simpa [nodeValue3724, Sparse.eval] using hc.symm

theorem sound3725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3725 node3725Labels = Sparse.eval nodeValue3725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3725) = mixedMoment B node3725 node3725Labels := rfl
  simpa [nodeValue3725, Sparse.eval] using hc.symm

theorem sound3730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3730 node3730Labels = Sparse.eval nodeValue3730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3730) = mixedMoment B node3730 node3730Labels := rfl
  simpa [nodeValue3730, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3783 node3783Labels = Sparse.eval nodeValue3783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3783) = mixedMoment B node3783 node3783Labels := rfl
  simpa [nodeValue3783, Sparse.eval] using hc.symm

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3789 node3789Labels = Sparse.eval nodeValue3789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3789) = mixedMoment B node3789 node3789Labels := rfl
  simpa [nodeValue3789, Sparse.eval] using hc.symm

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3810 node3810Labels = Sparse.eval nodeValue3810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3810) = mixedMoment B node3810 node3810Labels := rfl
  simpa [nodeValue3810, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3826 node3826Labels = Sparse.eval nodeValue3826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3826) = mixedMoment B node3826 node3826Labels := rfl
  simpa [nodeValue3826, Sparse.eval] using hc.symm

theorem sound3828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3828 node3828Labels = Sparse.eval nodeValue3828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3828) = mixedMoment B node3828 node3828Labels := rfl
  simpa [nodeValue3828, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

theorem sound3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3900 node3900Labels = Sparse.eval nodeValue3900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3900) = mixedMoment B node3900 node3900Labels := rfl
  simpa [nodeValue3900, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3944 node3944Labels = 0 := by
  exact mixedMoment_alpha B hF node3944 node3944Labels 1 permutation202
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

theorem sound3927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3927 node3927Labels = Sparse.eval nodeValue3927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3927) = mixedMoment B node3927 node3927Labels := rfl
  simpa [nodeValue3927, Sparse.eval] using hc.symm

theorem sound3944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3944 node3944Labels = Sparse.eval nodeValue3944 (mixedVector B) := by
  simpa only [nodeValue3944, Sparse.eval_nil] using zero3944 B _hB _hF

theorem sound3946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3946 node3946Labels = Sparse.eval nodeValue3946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3946) = mixedMoment B node3946 node3946Labels := rfl
  simpa [nodeValue3946, Sparse.eval] using hc.symm

theorem sound3949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3949 node3949Labels = Sparse.eval nodeValue3949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3949) = mixedMoment B node3949 node3949Labels := rfl
  simpa [nodeValue3949, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = 0 := by
  exact mixedMoment_alpha B hF node4008 node4008Labels 1 permutation213
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3972 node3972Labels = Sparse.eval nodeValue3972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3972) = mixedMoment B node3972 node3972Labels := rfl
  simpa [nodeValue3972, Sparse.eval] using hc.symm

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

theorem sound3978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3978 node3978Labels = Sparse.eval nodeValue3978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3978) = mixedMoment B node3978 node3978Labels := rfl
  simpa [nodeValue3978, Sparse.eval] using hc.symm

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

theorem sound4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4008 node4008Labels = Sparse.eval nodeValue4008 (mixedVector B) := by
  simpa only [nodeValue4008, Sparse.eval_nil] using zero4008 B _hB _hF

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4044 node4044Labels = 0 := by
  exact mixedMoment_alpha B hF node4044 node4044Labels 0 permutation499
    (by decide +kernel)

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

theorem sound4044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4044 node4044Labels = Sparse.eval nodeValue4044 (mixedVector B) := by
  simpa only [nodeValue4044, Sparse.eval_nil] using zero4044 B _hB _hF

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4797 node4797Labels = Sparse.eval nodeValue4797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4797) = mixedMoment B node4797 node4797Labels := rfl
  simpa [nodeValue4797, Sparse.eval] using hc.symm

theorem sound4799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4799 node4799Labels = Sparse.eval nodeValue4799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4799) = mixedMoment B node4799 node4799Labels := rfl
  simpa [nodeValue4799, Sparse.eval] using hc.symm

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

theorem sound4803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4803 node4803Labels = Sparse.eval nodeValue4803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4803) = mixedMoment B node4803 node4803Labels := rfl
  simpa [nodeValue4803, Sparse.eval] using hc.symm

theorem sound4825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4825 node4825Labels = Sparse.eval nodeValue4825 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4825) = mixedMoment B node4825 node4825Labels := rfl
  simpa [nodeValue4825, Sparse.eval] using hc.symm

theorem sound4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4851 node4851Labels = Sparse.eval nodeValue4851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4851) = mixedMoment B node4851 node4851Labels := rfl
  simpa [nodeValue4851, Sparse.eval] using hc.symm

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

theorem sound5129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5129 node5129Labels = Sparse.eval nodeValue5129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5129) = mixedMoment B node5129 node5129Labels := rfl
  simpa [nodeValue5129, Sparse.eval] using hc.symm

theorem sound5132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5132 node5132Labels = Sparse.eval nodeValue5132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5132) = mixedMoment B node5132 node5132Labels := rfl
  simpa [nodeValue5132, Sparse.eval] using hc.symm

theorem sound5144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5144 node5144Labels = Sparse.eval nodeValue5144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5144) = mixedMoment B node5144 node5144Labels := rfl
  simpa [nodeValue5144, Sparse.eval] using hc.symm

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

theorem sound5249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5249 node5249Labels = Sparse.eval nodeValue5249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5249) = mixedMoment B node5249 node5249Labels := rfl
  simpa [nodeValue5249, Sparse.eval] using hc.symm

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

theorem sound5350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5350 node5350Labels = Sparse.eval nodeValue5350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5350) = mixedMoment B node5350 node5350Labels := rfl
  simpa [nodeValue5350, Sparse.eval] using hc.symm

theorem sound5353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5353 node5353Labels = Sparse.eval nodeValue5353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5353) = mixedMoment B node5353 node5353Labels := rfl
  simpa [nodeValue5353, Sparse.eval] using hc.symm

theorem sound5362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5362 node5362Labels = Sparse.eval nodeValue5362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5362) = mixedMoment B node5362 node5362Labels := rfl
  simpa [nodeValue5362, Sparse.eval] using hc.symm

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

theorem sound5377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5377 node5377Labels = Sparse.eval nodeValue5377 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5377) = mixedMoment B node5377 node5377Labels := rfl
  simpa [nodeValue5377, Sparse.eval] using hc.symm

theorem sound5379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5379 node5379Labels = Sparse.eval nodeValue5379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5379) = mixedMoment B node5379 node5379Labels := rfl
  simpa [nodeValue5379, Sparse.eval] using hc.symm

theorem sound5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5380 node5380Labels = Sparse.eval nodeValue5380 (mixedVector B) := by
  have h := singleton5380 B _hB
  rw [sound3721 B _hB _hF, sound3836 B _hB _hF] at h
  norm_num [nodeValue5380, nodeValue3721, nodeValue3836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5403 node5403Labels = Sparse.eval nodeValue5403 (mixedVector B) := by
  have h := singleton5403 B _hB
  rw [sound3789 B _hB _hF, sound3810 B _hB _hF] at h
  norm_num [nodeValue5403, nodeValue3789, nodeValue3810, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5414 node5414Labels = Sparse.eval nodeValue5414 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5414) = mixedMoment B node5414 node5414Labels := rfl
  simpa [nodeValue5414, Sparse.eval] using hc.symm

theorem sound5419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5419 node5419Labels = Sparse.eval nodeValue5419 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5419) = mixedMoment B node5419 node5419Labels := rfl
  simpa [nodeValue5419, Sparse.eval] using hc.symm

theorem sound5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5422 node5422Labels = Sparse.eval nodeValue5422 (mixedVector B) := by
  have h := singleton5422 B _hB
  rw [sound3900 B _hB _hF, sound3964 B _hB _hF] at h
  norm_num [nodeValue5422, nodeValue3900, nodeValue3964, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5425 node5425Labels = Sparse.eval nodeValue5425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5425) = mixedMoment B node5425 node5425Labels := rfl
  simpa [nodeValue5425, Sparse.eval] using hc.symm

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5480 node5480Labels = Sparse.eval nodeValue5480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5480) = mixedMoment B node5480 node5480Labels := rfl
  simpa [nodeValue5480, Sparse.eval] using hc.symm

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources30
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm973 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA973 + difference 0 0) (sourceB973 + difference 0 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA973 + difference 0 0) (sourceB973 + difference 0 0) sourceC973) = raw16003 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16003; decide +kernel
    rw [ha]
    exact (canonical16003 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA973 + difference 0 1) (sourceB973 + difference 1 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA973 + difference 0 1) (sourceB973 + difference 1 0) sourceC973) = raw16004 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16004; decide +kernel
    rw [ha]
    exact (canonical16004 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA973 + difference 0 2) (sourceB973 + difference 2 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA973 + difference 0 2) (sourceB973 + difference 2 0) sourceC973) = raw16005 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16005; decide +kernel
    rw [ha]
    exact (canonical16005 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA973 + difference 0 3) (sourceB973 + difference 3 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3927) := by
    have ha : (tripleCharges (sourceA973 + difference 0 3) (sourceB973 + difference 3 0) sourceC973) = raw16006 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16006; decide +kernel
    rw [ha]
    exact (canonical16006 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA973 + difference 0 4) (sourceB973 + difference 4 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA973 + difference 0 4) (sourceB973 + difference 4 0) sourceC973) = raw16007 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16007; decide +kernel
    rw [ha]
    exact (canonical16007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA973 + difference 0 5) (sourceB973 + difference 5 0) sourceC973) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA973 + difference 0 5) (sourceB973 + difference 5 0) sourceC973) = raw16008 := by
      apply Matrix.ext; unfold tripleCharges sourceA973 sourceB973 sourceC973 difference raw16008; decide +kernel
    rw [ha]
    exact (canonical16008 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA973 + sourceB973) sourceC973) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA973 + sourceB973) sourceC973) = raw16009 := by
      apply Matrix.ext; unfold doubleCharges sourceA973 sourceB973 sourceC973 raw16009; decide +kernel
    rw [ha]
    exact (canonical16009 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA973 sourceB973 sourceC973
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm973, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq976 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm976 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA976 + difference 0 2) (sourceB976 + difference 2 0) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA976 + difference 0 2) (sourceB976 + difference 2 0) sourceC976) = raw16005 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16005; decide +kernel
    rw [ha]
    exact (canonical16005 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA976 + difference 1 2) (sourceB976 + difference 2 1) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA976 + difference 1 2) (sourceB976 + difference 2 1) sourceC976) = raw16018 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16018; decide +kernel
    rw [ha]
    exact (canonical16018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA976 + difference 2 2) (sourceB976 + difference 2 2) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA976 + difference 2 2) (sourceB976 + difference 2 2) sourceC976) = raw16003 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16003; decide +kernel
    rw [ha]
    exact (canonical16003 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA976 + difference 3 2) (sourceB976 + difference 2 3) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA976 + difference 3 2) (sourceB976 + difference 2 3) sourceC976) = raw16019 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16019; decide +kernel
    rw [ha]
    exact (canonical16019 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA976 + difference 4 2) (sourceB976 + difference 2 4) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA976 + difference 4 2) (sourceB976 + difference 2 4) sourceC976) = raw16020 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16020; decide +kernel
    rw [ha]
    exact (canonical16020 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA976 + difference 5 2) (sourceB976 + difference 2 5) sourceC976) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA976 + difference 5 2) (sourceB976 + difference 2 5) sourceC976) = raw16021 := by
      apply Matrix.ext; unfold tripleCharges sourceA976 sourceB976 sourceC976 difference raw16021; decide +kernel
    rw [ha]
    exact (canonical16021 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA976 + sourceB976) sourceC976) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA976 + sourceB976) sourceC976) = raw16009 := by
      apply Matrix.ext; unfold doubleCharges sourceA976 sourceB976 sourceC976 raw16009; decide +kernel
    rw [ha]
    exact (canonical16009 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA976 sourceB976 sourceC976
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm976, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm977 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA977 + difference 3 0) (sourceB977 + difference 0 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA977 + difference 3 0) (sourceB977 + difference 0 3) sourceC977) = raw16022 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16022; decide +kernel
    rw [ha]
    exact (canonical16022 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA977 + difference 3 1) (sourceB977 + difference 1 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA977 + difference 3 1) (sourceB977 + difference 1 3) sourceC977) = raw16011 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16011; decide +kernel
    rw [ha]
    exact (canonical16011 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA977 + difference 3 2) (sourceB977 + difference 2 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA977 + difference 3 2) (sourceB977 + difference 2 3) sourceC977) = raw16019 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16019; decide +kernel
    rw [ha]
    exact (canonical16019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA977 + difference 3 3) (sourceB977 + difference 3 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA977 + difference 3 3) (sourceB977 + difference 3 3) sourceC977) = raw16003 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16003; decide +kernel
    rw [ha]
    exact (canonical16003 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA977 + difference 3 4) (sourceB977 + difference 4 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA977 + difference 3 4) (sourceB977 + difference 4 3) sourceC977) = raw16023 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16023; decide +kernel
    rw [ha]
    exact (canonical16023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA977 + difference 3 5) (sourceB977 + difference 5 3) sourceC977) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA977 + difference 3 5) (sourceB977 + difference 5 3) sourceC977) = raw16024 := by
      apply Matrix.ext; unfold tripleCharges sourceA977 sourceB977 sourceC977 difference raw16024; decide +kernel
    rw [ha]
    exact (canonical16024 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA977 + sourceB977) sourceC977) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA977 + sourceB977) sourceC977) = raw16009 := by
      apply Matrix.ext; unfold doubleCharges sourceA977 sourceB977 sourceC977 raw16009; decide +kernel
    rw [ha]
    exact (canonical16009 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA977 sourceB977 sourceC977
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm977, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq978 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm978 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA978 + difference 0 1) (sourceB978 + difference 1 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA978 + difference 0 1) (sourceB978 + difference 1 0) sourceC978) = raw16025 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16025; decide +kernel
    rw [ha]
    exact (canonical16025 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA978 + difference 0 2) (sourceB978 + difference 2 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA978 + difference 0 2) (sourceB978 + difference 2 0) sourceC978) = raw16026 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16026; decide +kernel
    rw [ha]
    exact (canonical16026 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA978 + difference 0 3) (sourceB978 + difference 3 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA978 + difference 0 3) (sourceB978 + difference 3 0) sourceC978) = raw16027 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16027; decide +kernel
    rw [ha]
    exact (canonical16027 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA978 + difference 0 4) (sourceB978 + difference 4 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA978 + difference 0 4) (sourceB978 + difference 4 0) sourceC978) = raw16028 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16028; decide +kernel
    rw [ha]
    exact (canonical16028 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA978 + difference 0 5) (sourceB978 + difference 5 0) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA978 + difference 0 5) (sourceB978 + difference 5 0) sourceC978) = raw16029 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16029; decide +kernel
    rw [ha]
    exact (canonical16029 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA978 + difference 1 0) (sourceB978 + difference 0 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA978 + difference 1 0) (sourceB978 + difference 0 1) sourceC978) = raw16030 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16030; decide +kernel
    rw [ha]
    exact (canonical16030 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA978 + difference 1 2) (sourceB978 + difference 2 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA978 + difference 1 2) (sourceB978 + difference 2 1) sourceC978) = raw16031 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16031; decide +kernel
    rw [ha]
    exact (canonical16031 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA978 + difference 1 3) (sourceB978 + difference 3 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA978 + difference 1 3) (sourceB978 + difference 3 1) sourceC978) = raw16032 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16032; decide +kernel
    rw [ha]
    exact (canonical16032 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA978 + difference 1 4) (sourceB978 + difference 4 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA978 + difference 1 4) (sourceB978 + difference 4 1) sourceC978) = raw16033 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16033; decide +kernel
    rw [ha]
    exact (canonical16033 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA978 + difference 1 5) (sourceB978 + difference 5 1) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA978 + difference 1 5) (sourceB978 + difference 5 1) sourceC978) = raw16034 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16034; decide +kernel
    rw [ha]
    exact (canonical16034 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA978 + difference 2 0) (sourceB978 + difference 0 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA978 + difference 2 0) (sourceB978 + difference 0 2) sourceC978) = raw16035 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16035; decide +kernel
    rw [ha]
    exact (canonical16035 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA978 + difference 2 1) (sourceB978 + difference 1 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA978 + difference 2 1) (sourceB978 + difference 1 2) sourceC978) = raw16036 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16036; decide +kernel
    rw [ha]
    exact (canonical16036 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA978 + difference 2 3) (sourceB978 + difference 3 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA978 + difference 2 3) (sourceB978 + difference 3 2) sourceC978) = raw16037 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16037; decide +kernel
    rw [ha]
    exact (canonical16037 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA978 + difference 2 4) (sourceB978 + difference 4 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA978 + difference 2 4) (sourceB978 + difference 4 2) sourceC978) = raw16038 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16038; decide +kernel
    rw [ha]
    exact (canonical16038 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA978 + difference 2 5) (sourceB978 + difference 5 2) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA978 + difference 2 5) (sourceB978 + difference 5 2) sourceC978) = raw16039 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16039; decide +kernel
    rw [ha]
    exact (canonical16039 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA978 + difference 3 0) (sourceB978 + difference 0 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA978 + difference 3 0) (sourceB978 + difference 0 3) sourceC978) = raw16040 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16040; decide +kernel
    rw [ha]
    exact (canonical16040 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA978 + difference 3 1) (sourceB978 + difference 1 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA978 + difference 3 1) (sourceB978 + difference 1 3) sourceC978) = raw16041 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16041; decide +kernel
    rw [ha]
    exact (canonical16041 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA978 + difference 3 2) (sourceB978 + difference 2 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA978 + difference 3 2) (sourceB978 + difference 2 3) sourceC978) = raw16042 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16042; decide +kernel
    rw [ha]
    exact (canonical16042 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA978 + difference 3 4) (sourceB978 + difference 4 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA978 + difference 3 4) (sourceB978 + difference 4 3) sourceC978) = raw16043 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16043; decide +kernel
    rw [ha]
    exact (canonical16043 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA978 + difference 3 5) (sourceB978 + difference 5 3) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA978 + difference 3 5) (sourceB978 + difference 5 3) sourceC978) = raw16044 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16044; decide +kernel
    rw [ha]
    exact (canonical16044 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA978 + difference 4 0) (sourceB978 + difference 0 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4825) := by
    have ha : (tripleCharges (sourceA978 + difference 4 0) (sourceB978 + difference 0 4) sourceC978) = raw16045 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16045; decide +kernel
    rw [ha]
    exact (canonical16045 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA978 + difference 4 1) (sourceB978 + difference 1 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA978 + difference 4 1) (sourceB978 + difference 1 4) sourceC978) = raw16046 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16046; decide +kernel
    rw [ha]
    exact (canonical16046 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA978 + difference 4 2) (sourceB978 + difference 2 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5362) := by
    have ha : (tripleCharges (sourceA978 + difference 4 2) (sourceB978 + difference 2 4) sourceC978) = raw16047 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16047; decide +kernel
    rw [ha]
    exact (canonical16047 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA978 + difference 4 3) (sourceB978 + difference 3 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA978 + difference 4 3) (sourceB978 + difference 3 4) sourceC978) = raw16048 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16048; decide +kernel
    rw [ha]
    exact (canonical16048 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA978 + difference 4 5) (sourceB978 + difference 5 4) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA978 + difference 4 5) (sourceB978 + difference 5 4) sourceC978) = raw16049 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16049; decide +kernel
    rw [ha]
    exact (canonical16049 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA978 + difference 5 0) (sourceB978 + difference 0 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4797) := by
    have ha : (tripleCharges (sourceA978 + difference 5 0) (sourceB978 + difference 0 5) sourceC978) = raw16050 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16050; decide +kernel
    rw [ha]
    exact (canonical16050 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA978 + difference 5 1) (sourceB978 + difference 1 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA978 + difference 5 1) (sourceB978 + difference 1 5) sourceC978) = raw16051 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16051; decide +kernel
    rw [ha]
    exact (canonical16051 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA978 + difference 5 2) (sourceB978 + difference 2 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5132) := by
    have ha : (tripleCharges (sourceA978 + difference 5 2) (sourceB978 + difference 2 5) sourceC978) = raw16052 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16052; decide +kernel
    rw [ha]
    exact (canonical16052 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA978 + difference 5 3) (sourceB978 + difference 3 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA978 + difference 5 3) (sourceB978 + difference 3 5) sourceC978) = raw16053 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16053; decide +kernel
    rw [ha]
    exact (canonical16053 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA978 + difference 5 4) (sourceB978 + difference 4 5) sourceC978) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA978 + difference 5 4) (sourceB978 + difference 4 5) sourceC978) = raw16054 := by
      apply Matrix.ext; unfold tripleCharges sourceA978 sourceB978 sourceC978 difference raw16054; decide +kernel
    rw [ha]
    exact (canonical16054 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA978 sourceB978 sourceC978
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm978, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq982 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm982 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA982 + difference 0 1) (sourceB982 + difference 1 0) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA982 + difference 0 1) (sourceB982 + difference 1 0) sourceC982) = raw16122 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16122; decide +kernel
    rw [ha]
    exact (canonical16122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA982 + difference 1 1) (sourceB982 + difference 1 1) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA982 + difference 1 1) (sourceB982 + difference 1 1) sourceC982) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA982 + difference 2 1) (sourceB982 + difference 1 2) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA982 + difference 2 1) (sourceB982 + difference 1 2) sourceC982) = raw16123 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16123; decide +kernel
    rw [ha]
    exact (canonical16123 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA982 + difference 3 1) (sourceB982 + difference 1 3) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA982 + difference 3 1) (sourceB982 + difference 1 3) sourceC982) = raw16124 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16124; decide +kernel
    rw [ha]
    exact (canonical16124 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA982 + difference 4 1) (sourceB982 + difference 1 4) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3716) := by
    have ha : (tripleCharges (sourceA982 + difference 4 1) (sourceB982 + difference 1 4) sourceC982) = raw16125 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16125; decide +kernel
    rw [ha]
    exact (canonical16125 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA982 + difference 5 1) (sourceB982 + difference 1 5) sourceC982) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA982 + difference 5 1) (sourceB982 + difference 1 5) sourceC982) = raw16126 := by
      apply Matrix.ext; unfold tripleCharges sourceA982 sourceB982 sourceC982 difference raw16126; decide +kernel
    rw [ha]
    exact (canonical16126 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA982 + sourceB982) sourceC982) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA982 + sourceB982) sourceC982) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA982 sourceB982 sourceC982 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA982 sourceB982 sourceC982
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm982, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq983 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm983 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA983 + difference 2 0) (sourceB983 + difference 0 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA983 + difference 2 0) (sourceB983 + difference 0 2) sourceC983) = raw16117 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16117; decide +kernel
    rw [ha]
    exact (canonical16117 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA983 + difference 2 1) (sourceB983 + difference 1 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA983 + difference 2 1) (sourceB983 + difference 1 2) sourceC983) = raw16123 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16123; decide +kernel
    rw [ha]
    exact (canonical16123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA983 + difference 2 2) (sourceB983 + difference 2 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA983 + difference 2 2) (sourceB983 + difference 2 2) sourceC983) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA983 + difference 2 3) (sourceB983 + difference 3 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA983 + difference 2 3) (sourceB983 + difference 3 2) sourceC983) = raw16127 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16127; decide +kernel
    rw [ha]
    exact (canonical16127 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA983 + difference 2 4) (sourceB983 + difference 4 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA983 + difference 2 4) (sourceB983 + difference 4 2) sourceC983) = raw16128 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16128; decide +kernel
    rw [ha]
    exact (canonical16128 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA983 + difference 2 5) (sourceB983 + difference 5 2) sourceC983) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA983 + difference 2 5) (sourceB983 + difference 5 2) sourceC983) = raw16129 := by
      apply Matrix.ext; unfold tripleCharges sourceA983 sourceB983 sourceC983 difference raw16129; decide +kernel
    rw [ha]
    exact (canonical16129 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA983 + sourceB983) sourceC983) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA983 + sourceB983) sourceC983) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA983 sourceB983 sourceC983 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA983 sourceB983 sourceC983
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm983, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq986 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm986 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA986 + difference 0 4) (sourceB986 + difference 4 0) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA986 + difference 0 4) (sourceB986 + difference 4 0) sourceC986) = raw16137 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16137; decide +kernel
    rw [ha]
    exact (canonical16137 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA986 + difference 1 4) (sourceB986 + difference 4 1) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA986 + difference 1 4) (sourceB986 + difference 4 1) sourceC986) = raw16138 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16138; decide +kernel
    rw [ha]
    exact (canonical16138 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA986 + difference 2 4) (sourceB986 + difference 4 2) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA986 + difference 2 4) (sourceB986 + difference 4 2) sourceC986) = raw16128 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16128; decide +kernel
    rw [ha]
    exact (canonical16128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA986 + difference 3 4) (sourceB986 + difference 4 3) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA986 + difference 3 4) (sourceB986 + difference 4 3) sourceC986) = raw16139 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16139; decide +kernel
    rw [ha]
    exact (canonical16139 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA986 + difference 4 4) (sourceB986 + difference 4 4) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA986 + difference 4 4) (sourceB986 + difference 4 4) sourceC986) = raw16115 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16115; decide +kernel
    rw [ha]
    exact (canonical16115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA986 + difference 5 4) (sourceB986 + difference 4 5) sourceC986) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA986 + difference 5 4) (sourceB986 + difference 4 5) sourceC986) = raw16140 := by
      apply Matrix.ext; unfold tripleCharges sourceA986 sourceB986 sourceC986 difference raw16140; decide +kernel
    rw [ha]
    exact (canonical16140 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA986 + sourceB986) sourceC986) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA986 + sourceB986) sourceC986) = raw16121 := by
      apply Matrix.ext; unfold doubleCharges sourceA986 sourceB986 sourceC986 raw16121; decide +kernel
    rw [ha]
    exact (canonical16121 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA986 sourceB986 sourceC986
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm986, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq990 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm990 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA990 + difference 0 0) (sourceB990 + difference 0 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA990 + difference 0 0) (sourceB990 + difference 0 0) sourceC990) = raw16206 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16206; decide +kernel
    rw [ha]
    exact (canonical16206 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA990 + difference 0 1) (sourceB990 + difference 1 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4044) := by
    have ha : (tripleCharges (sourceA990 + difference 0 1) (sourceB990 + difference 1 0) sourceC990) = raw16207 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16207; decide +kernel
    rw [ha]
    exact (canonical16207 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA990 + difference 0 2) (sourceB990 + difference 2 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA990 + difference 0 2) (sourceB990 + difference 2 0) sourceC990) = raw16208 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16208; decide +kernel
    rw [ha]
    exact (canonical16208 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA990 + difference 0 3) (sourceB990 + difference 3 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA990 + difference 0 3) (sourceB990 + difference 3 0) sourceC990) = raw16209 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16209; decide +kernel
    rw [ha]
    exact (canonical16209 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA990 + difference 0 4) (sourceB990 + difference 4 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3944) := by
    have ha : (tripleCharges (sourceA990 + difference 0 4) (sourceB990 + difference 4 0) sourceC990) = raw16210 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16210; decide +kernel
    rw [ha]
    exact (canonical16210 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA990 + difference 0 5) (sourceB990 + difference 5 0) sourceC990) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA990 + difference 0 5) (sourceB990 + difference 5 0) sourceC990) = raw16211 := by
      apply Matrix.ext; unfold tripleCharges sourceA990 sourceB990 sourceC990 difference raw16211; decide +kernel
    rw [ha]
    exact (canonical16211 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA990 + sourceB990) sourceC990) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA990 + sourceB990) sourceC990) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA990 sourceB990 sourceC990 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA990 sourceB990 sourceC990
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm990, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq991 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm991 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA991 + difference 0 2) (sourceB991 + difference 2 0) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA991 + difference 0 2) (sourceB991 + difference 2 0) sourceC991) = raw16208 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16208; decide +kernel
    rw [ha]
    exact (canonical16208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA991 + difference 1 2) (sourceB991 + difference 2 1) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2977) := by
    have ha : (tripleCharges (sourceA991 + difference 1 2) (sourceB991 + difference 2 1) sourceC991) = raw16212 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16212; decide +kernel
    rw [ha]
    exact (canonical16212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA991 + difference 2 2) (sourceB991 + difference 2 2) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA991 + difference 2 2) (sourceB991 + difference 2 2) sourceC991) = raw16206 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16206; decide +kernel
    rw [ha]
    exact (canonical16206 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA991 + difference 3 2) (sourceB991 + difference 2 3) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3725) := by
    have ha : (tripleCharges (sourceA991 + difference 3 2) (sourceB991 + difference 2 3) sourceC991) = raw16213 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16213; decide +kernel
    rw [ha]
    exact (canonical16213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA991 + difference 4 2) (sourceB991 + difference 2 4) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA991 + difference 4 2) (sourceB991 + difference 2 4) sourceC991) = raw16214 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16214; decide +kernel
    rw [ha]
    exact (canonical16214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA991 + difference 5 2) (sourceB991 + difference 2 5) sourceC991) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA991 + difference 5 2) (sourceB991 + difference 2 5) sourceC991) = raw16215 := by
      apply Matrix.ext; unfold tripleCharges sourceA991 sourceB991 sourceC991 difference raw16215; decide +kernel
    rw [ha]
    exact (canonical16215 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA991 + sourceB991) sourceC991) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA991 + sourceB991) sourceC991) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA991 sourceB991 sourceC991 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA991 sourceB991 sourceC991
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm991, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources31
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq992 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm992 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA992 + difference 0 4) (sourceB992 + difference 4 0) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3944) := by
    have ha : (tripleCharges (sourceA992 + difference 0 4) (sourceB992 + difference 4 0) sourceC992) = raw16210 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16210; decide +kernel
    rw [ha]
    exact (canonical16210 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA992 + difference 1 4) (sourceB992 + difference 4 1) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2975) := by
    have ha : (tripleCharges (sourceA992 + difference 1 4) (sourceB992 + difference 4 1) sourceC992) = raw16216 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16216; decide +kernel
    rw [ha]
    exact (canonical16216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA992 + difference 2 4) (sourceB992 + difference 4 2) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA992 + difference 2 4) (sourceB992 + difference 4 2) sourceC992) = raw15744 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw15744; decide +kernel
    rw [ha]
    exact (canonical15744 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA992 + difference 3 4) (sourceB992 + difference 4 3) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3828) := by
    have ha : (tripleCharges (sourceA992 + difference 3 4) (sourceB992 + difference 4 3) sourceC992) = raw16217 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16217; decide +kernel
    rw [ha]
    exact (canonical16217 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA992 + difference 4 4) (sourceB992 + difference 4 4) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA992 + difference 4 4) (sourceB992 + difference 4 4) sourceC992) = raw16206 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16206; decide +kernel
    rw [ha]
    exact (canonical16206 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA992 + difference 5 4) (sourceB992 + difference 4 5) sourceC992) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3826) := by
    have ha : (tripleCharges (sourceA992 + difference 5 4) (sourceB992 + difference 4 5) sourceC992) = raw16218 := by
      apply Matrix.ext; unfold tripleCharges sourceA992 sourceB992 sourceC992 difference raw16218; decide +kernel
    rw [ha]
    exact (canonical16218 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA992 + sourceB992) sourceC992) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA992 + sourceB992) sourceC992) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA992 sourceB992 sourceC992 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA992 sourceB992 sourceC992
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm992, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck848 : Integer.Sparse.reindex keyMap MixedData.row848 = numericRow848 := by decide +kernel

theorem numericCheck848 (x : Master → ℝ) : Integer.Sparse.eval numericRow848 x =
    (1 : ℝ) * reducedSource848 x := by
  norm_num [numericRow848, reducedSource848, Integer.Sparse.eval, Sparse.eval, nodeValue2951, nodeValue3871, nodeValue3927, nodeValue3974, nodeValue3978, nodeValue3983, nodeValue4091]

theorem reindexCheck849 : Integer.Sparse.reindex keyMap MixedData.row849 = numericRow849 := by decide +kernel

theorem numericCheck849 (x : Master → ℝ) : Integer.Sparse.eval numericRow849 x =
    (1 : ℝ) * reducedSource849 x := by
  norm_num [numericRow849, reducedSource849, Integer.Sparse.eval, Sparse.eval, nodeValue2984, nodeValue3783, nodeValue3787, nodeValue3800, nodeValue3871, nodeValue3978, nodeValue4091]

theorem reindexCheck850 : Integer.Sparse.reindex keyMap MixedData.row850 = numericRow850 := by decide +kernel

theorem numericCheck850 (x : Master → ℝ) : Integer.Sparse.eval numericRow850 x =
    (1 : ℝ) * reducedSource850 x := by
  norm_num [numericRow850, reducedSource850, Integer.Sparse.eval, Sparse.eval, nodeValue2615, nodeValue3091, nodeValue3787, nodeValue3871, nodeValue3875, nodeValue3876, nodeValue4091]

theorem reindexCheck851 : Integer.Sparse.reindex keyMap MixedData.row851 = numericRow851 := by decide +kernel

theorem numericCheck851 (x : Master → ℝ) : Integer.Sparse.eval numericRow851 x =
    (17280 : ℝ) * reducedSource851 x := by
  norm_num [numericRow851, reducedSource851, Integer.Sparse.eval, Sparse.eval, nodeValue4797, nodeValue4799, nodeValue4803, nodeValue4825, nodeValue4851, nodeValue5129, nodeValue5132, nodeValue5144, nodeValue5249, nodeValue5350, nodeValue5353, nodeValue5362, nodeValue5377, nodeValue5379, nodeValue5380, nodeValue5403, nodeValue5406, nodeValue5414, nodeValue5419, nodeValue5422, nodeValue5424, nodeValue5425, nodeValue5429, nodeValue5430, nodeValue5447, nodeValue5478, nodeValue5480, nodeValue5481, nodeValue5482] <;> ring

theorem reindexCheck854 : Integer.Sparse.reindex keyMap MixedData.row854 = numericRow854 := by decide +kernel

theorem numericCheck854 (x : Master → ℝ) : Integer.Sparse.eval numericRow854 x =
    (1 : ℝ) * reducedSource854 x := by
  norm_num [numericRow854, reducedSource854, Integer.Sparse.eval, Sparse.eval, nodeValue2916, nodeValue3716, nodeValue3721, nodeValue3724, nodeValue3838, nodeValue3972, nodeValue4091]

theorem reindexCheck855 : Integer.Sparse.reindex keyMap MixedData.row855 = numericRow855 := by decide +kernel

theorem numericCheck855 (x : Master → ℝ) : Integer.Sparse.eval numericRow855 x =
    (1 : ℝ) * reducedSource855 x := by
  norm_num [numericRow855, reducedSource855, Integer.Sparse.eval, Sparse.eval, nodeValue3172, nodeValue3721, nodeValue3964, nodeValue3972, nodeValue4025, nodeValue4091]

theorem reindexCheck856 : Integer.Sparse.reindex keyMap MixedData.row856 = numericRow856 := by decide +kernel

theorem numericCheck856 (x : Master → ℝ) : Integer.Sparse.eval numericRow856 x =
    (1 : ℝ) * reducedSource856 x := by
  norm_num [numericRow856, reducedSource856, Integer.Sparse.eval, Sparse.eval, nodeValue3066, nodeValue3789, nodeValue3949, nodeValue3972, nodeValue4008, nodeValue4091]

theorem reindexCheck860 : Integer.Sparse.reindex keyMap MixedData.row860 = numericRow860 := by decide +kernel

theorem numericCheck860 (x : Master → ℝ) : Integer.Sparse.eval numericRow860 x =
    (1 : ℝ) * reducedSource860 x := by
  norm_num [numericRow860, reducedSource860, Integer.Sparse.eval, Sparse.eval, nodeValue3781, nodeValue3848, nodeValue3944, nodeValue3946, nodeValue3961, nodeValue4044, nodeValue4092]

theorem reindexCheck861 : Integer.Sparse.reindex keyMap MixedData.row861 = numericRow861 := by decide +kernel

theorem numericCheck861 (x : Master → ℝ) : Integer.Sparse.eval numericRow861 x =
    (1 : ℝ) * reducedSource861 x := by
  norm_num [numericRow861, reducedSource861, Integer.Sparse.eval, Sparse.eval, nodeValue2977, nodeValue3723, nodeValue3725, nodeValue3730, nodeValue3848, nodeValue3946, nodeValue4092]

theorem reindexCheck862 : Integer.Sparse.reindex keyMap MixedData.row862 = numericRow862 := by decide +kernel

theorem numericCheck862 (x : Master → ℝ) : Integer.Sparse.eval numericRow862 x =
    (1 : ℝ) * reducedSource862 x := by
  norm_num [numericRow862, reducedSource862, Integer.Sparse.eval, Sparse.eval, nodeValue2975, nodeValue3826, nodeValue3828, nodeValue3848, nodeValue3884, nodeValue3944, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource848 (mixedVector B) = 0 := by
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3927 : mixedVector B (Sum.inr 3927) = Sparse.eval nodeValue3927 (mixedVector B) := by
    change mixedMoment B node3927 node3927Labels = _
    exact sound3927 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm973, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2951, h3871, h3927, h3974, h3978, h3983, h4091, reducedSource848] using sourceEq973 B hB

theorem rowSound848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row848 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck848, numericCheck848, reducedZero848 B hB hF, mul_zero]

theorem reducedZero849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource849 (mixedVector B) = 0 := by
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h3783 : mixedVector B (Sum.inr 3783) = Sparse.eval nodeValue3783 (mixedVector B) := by
    change mixedMoment B node3783 node3783Labels = _
    exact sound3783 B hB hF
  have h3787 : mixedVector B (Sum.inr 3787) = Sparse.eval nodeValue3787 (mixedVector B) := by
    change mixedMoment B node3787 node3787Labels = _
    exact sound3787 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3978 : mixedVector B (Sum.inr 3978) = Sparse.eval nodeValue3978 (mixedVector B) := by
    change mixedMoment B node3978 node3978Labels = _
    exact sound3978 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm976, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2984, h3783, h3787, h3800, h3871, h3978, h4091, reducedSource849] using sourceEq976 B hB

theorem rowSound849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row849 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck849, numericCheck849, reducedZero849 B hB hF, mul_zero]

theorem reducedZero850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource850 (mixedVector B) = 0 := by
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3787 : mixedVector B (Sum.inr 3787) = Sparse.eval nodeValue3787 (mixedVector B) := by
    change mixedMoment B node3787 node3787Labels = _
    exact sound3787 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm977, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2615, h3091, h3787, h3871, h3875, h3876, h4091, reducedSource850] using sourceEq977 B hB

theorem rowSound850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row850 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck850, numericCheck850, reducedZero850 B hB hF, mul_zero]

theorem reducedZero851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource851 (mixedVector B) = 0 := by
  have h4797 : mixedVector B (Sum.inr 4797) = Sparse.eval nodeValue4797 (mixedVector B) := by
    change mixedMoment B node4797 node4797Labels = _
    exact sound4797 B hB hF
  have h4799 : mixedVector B (Sum.inr 4799) = Sparse.eval nodeValue4799 (mixedVector B) := by
    change mixedMoment B node4799 node4799Labels = _
    exact sound4799 B hB hF
  have h4803 : mixedVector B (Sum.inr 4803) = Sparse.eval nodeValue4803 (mixedVector B) := by
    change mixedMoment B node4803 node4803Labels = _
    exact sound4803 B hB hF
  have h4825 : mixedVector B (Sum.inr 4825) = Sparse.eval nodeValue4825 (mixedVector B) := by
    change mixedMoment B node4825 node4825Labels = _
    exact sound4825 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h5129 : mixedVector B (Sum.inr 5129) = Sparse.eval nodeValue5129 (mixedVector B) := by
    change mixedMoment B node5129 node5129Labels = _
    exact sound5129 B hB hF
  have h5132 : mixedVector B (Sum.inr 5132) = Sparse.eval nodeValue5132 (mixedVector B) := by
    change mixedMoment B node5132 node5132Labels = _
    exact sound5132 B hB hF
  have h5144 : mixedVector B (Sum.inr 5144) = Sparse.eval nodeValue5144 (mixedVector B) := by
    change mixedMoment B node5144 node5144Labels = _
    exact sound5144 B hB hF
  have h5249 : mixedVector B (Sum.inr 5249) = Sparse.eval nodeValue5249 (mixedVector B) := by
    change mixedMoment B node5249 node5249Labels = _
    exact sound5249 B hB hF
  have h5350 : mixedVector B (Sum.inr 5350) = Sparse.eval nodeValue5350 (mixedVector B) := by
    change mixedMoment B node5350 node5350Labels = _
    exact sound5350 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5362 : mixedVector B (Sum.inr 5362) = Sparse.eval nodeValue5362 (mixedVector B) := by
    change mixedMoment B node5362 node5362Labels = _
    exact sound5362 B hB hF
  have h5377 : mixedVector B (Sum.inr 5377) = Sparse.eval nodeValue5377 (mixedVector B) := by
    change mixedMoment B node5377 node5377Labels = _
    exact sound5377 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5414 : mixedVector B (Sum.inr 5414) = Sparse.eval nodeValue5414 (mixedVector B) := by
    change mixedMoment B node5414 node5414Labels = _
    exact sound5414 B hB hF
  have h5419 : mixedVector B (Sum.inr 5419) = Sparse.eval nodeValue5419 (mixedVector B) := by
    change mixedMoment B node5419 node5419Labels = _
    exact sound5419 B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5480 : mixedVector B (Sum.inr 5480) = Sparse.eval nodeValue5480 (mixedVector B) := by
    change mixedMoment B node5480 node5480Labels = _
    exact sound5480 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  simpa only [sourceForm978, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4797, h4799, h4803, h4825, h4851, h5129, h5132, h5144, h5249, h5350, h5353, h5362, h5377, h5379, h5380, h5403, h5406, h5414, h5419, h5422, h5424, h5425, h5429, h5430, h5447, h5478, h5480, h5481, h5482, reducedSource851] using sourceEq978 B hB

theorem rowSound851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row851 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck851, numericCheck851, reducedZero851 B hB hF, mul_zero]

theorem reducedZero854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource854 (mixedVector B) = 0 := by
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h3716 : mixedVector B (Sum.inr 3716) = Sparse.eval nodeValue3716 (mixedVector B) := by
    change mixedMoment B node3716 node3716Labels = _
    exact sound3716 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h3724 : mixedVector B (Sum.inr 3724) = Sparse.eval nodeValue3724 (mixedVector B) := by
    change mixedMoment B node3724 node3724Labels = _
    exact sound3724 B hB hF
  have h3838 : mixedVector B (Sum.inr 3838) = Sparse.eval nodeValue3838 (mixedVector B) := by
    change mixedMoment B node3838 node3838Labels = _
    exact sound3838 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm982, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2916, h3716, h3721, h3724, h3838, h3972, h4091, reducedSource854] using sourceEq982 B hB

theorem rowSound854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row854 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck854, numericCheck854, reducedZero854 B hB hF, mul_zero]

theorem reducedZero855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource855 (mixedVector B) = 0 := by
  have h3172 : mixedVector B (Sum.inr 3172) = Sparse.eval nodeValue3172 (mixedVector B) := by
    change mixedMoment B node3172 node3172Labels = _
    exact sound3172 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h3964 : mixedVector B (Sum.inr 3964) = Sparse.eval nodeValue3964 (mixedVector B) := by
    change mixedMoment B node3964 node3964Labels = _
    exact sound3964 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4025 : mixedVector B (Sum.inr 4025) = Sparse.eval nodeValue4025 (mixedVector B) := by
    change mixedMoment B node4025 node4025Labels = _
    exact sound4025 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm983, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3172, h3721, h3964, h3972, h4025, h4091, reducedSource855] using sourceEq983 B hB

theorem rowSound855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row855 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck855, numericCheck855, reducedZero855 B hB hF, mul_zero]

theorem reducedZero856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource856 (mixedVector B) = 0 := by
  have h3066 : mixedVector B (Sum.inr 3066) = Sparse.eval nodeValue3066 (mixedVector B) := by
    change mixedMoment B node3066 node3066Labels = _
    exact sound3066 B hB hF
  have h3789 : mixedVector B (Sum.inr 3789) = Sparse.eval nodeValue3789 (mixedVector B) := by
    change mixedMoment B node3789 node3789Labels = _
    exact sound3789 B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4008 : mixedVector B (Sum.inr 4008) = Sparse.eval nodeValue4008 (mixedVector B) := by
    change mixedMoment B node4008 node4008Labels = _
    exact sound4008 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm986, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3066, h3789, h3949, h3972, h4008, h4091, reducedSource856] using sourceEq986 B hB

theorem rowSound856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row856 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck856, numericCheck856, reducedZero856 B hB hF, mul_zero]

theorem reducedZero860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource860 (mixedVector B) = 0 := by
  have h3781 : mixedVector B (Sum.inr 3781) = Sparse.eval nodeValue3781 (mixedVector B) := by
    change mixedMoment B node3781 node3781Labels = _
    exact sound3781 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3944 : mixedVector B (Sum.inr 3944) = Sparse.eval nodeValue3944 (mixedVector B) := by
    change mixedMoment B node3944 node3944Labels = _
    exact sound3944 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4044 : mixedVector B (Sum.inr 4044) = Sparse.eval nodeValue4044 (mixedVector B) := by
    change mixedMoment B node4044 node4044Labels = _
    exact sound4044 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm990, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3781, h3848, h3944, h3946, h3961, h4044, h4092, reducedSource860] using sourceEq990 B hB

theorem rowSound860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row860 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck860, numericCheck860, reducedZero860 B hB hF, mul_zero]

theorem reducedZero861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource861 (mixedVector B) = 0 := by
  have h2977 : mixedVector B (Sum.inr 2977) = Sparse.eval nodeValue2977 (mixedVector B) := by
    change mixedMoment B node2977 node2977Labels = _
    exact sound2977 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3725 : mixedVector B (Sum.inr 3725) = Sparse.eval nodeValue3725 (mixedVector B) := by
    change mixedMoment B node3725 node3725Labels = _
    exact sound3725 B hB hF
  have h3730 : mixedVector B (Sum.inr 3730) = Sparse.eval nodeValue3730 (mixedVector B) := by
    change mixedMoment B node3730 node3730Labels = _
    exact sound3730 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm991, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2977, h3723, h3725, h3730, h3848, h3946, h4092, reducedSource861] using sourceEq991 B hB

theorem rowSound861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row861 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck861, numericCheck861, reducedZero861 B hB hF, mul_zero]

theorem reducedZero862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource862 (mixedVector B) = 0 := by
  have h2975 : mixedVector B (Sum.inr 2975) = Sparse.eval nodeValue2975 (mixedVector B) := by
    change mixedMoment B node2975 node2975Labels = _
    exact sound2975 B hB hF
  have h3826 : mixedVector B (Sum.inr 3826) = Sparse.eval nodeValue3826 (mixedVector B) := by
    change mixedMoment B node3826 node3826Labels = _
    exact sound3826 B hB hF
  have h3828 : mixedVector B (Sum.inr 3828) = Sparse.eval nodeValue3828 (mixedVector B) := by
    change mixedMoment B node3828 node3828Labels = _
    exact sound3828 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3944 : mixedVector B (Sum.inr 3944) = Sparse.eval nodeValue3944 (mixedVector B) := by
    change mixedMoment B node3944 node3944Labels = _
    exact sound3944 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm992, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2975, h3826, h3828, h3848, h3884, h3944, h4092, reducedSource862] using sourceEq992 B hB

theorem rowSound862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row862 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck862, numericCheck862, reducedZero862 B hB hF, mul_zero]

theorem sourceRowsAt848 : MixedData.sourceRows (848 : Fin 2425) =
    MixedData.row848 := by decide +kernel

theorem sourceRowsAt849 : MixedData.sourceRows (849 : Fin 2425) =
    MixedData.row849 := by decide +kernel

theorem sourceRowsAt850 : MixedData.sourceRows (850 : Fin 2425) =
    MixedData.row850 := by decide +kernel

theorem sourceRowsAt851 : MixedData.sourceRows (851 : Fin 2425) =
    MixedData.row851 := by decide +kernel

theorem sourceRowsAt852 : MixedData.sourceRows (852 : Fin 2425) =
    MixedData.row852 := by decide +kernel

theorem sourceRowsAt853 : MixedData.sourceRows (853 : Fin 2425) =
    MixedData.row853 := by decide +kernel

theorem sourceRowsAt854 : MixedData.sourceRows (854 : Fin 2425) =
    MixedData.row854 := by decide +kernel

theorem sourceRowsAt855 : MixedData.sourceRows (855 : Fin 2425) =
    MixedData.row855 := by decide +kernel

theorem sourceRowsAt856 : MixedData.sourceRows (856 : Fin 2425) =
    MixedData.row856 := by decide +kernel

theorem sourceRowsAt857 : MixedData.sourceRows (857 : Fin 2425) =
    MixedData.row857 := by decide +kernel

theorem sourceRowsAt858 : MixedData.sourceRows (858 : Fin 2425) =
    MixedData.row858 := by decide +kernel

theorem sourceRowsAt859 : MixedData.sourceRows (859 : Fin 2425) =
    MixedData.row859 := by decide +kernel

theorem sourceRowsAt860 : MixedData.sourceRows (860 : Fin 2425) =
    MixedData.row860 := by decide +kernel

theorem sourceRowsAt861 : MixedData.sourceRows (861 : Fin 2425) =
    MixedData.row861 := by decide +kernel

theorem sourceRowsAt862 : MixedData.sourceRows (862 : Fin 2425) =
    MixedData.row862 := by decide +kernel

theorem sourceRowsAt863 : MixedData.sourceRows (863 : Fin 2425) =
    MixedData.row863 := by decide +kernel

theorem chunkSound53_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 53) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 848 ∨ k.val = 849 ∨ k.val = 850 ∨ k.val = 851 ∨ k.val = 852 ∨ k.val = 853 ∨ k.val = 854 ∨ k.val = 855 ∨ k.val = 856 ∨ k.val = 857 ∨ k.val = 858 ∨ k.val = 859 ∨ k.val = 860 ∨ k.val = 861 ∨ k.val = 862 ∨ k.val = 863 := by omega
  rcases heq with h848 | h849 | h850 | h851 | h852 | h853 | h854 | h855 | h856 | h857 | h858 | h859 | h860 | h861 | h862 | h863
  · have he : k = (848 : Fin 2425) := Fin.ext h848
    subst k
    rw [sourceRowsAt848]
    exact rowSound848 B hB hF
  · have he : k = (849 : Fin 2425) := Fin.ext h849
    subst k
    rw [sourceRowsAt849]
    exact rowSound849 B hB hF
  · have he : k = (850 : Fin 2425) := Fin.ext h850
    subst k
    rw [sourceRowsAt850]
    exact rowSound850 B hB hF
  · have he : k = (851 : Fin 2425) := Fin.ext h851
    subst k
    rw [sourceRowsAt851]
    exact rowSound851 B hB hF
  · have he : k = (852 : Fin 2425) := Fin.ext h852
    subst k
    rw [sourceRowsAt852]
    exact rowSound852_e B hB hF
  · have he : k = (853 : Fin 2425) := Fin.ext h853
    subst k
    rw [sourceRowsAt853]
    exact rowSound853_e B hB hF
  · have he : k = (854 : Fin 2425) := Fin.ext h854
    subst k
    rw [sourceRowsAt854]
    exact rowSound854 B hB hF
  · have he : k = (855 : Fin 2425) := Fin.ext h855
    subst k
    rw [sourceRowsAt855]
    exact rowSound855 B hB hF
  · have he : k = (856 : Fin 2425) := Fin.ext h856
    subst k
    rw [sourceRowsAt856]
    exact rowSound856 B hB hF
  · have he : k = (857 : Fin 2425) := Fin.ext h857
    subst k
    rw [sourceRowsAt857]
    exact rowSound857_e B hB hF
  · have he : k = (858 : Fin 2425) := Fin.ext h858
    subst k
    rw [sourceRowsAt858]
    exact rowSound858_e B hB hF
  · have he : k = (859 : Fin 2425) := Fin.ext h859
    subst k
    rw [sourceRowsAt859]
    exact rowSound859_e B hB hF
  · have he : k = (860 : Fin 2425) := Fin.ext h860
    subst k
    rw [sourceRowsAt860]
    exact rowSound860 B hB hF
  · have he : k = (861 : Fin 2425) := Fin.ext h861
    subst k
    rw [sourceRowsAt861]
    exact rowSound861 B hB hF
  · have he : k = (862 : Fin 2425) := Fin.ext h862
    subst k
    rw [sourceRowsAt862]
    exact rowSound862 B hB hF
  · have he : k = (863 : Fin 2425) := Fin.ext h863
    subst k
    rw [sourceRowsAt863]
    exact rowSound863_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound53_e_oai
