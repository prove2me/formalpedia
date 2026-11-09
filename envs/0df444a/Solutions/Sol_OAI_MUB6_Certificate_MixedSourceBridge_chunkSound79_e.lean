-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:35:18.342232+00:00
-- url     : https://prove2.me/submissions/3acf6795-b8c6-4c73-883e-fe2bcd36fe08

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1264_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1266_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1267_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1268_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1269_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1272_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1278_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1279_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1374 raw1374Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw1374 raw1374Labels = mixedMoment B raw1374step0 raw1374step0Labels := by
      have ha : raw1374step0 = (fun i j => raw1374 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1374step0 raw1374; decide +kernel
      have hl : raw1374step0Labels = raw1374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1374 raw1374Labels permutation32 permutation4
    mixedMoment B raw1374step0 raw1374step0Labels = mixedMoment B raw1374step1 raw1374step1Labels := by
      have ha : raw1374step1 = raw1374step0 := by apply Matrix.ext; unfold raw1374step1 raw1374step0; decide +kernel
      have hl : raw1374step0Labels = labelEmbedding7 ∘ raw1374step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1374step0 raw1374step0Labels raw1374step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

theorem canonical1375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1375 raw1375Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw1375 raw1375Labels = mixedMoment B raw1375step0 raw1375step0Labels := by
      have ha : raw1375step0 = (fun i j => raw1375 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1375step0 raw1375; decide +kernel
      have hl : raw1375step0Labels = raw1375Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1375 raw1375Labels permutation32 permutation4
    _ = mixedMoment B node1134 node1134Labels := by rfl

theorem canonical1376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1376 raw1376Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw1376 raw1376Labels = mixedMoment B raw1376step0 raw1376step0Labels := by
      have ha : raw1376step0 = (fun i j => raw1376 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1376step0 raw1376; decide +kernel
      have hl : raw1376step0Labels = raw1376Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1376 raw1376Labels permutation32 permutation6
    mixedMoment B raw1376step0 raw1376step0Labels = mixedMoment B raw1376step1 raw1376step1Labels := by
      have ha : raw1376step1 = -raw1376step0 := by apply Matrix.ext; change ∀ i j, raw1376step1 i j = -(raw1376step0 i j); unfold raw1376step1 raw1376step0; decide +kernel
      have hl : raw1376step1Labels = raw1376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1376step1 raw1376step1Labels = mixedMoment B raw1376step2 raw1376step2Labels := by
      have ha : raw1376step2 = raw1376step1 := by apply Matrix.ext; unfold raw1376step2 raw1376step1; decide +kernel
      have hl : raw1376step1Labels = labelEmbedding1 ∘ raw1376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1376step1 raw1376step1Labels raw1376step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical1395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1395 raw1395Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw1395 raw1395Labels = mixedMoment B raw1395step0 raw1395step0Labels := by
      have ha : raw1395step0 = (fun i j => raw1395 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1395step0 raw1395; decide +kernel
      have hl : raw1395step0Labels = raw1395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1395 raw1395Labels permutation8 permutation4
    mixedMoment B raw1395step0 raw1395step0Labels = mixedMoment B raw1395step1 raw1395step1Labels := by
      have ha : raw1395step1 = raw1395step0 := by apply Matrix.ext; unfold raw1395step1 raw1395step0; decide +kernel
      have hl : raw1395step0Labels = labelEmbedding7 ∘ raw1395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1395step0 raw1395step0Labels raw1395step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical1396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1396 raw1396Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw1396 raw1396Labels = mixedMoment B raw1396step0 raw1396step0Labels := by
      have ha : raw1396step0 = (fun i j => raw1396 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1396step0 raw1396; decide +kernel
      have hl : raw1396step0Labels = raw1396Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1396 raw1396Labels permutation8 permutation4
    _ = mixedMoment B node1144 node1144Labels := by rfl

theorem canonical1397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1397 raw1397Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw1397 raw1397Labels = mixedMoment B raw1397step0 raw1397step0Labels := by
      have ha : raw1397step0 = (fun i j => raw1397 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1397step0 raw1397; decide +kernel
      have hl : raw1397step0Labels = raw1397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1397 raw1397Labels permutation8 permutation6
    mixedMoment B raw1397step0 raw1397step0Labels = mixedMoment B raw1397step1 raw1397step1Labels := by
      have ha : raw1397step1 = -raw1397step0 := by apply Matrix.ext; change ∀ i j, raw1397step1 i j = -(raw1397step0 i j); unfold raw1397step1 raw1397step0; decide +kernel
      have hl : raw1397step1Labels = raw1397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1397step1 raw1397step1Labels = mixedMoment B raw1397step2 raw1397step2Labels := by
      have ha : raw1397step2 = raw1397step1 := by apply Matrix.ext; unfold raw1397step2 raw1397step1; decide +kernel
      have hl : raw1397step1Labels = labelEmbedding1 ∘ raw1397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1397step1 raw1397step1Labels raw1397step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

theorem canonical1398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1398 raw1398Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw1398 raw1398Labels = mixedMoment B raw1398step0 raw1398step0Labels := by
      have ha : raw1398step0 = (fun i j => raw1398 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1398step0 raw1398; decide +kernel
      have hl : raw1398step0Labels = raw1398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1398 raw1398Labels permutation8 permutation4
    mixedMoment B raw1398step0 raw1398step0Labels = mixedMoment B raw1398step1 raw1398step1Labels := by
      have ha : raw1398step1 = raw1398step0 := by apply Matrix.ext; unfold raw1398step1 raw1398step0; decide +kernel
      have hl : raw1398step0Labels = labelEmbedding7 ∘ raw1398step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1398step0 raw1398step0Labels raw1398step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4559 node4559Labels := by rfl

theorem canonical1399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1399 raw1399Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw1399 raw1399Labels = mixedMoment B raw1399step0 raw1399step0Labels := by
      have ha : raw1399step0 = (fun i j => raw1399 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1399step0 raw1399; decide +kernel
      have hl : raw1399step0Labels = raw1399Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1399 raw1399Labels permutation8 permutation4
    _ = mixedMoment B node1145 node1145Labels := by rfl

theorem canonical1400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1400 raw1400Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw1400 raw1400Labels = mixedMoment B raw1400step0 raw1400step0Labels := by
      have ha : raw1400step0 = (fun i j => raw1400 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1400step0 raw1400; decide +kernel
      have hl : raw1400step0Labels = raw1400Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1400 raw1400Labels permutation9 permutation6
    mixedMoment B raw1400step0 raw1400step0Labels = mixedMoment B raw1400step1 raw1400step1Labels := by
      have ha : raw1400step1 = -raw1400step0 := by apply Matrix.ext; change ∀ i j, raw1400step1 i j = -(raw1400step0 i j); unfold raw1400step1 raw1400step0; decide +kernel
      have hl : raw1400step1Labels = raw1400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1400step1 raw1400step1Labels = mixedMoment B raw1400step2 raw1400step2Labels := by
      have ha : raw1400step2 = raw1400step1 := by apply Matrix.ext; unfold raw1400step2 raw1400step1; decide +kernel
      have hl : raw1400step1Labels = labelEmbedding1 ∘ raw1400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1400step1 raw1400step1Labels raw1400step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

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

theorem canonical1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1425 raw1425Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw1425 raw1425Labels = mixedMoment B raw1425step0 raw1425step0Labels := by
      have ha : raw1425step0 = (fun i j => raw1425 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1425step0 raw1425; decide +kernel
      have hl : raw1425step0Labels = raw1425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1425 raw1425Labels permutation32 permutation4
    mixedMoment B raw1425step0 raw1425step0Labels = mixedMoment B raw1425step1 raw1425step1Labels := by
      have ha : raw1425step1 = raw1425step0 := by apply Matrix.ext; unfold raw1425step1 raw1425step0; decide +kernel
      have hl : raw1425step0Labels = labelEmbedding7 ∘ raw1425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1425step0 raw1425step0Labels raw1425step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical1426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1426 raw1426Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw1426 raw1426Labels = mixedMoment B raw1426step0 raw1426step0Labels := by
      have ha : raw1426step0 = (fun i j => raw1426 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1426step0 raw1426; decide +kernel
      have hl : raw1426step0Labels = raw1426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1426 raw1426Labels permutation32 permutation4
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical1427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1427 raw1427Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw1427 raw1427Labels = mixedMoment B raw1427step0 raw1427step0Labels := by
      have ha : raw1427step0 = (fun i j => raw1427 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1427step0 raw1427; decide +kernel
      have hl : raw1427step0Labels = raw1427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1427 raw1427Labels permutation32 permutation6
    mixedMoment B raw1427step0 raw1427step0Labels = mixedMoment B raw1427step1 raw1427step1Labels := by
      have ha : raw1427step1 = -raw1427step0 := by apply Matrix.ext; change ∀ i j, raw1427step1 i j = -(raw1427step0 i j); unfold raw1427step1 raw1427step0; decide +kernel
      have hl : raw1427step1Labels = raw1427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1427step1 raw1427step1Labels = mixedMoment B raw1427step2 raw1427step2Labels := by
      have ha : raw1427step2 = raw1427step1 := by apply Matrix.ext; unfold raw1427step2 raw1427step1; decide +kernel
      have hl : raw1427step1Labels = labelEmbedding1 ∘ raw1427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1427step1 raw1427step1Labels raw1427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical1434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1434 raw1434Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw1434 raw1434Labels = mixedMoment B raw1434step0 raw1434step0Labels := by
      have ha : raw1434step0 = (fun i j => raw1434 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1434step0 raw1434; decide +kernel
      have hl : raw1434step0Labels = raw1434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1434 raw1434Labels permutation8 permutation4
    mixedMoment B raw1434step0 raw1434step0Labels = mixedMoment B raw1434step1 raw1434step1Labels := by
      have ha : raw1434step1 = raw1434step0 := by apply Matrix.ext; unfold raw1434step1 raw1434step0; decide +kernel
      have hl : raw1434step0Labels = labelEmbedding7 ∘ raw1434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1434step0 raw1434step0Labels raw1434step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1435 raw1435Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw1435 raw1435Labels = mixedMoment B raw1435step0 raw1435step0Labels := by
      have ha : raw1435step0 = (fun i j => raw1435 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1435step0 raw1435; decide +kernel
      have hl : raw1435step0Labels = raw1435Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1435 raw1435Labels permutation8 permutation4
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1436 raw1436Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw1436 raw1436Labels = mixedMoment B raw1436step0 raw1436step0Labels := by
      have ha : raw1436step0 = (fun i j => raw1436 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1436step0 raw1436; decide +kernel
      have hl : raw1436step0Labels = raw1436Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1436 raw1436Labels permutation8 permutation6
    mixedMoment B raw1436step0 raw1436step0Labels = mixedMoment B raw1436step1 raw1436step1Labels := by
      have ha : raw1436step1 = -raw1436step0 := by apply Matrix.ext; change ∀ i j, raw1436step1 i j = -(raw1436step0 i j); unfold raw1436step1 raw1436step0; decide +kernel
      have hl : raw1436step1Labels = raw1436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1436step1 raw1436step1Labels = mixedMoment B raw1436step2 raw1436step2Labels := by
      have ha : raw1436step2 = raw1436step1 := by apply Matrix.ext; unfold raw1436step2 raw1436step1; decide +kernel
      have hl : raw1436step1Labels = labelEmbedding1 ∘ raw1436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1436step1 raw1436step1Labels raw1436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical1443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1443 raw1443Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw1443 raw1443Labels = mixedMoment B raw1443step0 raw1443step0Labels := by
      have ha : raw1443step0 = (fun i j => raw1443 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1443step0 raw1443; decide +kernel
      have hl : raw1443step0Labels = raw1443Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1443 raw1443Labels permutation8 permutation4
    mixedMoment B raw1443step0 raw1443step0Labels = mixedMoment B raw1443step1 raw1443step1Labels := by
      have ha : raw1443step1 = raw1443step0 := by apply Matrix.ext; unfold raw1443step1 raw1443step0; decide +kernel
      have hl : raw1443step0Labels = labelEmbedding7 ∘ raw1443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1443step0 raw1443step0Labels raw1443step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

theorem canonical1444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1444 raw1444Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw1444 raw1444Labels = mixedMoment B raw1444step0 raw1444step0Labels := by
      have ha : raw1444step0 = (fun i j => raw1444 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1444step0 raw1444; decide +kernel
      have hl : raw1444step0Labels = raw1444Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1444 raw1444Labels permutation8 permutation4
    _ = mixedMoment B node1294 node1294Labels := by rfl

theorem canonical1445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1445 raw1445Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw1445 raw1445Labels = mixedMoment B raw1445step0 raw1445step0Labels := by
      have ha : raw1445step0 = (fun i j => raw1445 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1445step0 raw1445; decide +kernel
      have hl : raw1445step0Labels = raw1445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1445 raw1445Labels permutation8 permutation6
    mixedMoment B raw1445step0 raw1445step0Labels = mixedMoment B raw1445step1 raw1445step1Labels := by
      have ha : raw1445step1 = -raw1445step0 := by apply Matrix.ext; change ∀ i j, raw1445step1 i j = -(raw1445step0 i j); unfold raw1445step1 raw1445step0; decide +kernel
      have hl : raw1445step1Labels = raw1445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1445step1 raw1445step1Labels = mixedMoment B raw1445step2 raw1445step2Labels := by
      have ha : raw1445step2 = raw1445step1 := by apply Matrix.ext; unfold raw1445step2 raw1445step1; decide +kernel
      have hl : raw1445step1Labels = labelEmbedding1 ∘ raw1445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1445step1 raw1445step1Labels raw1445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22329 raw22329Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22329 raw22329Labels = mixedMoment B raw22329step0 raw22329step0Labels := by
      have hz : ∀ j, raw22329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22329step0 = (fun i j => raw22329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22329step0 raw22329; decide +kernel
      have hl : raw22329step0Labels = raw22329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329 raw22329Labels permutation434 hz
    mixedMoment B raw22329step0 raw22329step0Labels = mixedMoment B raw22329step1 raw22329step1Labels := by
      have hz : ∀ j, raw22329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22329step1 = (fun i j => raw22329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22329step1 raw22329step0; decide +kernel
      have hl : raw22329step1Labels = raw22329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step0 raw22329step0Labels permutation80 hz
    mixedMoment B raw22329step1 raw22329step1Labels = mixedMoment B raw22329step2 raw22329step2Labels := by
      have hz : ∀ j, raw22329step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22329step2 = (fun i j => raw22329step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22329step2 raw22329step1; decide +kernel
      have hl : raw22329step2Labels = raw22329step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step1 raw22329step1Labels permutation14 hz
    mixedMoment B raw22329step2 raw22329step2Labels = mixedMoment B raw22329step3 raw22329step3Labels := by
      have ha : raw22329step3 = -raw22329step2 := by apply Matrix.ext; change ∀ i j, raw22329step3 i j = -(raw22329step2 i j); unfold raw22329step3 raw22329step2; decide +kernel
      have hl : raw22329step3Labels = raw22329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22416 raw22416Labels = mixedMoment B node3311 node3311Labels := by
  calc
    mixedMoment B raw22416 raw22416Labels = mixedMoment B raw22416step0 raw22416step0Labels := by
      have hz : ∀ j, raw22416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22416step0 = (fun i j => raw22416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22416step0 raw22416; decide +kernel
      have hl : raw22416step0Labels = raw22416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416 raw22416Labels permutation434 hz
    mixedMoment B raw22416step0 raw22416step0Labels = mixedMoment B raw22416step1 raw22416step1Labels := by
      have hz : ∀ j, raw22416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22416step1 = (fun i j => raw22416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22416step1 raw22416step0; decide +kernel
      have hl : raw22416step1Labels = raw22416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416step0 raw22416step0Labels permutation80 hz
    mixedMoment B raw22416step1 raw22416step1Labels = mixedMoment B raw22416step2 raw22416step2Labels := by
      have hz : ∀ j, raw22416step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22416step2 = (fun i j => raw22416step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22416step2 raw22416step1; decide +kernel
      have hl : raw22416step2Labels = raw22416step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416step1 raw22416step1Labels permutation14 hz
    mixedMoment B raw22416step2 raw22416step2Labels = mixedMoment B raw22416step3 raw22416step3Labels := by
      have ha : raw22416step3 = (fun i j => raw22416step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22416step3 raw22416step2; decide +kernel
      have hl : raw22416step3Labels = raw22416step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22416step2 raw22416step2Labels permutation3 permutation2
    mixedMoment B raw22416step3 raw22416step3Labels = mixedMoment B raw22416step4 raw22416step4Labels := by
      have ha : raw22416step4 = -raw22416step3 := by apply Matrix.ext; change ∀ i j, raw22416step4 i j = -(raw22416step3 i j); unfold raw22416step4 raw22416step3; decide +kernel
      have hl : raw22416step4Labels = raw22416step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3311 node3311Labels := by rfl

theorem canonical22421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22421 raw22421Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22421 raw22421Labels = mixedMoment B raw22421step0 raw22421step0Labels := by
      have hz : ∀ j, raw22421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22421step0 = (fun i j => raw22421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22421step0 raw22421; decide +kernel
      have hl : raw22421step0Labels = raw22421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22421 raw22421Labels permutation434 hz
    mixedMoment B raw22421step0 raw22421step0Labels = mixedMoment B raw22421step1 raw22421step1Labels := by
      have hz : ∀ j, raw22421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22421step1 = (fun i j => raw22421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22421step1 raw22421step0; decide +kernel
      have hl : raw22421step1Labels = raw22421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22421step0 raw22421step0Labels permutation80 hz
    mixedMoment B raw22421step1 raw22421step1Labels = mixedMoment B raw22421step2 raw22421step2Labels := by
      have ha : raw22421step2 = (fun i j => raw22421step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22421step2 raw22421step1; decide +kernel
      have hl : raw22421step2Labels = raw22421step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22421step1 raw22421step1Labels permutation8 permutation4
    mixedMoment B raw22421step2 raw22421step2Labels = mixedMoment B raw22421step3 raw22421step3Labels := by
      have ha : raw22421step3 = -raw22421step2 := by apply Matrix.ext; change ∀ i j, raw22421step3 i j = -(raw22421step2 i j); unfold raw22421step3 raw22421step2; decide +kernel
      have hl : raw22421step3Labels = raw22421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical22452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22452 raw22452Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22452 raw22452Labels = mixedMoment B raw22452step0 raw22452step0Labels := by
      have hz : ∀ j, raw22452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22452step0 = (fun i j => raw22452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22452step0 raw22452; decide +kernel
      have hl : raw22452step0Labels = raw22452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22452 raw22452Labels permutation434 hz
    mixedMoment B raw22452step0 raw22452step0Labels = mixedMoment B raw22452step1 raw22452step1Labels := by
      have hz : ∀ j, raw22452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22452step1 = (fun i j => raw22452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22452step1 raw22452step0; decide +kernel
      have hl : raw22452step1Labels = raw22452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22452step0 raw22452step0Labels permutation80 hz
    mixedMoment B raw22452step1 raw22452step1Labels = mixedMoment B raw22452step2 raw22452step2Labels := by
      have ha : raw22452step2 = -raw22452step1 := by apply Matrix.ext; change ∀ i j, raw22452step2 i j = -(raw22452step1 i j); unfold raw22452step2 raw22452step1; decide +kernel
      have hl : raw22452step2Labels = raw22452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical22455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22455 raw22455Labels = mixedMoment B node3312 node3312Labels := by
  calc
    mixedMoment B raw22455 raw22455Labels = mixedMoment B raw22455step0 raw22455step0Labels := by
      have hz : ∀ j, raw22455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22455step0 = (fun i j => raw22455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22455step0 raw22455; decide +kernel
      have hl : raw22455step0Labels = raw22455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455 raw22455Labels permutation434 hz
    mixedMoment B raw22455step0 raw22455step0Labels = mixedMoment B raw22455step1 raw22455step1Labels := by
      have hz : ∀ j, raw22455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22455step1 = (fun i j => raw22455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22455step1 raw22455step0; decide +kernel
      have hl : raw22455step1Labels = raw22455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455step0 raw22455step0Labels permutation80 hz
    mixedMoment B raw22455step1 raw22455step1Labels = mixedMoment B raw22455step2 raw22455step2Labels := by
      have hz : ∀ j, raw22455step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22455step2 = (fun i j => raw22455step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22455step2 raw22455step1; decide +kernel
      have hl : raw22455step2Labels = raw22455step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455step1 raw22455step1Labels permutation14 hz
    mixedMoment B raw22455step2 raw22455step2Labels = mixedMoment B raw22455step3 raw22455step3Labels := by
      have ha : raw22455step3 = -raw22455step2 := by apply Matrix.ext; change ∀ i j, raw22455step3 i j = -(raw22455step2 i j); unfold raw22455step3 raw22455step2; decide +kernel
      have hl : raw22455step3Labels = raw22455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3312 node3312Labels := by rfl

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

theorem canonical22566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22566 raw22566Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw22566 raw22566Labels = mixedMoment B raw22566step0 raw22566step0Labels := by
      have hz : ∀ j, raw22566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22566step0 = (fun i j => raw22566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22566step0 raw22566; decide +kernel
      have hl : raw22566step0Labels = raw22566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22566 raw22566Labels permutation434 hz
    mixedMoment B raw22566step0 raw22566step0Labels = mixedMoment B raw22566step1 raw22566step1Labels := by
      have hz : ∀ j, raw22566step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22566step1 = (fun i j => raw22566step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22566step1 raw22566step0; decide +kernel
      have hl : raw22566step1Labels = raw22566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22566step0 raw22566step0Labels permutation80 hz
    mixedMoment B raw22566step1 raw22566step1Labels = mixedMoment B raw22566step2 raw22566step2Labels := by
      have hz : ∀ j, raw22566step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22566step2 = (fun i j => raw22566step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22566step2 raw22566step1; decide +kernel
      have hl : raw22566step2Labels = raw22566step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22566step1 raw22566step1Labels permutation14 hz
    mixedMoment B raw22566step2 raw22566step2Labels = mixedMoment B raw22566step3 raw22566step3Labels := by
      have ha : raw22566step3 = (fun i j => raw22566step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22566step3 raw22566step2; decide +kernel
      have hl : raw22566step3Labels = raw22566step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22566step2 raw22566step2Labels permutation2 permutation4
    mixedMoment B raw22566step3 raw22566step3Labels = mixedMoment B raw22566step4 raw22566step4Labels := by
      have ha : raw22566step4 = -raw22566step3 := by apply Matrix.ext; change ∀ i j, raw22566step4 i j = -(raw22566step3 i j); unfold raw22566step4 raw22566step3; decide +kernel
      have hl : raw22566step4Labels = raw22566step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1755 node1755Labels := by rfl

theorem canonical22567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22567 raw22567Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22567 raw22567Labels = mixedMoment B raw22567step0 raw22567step0Labels := by
      have hz : ∀ j, raw22567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22567step0 = (fun i j => raw22567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22567step0 raw22567; decide +kernel
      have hl : raw22567step0Labels = raw22567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22567 raw22567Labels permutation434 hz
    mixedMoment B raw22567step0 raw22567step0Labels = mixedMoment B raw22567step1 raw22567step1Labels := by
      have hz : ∀ j, raw22567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22567step1 = (fun i j => raw22567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22567step1 raw22567step0; decide +kernel
      have hl : raw22567step1Labels = raw22567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22567step0 raw22567step0Labels permutation56 hz
    mixedMoment B raw22567step1 raw22567step1Labels = mixedMoment B raw22567step2 raw22567step2Labels := by
      have ha : raw22567step2 = (fun i j => raw22567step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22567step2 raw22567step1; decide +kernel
      have hl : raw22567step2Labels = raw22567step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22567step1 raw22567step1Labels permutation8 permutation4
    mixedMoment B raw22567step2 raw22567step2Labels = mixedMoment B raw22567step3 raw22567step3Labels := by
      have ha : raw22567step3 = -raw22567step2 := by apply Matrix.ext; change ∀ i j, raw22567step3 i j = -(raw22567step2 i j); unfold raw22567step3 raw22567step2; decide +kernel
      have hl : raw22567step3Labels = raw22567step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical22568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22568 raw22568Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22568 raw22568Labels = mixedMoment B raw22568step0 raw22568step0Labels := by
      have hz : ∀ j, raw22568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22568step0 = (fun i j => raw22568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22568step0 raw22568; decide +kernel
      have hl : raw22568step0Labels = raw22568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22568 raw22568Labels permutation346 hz
    mixedMoment B raw22568step0 raw22568step0Labels = mixedMoment B raw22568step1 raw22568step1Labels := by
      have hz : ∀ j, raw22568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22568step1 = (fun i j => raw22568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22568step1 raw22568step0; decide +kernel
      have hl : raw22568step1Labels = raw22568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22568step0 raw22568step0Labels permutation56 hz
    mixedMoment B raw22568step1 raw22568step1Labels = mixedMoment B raw22568step2 raw22568step2Labels := by
      have ha : raw22568step2 = (fun i j => raw22568step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22568step2 raw22568step1; decide +kernel
      have hl : raw22568step2Labels = raw22568step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22568step1 raw22568step1Labels permutation8 permutation4
    mixedMoment B raw22568step2 raw22568step2Labels = mixedMoment B raw22568step3 raw22568step3Labels := by
      have ha : raw22568step3 = -raw22568step2 := by apply Matrix.ext; change ∀ i j, raw22568step3 i j = -(raw22568step2 i j); unfold raw22568step3 raw22568step2; decide +kernel
      have hl : raw22568step3Labels = raw22568step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical22651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22651 raw22651Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22651 raw22651Labels = mixedMoment B raw22651step0 raw22651step0Labels := by
      have hz : ∀ j, raw22651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22651step0 = (fun i j => raw22651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22651step0 raw22651; decide +kernel
      have hl : raw22651step0Labels = raw22651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22651 raw22651Labels permutation434 hz
    mixedMoment B raw22651step0 raw22651step0Labels = mixedMoment B raw22651step1 raw22651step1Labels := by
      have hz : ∀ j, raw22651step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22651step1 = (fun i j => raw22651step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22651step1 raw22651step0; decide +kernel
      have hl : raw22651step1Labels = raw22651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22651step0 raw22651step0Labels permutation56 hz
    mixedMoment B raw22651step1 raw22651step1Labels = mixedMoment B raw22651step2 raw22651step2Labels := by
      have ha : raw22651step2 = -raw22651step1 := by apply Matrix.ext; change ∀ i j, raw22651step2 i j = -(raw22651step1 i j); unfold raw22651step2 raw22651step1; decide +kernel
      have hl : raw22651step2Labels = raw22651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical22652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22652 raw22652Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22652 raw22652Labels = mixedMoment B raw22652step0 raw22652step0Labels := by
      have hz : ∀ j, raw22652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22652step0 = (fun i j => raw22652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22652step0 raw22652; decide +kernel
      have hl : raw22652step0Labels = raw22652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22652 raw22652Labels permutation346 hz
    mixedMoment B raw22652step0 raw22652step0Labels = mixedMoment B raw22652step1 raw22652step1Labels := by
      have hz : ∀ j, raw22652step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22652step1 = (fun i j => raw22652step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22652step1 raw22652step0; decide +kernel
      have hl : raw22652step1Labels = raw22652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22652step0 raw22652step0Labels permutation56 hz
    mixedMoment B raw22652step1 raw22652step1Labels = mixedMoment B raw22652step2 raw22652step2Labels := by
      have ha : raw22652step2 = -raw22652step1 := by apply Matrix.ext; change ∀ i j, raw22652step2 i j = -(raw22652step1 i j); unfold raw22652step2 raw22652step1; decide +kernel
      have hl : raw22652step2Labels = raw22652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical22653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22653 raw22653Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw22653 raw22653Labels = mixedMoment B raw22653step0 raw22653step0Labels := by
      have hz : ∀ j, raw22653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22653step0 = (fun i j => raw22653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22653step0 raw22653; decide +kernel
      have hl : raw22653step0Labels = raw22653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22653 raw22653Labels permutation434 hz
    mixedMoment B raw22653step0 raw22653step0Labels = mixedMoment B raw22653step1 raw22653step1Labels := by
      have hz : ∀ j, raw22653step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22653step1 = (fun i j => raw22653step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22653step1 raw22653step0; decide +kernel
      have hl : raw22653step1Labels = raw22653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22653step0 raw22653step0Labels permutation80 hz
    mixedMoment B raw22653step1 raw22653step1Labels = mixedMoment B raw22653step2 raw22653step2Labels := by
      have hz : ∀ j, raw22653step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22653step2 = (fun i j => raw22653step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22653step2 raw22653step1; decide +kernel
      have hl : raw22653step2Labels = raw22653step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22653step1 raw22653step1Labels permutation14 hz
    mixedMoment B raw22653step2 raw22653step2Labels = mixedMoment B raw22653step3 raw22653step3Labels := by
      have ha : raw22653step3 = (fun i j => raw22653step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22653step3 raw22653step2; decide +kernel
      have hl : raw22653step3Labels = raw22653step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22653step2 raw22653step2Labels permutation3 permutation2
    mixedMoment B raw22653step3 raw22653step3Labels = mixedMoment B raw22653step4 raw22653step4Labels := by
      have ha : raw22653step4 = -raw22653step3 := by apply Matrix.ext; change ∀ i j, raw22653step4 i j = -(raw22653step3 i j); unfold raw22653step4 raw22653step3; decide +kernel
      have hl : raw22653step4Labels = raw22653step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1755 node1755Labels := by rfl

theorem canonical22654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22654 raw22654Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw22654 raw22654Labels = mixedMoment B raw22654step0 raw22654step0Labels := by
      have hz : ∀ j, raw22654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22654step0 = (fun i j => raw22654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22654step0 raw22654; decide +kernel
      have hl : raw22654step0Labels = raw22654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22654 raw22654Labels permutation434 hz
    mixedMoment B raw22654step0 raw22654step0Labels = mixedMoment B raw22654step1 raw22654step1Labels := by
      have hz : ∀ j, raw22654step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22654step1 = (fun i j => raw22654step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22654step1 raw22654step0; decide +kernel
      have hl : raw22654step1Labels = raw22654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22654step0 raw22654step0Labels permutation80 hz
    mixedMoment B raw22654step1 raw22654step1Labels = mixedMoment B raw22654step2 raw22654step2Labels := by
      have hz : ∀ j, raw22654step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22654step2 = (fun i j => raw22654step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22654step2 raw22654step1; decide +kernel
      have hl : raw22654step2Labels = raw22654step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22654step1 raw22654step1Labels permutation14 hz
    mixedMoment B raw22654step2 raw22654step2Labels = mixedMoment B raw22654step3 raw22654step3Labels := by
      have ha : raw22654step3 = -raw22654step2 := by apply Matrix.ext; change ∀ i j, raw22654step3 i j = -(raw22654step2 i j); unfold raw22654step3 raw22654step2; decide +kernel
      have hl : raw22654step3Labels = raw22654step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1755 node1755Labels := by rfl

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

theorem canonical22656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22656 raw22656Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw22656 raw22656Labels = mixedMoment B raw22656step0 raw22656step0Labels := by
      have hz : ∀ j, raw22656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22656step0 = (fun i j => raw22656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22656step0 raw22656; decide +kernel
      have hl : raw22656step0Labels = raw22656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22656 raw22656Labels permutation346 hz
    mixedMoment B raw22656step0 raw22656step0Labels = mixedMoment B raw22656step1 raw22656step1Labels := by
      have ha : raw22656step1 = (fun i j => raw22656step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22656step1 raw22656step0; decide +kernel
      have hl : raw22656step1Labels = raw22656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22656step0 raw22656step0Labels permutation38 permutation3
    mixedMoment B raw22656step1 raw22656step1Labels = mixedMoment B raw22656step2 raw22656step2Labels := by
      have ha : raw22656step2 = raw22656step1 := by apply Matrix.ext; unfold raw22656step2 raw22656step1; decide +kernel
      have hl : raw22656step1Labels = labelEmbedding6 ∘ raw22656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22656step1 raw22656step1Labels raw22656step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4158 node4158Labels := by rfl

theorem canonical22657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22657 raw22657Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw22657 raw22657Labels = mixedMoment B raw22657step0 raw22657step0Labels := by
      have ha : raw22657step0 = (fun i j => raw22657 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22657step0 raw22657; decide +kernel
      have hl : raw22657step0Labels = raw22657Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22657 raw22657Labels permutation182 permutation3
    mixedMoment B raw22657step0 raw22657step0Labels = mixedMoment B raw22657step1 raw22657step1Labels := by
      have ha : raw22657step1 = raw22657step0 := by apply Matrix.ext; unfold raw22657step1 raw22657step0; decide +kernel
      have hl : raw22657step0Labels = labelEmbedding6 ∘ raw22657step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22657step0 raw22657step0Labels raw22657step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4533 node4533Labels := by rfl

theorem canonical22658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22658 raw22658Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw22658 raw22658Labels = mixedMoment B raw22658step0 raw22658step0Labels := by
      have hz : ∀ j, raw22658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22658step0 = (fun i j => raw22658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22658step0 raw22658; decide +kernel
      have hl : raw22658step0Labels = raw22658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22658 raw22658Labels permutation346 hz
    mixedMoment B raw22658step0 raw22658step0Labels = mixedMoment B raw22658step1 raw22658step1Labels := by
      have ha : raw22658step1 = (fun i j => raw22658step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22658step1 raw22658step0; decide +kernel
      have hl : raw22658step1Labels = raw22658step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22658step0 raw22658step0Labels permutation39 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

theorem canonical22659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22659 raw22659Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw22659 raw22659Labels = mixedMoment B raw22659step0 raw22659step0Labels := by
      have hz : ∀ j, raw22659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22659step0 = (fun i j => raw22659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22659step0 raw22659; decide +kernel
      have hl : raw22659step0Labels = raw22659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22659 raw22659Labels permutation346 hz
    mixedMoment B raw22659step0 raw22659step0Labels = mixedMoment B raw22659step1 raw22659step1Labels := by
      have ha : raw22659step1 = (fun i j => raw22659step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22659step1 raw22659step0; decide +kernel
      have hl : raw22659step1Labels = raw22659step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22659step0 raw22659step0Labels permutation39 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical22660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22660 raw22660Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw22660 raw22660Labels = mixedMoment B raw22660step0 raw22660step0Labels := by
      have hz : ∀ j, raw22660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22660step0 = (fun i j => raw22660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22660step0 raw22660; decide +kernel
      have hl : raw22660step0Labels = raw22660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22660 raw22660Labels permutation265 hz
    mixedMoment B raw22660step0 raw22660step0Labels = mixedMoment B raw22660step1 raw22660step1Labels := by
      have ha : raw22660step1 = (fun i j => raw22660step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22660step1 raw22660step0; decide +kernel
      have hl : raw22660step1Labels = raw22660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22660step0 raw22660step0Labels permutation38 permutation3
    mixedMoment B raw22660step1 raw22660step1Labels = mixedMoment B raw22660step2 raw22660step2Labels := by
      have ha : raw22660step2 = raw22660step1 := by apply Matrix.ext; unfold raw22660step2 raw22660step1; decide +kernel
      have hl : raw22660step1Labels = labelEmbedding6 ∘ raw22660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22660step1 raw22660step1Labels raw22660step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4158 node4158Labels := by rfl

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

theorem canonical22662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22662 raw22662Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw22662 raw22662Labels = mixedMoment B raw22662step0 raw22662step0Labels := by
      have hz : ∀ j, raw22662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22662step0 = (fun i j => raw22662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22662step0 raw22662; decide +kernel
      have hl : raw22662step0Labels = raw22662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22662 raw22662Labels permutation265 hz
    mixedMoment B raw22662step0 raw22662step0Labels = mixedMoment B raw22662step1 raw22662step1Labels := by
      have ha : raw22662step1 = (fun i j => raw22662step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22662step1 raw22662step0; decide +kernel
      have hl : raw22662step1Labels = raw22662step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22662step0 raw22662step0Labels permutation39 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

theorem canonical22663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22663 raw22663Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw22663 raw22663Labels = mixedMoment B raw22663step0 raw22663step0Labels := by
      have hz : ∀ j, raw22663 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22663step0 = (fun i j => raw22663 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22663step0 raw22663; decide +kernel
      have hl : raw22663step0Labels = raw22663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22663 raw22663Labels permutation265 hz
    mixedMoment B raw22663step0 raw22663step0Labels = mixedMoment B raw22663step1 raw22663step1Labels := by
      have ha : raw22663step1 = (fun i j => raw22663step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22663step1 raw22663step0; decide +kernel
      have hl : raw22663step1Labels = raw22663step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22663step0 raw22663step0Labels permutation39 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical22664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22664 raw22664Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw22664 raw22664Labels = mixedMoment B raw22664step0 raw22664step0Labels := by
      have hz : ∀ j, raw22664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22664step0 = (fun i j => raw22664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22664step0 raw22664; decide +kernel
      have hl : raw22664step0Labels = raw22664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22664 raw22664Labels permutation346 hz
    mixedMoment B raw22664step0 raw22664step0Labels = mixedMoment B raw22664step1 raw22664step1Labels := by
      have hz : ∀ j, raw22664step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22664step1 = (fun i j => raw22664step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22664step1 raw22664step0; decide +kernel
      have hl : raw22664step1Labels = raw22664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22664step0 raw22664step0Labels permutation56 hz
    mixedMoment B raw22664step1 raw22664step1Labels = mixedMoment B raw22664step2 raw22664step2Labels := by
      have ha : raw22664step2 = (fun i j => raw22664step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22664step2 raw22664step1; decide +kernel
      have hl : raw22664step2Labels = raw22664step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22664step1 raw22664step1Labels permutation8 permutation3
    mixedMoment B raw22664step2 raw22664step2Labels = mixedMoment B raw22664step3 raw22664step3Labels := by
      have ha : raw22664step3 = raw22664step2 := by apply Matrix.ext; unfold raw22664step3 raw22664step2; decide +kernel
      have hl : raw22664step2Labels = labelEmbedding6 ∘ raw22664step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22664step2 raw22664step2Labels raw22664step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4188 node4188Labels := by rfl

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

theorem canonical22666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22666 raw22666Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw22666 raw22666Labels = mixedMoment B raw22666step0 raw22666step0Labels := by
      have hz : ∀ j, raw22666 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22666step0 = (fun i j => raw22666 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22666step0 raw22666; decide +kernel
      have hl : raw22666step0Labels = raw22666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22666 raw22666Labels permutation265 hz
    mixedMoment B raw22666step0 raw22666step0Labels = mixedMoment B raw22666step1 raw22666step1Labels := by
      have ha : raw22666step1 = (fun i j => raw22666step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22666step1 raw22666step0; decide +kernel
      have hl : raw22666step1Labels = raw22666step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22666step0 raw22666step0Labels permutation32 permutation3
    mixedMoment B raw22666step1 raw22666step1Labels = mixedMoment B raw22666step2 raw22666step2Labels := by
      have ha : raw22666step2 = raw22666step1 := by apply Matrix.ext; unfold raw22666step2 raw22666step1; decide +kernel
      have hl : raw22666step1Labels = labelEmbedding6 ∘ raw22666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22666step1 raw22666step1Labels raw22666step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4556 node4556Labels := by rfl

theorem canonical22667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22667 raw22667Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw22667 raw22667Labels = mixedMoment B raw22667step0 raw22667step0Labels := by
      have hz : ∀ j, raw22667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22667step0 = (fun i j => raw22667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22667step0 raw22667; decide +kernel
      have hl : raw22667step0Labels = raw22667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22667 raw22667Labels permutation346 hz
    mixedMoment B raw22667step0 raw22667step0Labels = mixedMoment B raw22667step1 raw22667step1Labels := by
      have hz : ∀ j, raw22667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22667step1 = (fun i j => raw22667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22667step1 raw22667step0; decide +kernel
      have hl : raw22667step1Labels = raw22667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22667step0 raw22667step0Labels permutation56 hz
    mixedMoment B raw22667step1 raw22667step1Labels = mixedMoment B raw22667step2 raw22667step2Labels := by
      have ha : raw22667step2 = (fun i j => raw22667step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22667step2 raw22667step1; decide +kernel
      have hl : raw22667step2Labels = raw22667step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22667step1 raw22667step1Labels permutation9 permutation2
    _ = mixedMoment B node4619 node4619Labels := by rfl

theorem canonical22668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22668 raw22668Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw22668 raw22668Labels = mixedMoment B raw22668step0 raw22668step0Labels := by
      have hz : ∀ j, raw22668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22668step0 = (fun i j => raw22668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22668step0 raw22668; decide +kernel
      have hl : raw22668step0Labels = raw22668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22668 raw22668Labels permutation346 hz
    mixedMoment B raw22668step0 raw22668step0Labels = mixedMoment B raw22668step1 raw22668step1Labels := by
      have hz : ∀ j, raw22668step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22668step1 = (fun i j => raw22668step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22668step1 raw22668step0; decide +kernel
      have hl : raw22668step1Labels = raw22668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22668step0 raw22668step0Labels permutation56 hz
    mixedMoment B raw22668step1 raw22668step1Labels = mixedMoment B raw22668step2 raw22668step2Labels := by
      have ha : raw22668step2 = (fun i j => raw22668step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22668step2 raw22668step1; decide +kernel
      have hl : raw22668step2Labels = raw22668step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22668step1 raw22668step1Labels permutation9 permutation3
    mixedMoment B raw22668step2 raw22668step2Labels = mixedMoment B raw22668step3 raw22668step3Labels := by
      have ha : raw22668step3 = raw22668step2 := by apply Matrix.ext; unfold raw22668step3 raw22668step2; decide +kernel
      have hl : raw22668step2Labels = labelEmbedding6 ∘ raw22668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22668step2 raw22668step2Labels raw22668step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4161 node4161Labels := by rfl

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

theorem canonical22670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22670 raw22670Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw22670 raw22670Labels = mixedMoment B raw22670step0 raw22670step0Labels := by
      have hz : ∀ j, raw22670 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22670step0 = (fun i j => raw22670 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22670step0 raw22670; decide +kernel
      have hl : raw22670step0Labels = raw22670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22670 raw22670Labels permutation265 hz
    mixedMoment B raw22670step0 raw22670step0Labels = mixedMoment B raw22670step1 raw22670step1Labels := by
      have ha : raw22670step1 = (fun i j => raw22670step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22670step1 raw22670step0; decide +kernel
      have hl : raw22670step1Labels = raw22670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22670step0 raw22670step0Labels permutation33 permutation3
    mixedMoment B raw22670step1 raw22670step1Labels = mixedMoment B raw22670step2 raw22670step2Labels := by
      have ha : raw22670step2 = raw22670step1 := by apply Matrix.ext; unfold raw22670step2 raw22670step1; decide +kernel
      have hl : raw22670step1Labels = labelEmbedding6 ∘ raw22670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22670step1 raw22670step1Labels raw22670step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical22671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22671 raw22671Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw22671 raw22671Labels = mixedMoment B raw22671step0 raw22671step0Labels := by
      have hz : ∀ j, raw22671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22671step0 = (fun i j => raw22671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22671step0 raw22671; decide +kernel
      have hl : raw22671step0Labels = raw22671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22671 raw22671Labels permutation346 hz
    mixedMoment B raw22671step0 raw22671step0Labels = mixedMoment B raw22671step1 raw22671step1Labels := by
      have hz : ∀ j, raw22671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22671step1 = (fun i j => raw22671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22671step1 raw22671step0; decide +kernel
      have hl : raw22671step1Labels = raw22671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22671step0 raw22671step0Labels permutation56 hz
    mixedMoment B raw22671step1 raw22671step1Labels = mixedMoment B raw22671step2 raw22671step2Labels := by
      have ha : raw22671step2 = (fun i j => raw22671step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22671step2 raw22671step1; decide +kernel
      have hl : raw22671step2Labels = raw22671step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22671step1 raw22671step1Labels permutation9 permutation2
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical22672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22672 raw22672Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw22672 raw22672Labels = mixedMoment B raw22672step0 raw22672step0Labels := by
      have hz : ∀ j, raw22672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22672step0 = (fun i j => raw22672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22672step0 raw22672; decide +kernel
      have hl : raw22672step0Labels = raw22672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22672 raw22672Labels permutation346 hz
    mixedMoment B raw22672step0 raw22672step0Labels = mixedMoment B raw22672step1 raw22672step1Labels := by
      have hz : ∀ j, raw22672step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22672step1 = (fun i j => raw22672step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22672step1 raw22672step0; decide +kernel
      have hl : raw22672step1Labels = raw22672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22672step0 raw22672step0Labels permutation56 hz
    mixedMoment B raw22672step1 raw22672step1Labels = mixedMoment B raw22672step2 raw22672step2Labels := by
      have ha : raw22672step2 = (fun i j => raw22672step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22672step2 raw22672step1; decide +kernel
      have hl : raw22672step2Labels = raw22672step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22672step1 raw22672step1Labels permutation9 permutation2
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical22673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22673 raw22673Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw22673 raw22673Labels = mixedMoment B raw22673step0 raw22673step0Labels := by
      have hz : ∀ j, raw22673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22673step0 = (fun i j => raw22673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22673step0 raw22673; decide +kernel
      have hl : raw22673step0Labels = raw22673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22673 raw22673Labels permutation346 hz
    mixedMoment B raw22673step0 raw22673step0Labels = mixedMoment B raw22673step1 raw22673step1Labels := by
      have hz : ∀ j, raw22673step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22673step1 = (fun i j => raw22673step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22673step1 raw22673step0; decide +kernel
      have hl : raw22673step1Labels = raw22673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22673step0 raw22673step0Labels permutation56 hz
    mixedMoment B raw22673step1 raw22673step1Labels = mixedMoment B raw22673step2 raw22673step2Labels := by
      have ha : raw22673step2 = (fun i j => raw22673step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22673step2 raw22673step1; decide +kernel
      have hl : raw22673step2Labels = raw22673step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22673step1 raw22673step1Labels permutation8 permutation3
    mixedMoment B raw22673step2 raw22673step2Labels = mixedMoment B raw22673step3 raw22673step3Labels := by
      have ha : raw22673step3 = raw22673step2 := by apply Matrix.ext; unfold raw22673step3 raw22673step2; decide +kernel
      have hl : raw22673step2Labels = labelEmbedding6 ∘ raw22673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22673step2 raw22673step2Labels raw22673step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4160 node4160Labels := by rfl

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

theorem canonical22675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22675 raw22675Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw22675 raw22675Labels = mixedMoment B raw22675step0 raw22675step0Labels := by
      have hz : ∀ j, raw22675 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22675step0 = (fun i j => raw22675 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22675step0 raw22675; decide +kernel
      have hl : raw22675step0Labels = raw22675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22675 raw22675Labels permutation265 hz
    mixedMoment B raw22675step0 raw22675step0Labels = mixedMoment B raw22675step1 raw22675step1Labels := by
      have ha : raw22675step1 = (fun i j => raw22675step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22675step1 raw22675step0; decide +kernel
      have hl : raw22675step1Labels = raw22675step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22675step0 raw22675step0Labels permutation32 permutation3
    mixedMoment B raw22675step1 raw22675step1Labels = mixedMoment B raw22675step2 raw22675step2Labels := by
      have ha : raw22675step2 = raw22675step1 := by apply Matrix.ext; unfold raw22675step2 raw22675step1; decide +kernel
      have hl : raw22675step1Labels = labelEmbedding6 ∘ raw22675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22675step1 raw22675step1Labels raw22675step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4534 node4534Labels := by rfl

theorem canonical22676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22676 raw22676Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw22676 raw22676Labels = mixedMoment B raw22676step0 raw22676step0Labels := by
      have hz : ∀ j, raw22676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22676step0 = (fun i j => raw22676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22676step0 raw22676; decide +kernel
      have hl : raw22676step0Labels = raw22676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22676 raw22676Labels permutation346 hz
    mixedMoment B raw22676step0 raw22676step0Labels = mixedMoment B raw22676step1 raw22676step1Labels := by
      have hz : ∀ j, raw22676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22676step1 = (fun i j => raw22676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22676step1 raw22676step0; decide +kernel
      have hl : raw22676step1Labels = raw22676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22676step0 raw22676step0Labels permutation56 hz
    _ = mixedMoment B node4559 node4559Labels := by rfl

theorem canonical22699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22699 raw22699Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw22699 raw22699Labels = mixedMoment B raw22699step0 raw22699step0Labels := by
      have hz : ∀ j, raw22699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22699step0 = (fun i j => raw22699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22699step0 raw22699; decide +kernel
      have hl : raw22699step0Labels = raw22699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22699 raw22699Labels permutation346 hz
    mixedMoment B raw22699step0 raw22699step0Labels = mixedMoment B raw22699step1 raw22699step1Labels := by
      have hz : ∀ j, raw22699step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22699step1 = (fun i j => raw22699step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22699step1 raw22699step0; decide +kernel
      have hl : raw22699step1Labels = raw22699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22699step0 raw22699step0Labels permutation56 hz
    mixedMoment B raw22699step1 raw22699step1Labels = mixedMoment B raw22699step2 raw22699step2Labels := by
      have ha : raw22699step2 = (fun i j => raw22699step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22699step2 raw22699step1; decide +kernel
      have hl : raw22699step2Labels = raw22699step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22699step1 raw22699step1Labels permutation9 permutation7
    mixedMoment B raw22699step2 raw22699step2Labels = mixedMoment B raw22699step3 raw22699step3Labels := by
      have ha : raw22699step3 = -raw22699step2 := by apply Matrix.ext; change ∀ i j, raw22699step3 i j = -(raw22699step2 i j); unfold raw22699step3 raw22699step2; decide +kernel
      have hl : raw22699step3Labels = raw22699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22699step3 raw22699step3Labels = mixedMoment B raw22699step4 raw22699step4Labels := by
      have ha : raw22699step4 = raw22699step3 := by apply Matrix.ext; unfold raw22699step4 raw22699step3; decide +kernel
      have hl : raw22699step3Labels = labelEmbedding1 ∘ raw22699step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22699step3 raw22699step3Labels raw22699step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical22700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22700 raw22700Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw22700 raw22700Labels = mixedMoment B raw22700step0 raw22700step0Labels := by
      have hz : ∀ j, raw22700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22700step0 = (fun i j => raw22700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22700step0 raw22700; decide +kernel
      have hl : raw22700step0Labels = raw22700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22700 raw22700Labels permutation346 hz
    mixedMoment B raw22700step0 raw22700step0Labels = mixedMoment B raw22700step1 raw22700step1Labels := by
      have ha : raw22700step1 = (fun i j => raw22700step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22700step1 raw22700step0; decide +kernel
      have hl : raw22700step1Labels = raw22700step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22700step0 raw22700step0Labels permutation46 permutation5
    mixedMoment B raw22700step1 raw22700step1Labels = mixedMoment B raw22700step2 raw22700step2Labels := by
      have ha : raw22700step2 = -raw22700step1 := by apply Matrix.ext; change ∀ i j, raw22700step2 i j = -(raw22700step1 i j); unfold raw22700step2 raw22700step1; decide +kernel
      have hl : raw22700step2Labels = raw22700step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22700step2 raw22700step2Labels = mixedMoment B raw22700step3 raw22700step3Labels := by
      have ha : raw22700step3 = raw22700step2 := by apply Matrix.ext; unfold raw22700step3 raw22700step2; decide +kernel
      have hl : raw22700step2Labels = labelEmbedding1 ∘ raw22700step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22700step2 raw22700step2Labels raw22700step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical22701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22701 raw22701Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw22701 raw22701Labels = mixedMoment B raw22701step0 raw22701step0Labels := by
      have ha : raw22701step0 = (fun i j => raw22701 (permutation190 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22701step0 raw22701; decide +kernel
      have hl : raw22701step0Labels = raw22701Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22701 raw22701Labels permutation190 permutation5
    mixedMoment B raw22701step0 raw22701step0Labels = mixedMoment B raw22701step1 raw22701step1Labels := by
      have ha : raw22701step1 = -raw22701step0 := by apply Matrix.ext; change ∀ i j, raw22701step1 i j = -(raw22701step0 i j); unfold raw22701step1 raw22701step0; decide +kernel
      have hl : raw22701step1Labels = raw22701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22701step1 raw22701step1Labels = mixedMoment B raw22701step2 raw22701step2Labels := by
      have ha : raw22701step2 = raw22701step1 := by apply Matrix.ext; unfold raw22701step2 raw22701step1; decide +kernel
      have hl : raw22701step1Labels = labelEmbedding1 ∘ raw22701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22701step1 raw22701step1Labels raw22701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

theorem canonical22702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22702 raw22702Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw22702 raw22702Labels = mixedMoment B raw22702step0 raw22702step0Labels := by
      have hz : ∀ j, raw22702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22702step0 = (fun i j => raw22702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22702step0 raw22702; decide +kernel
      have hl : raw22702step0Labels = raw22702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22702 raw22702Labels permutation346 hz
    mixedMoment B raw22702step0 raw22702step0Labels = mixedMoment B raw22702step1 raw22702step1Labels := by
      have ha : raw22702step1 = (fun i j => raw22702step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22702step1 raw22702step0; decide +kernel
      have hl : raw22702step1Labels = raw22702step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22702step0 raw22702step0Labels permutation39 permutation7
    mixedMoment B raw22702step1 raw22702step1Labels = mixedMoment B raw22702step2 raw22702step2Labels := by
      have ha : raw22702step2 = -raw22702step1 := by apply Matrix.ext; change ∀ i j, raw22702step2 i j = -(raw22702step1 i j); unfold raw22702step2 raw22702step1; decide +kernel
      have hl : raw22702step2Labels = raw22702step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22702step2 raw22702step2Labels = mixedMoment B raw22702step3 raw22702step3Labels := by
      have ha : raw22702step3 = raw22702step2 := by apply Matrix.ext; unfold raw22702step3 raw22702step2; decide +kernel
      have hl : raw22702step2Labels = labelEmbedding1 ∘ raw22702step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22702step2 raw22702step2Labels raw22702step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical22703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22703 raw22703Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw22703 raw22703Labels = mixedMoment B raw22703step0 raw22703step0Labels := by
      have hz : ∀ j, raw22703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22703step0 = (fun i j => raw22703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22703step0 raw22703; decide +kernel
      have hl : raw22703step0Labels = raw22703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22703 raw22703Labels permutation346 hz
    mixedMoment B raw22703step0 raw22703step0Labels = mixedMoment B raw22703step1 raw22703step1Labels := by
      have ha : raw22703step1 = (fun i j => raw22703step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22703step1 raw22703step0; decide +kernel
      have hl : raw22703step1Labels = raw22703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22703step0 raw22703step0Labels permutation39 permutation7
    mixedMoment B raw22703step1 raw22703step1Labels = mixedMoment B raw22703step2 raw22703step2Labels := by
      have ha : raw22703step2 = -raw22703step1 := by apply Matrix.ext; change ∀ i j, raw22703step2 i j = -(raw22703step1 i j); unfold raw22703step2 raw22703step1; decide +kernel
      have hl : raw22703step2Labels = raw22703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22703step2 raw22703step2Labels = mixedMoment B raw22703step3 raw22703step3Labels := by
      have ha : raw22703step3 = raw22703step2 := by apply Matrix.ext; unfold raw22703step3 raw22703step2; decide +kernel
      have hl : raw22703step2Labels = labelEmbedding1 ∘ raw22703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22703step2 raw22703step2Labels raw22703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical22704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22704 raw22704Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw22704 raw22704Labels = mixedMoment B raw22704step0 raw22704step0Labels := by
      have hz : ∀ j, raw22704 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22704step0 = (fun i j => raw22704 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22704step0 raw22704; decide +kernel
      have hl : raw22704step0Labels = raw22704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22704 raw22704Labels permutation265 hz
    mixedMoment B raw22704step0 raw22704step0Labels = mixedMoment B raw22704step1 raw22704step1Labels := by
      have ha : raw22704step1 = (fun i j => raw22704step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22704step1 raw22704step0; decide +kernel
      have hl : raw22704step1Labels = raw22704step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22704step0 raw22704step0Labels permutation46 permutation5
    mixedMoment B raw22704step1 raw22704step1Labels = mixedMoment B raw22704step2 raw22704step2Labels := by
      have ha : raw22704step2 = -raw22704step1 := by apply Matrix.ext; change ∀ i j, raw22704step2 i j = -(raw22704step1 i j); unfold raw22704step2 raw22704step1; decide +kernel
      have hl : raw22704step2Labels = raw22704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22704step2 raw22704step2Labels = mixedMoment B raw22704step3 raw22704step3Labels := by
      have ha : raw22704step3 = raw22704step2 := by apply Matrix.ext; unfold raw22704step3 raw22704step2; decide +kernel
      have hl : raw22704step2Labels = labelEmbedding1 ∘ raw22704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22704step2 raw22704step2Labels raw22704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

theorem canonical22705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22705 raw22705Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw22705 raw22705Labels = mixedMoment B raw22705step0 raw22705step0Labels := by
      have ha : raw22705step0 = (fun i j => raw22705 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22705step0 raw22705; decide +kernel
      have hl : raw22705step0Labels = raw22705Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22705 raw22705Labels permutation166 permutation5
    mixedMoment B raw22705step0 raw22705step0Labels = mixedMoment B raw22705step1 raw22705step1Labels := by
      have ha : raw22705step1 = -raw22705step0 := by apply Matrix.ext; change ∀ i j, raw22705step1 i j = -(raw22705step0 i j); unfold raw22705step1 raw22705step0; decide +kernel
      have hl : raw22705step1Labels = raw22705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22705step1 raw22705step1Labels = mixedMoment B raw22705step2 raw22705step2Labels := by
      have ha : raw22705step2 = raw22705step1 := by apply Matrix.ext; unfold raw22705step2 raw22705step1; decide +kernel
      have hl : raw22705step1Labels = labelEmbedding1 ∘ raw22705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22705step1 raw22705step1Labels raw22705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

theorem canonical22706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22706 raw22706Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw22706 raw22706Labels = mixedMoment B raw22706step0 raw22706step0Labels := by
      have hz : ∀ j, raw22706 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22706step0 = (fun i j => raw22706 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22706step0 raw22706; decide +kernel
      have hl : raw22706step0Labels = raw22706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22706 raw22706Labels permutation265 hz
    mixedMoment B raw22706step0 raw22706step0Labels = mixedMoment B raw22706step1 raw22706step1Labels := by
      have ha : raw22706step1 = (fun i j => raw22706step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22706step1 raw22706step0; decide +kernel
      have hl : raw22706step1Labels = raw22706step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22706step0 raw22706step0Labels permutation39 permutation7
    mixedMoment B raw22706step1 raw22706step1Labels = mixedMoment B raw22706step2 raw22706step2Labels := by
      have ha : raw22706step2 = -raw22706step1 := by apply Matrix.ext; change ∀ i j, raw22706step2 i j = -(raw22706step1 i j); unfold raw22706step2 raw22706step1; decide +kernel
      have hl : raw22706step2Labels = raw22706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22706step2 raw22706step2Labels = mixedMoment B raw22706step3 raw22706step3Labels := by
      have ha : raw22706step3 = raw22706step2 := by apply Matrix.ext; unfold raw22706step3 raw22706step2; decide +kernel
      have hl : raw22706step2Labels = labelEmbedding1 ∘ raw22706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22706step2 raw22706step2Labels raw22706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical22707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22707 raw22707Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw22707 raw22707Labels = mixedMoment B raw22707step0 raw22707step0Labels := by
      have hz : ∀ j, raw22707 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22707step0 = (fun i j => raw22707 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22707step0 raw22707; decide +kernel
      have hl : raw22707step0Labels = raw22707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22707 raw22707Labels permutation265 hz
    mixedMoment B raw22707step0 raw22707step0Labels = mixedMoment B raw22707step1 raw22707step1Labels := by
      have ha : raw22707step1 = (fun i j => raw22707step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22707step1 raw22707step0; decide +kernel
      have hl : raw22707step1Labels = raw22707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22707step0 raw22707step0Labels permutation39 permutation7
    mixedMoment B raw22707step1 raw22707step1Labels = mixedMoment B raw22707step2 raw22707step2Labels := by
      have ha : raw22707step2 = -raw22707step1 := by apply Matrix.ext; change ∀ i j, raw22707step2 i j = -(raw22707step1 i j); unfold raw22707step2 raw22707step1; decide +kernel
      have hl : raw22707step2Labels = raw22707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22707step2 raw22707step2Labels = mixedMoment B raw22707step3 raw22707step3Labels := by
      have ha : raw22707step3 = raw22707step2 := by apply Matrix.ext; unfold raw22707step3 raw22707step2; decide +kernel
      have hl : raw22707step2Labels = labelEmbedding1 ∘ raw22707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22707step2 raw22707step2Labels raw22707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical22708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22708 raw22708Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw22708 raw22708Labels = mixedMoment B raw22708step0 raw22708step0Labels := by
      have hz : ∀ j, raw22708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22708step0 = (fun i j => raw22708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22708step0 raw22708; decide +kernel
      have hl : raw22708step0Labels = raw22708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22708 raw22708Labels permutation346 hz
    mixedMoment B raw22708step0 raw22708step0Labels = mixedMoment B raw22708step1 raw22708step1Labels := by
      have hz : ∀ j, raw22708step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22708step1 = (fun i j => raw22708step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22708step1 raw22708step0; decide +kernel
      have hl : raw22708step1Labels = raw22708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22708step0 raw22708step0Labels permutation56 hz
    mixedMoment B raw22708step1 raw22708step1Labels = mixedMoment B raw22708step2 raw22708step2Labels := by
      have ha : raw22708step2 = (fun i j => raw22708step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22708step2 raw22708step1; decide +kernel
      have hl : raw22708step2Labels = raw22708step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22708step1 raw22708step1Labels permutation11 permutation5
    mixedMoment B raw22708step2 raw22708step2Labels = mixedMoment B raw22708step3 raw22708step3Labels := by
      have ha : raw22708step3 = -raw22708step2 := by apply Matrix.ext; change ∀ i j, raw22708step3 i j = -(raw22708step2 i j); unfold raw22708step3 raw22708step2; decide +kernel
      have hl : raw22708step3Labels = raw22708step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22708step3 raw22708step3Labels = mixedMoment B raw22708step4 raw22708step4Labels := by
      have ha : raw22708step4 = raw22708step3 := by apply Matrix.ext; unfold raw22708step4 raw22708step3; decide +kernel
      have hl : raw22708step3Labels = labelEmbedding1 ∘ raw22708step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22708step3 raw22708step3Labels raw22708step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

theorem canonical22709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22709 raw22709Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw22709 raw22709Labels = mixedMoment B raw22709step0 raw22709step0Labels := by
      have hz : ∀ j, raw22709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22709step0 = (fun i j => raw22709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22709step0 raw22709; decide +kernel
      have hl : raw22709step0Labels = raw22709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22709 raw22709Labels permutation346 hz
    mixedMoment B raw22709step0 raw22709step0Labels = mixedMoment B raw22709step1 raw22709step1Labels := by
      have ha : raw22709step1 = (fun i j => raw22709step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22709step1 raw22709step0; decide +kernel
      have hl : raw22709step1Labels = raw22709step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22709step0 raw22709step0Labels permutation35 permutation5
    mixedMoment B raw22709step1 raw22709step1Labels = mixedMoment B raw22709step2 raw22709step2Labels := by
      have ha : raw22709step2 = -raw22709step1 := by apply Matrix.ext; change ∀ i j, raw22709step2 i j = -(raw22709step1 i j); unfold raw22709step2 raw22709step1; decide +kernel
      have hl : raw22709step2Labels = raw22709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22709step2 raw22709step2Labels = mixedMoment B raw22709step3 raw22709step3Labels := by
      have ha : raw22709step3 = raw22709step2 := by apply Matrix.ext; unfold raw22709step3 raw22709step2; decide +kernel
      have hl : raw22709step2Labels = labelEmbedding1 ∘ raw22709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22709step2 raw22709step2Labels raw22709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

theorem canonical22710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22710 raw22710Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw22710 raw22710Labels = mixedMoment B raw22710step0 raw22710step0Labels := by
      have hz : ∀ j, raw22710 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22710step0 = (fun i j => raw22710 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22710step0 raw22710; decide +kernel
      have hl : raw22710step0Labels = raw22710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22710 raw22710Labels permutation265 hz
    mixedMoment B raw22710step0 raw22710step0Labels = mixedMoment B raw22710step1 raw22710step1Labels := by
      have ha : raw22710step1 = (fun i j => raw22710step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22710step1 raw22710step0; decide +kernel
      have hl : raw22710step1Labels = raw22710step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22710step0 raw22710step0Labels permutation35 permutation5
    mixedMoment B raw22710step1 raw22710step1Labels = mixedMoment B raw22710step2 raw22710step2Labels := by
      have ha : raw22710step2 = -raw22710step1 := by apply Matrix.ext; change ∀ i j, raw22710step2 i j = -(raw22710step1 i j); unfold raw22710step2 raw22710step1; decide +kernel
      have hl : raw22710step2Labels = raw22710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22710step2 raw22710step2Labels = mixedMoment B raw22710step3 raw22710step3Labels := by
      have ha : raw22710step3 = raw22710step2 := by apply Matrix.ext; unfold raw22710step3 raw22710step2; decide +kernel
      have hl : raw22710step2Labels = labelEmbedding1 ∘ raw22710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22710step2 raw22710step2Labels raw22710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

theorem canonical22711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22711 raw22711Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw22711 raw22711Labels = mixedMoment B raw22711step0 raw22711step0Labels := by
      have hz : ∀ j, raw22711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22711step0 = (fun i j => raw22711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22711step0 raw22711; decide +kernel
      have hl : raw22711step0Labels = raw22711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22711 raw22711Labels permutation346 hz
    mixedMoment B raw22711step0 raw22711step0Labels = mixedMoment B raw22711step1 raw22711step1Labels := by
      have hz : ∀ j, raw22711step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22711step1 = (fun i j => raw22711step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22711step1 raw22711step0; decide +kernel
      have hl : raw22711step1Labels = raw22711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22711step0 raw22711step0Labels permutation56 hz
    mixedMoment B raw22711step1 raw22711step1Labels = mixedMoment B raw22711step2 raw22711step2Labels := by
      have ha : raw22711step2 = (fun i j => raw22711step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22711step2 raw22711step1; decide +kernel
      have hl : raw22711step2Labels = raw22711step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22711step1 raw22711step1Labels permutation9 permutation7
    mixedMoment B raw22711step2 raw22711step2Labels = mixedMoment B raw22711step3 raw22711step3Labels := by
      have ha : raw22711step3 = -raw22711step2 := by apply Matrix.ext; change ∀ i j, raw22711step3 i j = -(raw22711step2 i j); unfold raw22711step3 raw22711step2; decide +kernel
      have hl : raw22711step3Labels = raw22711step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22711step3 raw22711step3Labels = mixedMoment B raw22711step4 raw22711step4Labels := by
      have ha : raw22711step4 = raw22711step3 := by apply Matrix.ext; unfold raw22711step4 raw22711step3; decide +kernel
      have hl : raw22711step3Labels = labelEmbedding1 ∘ raw22711step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22711step3 raw22711step3Labels raw22711step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical22712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22712 raw22712Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw22712 raw22712Labels = mixedMoment B raw22712step0 raw22712step0Labels := by
      have hz : ∀ j, raw22712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22712step0 = (fun i j => raw22712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22712step0 raw22712; decide +kernel
      have hl : raw22712step0Labels = raw22712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22712 raw22712Labels permutation346 hz
    mixedMoment B raw22712step0 raw22712step0Labels = mixedMoment B raw22712step1 raw22712step1Labels := by
      have hz : ∀ j, raw22712step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22712step1 = (fun i j => raw22712step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22712step1 raw22712step0; decide +kernel
      have hl : raw22712step1Labels = raw22712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22712step0 raw22712step0Labels permutation56 hz
    mixedMoment B raw22712step1 raw22712step1Labels = mixedMoment B raw22712step2 raw22712step2Labels := by
      have ha : raw22712step2 = (fun i j => raw22712step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22712step2 raw22712step1; decide +kernel
      have hl : raw22712step2Labels = raw22712step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22712step1 raw22712step1Labels permutation9 permutation5
    mixedMoment B raw22712step2 raw22712step2Labels = mixedMoment B raw22712step3 raw22712step3Labels := by
      have ha : raw22712step3 = -raw22712step2 := by apply Matrix.ext; change ∀ i j, raw22712step3 i j = -(raw22712step2 i j); unfold raw22712step3 raw22712step2; decide +kernel
      have hl : raw22712step3Labels = raw22712step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22712step3 raw22712step3Labels = mixedMoment B raw22712step4 raw22712step4Labels := by
      have ha : raw22712step4 = raw22712step3 := by apply Matrix.ext; unfold raw22712step4 raw22712step3; decide +kernel
      have hl : raw22712step3Labels = labelEmbedding1 ∘ raw22712step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22712step3 raw22712step3Labels raw22712step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical22713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22713 raw22713Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw22713 raw22713Labels = mixedMoment B raw22713step0 raw22713step0Labels := by
      have hz : ∀ j, raw22713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22713step0 = (fun i j => raw22713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22713step0 raw22713; decide +kernel
      have hl : raw22713step0Labels = raw22713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22713 raw22713Labels permutation346 hz
    mixedMoment B raw22713step0 raw22713step0Labels = mixedMoment B raw22713step1 raw22713step1Labels := by
      have ha : raw22713step1 = (fun i j => raw22713step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22713step1 raw22713step0; decide +kernel
      have hl : raw22713step1Labels = raw22713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22713step0 raw22713step0Labels permutation33 permutation5
    mixedMoment B raw22713step1 raw22713step1Labels = mixedMoment B raw22713step2 raw22713step2Labels := by
      have ha : raw22713step2 = -raw22713step1 := by apply Matrix.ext; change ∀ i j, raw22713step2 i j = -(raw22713step1 i j); unfold raw22713step2 raw22713step1; decide +kernel
      have hl : raw22713step2Labels = raw22713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22713step2 raw22713step2Labels = mixedMoment B raw22713step3 raw22713step3Labels := by
      have ha : raw22713step3 = raw22713step2 := by apply Matrix.ext; unfold raw22713step3 raw22713step2; decide +kernel
      have hl : raw22713step2Labels = labelEmbedding1 ∘ raw22713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22713step2 raw22713step2Labels raw22713step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical22714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22714 raw22714Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw22714 raw22714Labels = mixedMoment B raw22714step0 raw22714step0Labels := by
      have hz : ∀ j, raw22714 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22714step0 = (fun i j => raw22714 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22714step0 raw22714; decide +kernel
      have hl : raw22714step0Labels = raw22714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22714 raw22714Labels permutation265 hz
    mixedMoment B raw22714step0 raw22714step0Labels = mixedMoment B raw22714step1 raw22714step1Labels := by
      have ha : raw22714step1 = (fun i j => raw22714step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22714step1 raw22714step0; decide +kernel
      have hl : raw22714step1Labels = raw22714step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22714step0 raw22714step0Labels permutation33 permutation5
    mixedMoment B raw22714step1 raw22714step1Labels = mixedMoment B raw22714step2 raw22714step2Labels := by
      have ha : raw22714step2 = -raw22714step1 := by apply Matrix.ext; change ∀ i j, raw22714step2 i j = -(raw22714step1 i j); unfold raw22714step2 raw22714step1; decide +kernel
      have hl : raw22714step2Labels = raw22714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22714step2 raw22714step2Labels = mixedMoment B raw22714step3 raw22714step3Labels := by
      have ha : raw22714step3 = raw22714step2 := by apply Matrix.ext; unfold raw22714step3 raw22714step2; decide +kernel
      have hl : raw22714step2Labels = labelEmbedding1 ∘ raw22714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22714step2 raw22714step2Labels raw22714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

theorem canonical22715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22715 raw22715Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw22715 raw22715Labels = mixedMoment B raw22715step0 raw22715step0Labels := by
      have hz : ∀ j, raw22715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22715step0 = (fun i j => raw22715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22715step0 raw22715; decide +kernel
      have hl : raw22715step0Labels = raw22715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22715 raw22715Labels permutation346 hz
    mixedMoment B raw22715step0 raw22715step0Labels = mixedMoment B raw22715step1 raw22715step1Labels := by
      have hz : ∀ j, raw22715step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22715step1 = (fun i j => raw22715step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22715step1 raw22715step0; decide +kernel
      have hl : raw22715step1Labels = raw22715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22715step0 raw22715step0Labels permutation56 hz
    mixedMoment B raw22715step1 raw22715step1Labels = mixedMoment B raw22715step2 raw22715step2Labels := by
      have ha : raw22715step2 = (fun i j => raw22715step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22715step2 raw22715step1; decide +kernel
      have hl : raw22715step2Labels = raw22715step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22715step1 raw22715step1Labels permutation9 permutation7
    mixedMoment B raw22715step2 raw22715step2Labels = mixedMoment B raw22715step3 raw22715step3Labels := by
      have ha : raw22715step3 = -raw22715step2 := by apply Matrix.ext; change ∀ i j, raw22715step3 i j = -(raw22715step2 i j); unfold raw22715step3 raw22715step2; decide +kernel
      have hl : raw22715step3Labels = raw22715step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22715step3 raw22715step3Labels = mixedMoment B raw22715step4 raw22715step4Labels := by
      have ha : raw22715step4 = raw22715step3 := by apply Matrix.ext; unfold raw22715step4 raw22715step3; decide +kernel
      have hl : raw22715step3Labels = labelEmbedding1 ∘ raw22715step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22715step3 raw22715step3Labels raw22715step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

theorem canonical22716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22716 raw22716Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw22716 raw22716Labels = mixedMoment B raw22716step0 raw22716step0Labels := by
      have hz : ∀ j, raw22716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22716step0 = (fun i j => raw22716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22716step0 raw22716; decide +kernel
      have hl : raw22716step0Labels = raw22716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22716 raw22716Labels permutation346 hz
    mixedMoment B raw22716step0 raw22716step0Labels = mixedMoment B raw22716step1 raw22716step1Labels := by
      have hz : ∀ j, raw22716step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22716step1 = (fun i j => raw22716step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22716step1 raw22716step0; decide +kernel
      have hl : raw22716step1Labels = raw22716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22716step0 raw22716step0Labels permutation56 hz
    mixedMoment B raw22716step1 raw22716step1Labels = mixedMoment B raw22716step2 raw22716step2Labels := by
      have ha : raw22716step2 = (fun i j => raw22716step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22716step2 raw22716step1; decide +kernel
      have hl : raw22716step2Labels = raw22716step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22716step1 raw22716step1Labels permutation9 permutation7
    mixedMoment B raw22716step2 raw22716step2Labels = mixedMoment B raw22716step3 raw22716step3Labels := by
      have ha : raw22716step3 = -raw22716step2 := by apply Matrix.ext; change ∀ i j, raw22716step3 i j = -(raw22716step2 i j); unfold raw22716step3 raw22716step2; decide +kernel
      have hl : raw22716step3Labels = raw22716step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22716step3 raw22716step3Labels = mixedMoment B raw22716step4 raw22716step4Labels := by
      have ha : raw22716step4 = raw22716step3 := by apply Matrix.ext; unfold raw22716step4 raw22716step3; decide +kernel
      have hl : raw22716step3Labels = labelEmbedding1 ∘ raw22716step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22716step3 raw22716step3Labels raw22716step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical22717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22717 raw22717Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw22717 raw22717Labels = mixedMoment B raw22717step0 raw22717step0Labels := by
      have hz : ∀ j, raw22717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22717step0 = (fun i j => raw22717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22717step0 raw22717; decide +kernel
      have hl : raw22717step0Labels = raw22717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22717 raw22717Labels permutation346 hz
    mixedMoment B raw22717step0 raw22717step0Labels = mixedMoment B raw22717step1 raw22717step1Labels := by
      have hz : ∀ j, raw22717step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22717step1 = (fun i j => raw22717step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22717step1 raw22717step0; decide +kernel
      have hl : raw22717step1Labels = raw22717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22717step0 raw22717step0Labels permutation56 hz
    mixedMoment B raw22717step1 raw22717step1Labels = mixedMoment B raw22717step2 raw22717step2Labels := by
      have ha : raw22717step2 = (fun i j => raw22717step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22717step2 raw22717step1; decide +kernel
      have hl : raw22717step2Labels = raw22717step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22717step1 raw22717step1Labels permutation10 permutation5
    mixedMoment B raw22717step2 raw22717step2Labels = mixedMoment B raw22717step3 raw22717step3Labels := by
      have ha : raw22717step3 = -raw22717step2 := by apply Matrix.ext; change ∀ i j, raw22717step3 i j = -(raw22717step2 i j); unfold raw22717step3 raw22717step2; decide +kernel
      have hl : raw22717step3Labels = raw22717step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22717step3 raw22717step3Labels = mixedMoment B raw22717step4 raw22717step4Labels := by
      have ha : raw22717step4 = raw22717step3 := by apply Matrix.ext; unfold raw22717step4 raw22717step3; decide +kernel
      have hl : raw22717step3Labels = labelEmbedding1 ∘ raw22717step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22717step3 raw22717step3Labels raw22717step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

theorem canonical22718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22718 raw22718Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw22718 raw22718Labels = mixedMoment B raw22718step0 raw22718step0Labels := by
      have hz : ∀ j, raw22718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22718step0 = (fun i j => raw22718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22718step0 raw22718; decide +kernel
      have hl : raw22718step0Labels = raw22718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22718 raw22718Labels permutation346 hz
    mixedMoment B raw22718step0 raw22718step0Labels = mixedMoment B raw22718step1 raw22718step1Labels := by
      have ha : raw22718step1 = (fun i j => raw22718step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22718step1 raw22718step0; decide +kernel
      have hl : raw22718step1Labels = raw22718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22718step0 raw22718step0Labels permutation34 permutation5
    mixedMoment B raw22718step1 raw22718step1Labels = mixedMoment B raw22718step2 raw22718step2Labels := by
      have ha : raw22718step2 = -raw22718step1 := by apply Matrix.ext; change ∀ i j, raw22718step2 i j = -(raw22718step1 i j); unfold raw22718step2 raw22718step1; decide +kernel
      have hl : raw22718step2Labels = raw22718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22718step2 raw22718step2Labels = mixedMoment B raw22718step3 raw22718step3Labels := by
      have ha : raw22718step3 = raw22718step2 := by apply Matrix.ext; unfold raw22718step3 raw22718step2; decide +kernel
      have hl : raw22718step2Labels = labelEmbedding1 ∘ raw22718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22718step2 raw22718step2Labels raw22718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical22719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22719 raw22719Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw22719 raw22719Labels = mixedMoment B raw22719step0 raw22719step0Labels := by
      have hz : ∀ j, raw22719 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22719step0 = (fun i j => raw22719 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22719step0 raw22719; decide +kernel
      have hl : raw22719step0Labels = raw22719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22719 raw22719Labels permutation265 hz
    mixedMoment B raw22719step0 raw22719step0Labels = mixedMoment B raw22719step1 raw22719step1Labels := by
      have ha : raw22719step1 = (fun i j => raw22719step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22719step1 raw22719step0; decide +kernel
      have hl : raw22719step1Labels = raw22719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22719step0 raw22719step0Labels permutation34 permutation5
    mixedMoment B raw22719step1 raw22719step1Labels = mixedMoment B raw22719step2 raw22719step2Labels := by
      have ha : raw22719step2 = -raw22719step1 := by apply Matrix.ext; change ∀ i j, raw22719step2 i j = -(raw22719step1 i j); unfold raw22719step2 raw22719step1; decide +kernel
      have hl : raw22719step2Labels = raw22719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22719step2 raw22719step2Labels = mixedMoment B raw22719step3 raw22719step3Labels := by
      have ha : raw22719step3 = raw22719step2 := by apply Matrix.ext; unfold raw22719step3 raw22719step2; decide +kernel
      have hl : raw22719step2Labels = labelEmbedding1 ∘ raw22719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22719step2 raw22719step2Labels raw22719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

theorem canonical22720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22720 raw22720Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw22720 raw22720Labels = mixedMoment B raw22720step0 raw22720step0Labels := by
      have hz : ∀ j, raw22720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22720step0 = (fun i j => raw22720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22720step0 raw22720; decide +kernel
      have hl : raw22720step0Labels = raw22720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22720 raw22720Labels permutation346 hz
    mixedMoment B raw22720step0 raw22720step0Labels = mixedMoment B raw22720step1 raw22720step1Labels := by
      have hz : ∀ j, raw22720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22720step1 = (fun i j => raw22720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22720step1 raw22720step0; decide +kernel
      have hl : raw22720step1Labels = raw22720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22720step0 raw22720step0Labels permutation56 hz
    mixedMoment B raw22720step1 raw22720step1Labels = mixedMoment B raw22720step2 raw22720step2Labels := by
      have ha : raw22720step2 = (fun i j => raw22720step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22720step2 raw22720step1; decide +kernel
      have hl : raw22720step2Labels = raw22720step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22720step1 raw22720step1Labels permutation9 permutation7
    mixedMoment B raw22720step2 raw22720step2Labels = mixedMoment B raw22720step3 raw22720step3Labels := by
      have ha : raw22720step3 = -raw22720step2 := by apply Matrix.ext; change ∀ i j, raw22720step3 i j = -(raw22720step2 i j); unfold raw22720step3 raw22720step2; decide +kernel
      have hl : raw22720step3Labels = raw22720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22720step3 raw22720step3Labels = mixedMoment B raw22720step4 raw22720step4Labels := by
      have ha : raw22720step4 = raw22720step3 := by apply Matrix.ext; unfold raw22720step4 raw22720step3; decide +kernel
      have hl : raw22720step3Labels = labelEmbedding1 ∘ raw22720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22720step3 raw22720step3Labels raw22720step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

theorem canonical22721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22721 raw22721Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw22721 raw22721Labels = mixedMoment B raw22721step0 raw22721step0Labels := by
      have hz : ∀ j, raw22721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22721step0 = (fun i j => raw22721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22721step0 raw22721; decide +kernel
      have hl : raw22721step0Labels = raw22721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22721 raw22721Labels permutation346 hz
    mixedMoment B raw22721step0 raw22721step0Labels = mixedMoment B raw22721step1 raw22721step1Labels := by
      have ha : raw22721step1 = (fun i j => raw22721step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22721step1 raw22721step0; decide +kernel
      have hl : raw22721step1Labels = raw22721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22721step0 raw22721step0Labels permutation39 permutation2
    _ = mixedMoment B node627 node627Labels := by rfl

theorem canonical22722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22722 raw22722Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw22722 raw22722Labels = mixedMoment B raw22722step0 raw22722step0Labels := by
      have hz : ∀ j, raw22722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22722step0 = (fun i j => raw22722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22722step0 raw22722; decide +kernel
      have hl : raw22722step0Labels = raw22722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22722 raw22722Labels permutation265 hz
    mixedMoment B raw22722step0 raw22722step0Labels = mixedMoment B raw22722step1 raw22722step1Labels := by
      have ha : raw22722step1 = (fun i j => raw22722step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22722step1 raw22722step0; decide +kernel
      have hl : raw22722step1Labels = raw22722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22722step0 raw22722step0Labels permutation39 permutation2
    _ = mixedMoment B node627 node627Labels := by rfl

theorem canonical22723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22723 raw22723Labels = mixedMoment B node642 node642Labels := by
  calc
    mixedMoment B raw22723 raw22723Labels = mixedMoment B raw22723step0 raw22723step0Labels := by
      have hz : ∀ j, raw22723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22723step0 = (fun i j => raw22723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22723step0 raw22723; decide +kernel
      have hl : raw22723step0Labels = raw22723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22723 raw22723Labels permutation346 hz
    mixedMoment B raw22723step0 raw22723step0Labels = mixedMoment B raw22723step1 raw22723step1Labels := by
      have hz : ∀ j, raw22723step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22723step1 = (fun i j => raw22723step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22723step1 raw22723step0; decide +kernel
      have hl : raw22723step1Labels = raw22723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22723step0 raw22723step0Labels permutation56 hz
    mixedMoment B raw22723step1 raw22723step1Labels = mixedMoment B raw22723step2 raw22723step2Labels := by
      have ha : raw22723step2 = (fun i j => raw22723step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22723step2 raw22723step1; decide +kernel
      have hl : raw22723step2Labels = raw22723step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22723step1 raw22723step1Labels permutation9 permutation2
    _ = mixedMoment B node642 node642Labels := by rfl

theorem canonical22724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22724 raw22724Labels = mixedMoment B node635 node635Labels := by
  calc
    mixedMoment B raw22724 raw22724Labels = mixedMoment B raw22724step0 raw22724step0Labels := by
      have hz : ∀ j, raw22724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22724step0 = (fun i j => raw22724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22724step0 raw22724; decide +kernel
      have hl : raw22724step0Labels = raw22724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22724 raw22724Labels permutation346 hz
    mixedMoment B raw22724step0 raw22724step0Labels = mixedMoment B raw22724step1 raw22724step1Labels := by
      have hz : ∀ j, raw22724step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22724step1 = (fun i j => raw22724step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22724step1 raw22724step0; decide +kernel
      have hl : raw22724step1Labels = raw22724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22724step0 raw22724step0Labels permutation56 hz
    mixedMoment B raw22724step1 raw22724step1Labels = mixedMoment B raw22724step2 raw22724step2Labels := by
      have ha : raw22724step2 = (fun i j => raw22724step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22724step2 raw22724step1; decide +kernel
      have hl : raw22724step2Labels = raw22724step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22724step1 raw22724step1Labels permutation9 permutation2
    _ = mixedMoment B node635 node635Labels := by rfl

theorem canonical22725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22725 raw22725Labels = mixedMoment B node636 node636Labels := by
  calc
    mixedMoment B raw22725 raw22725Labels = mixedMoment B raw22725step0 raw22725step0Labels := by
      have hz : ∀ j, raw22725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22725step0 = (fun i j => raw22725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22725step0 raw22725; decide +kernel
      have hl : raw22725step0Labels = raw22725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22725 raw22725Labels permutation346 hz
    mixedMoment B raw22725step0 raw22725step0Labels = mixedMoment B raw22725step1 raw22725step1Labels := by
      have hz : ∀ j, raw22725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22725step1 = (fun i j => raw22725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22725step1 raw22725step0; decide +kernel
      have hl : raw22725step1Labels = raw22725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22725step0 raw22725step0Labels permutation56 hz
    _ = mixedMoment B node636 node636Labels := by rfl

theorem canonical22726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22726 raw22726Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw22726 raw22726Labels = mixedMoment B raw22726step0 raw22726step0Labels := by
      have ha : raw22726step0 = (fun i j => raw22726 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22726step0 raw22726; decide +kernel
      have hl : raw22726step0Labels = raw22726Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22726 raw22726Labels permutation183 permutation2
    _ = mixedMoment B node1149 node1149Labels := by rfl

theorem canonical22727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22727 raw22727Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw22727 raw22727Labels = mixedMoment B raw22727step0 raw22727step0Labels := by
      have hz : ∀ j, raw22727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22727step0 = (fun i j => raw22727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22727step0 raw22727; decide +kernel
      have hl : raw22727step0Labels = raw22727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22727 raw22727Labels permutation346 hz
    mixedMoment B raw22727step0 raw22727step0Labels = mixedMoment B raw22727step1 raw22727step1Labels := by
      have ha : raw22727step1 = (fun i j => raw22727step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22727step1 raw22727step0; decide +kernel
      have hl : raw22727step1Labels = raw22727step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22727step0 raw22727step0Labels permutation39 permutation2
    _ = mixedMoment B node1134 node1134Labels := by rfl

theorem canonical22728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22728 raw22728Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw22728 raw22728Labels = mixedMoment B raw22728step0 raw22728step0Labels := by
      have hz : ∀ j, raw22728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22728step0 = (fun i j => raw22728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22728step0 raw22728; decide +kernel
      have hl : raw22728step0Labels = raw22728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22728 raw22728Labels permutation346 hz
    mixedMoment B raw22728step0 raw22728step0Labels = mixedMoment B raw22728step1 raw22728step1Labels := by
      have ha : raw22728step1 = (fun i j => raw22728step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22728step1 raw22728step0; decide +kernel
      have hl : raw22728step1Labels = raw22728step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22728step0 raw22728step0Labels permutation38 permutation2
    _ = mixedMoment B node1237 node1237Labels := by rfl

theorem canonical22729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22729 raw22729Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw22729 raw22729Labels = mixedMoment B raw22729step0 raw22729step0Labels := by
      have hz : ∀ j, raw22729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22729step0 = (fun i j => raw22729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22729step0 raw22729; decide +kernel
      have hl : raw22729step0Labels = raw22729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22729 raw22729Labels permutation346 hz
    mixedMoment B raw22729step0 raw22729step0Labels = mixedMoment B raw22729step1 raw22729step1Labels := by
      have ha : raw22729step1 = (fun i j => raw22729step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22729step1 raw22729step0; decide +kernel
      have hl : raw22729step1Labels = raw22729step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22729step0 raw22729step0Labels permutation39 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical22730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22730 raw22730Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw22730 raw22730Labels = mixedMoment B raw22730step0 raw22730step0Labels := by
      have ha : raw22730step0 = (fun i j => raw22730 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22730step0 raw22730; decide +kernel
      have hl : raw22730step0Labels = raw22730Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22730 raw22730Labels permutation159 permutation2
    _ = mixedMoment B node1149 node1149Labels := by rfl

theorem canonical22731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22731 raw22731Labels = mixedMoment B node1160 node1160Labels := by
  calc
    mixedMoment B raw22731 raw22731Labels = mixedMoment B raw22731step0 raw22731step0Labels := by
      have hz : ∀ j, raw22731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22731step0 = (fun i j => raw22731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22731step0 raw22731; decide +kernel
      have hl : raw22731step0Labels = raw22731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22731 raw22731Labels permutation346 hz
    mixedMoment B raw22731step0 raw22731step0Labels = mixedMoment B raw22731step1 raw22731step1Labels := by
      have ha : raw22731step1 = (fun i j => raw22731step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22731step1 raw22731step0; decide +kernel
      have hl : raw22731step1Labels = raw22731step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22731step0 raw22731step0Labels permutation33 permutation2
    _ = mixedMoment B node1160 node1160Labels := by rfl

theorem canonical22732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22732 raw22732Labels = mixedMoment B node1154 node1154Labels := by
  calc
    mixedMoment B raw22732 raw22732Labels = mixedMoment B raw22732step0 raw22732step0Labels := by
      have hz : ∀ j, raw22732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22732step0 = (fun i j => raw22732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22732step0 raw22732; decide +kernel
      have hl : raw22732step0Labels = raw22732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22732 raw22732Labels permutation346 hz
    mixedMoment B raw22732step0 raw22732step0Labels = mixedMoment B raw22732step1 raw22732step1Labels := by
      have ha : raw22732step1 = (fun i j => raw22732step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22732step1 raw22732step0; decide +kernel
      have hl : raw22732step1Labels = raw22732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22732step0 raw22732step0Labels permutation33 permutation2
    _ = mixedMoment B node1154 node1154Labels := by rfl

theorem canonical22733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22733 raw22733Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw22733 raw22733Labels = mixedMoment B raw22733step0 raw22733step0Labels := by
      have hz : ∀ j, raw22733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22733step0 = (fun i j => raw22733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22733step0 raw22733; decide +kernel
      have hl : raw22733step0Labels = raw22733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22733 raw22733Labels permutation346 hz
    _ = mixedMoment B node1155 node1155Labels := by rfl

theorem canonical22734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22734 raw22734Labels = mixedMoment B node1160 node1160Labels := by
  calc
    mixedMoment B raw22734 raw22734Labels = mixedMoment B raw22734step0 raw22734step0Labels := by
      have hz : ∀ j, raw22734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22734step0 = (fun i j => raw22734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22734step0 raw22734; decide +kernel
      have hl : raw22734step0Labels = raw22734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22734 raw22734Labels permutation265 hz
    mixedMoment B raw22734step0 raw22734step0Labels = mixedMoment B raw22734step1 raw22734step1Labels := by
      have ha : raw22734step1 = (fun i j => raw22734step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22734step1 raw22734step0; decide +kernel
      have hl : raw22734step1Labels = raw22734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22734step0 raw22734step0Labels permutation33 permutation2
    _ = mixedMoment B node1160 node1160Labels := by rfl

theorem canonical22735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22735 raw22735Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw22735 raw22735Labels = mixedMoment B raw22735step0 raw22735step0Labels := by
      have hz : ∀ j, raw22735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22735step0 = (fun i j => raw22735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22735step0 raw22735; decide +kernel
      have hl : raw22735step0Labels = raw22735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22735 raw22735Labels permutation346 hz
    mixedMoment B raw22735step0 raw22735step0Labels = mixedMoment B raw22735step1 raw22735step1Labels := by
      have hz : ∀ j, raw22735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22735step1 = (fun i j => raw22735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22735step1 raw22735step0; decide +kernel
      have hl : raw22735step1Labels = raw22735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22735step0 raw22735step0Labels permutation56 hz
    _ = mixedMoment B node1295 node1295Labels := by rfl

theorem canonical22736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22736 raw22736Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw22736 raw22736Labels = mixedMoment B raw22736step0 raw22736step0Labels := by
      have hz : ∀ j, raw22736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22736step0 = (fun i j => raw22736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22736step0 raw22736; decide +kernel
      have hl : raw22736step0Labels = raw22736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22736 raw22736Labels permutation346 hz
    mixedMoment B raw22736step0 raw22736step0Labels = mixedMoment B raw22736step1 raw22736step1Labels := by
      have hz : ∀ j, raw22736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22736step1 = (fun i j => raw22736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22736step1 raw22736step0; decide +kernel
      have hl : raw22736step1Labels = raw22736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22736step0 raw22736step0Labels permutation56 hz
    mixedMoment B raw22736step1 raw22736step1Labels = mixedMoment B raw22736step2 raw22736step2Labels := by
      have ha : raw22736step2 = (fun i j => raw22736step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22736step2 raw22736step1; decide +kernel
      have hl : raw22736step2Labels = raw22736step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22736step1 raw22736step1Labels permutation9 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

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

theorem canonical10347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10347 raw10347Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw10347 raw10347Labels = mixedMoment B raw10347step0 raw10347step0Labels := by
      have hz : ∀ j, raw10347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10347step0 = (fun i j => raw10347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10347step0 raw10347; decide +kernel
      have hl : raw10347step0Labels = raw10347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10347 raw10347Labels permutation346 hz
    mixedMoment B raw10347step0 raw10347step0Labels = mixedMoment B raw10347step1 raw10347step1Labels := by
      have ha : raw10347step1 = (fun i j => raw10347step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10347step1 raw10347step0; decide +kernel
      have hl : raw10347step1Labels = raw10347step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10347step0 raw10347step0Labels permutation38 permutation2
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical10352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10352 raw10352Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw10352 raw10352Labels = mixedMoment B raw10352step0 raw10352step0Labels := by
      have hz : ∀ j, raw10352 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10352step0 = (fun i j => raw10352 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10352step0 raw10352; decide +kernel
      have hl : raw10352step0Labels = raw10352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10352 raw10352Labels permutation265 hz
    mixedMoment B raw10352step0 raw10352step0Labels = mixedMoment B raw10352step1 raw10352step1Labels := by
      have ha : raw10352step1 = (fun i j => raw10352step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10352step1 raw10352step0; decide +kernel
      have hl : raw10352step1Labels = raw10352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10352step0 raw10352step0Labels permutation38 permutation2
    _ = mixedMoment B node4603 node4603Labels := by rfl

theorem canonical10357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10357 raw10357Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw10357 raw10357Labels = mixedMoment B raw10357step0 raw10357step0Labels := by
      have hz : ∀ j, raw10357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10357step0 = (fun i j => raw10357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10357step0 raw10357; decide +kernel
      have hl : raw10357step0Labels = raw10357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10357 raw10357Labels permutation346 hz
    mixedMoment B raw10357step0 raw10357step0Labels = mixedMoment B raw10357step1 raw10357step1Labels := by
      have hz : ∀ j, raw10357step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10357step1 = (fun i j => raw10357step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10357step1 raw10357step0; decide +kernel
      have hl : raw10357step1Labels = raw10357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10357step0 raw10357step0Labels permutation56 hz
    _ = mixedMoment B node4620 node4620Labels := by rfl

theorem canonical10363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10363 raw10363Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10363 raw10363Labels = mixedMoment B raw10363step0 raw10363step0Labels := by
      have hz : ∀ j, raw10363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10363step0 = (fun i j => raw10363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10363step0 raw10363; decide +kernel
      have hl : raw10363step0Labels = raw10363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10363 raw10363Labels permutation346 hz
    mixedMoment B raw10363step0 raw10363step0Labels = mixedMoment B raw10363step1 raw10363step1Labels := by
      have ha : raw10363step1 = (fun i j => raw10363step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10363step1 raw10363step0; decide +kernel
      have hl : raw10363step1Labels = raw10363step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10363step0 raw10363step0Labels permutation33 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

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

theorem canonical10367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10367 raw10367Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw10367 raw10367Labels = mixedMoment B raw10367step0 raw10367step0Labels := by
      have hz : ∀ j, raw10367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10367step0 = (fun i j => raw10367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10367step0 raw10367; decide +kernel
      have hl : raw10367step0Labels = raw10367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10367 raw10367Labels permutation346 hz
    mixedMoment B raw10367step0 raw10367step0Labels = mixedMoment B raw10367step1 raw10367step1Labels := by
      have hz : ∀ j, raw10367step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10367step1 = (fun i j => raw10367step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10367step1 raw10367step0; decide +kernel
      have hl : raw10367step1Labels = raw10367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10367step0 raw10367step0Labels permutation56 hz
    _ = mixedMoment B node4609 node4609Labels := by rfl

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

theorem canonical10407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10407 raw10407Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw10407 raw10407Labels = mixedMoment B raw10407step0 raw10407step0Labels := by
      have hz : ∀ j, raw10407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10407step0 = (fun i j => raw10407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10407step0 raw10407; decide +kernel
      have hl : raw10407step0Labels = raw10407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10407 raw10407Labels permutation346 hz
    mixedMoment B raw10407step0 raw10407step0Labels = mixedMoment B raw10407step1 raw10407step1Labels := by
      have ha : raw10407step1 = (fun i j => raw10407step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10407step1 raw10407step0; decide +kernel
      have hl : raw10407step1Labels = raw10407step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10407step0 raw10407step0Labels permutation39 permutation7
    mixedMoment B raw10407step1 raw10407step1Labels = mixedMoment B raw10407step2 raw10407step2Labels := by
      have ha : raw10407step2 = -raw10407step1 := by apply Matrix.ext; change ∀ i j, raw10407step2 i j = -(raw10407step1 i j); unfold raw10407step2 raw10407step1; decide +kernel
      have hl : raw10407step2Labels = raw10407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10407step2 raw10407step2Labels = mixedMoment B raw10407step3 raw10407step3Labels := by
      have ha : raw10407step3 = raw10407step2 := by apply Matrix.ext; unfold raw10407step3 raw10407step2; decide +kernel
      have hl : raw10407step2Labels = labelEmbedding1 ∘ raw10407step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10407step2 raw10407step2Labels raw10407step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical10412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10412 raw10412Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw10412 raw10412Labels = mixedMoment B raw10412step0 raw10412step0Labels := by
      have hz : ∀ j, raw10412 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10412step0 = (fun i j => raw10412 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10412step0 raw10412; decide +kernel
      have hl : raw10412step0Labels = raw10412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10412 raw10412Labels permutation265 hz
    mixedMoment B raw10412step0 raw10412step0Labels = mixedMoment B raw10412step1 raw10412step1Labels := by
      have ha : raw10412step1 = (fun i j => raw10412step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10412step1 raw10412step0; decide +kernel
      have hl : raw10412step1Labels = raw10412step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10412step0 raw10412step0Labels permutation39 permutation7
    mixedMoment B raw10412step1 raw10412step1Labels = mixedMoment B raw10412step2 raw10412step2Labels := by
      have ha : raw10412step2 = -raw10412step1 := by apply Matrix.ext; change ∀ i j, raw10412step2 i j = -(raw10412step1 i j); unfold raw10412step2 raw10412step1; decide +kernel
      have hl : raw10412step2Labels = raw10412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10412step2 raw10412step2Labels = mixedMoment B raw10412step3 raw10412step3Labels := by
      have ha : raw10412step3 = raw10412step2 := by apply Matrix.ext; unfold raw10412step3 raw10412step2; decide +kernel
      have hl : raw10412step2Labels = labelEmbedding1 ∘ raw10412step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10412step2 raw10412step2Labels raw10412step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical10417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10417 raw10417Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw10417 raw10417Labels = mixedMoment B raw10417step0 raw10417step0Labels := by
      have hz : ∀ j, raw10417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10417step0 = (fun i j => raw10417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10417step0 raw10417; decide +kernel
      have hl : raw10417step0Labels = raw10417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10417 raw10417Labels permutation346 hz
    mixedMoment B raw10417step0 raw10417step0Labels = mixedMoment B raw10417step1 raw10417step1Labels := by
      have hz : ∀ j, raw10417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10417step1 = (fun i j => raw10417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10417step1 raw10417step0; decide +kernel
      have hl : raw10417step1Labels = raw10417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10417step0 raw10417step0Labels permutation56 hz
    mixedMoment B raw10417step1 raw10417step1Labels = mixedMoment B raw10417step2 raw10417step2Labels := by
      have ha : raw10417step2 = (fun i j => raw10417step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10417step2 raw10417step1; decide +kernel
      have hl : raw10417step2Labels = raw10417step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10417step1 raw10417step1Labels permutation11 permutation5
    mixedMoment B raw10417step2 raw10417step2Labels = mixedMoment B raw10417step3 raw10417step3Labels := by
      have ha : raw10417step3 = -raw10417step2 := by apply Matrix.ext; change ∀ i j, raw10417step3 i j = -(raw10417step2 i j); unfold raw10417step3 raw10417step2; decide +kernel
      have hl : raw10417step3Labels = raw10417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10417step3 raw10417step3Labels = mixedMoment B raw10417step4 raw10417step4Labels := by
      have ha : raw10417step4 = raw10417step3 := by apply Matrix.ext; unfold raw10417step4 raw10417step3; decide +kernel
      have hl : raw10417step3Labels = labelEmbedding1 ∘ raw10417step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10417step3 raw10417step3Labels raw10417step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3306 node3306Labels := by rfl

theorem canonical10423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10423 raw10423Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw10423 raw10423Labels = mixedMoment B raw10423step0 raw10423step0Labels := by
      have hz : ∀ j, raw10423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10423step0 = (fun i j => raw10423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10423step0 raw10423; decide +kernel
      have hl : raw10423step0Labels = raw10423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10423 raw10423Labels permutation346 hz
    mixedMoment B raw10423step0 raw10423step0Labels = mixedMoment B raw10423step1 raw10423step1Labels := by
      have ha : raw10423step1 = (fun i j => raw10423step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10423step1 raw10423step0; decide +kernel
      have hl : raw10423step1Labels = raw10423step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10423step0 raw10423step0Labels permutation39 permutation7
    mixedMoment B raw10423step1 raw10423step1Labels = mixedMoment B raw10423step2 raw10423step2Labels := by
      have ha : raw10423step2 = -raw10423step1 := by apply Matrix.ext; change ∀ i j, raw10423step2 i j = -(raw10423step1 i j); unfold raw10423step2 raw10423step1; decide +kernel
      have hl : raw10423step2Labels = raw10423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10423step2 raw10423step2Labels = mixedMoment B raw10423step3 raw10423step3Labels := by
      have ha : raw10423step3 = raw10423step2 := by apply Matrix.ext; unfold raw10423step3 raw10423step2; decide +kernel
      have hl : raw10423step2Labels = labelEmbedding1 ∘ raw10423step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10423step2 raw10423step2Labels raw10423step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical10424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10424 raw10424Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw10424 raw10424Labels = mixedMoment B raw10424step0 raw10424step0Labels := by
      have hz : ∀ j, raw10424 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10424step0 = (fun i j => raw10424 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10424step0 raw10424; decide +kernel
      have hl : raw10424step0Labels = raw10424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10424 raw10424Labels permutation265 hz
    mixedMoment B raw10424step0 raw10424step0Labels = mixedMoment B raw10424step1 raw10424step1Labels := by
      have ha : raw10424step1 = (fun i j => raw10424step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10424step1 raw10424step0; decide +kernel
      have hl : raw10424step1Labels = raw10424step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10424step0 raw10424step0Labels permutation39 permutation7
    mixedMoment B raw10424step1 raw10424step1Labels = mixedMoment B raw10424step2 raw10424step2Labels := by
      have ha : raw10424step2 = -raw10424step1 := by apply Matrix.ext; change ∀ i j, raw10424step2 i j = -(raw10424step1 i j); unfold raw10424step2 raw10424step1; decide +kernel
      have hl : raw10424step2Labels = raw10424step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10424step2 raw10424step2Labels = mixedMoment B raw10424step3 raw10424step3Labels := by
      have ha : raw10424step3 = raw10424step2 := by apply Matrix.ext; unfold raw10424step3 raw10424step2; decide +kernel
      have hl : raw10424step2Labels = labelEmbedding1 ∘ raw10424step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10424step2 raw10424step2Labels raw10424step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical10425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10425 raw10425Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw10425 raw10425Labels = mixedMoment B raw10425step0 raw10425step0Labels := by
      have hz : ∀ j, raw10425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10425step0 = (fun i j => raw10425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10425step0 raw10425; decide +kernel
      have hl : raw10425step0Labels = raw10425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10425 raw10425Labels permutation346 hz
    mixedMoment B raw10425step0 raw10425step0Labels = mixedMoment B raw10425step1 raw10425step1Labels := by
      have hz : ∀ j, raw10425step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10425step1 = (fun i j => raw10425step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10425step1 raw10425step0; decide +kernel
      have hl : raw10425step1Labels = raw10425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10425step0 raw10425step0Labels permutation56 hz
    mixedMoment B raw10425step1 raw10425step1Labels = mixedMoment B raw10425step2 raw10425step2Labels := by
      have ha : raw10425step2 = (fun i j => raw10425step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10425step2 raw10425step1; decide +kernel
      have hl : raw10425step2Labels = raw10425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10425step1 raw10425step1Labels permutation9 permutation7
    mixedMoment B raw10425step2 raw10425step2Labels = mixedMoment B raw10425step3 raw10425step3Labels := by
      have ha : raw10425step3 = -raw10425step2 := by apply Matrix.ext; change ∀ i j, raw10425step3 i j = -(raw10425step2 i j); unfold raw10425step3 raw10425step2; decide +kernel
      have hl : raw10425step3Labels = raw10425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10425step3 raw10425step3Labels = mixedMoment B raw10425step4 raw10425step4Labels := by
      have ha : raw10425step4 = raw10425step3 := by apply Matrix.ext; unfold raw10425step4 raw10425step3; decide +kernel
      have hl : raw10425step3Labels = labelEmbedding1 ∘ raw10425step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10425step3 raw10425step3Labels raw10425step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

theorem canonical10426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10426 raw10426Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw10426 raw10426Labels = mixedMoment B raw10426step0 raw10426step0Labels := by
      have hz : ∀ j, raw10426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10426step0 = (fun i j => raw10426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10426step0 raw10426; decide +kernel
      have hl : raw10426step0Labels = raw10426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10426 raw10426Labels permutation346 hz
    mixedMoment B raw10426step0 raw10426step0Labels = mixedMoment B raw10426step1 raw10426step1Labels := by
      have hz : ∀ j, raw10426step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10426step1 = (fun i j => raw10426step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10426step1 raw10426step0; decide +kernel
      have hl : raw10426step1Labels = raw10426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10426step0 raw10426step0Labels permutation56 hz
    mixedMoment B raw10426step1 raw10426step1Labels = mixedMoment B raw10426step2 raw10426step2Labels := by
      have ha : raw10426step2 = (fun i j => raw10426step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10426step2 raw10426step1; decide +kernel
      have hl : raw10426step2Labels = raw10426step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10426step1 raw10426step1Labels permutation9 permutation7
    mixedMoment B raw10426step2 raw10426step2Labels = mixedMoment B raw10426step3 raw10426step3Labels := by
      have ha : raw10426step3 = -raw10426step2 := by apply Matrix.ext; change ∀ i j, raw10426step3 i j = -(raw10426step2 i j); unfold raw10426step3 raw10426step2; decide +kernel
      have hl : raw10426step3Labels = raw10426step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10426step3 raw10426step3Labels = mixedMoment B raw10426step4 raw10426step4Labels := by
      have ha : raw10426step4 = raw10426step3 := by apply Matrix.ext; unfold raw10426step4 raw10426step3; decide +kernel
      have hl : raw10426step3Labels = labelEmbedding1 ∘ raw10426step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10426step3 raw10426step3Labels raw10426step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical10427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10427 raw10427Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw10427 raw10427Labels = mixedMoment B raw10427step0 raw10427step0Labels := by
      have hz : ∀ j, raw10427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10427step0 = (fun i j => raw10427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10427step0 raw10427; decide +kernel
      have hl : raw10427step0Labels = raw10427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10427 raw10427Labels permutation346 hz
    mixedMoment B raw10427step0 raw10427step0Labels = mixedMoment B raw10427step1 raw10427step1Labels := by
      have hz : ∀ j, raw10427step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10427step1 = (fun i j => raw10427step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10427step1 raw10427step0; decide +kernel
      have hl : raw10427step1Labels = raw10427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10427step0 raw10427step0Labels permutation56 hz
    mixedMoment B raw10427step1 raw10427step1Labels = mixedMoment B raw10427step2 raw10427step2Labels := by
      have ha : raw10427step2 = (fun i j => raw10427step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10427step2 raw10427step1; decide +kernel
      have hl : raw10427step2Labels = raw10427step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10427step1 raw10427step1Labels permutation9 permutation7
    mixedMoment B raw10427step2 raw10427step2Labels = mixedMoment B raw10427step3 raw10427step3Labels := by
      have ha : raw10427step3 = -raw10427step2 := by apply Matrix.ext; change ∀ i j, raw10427step3 i j = -(raw10427step2 i j); unfold raw10427step3 raw10427step2; decide +kernel
      have hl : raw10427step3Labels = raw10427step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10427step3 raw10427step3Labels = mixedMoment B raw10427step4 raw10427step4Labels := by
      have ha : raw10427step4 = raw10427step3 := by apply Matrix.ext; unfold raw10427step4 raw10427step3; decide +kernel
      have hl : raw10427step3Labels = labelEmbedding1 ∘ raw10427step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10427step3 raw10427step3Labels raw10427step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical10438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10438 raw10438Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw10438 raw10438Labels = mixedMoment B raw10438step0 raw10438step0Labels := by
      have hz : ∀ j, raw10438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10438step0 = (fun i j => raw10438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10438step0 raw10438; decide +kernel
      have hl : raw10438step0Labels = raw10438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10438 raw10438Labels permutation346 hz
    mixedMoment B raw10438step0 raw10438step0Labels = mixedMoment B raw10438step1 raw10438step1Labels := by
      have hz : ∀ j, raw10438step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10438step1 = (fun i j => raw10438step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10438step1 raw10438step0; decide +kernel
      have hl : raw10438step1Labels = raw10438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10438step0 raw10438step0Labels permutation56 hz
    mixedMoment B raw10438step1 raw10438step1Labels = mixedMoment B raw10438step2 raw10438step2Labels := by
      have ha : raw10438step2 = (fun i j => raw10438step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10438step2 raw10438step1; decide +kernel
      have hl : raw10438step2Labels = raw10438step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10438step1 raw10438step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical10441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10441 raw10441Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw10441 raw10441Labels = mixedMoment B raw10441step0 raw10441step0Labels := by
      have hz : ∀ j, raw10441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10441step0 = (fun i j => raw10441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10441step0 raw10441; decide +kernel
      have hl : raw10441step0Labels = raw10441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10441 raw10441Labels permutation346 hz
    mixedMoment B raw10441step0 raw10441step0Labels = mixedMoment B raw10441step1 raw10441step1Labels := by
      have ha : raw10441step1 = (fun i j => raw10441step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10441step1 raw10441step0; decide +kernel
      have hl : raw10441step1Labels = raw10441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10441step0 raw10441step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical10447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10447 raw10447Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw10447 raw10447Labels = mixedMoment B raw10447step0 raw10447step0Labels := by
      have hz : ∀ j, raw10447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10447step0 = (fun i j => raw10447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10447step0 raw10447; decide +kernel
      have hl : raw10447step0Labels = raw10447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10447 raw10447Labels permutation346 hz
    mixedMoment B raw10447step0 raw10447step0Labels = mixedMoment B raw10447step1 raw10447step1Labels := by
      have hz : ∀ j, raw10447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10447step1 = (fun i j => raw10447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10447step1 raw10447step0; decide +kernel
      have hl : raw10447step1Labels = raw10447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10447step0 raw10447step0Labels permutation56 hz
    mixedMoment B raw10447step1 raw10447step1Labels = mixedMoment B raw10447step2 raw10447step2Labels := by
      have ha : raw10447step2 = (fun i j => raw10447step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10447step2 raw10447step1; decide +kernel
      have hl : raw10447step2Labels = raw10447step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10447step1 raw10447step1Labels permutation9 permutation2
    _ = mixedMoment B node1246 node1246Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4549 node4549Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1134 node1134Labels + mixedMoment B node3265 node3265Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1374 singletonSmall4549
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4549) = raw1374Labels := by decide +kernel
  rw [hl, canonical1374 B hB] at h
  have hc0 : mixedMoment B raw1374 (Fin.cases (0 : Fin 2) singletonSmall4549) =
      mixedMoment B node1134 node1134Labels := by
    have ha : raw1374 = raw1375 := by apply Matrix.ext; unfold raw1374 raw1375; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4549 = raw1375Labels := by decide +kernel
    rw [ha, hj, canonical1375 B hB]
  have hc1 : mixedMoment B raw1374 (Fin.cases (1 : Fin 2) singletonSmall4549) =
      mixedMoment B node3265 node3265Labels := by
    have ha : raw1374 = raw1376 := by apply Matrix.ext; unfold raw1374 raw1376; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4549 = raw1376Labels := by decide +kernel
    rw [ha, hj, canonical1376 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4558 node4558Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1144 node1144Labels + mixedMoment B node3276 node3276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1395 singletonSmall4558
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4558) = raw1395Labels := by decide +kernel
  rw [hl, canonical1395 B hB] at h
  have hc0 : mixedMoment B raw1395 (Fin.cases (0 : Fin 2) singletonSmall4558) =
      mixedMoment B node1144 node1144Labels := by
    have ha : raw1395 = raw1396 := by apply Matrix.ext; unfold raw1395 raw1396; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4558 = raw1396Labels := by decide +kernel
    rw [ha, hj, canonical1396 B hB]
  have hc1 : mixedMoment B raw1395 (Fin.cases (1 : Fin 2) singletonSmall4558) =
      mixedMoment B node3276 node3276Labels := by
    have ha : raw1395 = raw1397 := by apply Matrix.ext; unfold raw1395 raw1397; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4558 = raw1397Labels := by decide +kernel
    rw [ha, hj, canonical1397 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4559 node4559Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1145 node1145Labels + mixedMoment B node3277 node3277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1398 singletonSmall4559
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4559) = raw1398Labels := by decide +kernel
  rw [hl, canonical1398 B hB] at h
  have hc0 : mixedMoment B raw1398 (Fin.cases (0 : Fin 2) singletonSmall4559) =
      mixedMoment B node1145 node1145Labels := by
    have ha : raw1398 = raw1399 := by apply Matrix.ext; unfold raw1398 raw1399; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4559 = raw1399Labels := by decide +kernel
    rw [ha, hj, canonical1399 B hB]
  have hc1 : mixedMoment B raw1398 (Fin.cases (1 : Fin 2) singletonSmall4559) =
      mixedMoment B node3277 node3277Labels := by
    have ha : raw1398 = raw1400 := by apply Matrix.ext; unfold raw1398 raw1400; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4559 = raw1400Labels := by decide +kernel
    rw [ha, hj, canonical1400 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4602 node4602Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1236 node1236Labels + mixedMoment B node3293 node3293Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1425 singletonSmall4602
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4602) = raw1425Labels := by decide +kernel
  rw [hl, canonical1425 B hB] at h
  have hc0 : mixedMoment B raw1425 (Fin.cases (0 : Fin 2) singletonSmall4602) =
      mixedMoment B node1236 node1236Labels := by
    have ha : raw1425 = raw1426 := by apply Matrix.ext; unfold raw1425 raw1426; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4602 = raw1426Labels := by decide +kernel
    rw [ha, hj, canonical1426 B hB]
  have hc1 : mixedMoment B raw1425 (Fin.cases (1 : Fin 2) singletonSmall4602) =
      mixedMoment B node3293 node3293Labels := by
    have ha : raw1425 = raw1427 := by apply Matrix.ext; unfold raw1425 raw1427; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4602 = raw1427Labels := by decide +kernel
    rw [ha, hj, canonical1427 B hB]
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

theorem singleton4608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4608 node4608Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1242 node1242Labels + mixedMoment B node3300 node3300Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1434 singletonSmall4608
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4608) = raw1434Labels := by decide +kernel
  rw [hl, canonical1434 B hB] at h
  have hc0 : mixedMoment B raw1434 (Fin.cases (0 : Fin 2) singletonSmall4608) =
      mixedMoment B node1242 node1242Labels := by
    have ha : raw1434 = raw1435 := by apply Matrix.ext; unfold raw1434 raw1435; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4608 = raw1435Labels := by decide +kernel
    rw [ha, hj, canonical1435 B hB]
  have hc1 : mixedMoment B raw1434 (Fin.cases (1 : Fin 2) singletonSmall4608) =
      mixedMoment B node3300 node3300Labels := by
    have ha : raw1434 = raw1436 := by apply Matrix.ext; unfold raw1434 raw1436; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4608 = raw1436Labels := by decide +kernel
    rw [ha, hj, canonical1436 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4619 node4619Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1294 node1294Labels + mixedMoment B node3305 node3305Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1443 singletonSmall4619
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4619) = raw1443Labels := by decide +kernel
  rw [hl, canonical1443 B hB] at h
  have hc0 : mixedMoment B raw1443 (Fin.cases (0 : Fin 2) singletonSmall4619) =
      mixedMoment B node1294 node1294Labels := by
    have ha : raw1443 = raw1444 := by apply Matrix.ext; unfold raw1443 raw1444; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4619 = raw1444Labels := by decide +kernel
    rw [ha, hj, canonical1444 B hB]
  have hc1 : mixedMoment B raw1443 (Fin.cases (1 : Fin 2) singletonSmall4619) =
      mixedMoment B node3305 node3305Labels := by
    have ha : raw1443 = raw1445 := by apply Matrix.ext; unfold raw1443 raw1445; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4619 = raw1445Labels := by decide +kernel
    rw [ha, hj, canonical1445 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node642 node642Labels = Sparse.eval nodeValue642 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 642) = mixedMoment B node642 node642Labels := rfl
  simpa [nodeValue642, Sparse.eval] using hc.symm

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

theorem sound1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1134 node1134Labels = Sparse.eval nodeValue1134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1134) = mixedMoment B node1134 node1134Labels := rfl
  simpa [nodeValue1134, Sparse.eval] using hc.symm

theorem sound1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1144 node1144Labels = Sparse.eval nodeValue1144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1144) = mixedMoment B node1144 node1144Labels := rfl
  simpa [nodeValue1144, Sparse.eval] using hc.symm

theorem sound1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1145 node1145Labels = Sparse.eval nodeValue1145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1145) = mixedMoment B node1145 node1145Labels := rfl
  simpa [nodeValue1145, Sparse.eval] using hc.symm

theorem sound1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1149 node1149Labels = Sparse.eval nodeValue1149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1149) = mixedMoment B node1149 node1149Labels := rfl
  simpa [nodeValue1149, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1154 node1154Labels = Sparse.eval nodeValue1154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1154) = mixedMoment B node1154 node1154Labels := rfl
  simpa [nodeValue1154, Sparse.eval] using hc.symm

theorem sound1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1155 node1155Labels = Sparse.eval nodeValue1155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1155) = mixedMoment B node1155 node1155Labels := rfl
  simpa [nodeValue1155, Sparse.eval] using hc.symm

theorem sound1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1160 node1160Labels = Sparse.eval nodeValue1160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1160) = mixedMoment B node1160 node1160Labels := rfl
  simpa [nodeValue1160, Sparse.eval] using hc.symm

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

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1237 node1237Labels = Sparse.eval nodeValue1237 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1237) = mixedMoment B node1237 node1237Labels := rfl
  simpa [nodeValue1237, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

theorem sound1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1295 node1295Labels = Sparse.eval nodeValue1295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1295) = mixedMoment B node1295 node1295Labels := rfl
  simpa [nodeValue1295, Sparse.eval] using hc.symm

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

theorem sound1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1522 node1522Labels = Sparse.eval nodeValue1522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1522) = mixedMoment B node1522 node1522Labels := rfl
  simpa [nodeValue1522, Sparse.eval] using hc.symm

theorem sound1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1523 node1523Labels = Sparse.eval nodeValue1523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1523) = mixedMoment B node1523 node1523Labels := rfl
  simpa [nodeValue1523, Sparse.eval] using hc.symm

theorem sound1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1526 node1526Labels = Sparse.eval nodeValue1526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1526) = mixedMoment B node1526 node1526Labels := rfl
  simpa [nodeValue1526, Sparse.eval] using hc.symm

theorem sound1533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1533 node1533Labels = Sparse.eval nodeValue1533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1533) = mixedMoment B node1533 node1533Labels := rfl
  simpa [nodeValue1533, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1755 node1755Labels = 0 := by
  exact mixedMoment_order_one B hB node1755 node1755Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

theorem sound1755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1755 node1755Labels = Sparse.eval nodeValue1755 (mixedVector B) := by
  simpa only [nodeValue1755, Sparse.eval_nil] using zero1755 B _hB _hF

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

theorem sound3265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3265 node3265Labels = Sparse.eval nodeValue3265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3265) = mixedMoment B node3265 node3265Labels := rfl
  simpa [nodeValue3265, Sparse.eval] using hc.symm

theorem sound3267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3267 node3267Labels = Sparse.eval nodeValue3267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3267) = mixedMoment B node3267 node3267Labels := rfl
  simpa [nodeValue3267, Sparse.eval] using hc.symm

theorem sound3268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3268 node3268Labels = Sparse.eval nodeValue3268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3268) = mixedMoment B node3268 node3268Labels := rfl
  simpa [nodeValue3268, Sparse.eval] using hc.symm

theorem sound3271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3271 node3271Labels = Sparse.eval nodeValue3271 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3271) = mixedMoment B node3271 node3271Labels := rfl
  simpa [nodeValue3271, Sparse.eval] using hc.symm

theorem sound3272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3272 node3272Labels = Sparse.eval nodeValue3272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3272) = mixedMoment B node3272 node3272Labels := rfl
  simpa [nodeValue3272, Sparse.eval] using hc.symm

theorem sound3276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3276 node3276Labels = Sparse.eval nodeValue3276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3276) = mixedMoment B node3276 node3276Labels := rfl
  simpa [nodeValue3276, Sparse.eval] using hc.symm

theorem sound3277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3277 node3277Labels = Sparse.eval nodeValue3277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3277) = mixedMoment B node3277 node3277Labels := rfl
  simpa [nodeValue3277, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3294 node3294Labels = Sparse.eval nodeValue3294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3294) = mixedMoment B node3294 node3294Labels := rfl
  simpa [nodeValue3294, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

theorem sound3306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3306 node3306Labels = Sparse.eval nodeValue3306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3306) = mixedMoment B node3306 node3306Labels := rfl
  simpa [nodeValue3306, Sparse.eval] using hc.symm

theorem sound3311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3311 node3311Labels = Sparse.eval nodeValue3311 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3311) = mixedMoment B node3311 node3311Labels := rfl
  simpa [nodeValue3311, Sparse.eval] using hc.symm

theorem sound3312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3312 node3312Labels = Sparse.eval nodeValue3312 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3312) = mixedMoment B node3312 node3312Labels := rfl
  simpa [nodeValue3312, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = 0 := by
  exact mixedMoment_order_one B hB node3485 node3485Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = Sparse.eval nodeValue3485 (mixedVector B) := by
  simpa only [nodeValue3485, Sparse.eval_nil] using zero3485 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = 0 := by
  exact mixedMoment_order_one B hB node3547 node3547Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node627 node627Labels = Sparse.eval nodeValue627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 627) = mixedMoment B node627 node627Labels := rfl
  simpa [nodeValue627, Sparse.eval] using hc.symm

theorem sound635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node635 node635Labels = Sparse.eval nodeValue635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 635) = mixedMoment B node635 node635Labels := rfl
  simpa [nodeValue635, Sparse.eval] using hc.symm

theorem sound636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node636 node636Labels = Sparse.eval nodeValue636 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 636) = mixedMoment B node636 node636Labels := rfl
  simpa [nodeValue636, Sparse.eval] using hc.symm

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

theorem sound4158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4158 node4158Labels = Sparse.eval nodeValue4158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4158) = mixedMoment B node4158 node4158Labels := rfl
  simpa [nodeValue4158, Sparse.eval] using hc.symm

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

theorem sound4160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4160 node4160Labels = Sparse.eval nodeValue4160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4160) = mixedMoment B node4160 node4160Labels := rfl
  simpa [nodeValue4160, Sparse.eval] using hc.symm

theorem sound4161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4161 node4161Labels = Sparse.eval nodeValue4161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4161) = mixedMoment B node4161 node4161Labels := rfl
  simpa [nodeValue4161, Sparse.eval] using hc.symm

theorem sound4188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4188 node4188Labels = Sparse.eval nodeValue4188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4188) = mixedMoment B node4188 node4188Labels := rfl
  simpa [nodeValue4188, Sparse.eval] using hc.symm

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

theorem sound4549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4549 node4549Labels = Sparse.eval nodeValue4549 (mixedVector B) := by
  have h := singleton4549 B _hB
  rw [sound1134 B _hB _hF, sound3265 B _hB _hF] at h
  norm_num [nodeValue4549, nodeValue1134, nodeValue3265, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4556 node4556Labels = Sparse.eval nodeValue4556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4556) = mixedMoment B node4556 node4556Labels := rfl
  simpa [nodeValue4556, Sparse.eval] using hc.symm

theorem sound4558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4558 node4558Labels = Sparse.eval nodeValue4558 (mixedVector B) := by
  have h := singleton4558 B _hB
  rw [sound1144 B _hB _hF, sound3276 B _hB _hF] at h
  norm_num [nodeValue4558, nodeValue1144, nodeValue3276, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4559 node4559Labels = Sparse.eval nodeValue4559 (mixedVector B) := by
  have h := singleton4559 B _hB
  rw [sound1145 B _hB _hF, sound3277 B _hB _hF] at h
  norm_num [nodeValue4559, nodeValue1145, nodeValue3277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4603 node4603Labels = Sparse.eval nodeValue4603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4603) = mixedMoment B node4603 node4603Labels := rfl
  simpa [nodeValue4603, Sparse.eval] using hc.symm

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

theorem sound4608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4608 node4608Labels = Sparse.eval nodeValue4608 (mixedVector B) := by
  have h := singleton4608 B _hB
  rw [sound1242 B _hB _hF, sound3300 B _hB _hF] at h
  norm_num [nodeValue4608, nodeValue1242, nodeValue3300, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4609 node4609Labels = Sparse.eval nodeValue4609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4609) = mixedMoment B node4609 node4609Labels := rfl
  simpa [nodeValue4609, Sparse.eval] using hc.symm

theorem sound4619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4619 node4619Labels = Sparse.eval nodeValue4619 (mixedVector B) := by
  have h := singleton4619 B _hB
  rw [sound1294 B _hB _hF, sound3305 B _hB _hF] at h
  norm_num [nodeValue4619, nodeValue1294, nodeValue3305, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4620 node4620Labels = Sparse.eval nodeValue4620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4620) = mixedMoment B node4620 node4620Labels := rfl
  simpa [nodeValue4620, Sparse.eval] using hc.symm

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

theorem sound5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = Sparse.eval nodeValue5111 (mixedVector B) := by
  simpa only [nodeValue5111, Sparse.eval_nil] using zero5111 B _hB _hF

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

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources46
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1477 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 0) (sourceB1477 + difference 0 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 0) (sourceB1477 + difference 0 4) sourceC1477) = raw22566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22566; decide +kernel
    rw [ha]
    exact (canonical22566 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 1) (sourceB1477 + difference 1 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 1) (sourceB1477 + difference 1 4) sourceC1477) = raw22421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22421; decide +kernel
    rw [ha]
    exact (canonical22421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 2) (sourceB1477 + difference 2 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 2) (sourceB1477 + difference 2 4) sourceC1477) = raw22567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22567; decide +kernel
    rw [ha]
    exact (canonical22567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 3) (sourceB1477 + difference 3 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 3) (sourceB1477 + difference 3 4) sourceC1477) = raw22568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22568; decide +kernel
    rw [ha]
    exact (canonical22568 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 4) (sourceB1477 + difference 4 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3311) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 4) (sourceB1477 + difference 4 4) sourceC1477) = raw22416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22416; decide +kernel
    rw [ha]
    exact (canonical22416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 5) (sourceB1477 + difference 5 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3312) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 5) (sourceB1477 + difference 5 4) sourceC1477) = raw22455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22455; decide +kernel
    rw [ha]
    exact (canonical22455 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1477 + sourceB1477) sourceC1477) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1477 + sourceB1477) sourceC1477) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1477 sourceB1477 sourceC1477 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1477 sourceB1477 sourceC1477
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1477, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1482 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 0) (sourceB1482 + difference 0 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3312) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 0) (sourceB1482 + difference 0 0) sourceC1482) = raw22455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22455; decide +kernel
    rw [ha]
    exact (canonical22455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 1) (sourceB1482 + difference 1 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 1) (sourceB1482 + difference 1 0) sourceC1482) = raw22452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22452; decide +kernel
    rw [ha]
    exact (canonical22452 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 2) (sourceB1482 + difference 2 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 2) (sourceB1482 + difference 2 0) sourceC1482) = raw22651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22651; decide +kernel
    rw [ha]
    exact (canonical22651 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 3) (sourceB1482 + difference 3 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 3) (sourceB1482 + difference 3 0) sourceC1482) = raw22652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22652; decide +kernel
    rw [ha]
    exact (canonical22652 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 4) (sourceB1482 + difference 4 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 4) (sourceB1482 + difference 4 0) sourceC1482) = raw22653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22653; decide +kernel
    rw [ha]
    exact (canonical22653 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1482 + difference 0 5) (sourceB1482 + difference 5 0) sourceC1482) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1482 + difference 0 5) (sourceB1482 + difference 5 0) sourceC1482) = raw22654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1482 sourceB1482 sourceC1482 difference raw22654; decide +kernel
    rw [ha]
    exact (canonical22654 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1482 + sourceB1482) sourceC1482) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1482 + sourceB1482) sourceC1482) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1482 sourceB1482 sourceC1482 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1482 sourceB1482 sourceC1482
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1482, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1483 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 1) (sourceB1483 + difference 1 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 1) (sourceB1483 + difference 1 0) sourceC1483) = raw10363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10363; decide +kernel
    rw [ha]
    exact (canonical10363 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 2) (sourceB1483 + difference 2 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 2) (sourceB1483 + difference 2 0) sourceC1483) = raw10364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10364; decide +kernel
    rw [ha]
    exact (canonical10364 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 3) (sourceB1483 + difference 3 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 3) (sourceB1483 + difference 3 0) sourceC1483) = raw10365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10365; decide +kernel
    rw [ha]
    exact (canonical10365 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 4) (sourceB1483 + difference 4 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 4) (sourceB1483 + difference 4 0) sourceC1483) = raw22655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22655; decide +kernel
    rw [ha]
    exact (canonical22655 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1483 + difference 0 5) (sourceB1483 + difference 5 0) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA1483 + difference 0 5) (sourceB1483 + difference 5 0) sourceC1483) = raw10366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10366; decide +kernel
    rw [ha]
    exact (canonical10366 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 0) (sourceB1483 + difference 0 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 0) (sourceB1483 + difference 0 1) sourceC1483) = raw22656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22656; decide +kernel
    rw [ha]
    exact (canonical22656 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 2) (sourceB1483 + difference 2 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 2) (sourceB1483 + difference 2 1) sourceC1483) = raw22657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22657; decide +kernel
    rw [ha]
    exact (canonical22657 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 3) (sourceB1483 + difference 3 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 3) (sourceB1483 + difference 3 1) sourceC1483) = raw22658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22658; decide +kernel
    rw [ha]
    exact (canonical22658 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 4) (sourceB1483 + difference 4 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 4) (sourceB1483 + difference 4 1) sourceC1483) = raw10347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10347; decide +kernel
    rw [ha]
    exact (canonical10347 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1483 + difference 1 5) (sourceB1483 + difference 5 1) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1483 + difference 1 5) (sourceB1483 + difference 5 1) sourceC1483) = raw22659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22659; decide +kernel
    rw [ha]
    exact (canonical22659 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 0) (sourceB1483 + difference 0 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 0) (sourceB1483 + difference 0 2) sourceC1483) = raw22660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22660; decide +kernel
    rw [ha]
    exact (canonical22660 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 1) (sourceB1483 + difference 1 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 1) (sourceB1483 + difference 1 2) sourceC1483) = raw22661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22661; decide +kernel
    rw [ha]
    exact (canonical22661 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 3) (sourceB1483 + difference 3 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 3) (sourceB1483 + difference 3 2) sourceC1483) = raw22662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22662; decide +kernel
    rw [ha]
    exact (canonical22662 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 4) (sourceB1483 + difference 4 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 4) (sourceB1483 + difference 4 2) sourceC1483) = raw10352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10352; decide +kernel
    rw [ha]
    exact (canonical10352 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1483 + difference 2 5) (sourceB1483 + difference 5 2) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1483 + difference 2 5) (sourceB1483 + difference 5 2) sourceC1483) = raw22663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22663; decide +kernel
    rw [ha]
    exact (canonical22663 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 0) (sourceB1483 + difference 0 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4188) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 0) (sourceB1483 + difference 0 3) sourceC1483) = raw22664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22664; decide +kernel
    rw [ha]
    exact (canonical22664 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 1) (sourceB1483 + difference 1 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 1) (sourceB1483 + difference 1 3) sourceC1483) = raw22665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22665; decide +kernel
    rw [ha]
    exact (canonical22665 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 2) (sourceB1483 + difference 2 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 2) (sourceB1483 + difference 2 3) sourceC1483) = raw22666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22666; decide +kernel
    rw [ha]
    exact (canonical22666 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 4) (sourceB1483 + difference 4 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 4) (sourceB1483 + difference 4 3) sourceC1483) = raw10357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10357; decide +kernel
    rw [ha]
    exact (canonical10357 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1483 + difference 3 5) (sourceB1483 + difference 5 3) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1483 + difference 3 5) (sourceB1483 + difference 5 3) sourceC1483) = raw22667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22667; decide +kernel
    rw [ha]
    exact (canonical22667 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 0) (sourceB1483 + difference 0 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 0) (sourceB1483 + difference 0 4) sourceC1483) = raw22668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22668; decide +kernel
    rw [ha]
    exact (canonical22668 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 1) (sourceB1483 + difference 1 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 1) (sourceB1483 + difference 1 4) sourceC1483) = raw22669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22669; decide +kernel
    rw [ha]
    exact (canonical22669 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 2) (sourceB1483 + difference 2 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 2) (sourceB1483 + difference 2 4) sourceC1483) = raw22670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22670; decide +kernel
    rw [ha]
    exact (canonical22670 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 3) (sourceB1483 + difference 3 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 3) (sourceB1483 + difference 3 4) sourceC1483) = raw22671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22671; decide +kernel
    rw [ha]
    exact (canonical22671 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1483 + difference 4 5) (sourceB1483 + difference 5 4) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1483 + difference 4 5) (sourceB1483 + difference 5 4) sourceC1483) = raw22672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22672; decide +kernel
    rw [ha]
    exact (canonical22672 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 0) (sourceB1483 + difference 0 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4160) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 0) (sourceB1483 + difference 0 5) sourceC1483) = raw22673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22673; decide +kernel
    rw [ha]
    exact (canonical22673 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 1) (sourceB1483 + difference 1 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4534) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 1) (sourceB1483 + difference 1 5) sourceC1483) = raw22674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22674; decide +kernel
    rw [ha]
    exact (canonical22674 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 2) (sourceB1483 + difference 2 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4534) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 2) (sourceB1483 + difference 2 5) sourceC1483) = raw22675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22675; decide +kernel
    rw [ha]
    exact (canonical22675 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 3) (sourceB1483 + difference 3 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 3) (sourceB1483 + difference 3 5) sourceC1483) = raw22676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw22676; decide +kernel
    rw [ha]
    exact (canonical22676 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1483 + difference 5 4) (sourceB1483 + difference 4 5) sourceC1483) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1483 + difference 5 4) (sourceB1483 + difference 4 5) sourceC1483) = raw10367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1483 sourceB1483 sourceC1483 difference raw10367; decide +kernel
    rw [ha]
    exact (canonical10367 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1483 sourceB1483 sourceC1483
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1483, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1485 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 1) (sourceB1485 + difference 1 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 1) (sourceB1485 + difference 1 0) sourceC1485) = raw10423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10423; decide +kernel
    rw [ha]
    exact (canonical10423 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 2) (sourceB1485 + difference 2 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 2) (sourceB1485 + difference 2 0) sourceC1485) = raw10424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10424; decide +kernel
    rw [ha]
    exact (canonical10424 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 3) (sourceB1485 + difference 3 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 3) (sourceB1485 + difference 3 0) sourceC1485) = raw10425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10425; decide +kernel
    rw [ha]
    exact (canonical10425 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 4) (sourceB1485 + difference 4 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 4) (sourceB1485 + difference 4 0) sourceC1485) = raw22699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22699; decide +kernel
    rw [ha]
    exact (canonical22699 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1485 + difference 0 5) (sourceB1485 + difference 5 0) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA1485 + difference 0 5) (sourceB1485 + difference 5 0) sourceC1485) = raw10426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10426; decide +kernel
    rw [ha]
    exact (canonical10426 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 0) (sourceB1485 + difference 0 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 0) (sourceB1485 + difference 0 1) sourceC1485) = raw22700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22700; decide +kernel
    rw [ha]
    exact (canonical22700 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 2) (sourceB1485 + difference 2 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 2) (sourceB1485 + difference 2 1) sourceC1485) = raw22701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22701; decide +kernel
    rw [ha]
    exact (canonical22701 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 3) (sourceB1485 + difference 3 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 3) (sourceB1485 + difference 3 1) sourceC1485) = raw22702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22702; decide +kernel
    rw [ha]
    exact (canonical22702 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 4) (sourceB1485 + difference 4 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 4) (sourceB1485 + difference 4 1) sourceC1485) = raw10407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10407; decide +kernel
    rw [ha]
    exact (canonical10407 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1485 + difference 1 5) (sourceB1485 + difference 5 1) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1485 + difference 1 5) (sourceB1485 + difference 5 1) sourceC1485) = raw22703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22703; decide +kernel
    rw [ha]
    exact (canonical22703 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 0) (sourceB1485 + difference 0 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 0) (sourceB1485 + difference 0 2) sourceC1485) = raw22704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22704; decide +kernel
    rw [ha]
    exact (canonical22704 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 1) (sourceB1485 + difference 1 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 1) (sourceB1485 + difference 1 2) sourceC1485) = raw22705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22705; decide +kernel
    rw [ha]
    exact (canonical22705 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 3) (sourceB1485 + difference 3 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 3) (sourceB1485 + difference 3 2) sourceC1485) = raw22706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22706; decide +kernel
    rw [ha]
    exact (canonical22706 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 4) (sourceB1485 + difference 4 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 4) (sourceB1485 + difference 4 2) sourceC1485) = raw10412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10412; decide +kernel
    rw [ha]
    exact (canonical10412 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1485 + difference 2 5) (sourceB1485 + difference 5 2) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1485 + difference 2 5) (sourceB1485 + difference 5 2) sourceC1485) = raw22707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22707; decide +kernel
    rw [ha]
    exact (canonical22707 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 0) (sourceB1485 + difference 0 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 0) (sourceB1485 + difference 0 3) sourceC1485) = raw22708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22708; decide +kernel
    rw [ha]
    exact (canonical22708 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 1) (sourceB1485 + difference 1 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 1) (sourceB1485 + difference 1 3) sourceC1485) = raw22709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22709; decide +kernel
    rw [ha]
    exact (canonical22709 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 2) (sourceB1485 + difference 2 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 2) (sourceB1485 + difference 2 3) sourceC1485) = raw22710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22710; decide +kernel
    rw [ha]
    exact (canonical22710 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 4) (sourceB1485 + difference 4 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 4) (sourceB1485 + difference 4 3) sourceC1485) = raw10417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10417; decide +kernel
    rw [ha]
    exact (canonical10417 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1485 + difference 3 5) (sourceB1485 + difference 5 3) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1485 + difference 3 5) (sourceB1485 + difference 5 3) sourceC1485) = raw22711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22711; decide +kernel
    rw [ha]
    exact (canonical22711 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 0) (sourceB1485 + difference 0 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 0) (sourceB1485 + difference 0 4) sourceC1485) = raw22712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22712; decide +kernel
    rw [ha]
    exact (canonical22712 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 1) (sourceB1485 + difference 1 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 1) (sourceB1485 + difference 1 4) sourceC1485) = raw22713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22713; decide +kernel
    rw [ha]
    exact (canonical22713 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 2) (sourceB1485 + difference 2 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 2) (sourceB1485 + difference 2 4) sourceC1485) = raw22714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22714; decide +kernel
    rw [ha]
    exact (canonical22714 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 3) (sourceB1485 + difference 3 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 3) (sourceB1485 + difference 3 4) sourceC1485) = raw22715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22715; decide +kernel
    rw [ha]
    exact (canonical22715 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1485 + difference 4 5) (sourceB1485 + difference 5 4) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1485 + difference 4 5) (sourceB1485 + difference 5 4) sourceC1485) = raw22716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22716; decide +kernel
    rw [ha]
    exact (canonical22716 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 0) (sourceB1485 + difference 0 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 0) (sourceB1485 + difference 0 5) sourceC1485) = raw22717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22717; decide +kernel
    rw [ha]
    exact (canonical22717 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 1) (sourceB1485 + difference 1 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 1) (sourceB1485 + difference 1 5) sourceC1485) = raw22718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22718; decide +kernel
    rw [ha]
    exact (canonical22718 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 2) (sourceB1485 + difference 2 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 2) (sourceB1485 + difference 2 5) sourceC1485) = raw22719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22719; decide +kernel
    rw [ha]
    exact (canonical22719 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 3) (sourceB1485 + difference 3 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 3) (sourceB1485 + difference 3 5) sourceC1485) = raw22720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw22720; decide +kernel
    rw [ha]
    exact (canonical22720 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1485 + difference 5 4) (sourceB1485 + difference 4 5) sourceC1485) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1485 + difference 5 4) (sourceB1485 + difference 4 5) sourceC1485) = raw10427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1485 sourceB1485 sourceC1485 difference raw10427; decide +kernel
    rw [ha]
    exact (canonical10427 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1485 sourceB1485 sourceC1485
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1485, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1486 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1486 + difference 0 0) (sourceB1486 + difference 0 0) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1486 + difference 0 0) (sourceB1486 + difference 0 0) sourceC1486) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1486 + difference 1 0) (sourceB1486 + difference 0 1) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1486 + difference 1 0) (sourceB1486 + difference 0 1) sourceC1486) = raw22721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22721; decide +kernel
    rw [ha]
    exact (canonical22721 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1486 + difference 2 0) (sourceB1486 + difference 0 2) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1486 + difference 2 0) (sourceB1486 + difference 0 2) sourceC1486) = raw22722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22722; decide +kernel
    rw [ha]
    exact (canonical22722 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1486 + difference 3 0) (sourceB1486 + difference 0 3) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 642) := by
    have ha : (tripleCharges (sourceA1486 + difference 3 0) (sourceB1486 + difference 0 3) sourceC1486) = raw22723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22723; decide +kernel
    rw [ha]
    exact (canonical22723 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1486 + difference 4 0) (sourceB1486 + difference 0 4) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 635) := by
    have ha : (tripleCharges (sourceA1486 + difference 4 0) (sourceB1486 + difference 0 4) sourceC1486) = raw22724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22724; decide +kernel
    rw [ha]
    exact (canonical22724 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1486 + difference 5 0) (sourceB1486 + difference 0 5) sourceC1486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 636) := by
    have ha : (tripleCharges (sourceA1486 + difference 5 0) (sourceB1486 + difference 0 5) sourceC1486) = raw22725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1486 sourceB1486 sourceC1486 difference raw22725; decide +kernel
    rw [ha]
    exact (canonical22725 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1486 + sourceB1486) sourceC1486) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1486 + sourceB1486) sourceC1486) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA1486 sourceB1486 sourceC1486 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1486 sourceB1486 sourceC1486
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1486, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1487 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 0) (sourceB1487 + difference 0 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 0) (sourceB1487 + difference 0 1) sourceC1487) = raw22721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22721; decide +kernel
    rw [ha]
    exact (canonical22721 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 1) (sourceB1487 + difference 1 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 1) (sourceB1487 + difference 1 1) sourceC1487) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 2) (sourceB1487 + difference 2 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1149) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 2) (sourceB1487 + difference 2 1) sourceC1487) = raw22726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22726; decide +kernel
    rw [ha]
    exact (canonical22726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 3) (sourceB1487 + difference 3 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 3) (sourceB1487 + difference 3 1) sourceC1487) = raw22727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22727; decide +kernel
    rw [ha]
    exact (canonical22727 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 4) (sourceB1487 + difference 4 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 4) (sourceB1487 + difference 4 1) sourceC1487) = raw22728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22728; decide +kernel
    rw [ha]
    exact (canonical22728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1487 + difference 1 5) (sourceB1487 + difference 5 1) sourceC1487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1487 + difference 1 5) (sourceB1487 + difference 5 1) sourceC1487) = raw22729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1487 sourceB1487 sourceC1487 difference raw22729; decide +kernel
    rw [ha]
    exact (canonical22729 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1487 + sourceB1487) sourceC1487) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1487 + sourceB1487) sourceC1487) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA1487 sourceB1487 sourceC1487 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1487 sourceB1487 sourceC1487
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1487, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1488 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1488 + difference 0 1) (sourceB1488 + difference 1 0) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA1488 + difference 0 1) (sourceB1488 + difference 1 0) sourceC1488) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1488 + difference 1 1) (sourceB1488 + difference 1 1) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1488 + difference 1 1) (sourceB1488 + difference 1 1) sourceC1488) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1488 + difference 2 1) (sourceB1488 + difference 1 2) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1149) := by
    have ha : (tripleCharges (sourceA1488 + difference 2 1) (sourceB1488 + difference 1 2) sourceC1488) = raw22730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw22730; decide +kernel
    rw [ha]
    exact (canonical22730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1488 + difference 3 1) (sourceB1488 + difference 1 3) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1160) := by
    have ha : (tripleCharges (sourceA1488 + difference 3 1) (sourceB1488 + difference 1 3) sourceC1488) = raw22731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw22731; decide +kernel
    rw [ha]
    exact (canonical22731 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1488 + difference 4 1) (sourceB1488 + difference 1 4) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1154) := by
    have ha : (tripleCharges (sourceA1488 + difference 4 1) (sourceB1488 + difference 1 4) sourceC1488) = raw22732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw22732; decide +kernel
    rw [ha]
    exact (canonical22732 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1488 + difference 5 1) (sourceB1488 + difference 1 5) sourceC1488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1155) := by
    have ha : (tripleCharges (sourceA1488 + difference 5 1) (sourceB1488 + difference 1 5) sourceC1488) = raw22733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1488 sourceB1488 sourceC1488 difference raw22733; decide +kernel
    rw [ha]
    exact (canonical22733 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1488 + sourceB1488) sourceC1488) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1488 + sourceB1488) sourceC1488) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA1488 sourceB1488 sourceC1488 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1488 sourceB1488 sourceC1488
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1488, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1489 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 0) (sourceB1489 + difference 0 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 642) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 0) (sourceB1489 + difference 0 3) sourceC1489) = raw22723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22723; decide +kernel
    rw [ha]
    exact (canonical22723 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 1) (sourceB1489 + difference 1 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1160) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 1) (sourceB1489 + difference 1 3) sourceC1489) = raw22731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22731; decide +kernel
    rw [ha]
    exact (canonical22731 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 2) (sourceB1489 + difference 2 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1160) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 2) (sourceB1489 + difference 2 3) sourceC1489) = raw22734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22734; decide +kernel
    rw [ha]
    exact (canonical22734 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 3) (sourceB1489 + difference 3 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 3) (sourceB1489 + difference 3 3) sourceC1489) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 4) (sourceB1489 + difference 4 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 4) (sourceB1489 + difference 4 3) sourceC1489) = raw22735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22735; decide +kernel
    rw [ha]
    exact (canonical22735 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1489 + difference 3 5) (sourceB1489 + difference 5 3) sourceC1489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1489 + difference 3 5) (sourceB1489 + difference 5 3) sourceC1489) = raw22736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1489 sourceB1489 sourceC1489 difference raw22736; decide +kernel
    rw [ha]
    exact (canonical22736 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1489 + sourceB1489) sourceC1489) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1489 + sourceB1489) sourceC1489) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA1489 sourceB1489 sourceC1489 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1489 sourceB1489 sourceC1489
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1489, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1265 : Integer.Sparse.reindex keyMap MixedData.row1265 = numericRow1265 := by decide +kernel

theorem numericCheck1265 (x : Master → ℝ) : Integer.Sparse.eval numericRow1265 x =
    (1 : ℝ) * reducedSource1265 x := by
  norm_num [numericRow1265, reducedSource1265, Integer.Sparse.eval, Sparse.eval, nodeValue1755, nodeValue3301, nodeValue3311, nodeValue3312, nodeValue4071]

theorem reindexCheck1270 : Integer.Sparse.reindex keyMap MixedData.row1270 = numericRow1270 := by decide +kernel

theorem numericCheck1270 (x : Master → ℝ) : Integer.Sparse.eval numericRow1270 x =
    (1 : ℝ) * reducedSource1270 x := by
  norm_num [numericRow1270, reducedSource1270, Integer.Sparse.eval, Sparse.eval, nodeValue1751, nodeValue1755, nodeValue3312, nodeValue4071]

theorem reindexCheck1271 : Integer.Sparse.reindex keyMap MixedData.row1271 = numericRow1271 := by decide +kernel

theorem numericCheck1271 (x : Master → ℝ) : Integer.Sparse.eval numericRow1271 x =
    (4 : ℝ) * reducedSource1271 x := by
  norm_num [numericRow1271, reducedSource1271, Integer.Sparse.eval, Sparse.eval, nodeValue4158, nodeValue4160, nodeValue4161, nodeValue4188, nodeValue4533, nodeValue4534, nodeValue4535, nodeValue4549, nodeValue4556, nodeValue4558, nodeValue4559, nodeValue4602, nodeValue4603, nodeValue4608, nodeValue4609, nodeValue4619, nodeValue4620, nodeValue5111, nodeValue5141, nodeValue5274, nodeValue5275] <;> ring

theorem reindexCheck1273 : Integer.Sparse.reindex keyMap MixedData.row1273 = numericRow1273 := by decide +kernel

theorem numericCheck1273 (x : Master → ℝ) : Integer.Sparse.eval numericRow1273 x =
    (1 : ℝ) * reducedSource1273 x := by
  norm_num [numericRow1273, reducedSource1273, Integer.Sparse.eval, Sparse.eval, nodeValue1522, nodeValue1523, nodeValue1526, nodeValue1533, nodeValue3265, nodeValue3267, nodeValue3268, nodeValue3271, nodeValue3272, nodeValue3276, nodeValue3277, nodeValue3293, nodeValue3294, nodeValue3300, nodeValue3302, nodeValue3305, nodeValue3306, nodeValue3485, nodeValue3522, nodeValue3547, nodeValue3548]

theorem reindexCheck1274 : Integer.Sparse.reindex keyMap MixedData.row1274 = numericRow1274 := by decide +kernel

theorem numericCheck1274 (x : Master → ℝ) : Integer.Sparse.eval numericRow1274 x =
    (1 : ℝ) * reducedSource1274 x := by
  norm_num [numericRow1274, reducedSource1274, Integer.Sparse.eval, Sparse.eval, nodeValue627, nodeValue635, nodeValue636, nodeValue642, nodeValue1246, nodeValue4092]

theorem reindexCheck1275 : Integer.Sparse.reindex keyMap MixedData.row1275 = numericRow1275 := by decide +kernel

theorem numericCheck1275 (x : Master → ℝ) : Integer.Sparse.eval numericRow1275 x =
    (1 : ℝ) * reducedSource1275 x := by
  norm_num [numericRow1275, reducedSource1275, Integer.Sparse.eval, Sparse.eval, nodeValue627, nodeValue1134, nodeValue1149, nodeValue1236, nodeValue1237, nodeValue1246, nodeValue4092]

theorem reindexCheck1276 : Integer.Sparse.reindex keyMap MixedData.row1276 = numericRow1276 := by decide +kernel

theorem numericCheck1276 (x : Master → ℝ) : Integer.Sparse.eval numericRow1276 x =
    (1 : ℝ) * reducedSource1276 x := by
  norm_num [numericRow1276, reducedSource1276, Integer.Sparse.eval, Sparse.eval, nodeValue1149, nodeValue1154, nodeValue1155, nodeValue1160, nodeValue1246, nodeValue2561, nodeValue4092]

theorem reindexCheck1277 : Integer.Sparse.reindex keyMap MixedData.row1277 = numericRow1277 := by decide +kernel

theorem numericCheck1277 (x : Master → ℝ) : Integer.Sparse.eval numericRow1277 x =
    (1 : ℝ) * reducedSource1277 x := by
  norm_num [numericRow1277, reducedSource1277, Integer.Sparse.eval, Sparse.eval, nodeValue642, nodeValue1160, nodeValue1246, nodeValue1294, nodeValue1295, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1265 (mixedVector B) = 0 := by
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h3301 : mixedVector B (Sum.inr 3301) = Sparse.eval nodeValue3301 (mixedVector B) := by
    change mixedMoment B node3301 node3301Labels = _
    exact sound3301 B hB hF
  have h3311 : mixedVector B (Sum.inr 3311) = Sparse.eval nodeValue3311 (mixedVector B) := by
    change mixedMoment B node3311 node3311Labels = _
    exact sound3311 B hB hF
  have h3312 : mixedVector B (Sum.inr 3312) = Sparse.eval nodeValue3312 (mixedVector B) := by
    change mixedMoment B node3312 node3312Labels = _
    exact sound3312 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1477, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1755, h3301, h3311, h3312, h4071, reducedSource1265] using sourceEq1477 B hB

theorem rowSound1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1265 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1265, numericCheck1265, reducedZero1265 B hB hF, mul_zero]

theorem reducedZero1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1270 (mixedVector B) = 0 := by
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h3312 : mixedVector B (Sum.inr 3312) = Sparse.eval nodeValue3312 (mixedVector B) := by
    change mixedMoment B node3312 node3312Labels = _
    exact sound3312 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1482, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1751, h1755, h3312, h4071, reducedSource1270] using sourceEq1482 B hB

theorem rowSound1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1270 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1270, numericCheck1270, reducedZero1270 B hB hF, mul_zero]

theorem reducedZero1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1271 (mixedVector B) = 0 := by
  have h4158 : mixedVector B (Sum.inr 4158) = Sparse.eval nodeValue4158 (mixedVector B) := by
    change mixedMoment B node4158 node4158Labels = _
    exact sound4158 B hB hF
  have h4160 : mixedVector B (Sum.inr 4160) = Sparse.eval nodeValue4160 (mixedVector B) := by
    change mixedMoment B node4160 node4160Labels = _
    exact sound4160 B hB hF
  have h4161 : mixedVector B (Sum.inr 4161) = Sparse.eval nodeValue4161 (mixedVector B) := by
    change mixedMoment B node4161 node4161Labels = _
    exact sound4161 B hB hF
  have h4188 : mixedVector B (Sum.inr 4188) = Sparse.eval nodeValue4188 (mixedVector B) := by
    change mixedMoment B node4188 node4188Labels = _
    exact sound4188 B hB hF
  have h4533 : mixedVector B (Sum.inr 4533) = Sparse.eval nodeValue4533 (mixedVector B) := by
    change mixedMoment B node4533 node4533Labels = _
    exact sound4533 B hB hF
  have h4534 : mixedVector B (Sum.inr 4534) = Sparse.eval nodeValue4534 (mixedVector B) := by
    change mixedMoment B node4534 node4534Labels = _
    exact sound4534 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4556 : mixedVector B (Sum.inr 4556) = Sparse.eval nodeValue4556 (mixedVector B) := by
    change mixedMoment B node4556 node4556Labels = _
    exact sound4556 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4603 : mixedVector B (Sum.inr 4603) = Sparse.eval nodeValue4603 (mixedVector B) := by
    change mixedMoment B node4603 node4603Labels = _
    exact sound4603 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4609 : mixedVector B (Sum.inr 4609) = Sparse.eval nodeValue4609 (mixedVector B) := by
    change mixedMoment B node4609 node4609Labels = _
    exact sound4609 B hB hF
  have h4619 : mixedVector B (Sum.inr 4619) = Sparse.eval nodeValue4619 (mixedVector B) := by
    change mixedMoment B node4619 node4619Labels = _
    exact sound4619 B hB hF
  have h4620 : mixedVector B (Sum.inr 4620) = Sparse.eval nodeValue4620 (mixedVector B) := by
    change mixedMoment B node4620 node4620Labels = _
    exact sound4620 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  simpa only [sourceForm1483, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4158, h4160, h4161, h4188, h4533, h4534, h4535, h4549, h4556, h4558, h4559, h4602, h4603, h4608, h4609, h4619, h4620, h5111, h5141, h5274, h5275, reducedSource1271] using sourceEq1483 B hB

theorem rowSound1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1271 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1271, numericCheck1271, reducedZero1271 B hB hF, mul_zero]

theorem reducedZero1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1273 (mixedVector B) = 0 := by
  have h1522 : mixedVector B (Sum.inr 1522) = Sparse.eval nodeValue1522 (mixedVector B) := by
    change mixedMoment B node1522 node1522Labels = _
    exact sound1522 B hB hF
  have h1523 : mixedVector B (Sum.inr 1523) = Sparse.eval nodeValue1523 (mixedVector B) := by
    change mixedMoment B node1523 node1523Labels = _
    exact sound1523 B hB hF
  have h1526 : mixedVector B (Sum.inr 1526) = Sparse.eval nodeValue1526 (mixedVector B) := by
    change mixedMoment B node1526 node1526Labels = _
    exact sound1526 B hB hF
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h3265 : mixedVector B (Sum.inr 3265) = Sparse.eval nodeValue3265 (mixedVector B) := by
    change mixedMoment B node3265 node3265Labels = _
    exact sound3265 B hB hF
  have h3267 : mixedVector B (Sum.inr 3267) = Sparse.eval nodeValue3267 (mixedVector B) := by
    change mixedMoment B node3267 node3267Labels = _
    exact sound3267 B hB hF
  have h3268 : mixedVector B (Sum.inr 3268) = Sparse.eval nodeValue3268 (mixedVector B) := by
    change mixedMoment B node3268 node3268Labels = _
    exact sound3268 B hB hF
  have h3271 : mixedVector B (Sum.inr 3271) = Sparse.eval nodeValue3271 (mixedVector B) := by
    change mixedMoment B node3271 node3271Labels = _
    exact sound3271 B hB hF
  have h3272 : mixedVector B (Sum.inr 3272) = Sparse.eval nodeValue3272 (mixedVector B) := by
    change mixedMoment B node3272 node3272Labels = _
    exact sound3272 B hB hF
  have h3276 : mixedVector B (Sum.inr 3276) = Sparse.eval nodeValue3276 (mixedVector B) := by
    change mixedMoment B node3276 node3276Labels = _
    exact sound3276 B hB hF
  have h3277 : mixedVector B (Sum.inr 3277) = Sparse.eval nodeValue3277 (mixedVector B) := by
    change mixedMoment B node3277 node3277Labels = _
    exact sound3277 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  simpa only [sourceForm1485, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1522, h1523, h1526, h1533, h3265, h3267, h3268, h3271, h3272, h3276, h3277, h3293, h3294, h3300, h3302, h3305, h3306, h3485, h3522, h3547, h3548, reducedSource1273] using sourceEq1485 B hB

theorem rowSound1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1273 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1273, numericCheck1273, reducedZero1273 B hB hF, mul_zero]

theorem reducedZero1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1274 (mixedVector B) = 0 := by
  have h627 : mixedVector B (Sum.inr 627) = Sparse.eval nodeValue627 (mixedVector B) := by
    change mixedMoment B node627 node627Labels = _
    exact sound627 B hB hF
  have h635 : mixedVector B (Sum.inr 635) = Sparse.eval nodeValue635 (mixedVector B) := by
    change mixedMoment B node635 node635Labels = _
    exact sound635 B hB hF
  have h636 : mixedVector B (Sum.inr 636) = Sparse.eval nodeValue636 (mixedVector B) := by
    change mixedMoment B node636 node636Labels = _
    exact sound636 B hB hF
  have h642 : mixedVector B (Sum.inr 642) = Sparse.eval nodeValue642 (mixedVector B) := by
    change mixedMoment B node642 node642Labels = _
    exact sound642 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1486, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h627, h635, h636, h642, h1246, h4092, reducedSource1274] using sourceEq1486 B hB

theorem rowSound1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1274 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1274, numericCheck1274, reducedZero1274 B hB hF, mul_zero]

theorem reducedZero1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1275 (mixedVector B) = 0 := by
  have h627 : mixedVector B (Sum.inr 627) = Sparse.eval nodeValue627 (mixedVector B) := by
    change mixedMoment B node627 node627Labels = _
    exact sound627 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1149 : mixedVector B (Sum.inr 1149) = Sparse.eval nodeValue1149 (mixedVector B) := by
    change mixedMoment B node1149 node1149Labels = _
    exact sound1149 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1487, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h627, h1134, h1149, h1236, h1237, h1246, h4092, reducedSource1275] using sourceEq1487 B hB

theorem rowSound1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1275 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1275, numericCheck1275, reducedZero1275 B hB hF, mul_zero]

theorem reducedZero1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1276 (mixedVector B) = 0 := by
  have h1149 : mixedVector B (Sum.inr 1149) = Sparse.eval nodeValue1149 (mixedVector B) := by
    change mixedMoment B node1149 node1149Labels = _
    exact sound1149 B hB hF
  have h1154 : mixedVector B (Sum.inr 1154) = Sparse.eval nodeValue1154 (mixedVector B) := by
    change mixedMoment B node1154 node1154Labels = _
    exact sound1154 B hB hF
  have h1155 : mixedVector B (Sum.inr 1155) = Sparse.eval nodeValue1155 (mixedVector B) := by
    change mixedMoment B node1155 node1155Labels = _
    exact sound1155 B hB hF
  have h1160 : mixedVector B (Sum.inr 1160) = Sparse.eval nodeValue1160 (mixedVector B) := by
    change mixedMoment B node1160 node1160Labels = _
    exact sound1160 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h2561 : mixedVector B (Sum.inr 2561) = Sparse.eval nodeValue2561 (mixedVector B) := by
    change mixedMoment B node2561 node2561Labels = _
    exact sound2561 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1488, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1149, h1154, h1155, h1160, h1246, h2561, h4092, reducedSource1276] using sourceEq1488 B hB

theorem rowSound1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1276 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1276, numericCheck1276, reducedZero1276 B hB hF, mul_zero]

theorem reducedZero1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1277 (mixedVector B) = 0 := by
  have h642 : mixedVector B (Sum.inr 642) = Sparse.eval nodeValue642 (mixedVector B) := by
    change mixedMoment B node642 node642Labels = _
    exact sound642 B hB hF
  have h1160 : mixedVector B (Sum.inr 1160) = Sparse.eval nodeValue1160 (mixedVector B) := by
    change mixedMoment B node1160 node1160Labels = _
    exact sound1160 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h1295 : mixedVector B (Sum.inr 1295) = Sparse.eval nodeValue1295 (mixedVector B) := by
    change mixedMoment B node1295 node1295Labels = _
    exact sound1295 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1489, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h642, h1160, h1246, h1294, h1295, h4092, reducedSource1277] using sourceEq1489 B hB

theorem rowSound1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1277 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1277, numericCheck1277, reducedZero1277 B hB hF, mul_zero]

theorem sourceRowsAt1264 : MixedData.sourceRows (1264 : Fin 2425) =
    MixedData.row1264 := by decide +kernel

theorem sourceRowsAt1265 : MixedData.sourceRows (1265 : Fin 2425) =
    MixedData.row1265 := by decide +kernel

theorem sourceRowsAt1266 : MixedData.sourceRows (1266 : Fin 2425) =
    MixedData.row1266 := by decide +kernel

theorem sourceRowsAt1267 : MixedData.sourceRows (1267 : Fin 2425) =
    MixedData.row1267 := by decide +kernel

theorem sourceRowsAt1268 : MixedData.sourceRows (1268 : Fin 2425) =
    MixedData.row1268 := by decide +kernel

theorem sourceRowsAt1269 : MixedData.sourceRows (1269 : Fin 2425) =
    MixedData.row1269 := by decide +kernel

theorem sourceRowsAt1270 : MixedData.sourceRows (1270 : Fin 2425) =
    MixedData.row1270 := by decide +kernel

theorem sourceRowsAt1271 : MixedData.sourceRows (1271 : Fin 2425) =
    MixedData.row1271 := by decide +kernel

theorem sourceRowsAt1272 : MixedData.sourceRows (1272 : Fin 2425) =
    MixedData.row1272 := by decide +kernel

theorem sourceRowsAt1273 : MixedData.sourceRows (1273 : Fin 2425) =
    MixedData.row1273 := by decide +kernel

theorem sourceRowsAt1274 : MixedData.sourceRows (1274 : Fin 2425) =
    MixedData.row1274 := by decide +kernel

theorem sourceRowsAt1275 : MixedData.sourceRows (1275 : Fin 2425) =
    MixedData.row1275 := by decide +kernel

theorem sourceRowsAt1276 : MixedData.sourceRows (1276 : Fin 2425) =
    MixedData.row1276 := by decide +kernel

theorem sourceRowsAt1277 : MixedData.sourceRows (1277 : Fin 2425) =
    MixedData.row1277 := by decide +kernel

theorem sourceRowsAt1278 : MixedData.sourceRows (1278 : Fin 2425) =
    MixedData.row1278 := by decide +kernel

theorem sourceRowsAt1279 : MixedData.sourceRows (1279 : Fin 2425) =
    MixedData.row1279 := by decide +kernel

theorem chunkSound79_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 79) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1264 ∨ k.val = 1265 ∨ k.val = 1266 ∨ k.val = 1267 ∨ k.val = 1268 ∨ k.val = 1269 ∨ k.val = 1270 ∨ k.val = 1271 ∨ k.val = 1272 ∨ k.val = 1273 ∨ k.val = 1274 ∨ k.val = 1275 ∨ k.val = 1276 ∨ k.val = 1277 ∨ k.val = 1278 ∨ k.val = 1279 := by omega
  rcases heq with h1264 | h1265 | h1266 | h1267 | h1268 | h1269 | h1270 | h1271 | h1272 | h1273 | h1274 | h1275 | h1276 | h1277 | h1278 | h1279
  · have he : k = (1264 : Fin 2425) := Fin.ext h1264
    subst k
    rw [sourceRowsAt1264]
    exact rowSound1264_e B hB hF
  · have he : k = (1265 : Fin 2425) := Fin.ext h1265
    subst k
    rw [sourceRowsAt1265]
    exact rowSound1265 B hB hF
  · have he : k = (1266 : Fin 2425) := Fin.ext h1266
    subst k
    rw [sourceRowsAt1266]
    exact rowSound1266_e B hB hF
  · have he : k = (1267 : Fin 2425) := Fin.ext h1267
    subst k
    rw [sourceRowsAt1267]
    exact rowSound1267_e B hB hF
  · have he : k = (1268 : Fin 2425) := Fin.ext h1268
    subst k
    rw [sourceRowsAt1268]
    exact rowSound1268_e B hB hF
  · have he : k = (1269 : Fin 2425) := Fin.ext h1269
    subst k
    rw [sourceRowsAt1269]
    exact rowSound1269_e B hB hF
  · have he : k = (1270 : Fin 2425) := Fin.ext h1270
    subst k
    rw [sourceRowsAt1270]
    exact rowSound1270 B hB hF
  · have he : k = (1271 : Fin 2425) := Fin.ext h1271
    subst k
    rw [sourceRowsAt1271]
    exact rowSound1271 B hB hF
  · have he : k = (1272 : Fin 2425) := Fin.ext h1272
    subst k
    rw [sourceRowsAt1272]
    exact rowSound1272_e B hB hF
  · have he : k = (1273 : Fin 2425) := Fin.ext h1273
    subst k
    rw [sourceRowsAt1273]
    exact rowSound1273 B hB hF
  · have he : k = (1274 : Fin 2425) := Fin.ext h1274
    subst k
    rw [sourceRowsAt1274]
    exact rowSound1274 B hB hF
  · have he : k = (1275 : Fin 2425) := Fin.ext h1275
    subst k
    rw [sourceRowsAt1275]
    exact rowSound1275 B hB hF
  · have he : k = (1276 : Fin 2425) := Fin.ext h1276
    subst k
    rw [sourceRowsAt1276]
    exact rowSound1276 B hB hF
  · have he : k = (1277 : Fin 2425) := Fin.ext h1277
    subst k
    rw [sourceRowsAt1277]
    exact rowSound1277 B hB hF
  · have he : k = (1278 : Fin 2425) := Fin.ext h1278
    subst k
    rw [sourceRowsAt1278]
    exact rowSound1278_e B hB hF
  · have he : k = (1279 : Fin 2425) := Fin.ext h1279
    subst k
    rw [sourceRowsAt1279]
    exact rowSound1279_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e_oai
