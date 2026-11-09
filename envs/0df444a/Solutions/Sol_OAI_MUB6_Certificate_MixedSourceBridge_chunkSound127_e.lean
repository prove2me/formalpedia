-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:46:00.702379+00:00
-- url     : https://prove2.me/submissions/67878abd-7f41-4b68-9a4e-dfa27c03bdde

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2033_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2034_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2035_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2036_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2037_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2038_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2039_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2040_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound2046_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1566 raw1566Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw1566 raw1566Labels = mixedMoment B raw1566step0 raw1566step0Labels := by
      have ha : raw1566step0 = (fun i j => raw1566 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1566step0 raw1566; decide +kernel
      have hl : raw1566step0Labels = raw1566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1566 raw1566Labels permutation32 permutation4
    mixedMoment B raw1566step0 raw1566step0Labels = mixedMoment B raw1566step1 raw1566step1Labels := by
      have ha : raw1566step1 = raw1566step0 := by apply Matrix.ext; unfold raw1566step1 raw1566step0; decide +kernel
      have hl : raw1566step0Labels = labelEmbedding7 ∘ raw1566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1566step0 raw1566step0Labels raw1566step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical1567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1567 raw1567Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw1567 raw1567Labels = mixedMoment B raw1567step0 raw1567step0Labels := by
      have ha : raw1567step0 = (fun i j => raw1567 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1567step0 raw1567; decide +kernel
      have hl : raw1567step0Labels = raw1567Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1567 raw1567Labels permutation32 permutation4
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical1568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1568 raw1568Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw1568 raw1568Labels = mixedMoment B raw1568step0 raw1568step0Labels := by
      have ha : raw1568step0 = (fun i j => raw1568 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1568step0 raw1568; decide +kernel
      have hl : raw1568step0Labels = raw1568Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1568 raw1568Labels permutation32 permutation6
    mixedMoment B raw1568step0 raw1568step0Labels = mixedMoment B raw1568step1 raw1568step1Labels := by
      have ha : raw1568step1 = -raw1568step0 := by apply Matrix.ext; change ∀ i j, raw1568step1 i j = -(raw1568step0 i j); unfold raw1568step1 raw1568step0; decide +kernel
      have hl : raw1568step1Labels = raw1568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1568step1 raw1568step1Labels = mixedMoment B raw1568step2 raw1568step2Labels := by
      have ha : raw1568step2 = raw1568step1 := by apply Matrix.ext; unfold raw1568step2 raw1568step1; decide +kernel
      have hl : raw1568step1Labels = labelEmbedding1 ∘ raw1568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1568step1 raw1568step1Labels raw1568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

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

theorem canonical1587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1587 raw1587Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw1587 raw1587Labels = mixedMoment B raw1587step0 raw1587step0Labels := by
      have ha : raw1587step0 = (fun i j => raw1587 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1587step0 raw1587; decide +kernel
      have hl : raw1587step0Labels = raw1587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1587 raw1587Labels permutation8 permutation4
    mixedMoment B raw1587step0 raw1587step0Labels = mixedMoment B raw1587step1 raw1587step1Labels := by
      have ha : raw1587step1 = raw1587step0 := by apply Matrix.ext; unfold raw1587step1 raw1587step0; decide +kernel
      have hl : raw1587step0Labels = labelEmbedding7 ∘ raw1587step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1587step0 raw1587step0Labels raw1587step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

theorem canonical1588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1588 raw1588Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw1588 raw1588Labels = mixedMoment B raw1588step0 raw1588step0Labels := by
      have ha : raw1588step0 = (fun i j => raw1588 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1588step0 raw1588; decide +kernel
      have hl : raw1588step0Labels = raw1588Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1588 raw1588Labels permutation8 permutation4
    _ = mixedMoment B node1819 node1819Labels := by rfl

theorem canonical1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1589 raw1589Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw1589 raw1589Labels = mixedMoment B raw1589step0 raw1589step0Labels := by
      have ha : raw1589step0 = (fun i j => raw1589 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1589step0 raw1589; decide +kernel
      have hl : raw1589step0Labels = raw1589Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1589 raw1589Labels permutation9 permutation6
    mixedMoment B raw1589step0 raw1589step0Labels = mixedMoment B raw1589step1 raw1589step1Labels := by
      have ha : raw1589step1 = -raw1589step0 := by apply Matrix.ext; change ∀ i j, raw1589step1 i j = -(raw1589step0 i j); unfold raw1589step1 raw1589step0; decide +kernel
      have hl : raw1589step1Labels = raw1589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1589step1 raw1589step1Labels = mixedMoment B raw1589step2 raw1589step2Labels := by
      have ha : raw1589step2 = raw1589step1 := by apply Matrix.ext; unfold raw1589step2 raw1589step1; decide +kernel
      have hl : raw1589step1Labels = labelEmbedding1 ∘ raw1589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1589step1 raw1589step1Labels raw1589step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16502 raw16502Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw16502 raw16502Labels = mixedMoment B raw16502step0 raw16502step0Labels := by
      have hz : ∀ j, raw16502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16502step0 = (fun i j => raw16502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16502step0 raw16502; decide +kernel
      have hl : raw16502step0Labels = raw16502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16502 raw16502Labels permutation346 hz
    mixedMoment B raw16502step0 raw16502step0Labels = mixedMoment B raw16502step1 raw16502step1Labels := by
      have ha : raw16502step1 = (fun i j => raw16502step0 (permutation63 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16502step1 raw16502step0; decide +kernel
      have hl : raw16502step1Labels = raw16502step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16502step0 raw16502step0Labels permutation63 permutation7
    mixedMoment B raw16502step1 raw16502step1Labels = mixedMoment B raw16502step2 raw16502step2Labels := by
      have ha : raw16502step2 = -raw16502step1 := by apply Matrix.ext; change ∀ i j, raw16502step2 i j = -(raw16502step1 i j); unfold raw16502step2 raw16502step1; decide +kernel
      have hl : raw16502step2Labels = raw16502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16502step2 raw16502step2Labels = mixedMoment B raw16502step3 raw16502step3Labels := by
      have ha : raw16502step3 = raw16502step2 := by apply Matrix.ext; unfold raw16502step3 raw16502step2; decide +kernel
      have hl : raw16502step2Labels = labelEmbedding1 ∘ raw16502step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16502step2 raw16502step2Labels raw16502step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16513 raw16513Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw16513 raw16513Labels = mixedMoment B raw16513step0 raw16513step0Labels := by
      have ha : raw16513step0 = (fun i j => raw16513 (permutation306 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16513step0 raw16513; decide +kernel
      have hl : raw16513step0Labels = raw16513Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16513 raw16513Labels permutation306 permutation7
    mixedMoment B raw16513step0 raw16513step0Labels = mixedMoment B raw16513step1 raw16513step1Labels := by
      have ha : raw16513step1 = -raw16513step0 := by apply Matrix.ext; change ∀ i j, raw16513step1 i j = -(raw16513step0 i j); unfold raw16513step1 raw16513step0; decide +kernel
      have hl : raw16513step1Labels = raw16513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16513step1 raw16513step1Labels = mixedMoment B raw16513step2 raw16513step2Labels := by
      have ha : raw16513step2 = raw16513step1 := by apply Matrix.ext; unfold raw16513step2 raw16513step1; decide +kernel
      have hl : raw16513step1Labels = labelEmbedding1 ∘ raw16513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16513step1 raw16513step1Labels raw16513step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

theorem canonical16518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16518 raw16518Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw16518 raw16518Labels = mixedMoment B raw16518step0 raw16518step0Labels := by
      have hz : ∀ j, raw16518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16518step0 = (fun i j => raw16518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16518step0 raw16518; decide +kernel
      have hl : raw16518step0Labels = raw16518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16518 raw16518Labels permutation346 hz
    mixedMoment B raw16518step0 raw16518step0Labels = mixedMoment B raw16518step1 raw16518step1Labels := by
      have ha : raw16518step1 = (fun i j => raw16518step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16518step1 raw16518step0; decide +kernel
      have hl : raw16518step1Labels = raw16518step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16518step0 raw16518step0Labels permutation45 permutation5
    mixedMoment B raw16518step1 raw16518step1Labels = mixedMoment B raw16518step2 raw16518step2Labels := by
      have ha : raw16518step2 = -raw16518step1 := by apply Matrix.ext; change ∀ i j, raw16518step2 i j = -(raw16518step1 i j); unfold raw16518step2 raw16518step1; decide +kernel
      have hl : raw16518step2Labels = raw16518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16518step2 raw16518step2Labels = mixedMoment B raw16518step3 raw16518step3Labels := by
      have ha : raw16518step3 = raw16518step2 := by apply Matrix.ext; unfold raw16518step3 raw16518step2; decide +kernel
      have hl : raw16518step2Labels = labelEmbedding1 ∘ raw16518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16518step2 raw16518step2Labels raw16518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3868 node3868Labels := by rfl

theorem canonical16522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16522 raw16522Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw16522 raw16522Labels = mixedMoment B raw16522step0 raw16522step0Labels := by
      have hz : ∀ j, raw16522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16522step0 = (fun i j => raw16522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16522step0 raw16522; decide +kernel
      have hl : raw16522step0Labels = raw16522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16522 raw16522Labels permutation346 hz
    mixedMoment B raw16522step0 raw16522step0Labels = mixedMoment B raw16522step1 raw16522step1Labels := by
      have ha : raw16522step1 = (fun i j => raw16522step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16522step1 raw16522step0; decide +kernel
      have hl : raw16522step1Labels = raw16522step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16522step0 raw16522step0Labels permutation44 permutation5
    mixedMoment B raw16522step1 raw16522step1Labels = mixedMoment B raw16522step2 raw16522step2Labels := by
      have ha : raw16522step2 = -raw16522step1 := by apply Matrix.ext; change ∀ i j, raw16522step2 i j = -(raw16522step1 i j); unfold raw16522step2 raw16522step1; decide +kernel
      have hl : raw16522step2Labels = raw16522step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16522step2 raw16522step2Labels = mixedMoment B raw16522step3 raw16522step3Labels := by
      have ha : raw16522step3 = raw16522step2 := by apply Matrix.ext; unfold raw16522step3 raw16522step2; decide +kernel
      have hl : raw16522step2Labels = labelEmbedding1 ∘ raw16522step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16522step2 raw16522step2Labels raw16522step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical16524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16524 raw16524Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw16524 raw16524Labels = mixedMoment B raw16524step0 raw16524step0Labels := by
      have ha : raw16524step0 = (fun i j => raw16524 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16524step0 raw16524; decide +kernel
      have hl : raw16524step0Labels = raw16524Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16524 raw16524Labels permutation581 permutation7
    mixedMoment B raw16524step0 raw16524step0Labels = mixedMoment B raw16524step1 raw16524step1Labels := by
      have ha : raw16524step1 = raw16524step0 := by apply Matrix.ext; unfold raw16524step1 raw16524step0; decide +kernel
      have hl : raw16524step0Labels = labelEmbedding1 ∘ raw16524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16524step0 raw16524step0Labels raw16524step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical16525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16525 raw16525Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw16525 raw16525Labels = mixedMoment B raw16525step0 raw16525step0Labels := by
      have hz : ∀ j, raw16525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16525step0 = (fun i j => raw16525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16525step0 raw16525; decide +kernel
      have hl : raw16525step0Labels = raw16525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16525 raw16525Labels permutation346 hz
    mixedMoment B raw16525step0 raw16525step0Labels = mixedMoment B raw16525step1 raw16525step1Labels := by
      have ha : raw16525step1 = (fun i j => raw16525step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16525step1 raw16525step0; decide +kernel
      have hl : raw16525step1Labels = raw16525step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16525step0 raw16525step0Labels permutation123 permutation7
    mixedMoment B raw16525step1 raw16525step1Labels = mixedMoment B raw16525step2 raw16525step2Labels := by
      have ha : raw16525step2 = raw16525step1 := by apply Matrix.ext; unfold raw16525step2 raw16525step1; decide +kernel
      have hl : raw16525step1Labels = labelEmbedding1 ∘ raw16525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16525step1 raw16525step1Labels raw16525step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

theorem canonical16526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16526 raw16526Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw16526 raw16526Labels = mixedMoment B raw16526step0 raw16526step0Labels := by
      have hz : ∀ j, raw16526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16526step0 = (fun i j => raw16526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16526step0 raw16526; decide +kernel
      have hl : raw16526step0Labels = raw16526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16526 raw16526Labels permutation346 hz
    mixedMoment B raw16526step0 raw16526step0Labels = mixedMoment B raw16526step1 raw16526step1Labels := by
      have ha : raw16526step1 = (fun i j => raw16526step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16526step1 raw16526step0; decide +kernel
      have hl : raw16526step1Labels = raw16526step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16526step0 raw16526step0Labels permutation123 permutation7
    mixedMoment B raw16526step1 raw16526step1Labels = mixedMoment B raw16526step2 raw16526step2Labels := by
      have ha : raw16526step2 = raw16526step1 := by apply Matrix.ext; unfold raw16526step2 raw16526step1; decide +kernel
      have hl : raw16526step1Labels = labelEmbedding1 ∘ raw16526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16526step1 raw16526step1Labels raw16526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical16528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16528 raw16528Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw16528 raw16528Labels = mixedMoment B raw16528step0 raw16528step0Labels := by
      have hz : ∀ j, raw16528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16528step0 = (fun i j => raw16528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16528step0 raw16528; decide +kernel
      have hl : raw16528step0Labels = raw16528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16528 raw16528Labels permutation346 hz
    mixedMoment B raw16528step0 raw16528step0Labels = mixedMoment B raw16528step1 raw16528step1Labels := by
      have ha : raw16528step1 = (fun i j => raw16528step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16528step1 raw16528step0; decide +kernel
      have hl : raw16528step1Labels = raw16528step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16528step0 raw16528step0Labels permutation143 permutation5
    mixedMoment B raw16528step1 raw16528step1Labels = mixedMoment B raw16528step2 raw16528step2Labels := by
      have ha : raw16528step2 = raw16528step1 := by apply Matrix.ext; unfold raw16528step2 raw16528step1; decide +kernel
      have hl : raw16528step1Labels = labelEmbedding1 ∘ raw16528step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16528step1 raw16528step1Labels raw16528step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical16538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16538 raw16538Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw16538 raw16538Labels = mixedMoment B raw16538step0 raw16538step0Labels := by
      have hz : ∀ j, raw16538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16538step0 = (fun i j => raw16538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16538step0 raw16538; decide +kernel
      have hl : raw16538step0Labels = raw16538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16538 raw16538Labels permutation346 hz
    mixedMoment B raw16538step0 raw16538step0Labels = mixedMoment B raw16538step1 raw16538step1Labels := by
      have hz : ∀ j, raw16538step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw16538step1 = (fun i j => raw16538step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw16538step1 raw16538step0; decide +kernel
      have hl : raw16538step1Labels = raw16538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16538step0 raw16538step0Labels permutation32 hz
    mixedMoment B raw16538step1 raw16538step1Labels = mixedMoment B raw16538step2 raw16538step2Labels := by
      have ha : raw16538step2 = (fun i j => raw16538step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16538step2 raw16538step1; decide +kernel
      have hl : raw16538step2Labels = raw16538step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16538step1 raw16538step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical16540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16540 raw16540Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw16540 raw16540Labels = mixedMoment B raw16540step0 raw16540step0Labels := by
      have ha : raw16540step0 = (fun i j => raw16540 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16540step0 raw16540; decide +kernel
      have hl : raw16540step0Labels = raw16540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16540 raw16540Labels permutation271 permutation2
    _ = mixedMoment B node3720 node3720Labels := by rfl

theorem canonical16541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16541 raw16541Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw16541 raw16541Labels = mixedMoment B raw16541step0 raw16541step0Labels := by
      have hz : ∀ j, raw16541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16541step0 = (fun i j => raw16541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16541step0 raw16541; decide +kernel
      have hl : raw16541step0Labels = raw16541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16541 raw16541Labels permutation346 hz
    mixedMoment B raw16541step0 raw16541step0Labels = mixedMoment B raw16541step1 raw16541step1Labels := by
      have ha : raw16541step1 = (fun i j => raw16541step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16541step1 raw16541step0; decide +kernel
      have hl : raw16541step1Labels = raw16541step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16541step0 raw16541step0Labels permutation56 permutation2
    _ = mixedMoment B node3733 node3733Labels := by rfl

theorem canonical16542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16542 raw16542Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw16542 raw16542Labels = mixedMoment B raw16542step0 raw16542step0Labels := by
      have hz : ∀ j, raw16542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16542step0 = (fun i j => raw16542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16542step0 raw16542; decide +kernel
      have hl : raw16542step0Labels = raw16542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16542 raw16542Labels permutation346 hz
    mixedMoment B raw16542step0 raw16542step0Labels = mixedMoment B raw16542step1 raw16542step1Labels := by
      have ha : raw16542step1 = (fun i j => raw16542step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16542step1 raw16542step0; decide +kernel
      have hl : raw16542step1Labels = raw16542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16542step0 raw16542step0Labels permutation126 permutation2
    mixedMoment B raw16542step1 raw16542step1Labels = mixedMoment B raw16542step2 raw16542step2Labels := by
      have ha : raw16542step2 = -raw16542step1 := by apply Matrix.ext; change ∀ i j, raw16542step2 i j = -(raw16542step1 i j); unfold raw16542step2 raw16542step1; decide +kernel
      have hl : raw16542step2Labels = raw16542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical16550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16550 raw16550Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw16550 raw16550Labels = mixedMoment B raw16550step0 raw16550step0Labels := by
      have ha : raw16550step0 = (fun i j => raw16550 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16550step0 raw16550; decide +kernel
      have hl : raw16550step0Labels = raw16550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16550 raw16550Labels permutation589 permutation2
    mixedMoment B raw16550step0 raw16550step0Labels = mixedMoment B raw16550step1 raw16550step1Labels := by
      have ha : raw16550step1 = -raw16550step0 := by apply Matrix.ext; change ∀ i j, raw16550step1 i j = -(raw16550step0 i j); unfold raw16550step1 raw16550step0; decide +kernel
      have hl : raw16550step1Labels = raw16550step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

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

theorem canonical2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2250 raw2250Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw2250 raw2250Labels = mixedMoment B raw2250step0 raw2250step0Labels := by
      have ha : raw2250step0 = (fun i j => raw2250 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2250step0 raw2250; decide +kernel
      have hl : raw2250step0Labels = raw2250Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2250 raw2250Labels permutation32 permutation4
    mixedMoment B raw2250step0 raw2250step0Labels = mixedMoment B raw2250step1 raw2250step1Labels := by
      have ha : raw2250step1 = raw2250step0 := by apply Matrix.ext; unfold raw2250step1 raw2250step0; decide +kernel
      have hl : raw2250step0Labels = labelEmbedding7 ∘ raw2250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2250step0 raw2250step0Labels raw2250step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2251 raw2251Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw2251 raw2251Labels = mixedMoment B raw2251step0 raw2251step0Labels := by
      have ha : raw2251step0 = (fun i j => raw2251 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2251step0 raw2251; decide +kernel
      have hl : raw2251step0Labels = raw2251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2251 raw2251Labels permutation32 permutation4
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2252 raw2252Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw2252 raw2252Labels = mixedMoment B raw2252step0 raw2252step0Labels := by
      have ha : raw2252step0 = (fun i j => raw2252 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2252step0 raw2252; decide +kernel
      have hl : raw2252step0Labels = raw2252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2252 raw2252Labels permutation32 permutation6
    mixedMoment B raw2252step0 raw2252step0Labels = mixedMoment B raw2252step1 raw2252step1Labels := by
      have ha : raw2252step1 = -raw2252step0 := by apply Matrix.ext; change ∀ i j, raw2252step1 i j = -(raw2252step0 i j); unfold raw2252step1 raw2252step0; decide +kernel
      have hl : raw2252step1Labels = raw2252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2252step1 raw2252step1Labels = mixedMoment B raw2252step2 raw2252step2Labels := by
      have ha : raw2252step2 = raw2252step1 := by apply Matrix.ext; unfold raw2252step2 raw2252step1; decide +kernel
      have hl : raw2252step1Labels = labelEmbedding1 ∘ raw2252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2252step1 raw2252step1Labels raw2252step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2265 raw2265Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw2265 raw2265Labels = mixedMoment B raw2265step0 raw2265step0Labels := by
      have ha : raw2265step0 = (fun i j => raw2265 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2265step0 raw2265; decide +kernel
      have hl : raw2265step0Labels = raw2265Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2265 raw2265Labels permutation32 permutation4
    mixedMoment B raw2265step0 raw2265step0Labels = mixedMoment B raw2265step1 raw2265step1Labels := by
      have ha : raw2265step1 = raw2265step0 := by apply Matrix.ext; unfold raw2265step1 raw2265step0; decide +kernel
      have hl : raw2265step0Labels = labelEmbedding7 ∘ raw2265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2265step0 raw2265step0Labels raw2265step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2266 raw2266Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw2266 raw2266Labels = mixedMoment B raw2266step0 raw2266step0Labels := by
      have ha : raw2266step0 = (fun i j => raw2266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2266step0 raw2266; decide +kernel
      have hl : raw2266step0Labels = raw2266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2266 raw2266Labels permutation32 permutation4
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2267 raw2267Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw2267 raw2267Labels = mixedMoment B raw2267step0 raw2267step0Labels := by
      have ha : raw2267step0 = (fun i j => raw2267 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2267step0 raw2267; decide +kernel
      have hl : raw2267step0Labels = raw2267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2267 raw2267Labels permutation32 permutation6
    mixedMoment B raw2267step0 raw2267step0Labels = mixedMoment B raw2267step1 raw2267step1Labels := by
      have ha : raw2267step1 = -raw2267step0 := by apply Matrix.ext; change ∀ i j, raw2267step1 i j = -(raw2267step0 i j); unfold raw2267step1 raw2267step0; decide +kernel
      have hl : raw2267step1Labels = raw2267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2267step1 raw2267step1Labels = mixedMoment B raw2267step2 raw2267step2Labels := by
      have ha : raw2267step2 = raw2267step1 := by apply Matrix.ext; unfold raw2267step2 raw2267step1; decide +kernel
      have hl : raw2267step1Labels = labelEmbedding1 ∘ raw2267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2267step1 raw2267step1Labels raw2267step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2313 raw2313Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2313 raw2313Labels = mixedMoment B raw2313step0 raw2313step0Labels := by
      have ha : raw2313step0 = (fun i j => raw2313 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2313step0 raw2313; decide +kernel
      have hl : raw2313step0Labels = raw2313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2313 raw2313Labels permutation8 permutation5
    mixedMoment B raw2313step0 raw2313step0Labels = mixedMoment B raw2313step1 raw2313step1Labels := by
      have ha : raw2313step1 = raw2313step0 := by apply Matrix.ext; unfold raw2313step1 raw2313step0; decide +kernel
      have hl : raw2313step0Labels = labelEmbedding8 ∘ raw2313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2313step0 raw2313step0Labels raw2313step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2314 raw2314Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw2314 raw2314Labels = mixedMoment B raw2314step0 raw2314step0Labels := by
      have ha : raw2314step0 = (fun i j => raw2314 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2314step0 raw2314; decide +kernel
      have hl : raw2314step0Labels = raw2314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2314 raw2314Labels permutation8 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical2315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2315 raw2315Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw2315 raw2315Labels = mixedMoment B raw2315step0 raw2315step0Labels := by
      have ha : raw2315step0 = (fun i j => raw2315 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2315step0 raw2315; decide +kernel
      have hl : raw2315step0Labels = raw2315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2315 raw2315Labels permutation11 permutation3
    mixedMoment B raw2315step0 raw2315step0Labels = mixedMoment B raw2315step1 raw2315step1Labels := by
      have ha : raw2315step1 = -raw2315step0 := by apply Matrix.ext; change ∀ i j, raw2315step1 i j = -(raw2315step0 i j); unfold raw2315step1 raw2315step0; decide +kernel
      have hl : raw2315step1Labels = raw2315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2315step1 raw2315step1Labels = mixedMoment B raw2315step2 raw2315step2Labels := by
      have ha : raw2315step2 = raw2315step1 := by apply Matrix.ext; unfold raw2315step2 raw2315step1; decide +kernel
      have hl : raw2315step1Labels = labelEmbedding1 ∘ raw2315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2315step1 raw2315step1Labels raw2315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24552 raw24552Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24552 raw24552Labels = mixedMoment B raw24552step0 raw24552step0Labels := by
      have hz : ∀ j, raw24552 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24552step0 = (fun i j => raw24552 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24552step0 raw24552; decide +kernel
      have hl : raw24552step0Labels = raw24552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24552 raw24552Labels permutation265 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29347 raw29347Labels = mixedMoment B node3133 node3133Labels := by
  calc
    mixedMoment B raw29347 raw29347Labels = mixedMoment B raw29347step0 raw29347step0Labels := by
      have ha : raw29347step0 = (fun i j => raw29347 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29347step0 raw29347; decide +kernel
      have hl : raw29347step0Labels = raw29347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29347 raw29347Labels permutation159 permutation2
    _ = mixedMoment B node3133 node3133Labels := by rfl

theorem canonical29348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29348 raw29348Labels = mixedMoment B node3138 node3138Labels := by
  calc
    mixedMoment B raw29348 raw29348Labels = mixedMoment B raw29348step0 raw29348step0Labels := by
      have hz : ∀ j, raw29348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29348step0 = (fun i j => raw29348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29348step0 raw29348; decide +kernel
      have hl : raw29348step0Labels = raw29348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29348 raw29348Labels permutation346 hz
    mixedMoment B raw29348step0 raw29348step0Labels = mixedMoment B raw29348step1 raw29348step1Labels := by
      have ha : raw29348step1 = (fun i j => raw29348step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29348step1 raw29348step0; decide +kernel
      have hl : raw29348step1Labels = raw29348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29348step0 raw29348step0Labels permutation33 permutation2
    _ = mixedMoment B node3138 node3138Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29487 raw29487Labels = mixedMoment B node2351 node2351Labels := by
  calc
    _ = mixedMoment B node2351 node2351Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32878 raw32878Labels = mixedMoment B node3721 node3721Labels := by
  calc
    _ = mixedMoment B node3721 node3721Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34776 raw34776Labels = mixedMoment B node3716 node3716Labels := by
  calc
    _ = mixedMoment B node3716 node3716Labels := by rfl

theorem canonical34777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34777 raw34777Labels = mixedMoment B node3709 node3709Labels := by
  calc
    _ = mixedMoment B node3709 node3709Labels := by rfl

theorem canonical34780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34780 raw34780Labels = mixedMoment B node3135 node3135Labels := by
  calc
    mixedMoment B raw34780 raw34780Labels = mixedMoment B raw34780step0 raw34780step0Labels := by
      have ha : raw34780step0 = (fun i j => raw34780 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34780step0 raw34780; decide +kernel
      have hl : raw34780step0Labels = raw34780Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34780 raw34780Labels permutation265 permutation2
    _ = mixedMoment B node3135 node3135Labels := by rfl

theorem canonical34781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34781 raw34781Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw34781 raw34781Labels = mixedMoment B raw34781step0 raw34781step0Labels := by
      have ha : raw34781step0 = (fun i j => raw34781 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34781step0 raw34781; decide +kernel
      have hl : raw34781step0Labels = raw34781Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34781 raw34781Labels permutation153 permutation2
    _ = mixedMoment B node3721 node3721Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical273
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34985 raw34985Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw34985 raw34985Labels = mixedMoment B raw34985step0 raw34985step0Labels := by
      have hz : ∀ j, raw34985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34985step0 = (fun i j => raw34985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34985step0 raw34985; decide +kernel
      have hl : raw34985step0Labels = raw34985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34985 raw34985Labels permutation346 hz
    mixedMoment B raw34985step0 raw34985step0Labels = mixedMoment B raw34985step1 raw34985step1Labels := by
      have ha : raw34985step1 = (fun i j => raw34985step0 (permutation63 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34985step1 raw34985step0; decide +kernel
      have hl : raw34985step1Labels = raw34985step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34985step0 raw34985step0Labels permutation63 permutation7
    mixedMoment B raw34985step1 raw34985step1Labels = mixedMoment B raw34985step2 raw34985step2Labels := by
      have ha : raw34985step2 = -raw34985step1 := by apply Matrix.ext; change ∀ i j, raw34985step2 i j = -(raw34985step1 i j); unfold raw34985step2 raw34985step1; decide +kernel
      have hl : raw34985step2Labels = raw34985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34985step2 raw34985step2Labels = mixedMoment B raw34985step3 raw34985step3Labels := by
      have ha : raw34985step3 = raw34985step2 := by apply Matrix.ext; unfold raw34985step3 raw34985step2; decide +kernel
      have hl : raw34985step2Labels = labelEmbedding1 ∘ raw34985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34985step2 raw34985step2Labels raw34985step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical34986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34986 raw34986Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw34986 raw34986Labels = mixedMoment B raw34986step0 raw34986step0Labels := by
      have ha : raw34986step0 = (fun i j => raw34986 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34986step0 raw34986; decide +kernel
      have hl : raw34986step0Labels = raw34986Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34986 raw34986Labels permutation572 permutation7
    mixedMoment B raw34986step0 raw34986step0Labels = mixedMoment B raw34986step1 raw34986step1Labels := by
      have ha : raw34986step1 = raw34986step0 := by apply Matrix.ext; unfold raw34986step1 raw34986step0; decide +kernel
      have hl : raw34986step0Labels = labelEmbedding1 ∘ raw34986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34986step0 raw34986step0Labels raw34986step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical34987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34987 raw34987Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw34987 raw34987Labels = mixedMoment B raw34987step0 raw34987step0Labels := by
      have hz : ∀ j, raw34987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34987step0 = (fun i j => raw34987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34987step0 raw34987; decide +kernel
      have hl : raw34987step0Labels = raw34987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34987 raw34987Labels permutation346 hz
    mixedMoment B raw34987step0 raw34987step0Labels = mixedMoment B raw34987step1 raw34987step1Labels := by
      have ha : raw34987step1 = (fun i j => raw34987step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34987step1 raw34987step0; decide +kernel
      have hl : raw34987step1Labels = raw34987step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34987step0 raw34987step0Labels permutation123 permutation7
    mixedMoment B raw34987step1 raw34987step1Labels = mixedMoment B raw34987step2 raw34987step2Labels := by
      have ha : raw34987step2 = raw34987step1 := by apply Matrix.ext; unfold raw34987step2 raw34987step1; decide +kernel
      have hl : raw34987step1Labels = labelEmbedding1 ∘ raw34987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34987step1 raw34987step1Labels raw34987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

theorem canonical34988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34988 raw34988Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw34988 raw34988Labels = mixedMoment B raw34988step0 raw34988step0Labels := by
      have hz : ∀ j, raw34988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34988step0 = (fun i j => raw34988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34988step0 raw34988; decide +kernel
      have hl : raw34988step0Labels = raw34988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34988 raw34988Labels permutation346 hz
    mixedMoment B raw34988step0 raw34988step0Labels = mixedMoment B raw34988step1 raw34988step1Labels := by
      have ha : raw34988step1 = (fun i j => raw34988step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34988step1 raw34988step0; decide +kernel
      have hl : raw34988step1Labels = raw34988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34988step0 raw34988step0Labels permutation123 permutation7
    mixedMoment B raw34988step1 raw34988step1Labels = mixedMoment B raw34988step2 raw34988step2Labels := by
      have ha : raw34988step2 = raw34988step1 := by apply Matrix.ext; unfold raw34988step2 raw34988step1; decide +kernel
      have hl : raw34988step1Labels = labelEmbedding1 ∘ raw34988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34988step1 raw34988step1Labels raw34988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical34989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34989 raw34989Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw34989 raw34989Labels = mixedMoment B raw34989step0 raw34989step0Labels := by
      have hz : ∀ j, raw34989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34989step0 = (fun i j => raw34989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34989step0 raw34989; decide +kernel
      have hl : raw34989step0Labels = raw34989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34989 raw34989Labels permutation346 hz
    mixedMoment B raw34989step0 raw34989step0Labels = mixedMoment B raw34989step1 raw34989step1Labels := by
      have ha : raw34989step1 = (fun i j => raw34989step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34989step1 raw34989step0; decide +kernel
      have hl : raw34989step1Labels = raw34989step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34989step0 raw34989step0Labels permutation44 permutation5
    mixedMoment B raw34989step1 raw34989step1Labels = mixedMoment B raw34989step2 raw34989step2Labels := by
      have ha : raw34989step2 = -raw34989step1 := by apply Matrix.ext; change ∀ i j, raw34989step2 i j = -(raw34989step1 i j); unfold raw34989step2 raw34989step1; decide +kernel
      have hl : raw34989step2Labels = raw34989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34989step2 raw34989step2Labels = mixedMoment B raw34989step3 raw34989step3Labels := by
      have ha : raw34989step3 = raw34989step2 := by apply Matrix.ext; unfold raw34989step3 raw34989step2; decide +kernel
      have hl : raw34989step2Labels = labelEmbedding1 ∘ raw34989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34989step2 raw34989step2Labels raw34989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical34990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34990 raw34990Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw34990 raw34990Labels = mixedMoment B raw34990step0 raw34990step0Labels := by
      have ha : raw34990step0 = (fun i j => raw34990 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34990step0 raw34990; decide +kernel
      have hl : raw34990step0Labels = raw34990Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34990 raw34990Labels permutation166 permutation5
    mixedMoment B raw34990step0 raw34990step0Labels = mixedMoment B raw34990step1 raw34990step1Labels := by
      have ha : raw34990step1 = -raw34990step0 := by apply Matrix.ext; change ∀ i j, raw34990step1 i j = -(raw34990step0 i j); unfold raw34990step1 raw34990step0; decide +kernel
      have hl : raw34990step1Labels = raw34990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34990step1 raw34990step1Labels = mixedMoment B raw34990step2 raw34990step2Labels := by
      have ha : raw34990step2 = raw34990step1 := by apply Matrix.ext; unfold raw34990step2 raw34990step1; decide +kernel
      have hl : raw34990step1Labels = labelEmbedding1 ∘ raw34990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34990step1 raw34990step1Labels raw34990step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

theorem canonical34991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34991 raw34991Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw34991 raw34991Labels = mixedMoment B raw34991step0 raw34991step0Labels := by
      have ha : raw34991step0 = (fun i j => raw34991 (permutation306 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34991step0 raw34991; decide +kernel
      have hl : raw34991step0Labels = raw34991Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34991 raw34991Labels permutation306 permutation7
    mixedMoment B raw34991step0 raw34991step0Labels = mixedMoment B raw34991step1 raw34991step1Labels := by
      have ha : raw34991step1 = -raw34991step0 := by apply Matrix.ext; change ∀ i j, raw34991step1 i j = -(raw34991step0 i j); unfold raw34991step1 raw34991step0; decide +kernel
      have hl : raw34991step1Labels = raw34991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34991step1 raw34991step1Labels = mixedMoment B raw34991step2 raw34991step2Labels := by
      have ha : raw34991step2 = raw34991step1 := by apply Matrix.ext; unfold raw34991step2 raw34991step1; decide +kernel
      have hl : raw34991step1Labels = labelEmbedding1 ∘ raw34991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34991step1 raw34991step1Labels raw34991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical34992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34992 raw34992Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw34992 raw34992Labels = mixedMoment B raw34992step0 raw34992step0Labels := by
      have ha : raw34992step0 = (fun i j => raw34992 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34992step0 raw34992; decide +kernel
      have hl : raw34992step0Labels = raw34992Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34992 raw34992Labels permutation581 permutation7
    mixedMoment B raw34992step0 raw34992step0Labels = mixedMoment B raw34992step1 raw34992step1Labels := by
      have ha : raw34992step1 = raw34992step0 := by apply Matrix.ext; unfold raw34992step1 raw34992step0; decide +kernel
      have hl : raw34992step0Labels = labelEmbedding1 ∘ raw34992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34992step0 raw34992step0Labels raw34992step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

theorem canonical34993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34993 raw34993Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw34993 raw34993Labels = mixedMoment B raw34993step0 raw34993step0Labels := by
      have ha : raw34993step0 = (fun i j => raw34993 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34993step0 raw34993; decide +kernel
      have hl : raw34993step0Labels = raw34993Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34993 raw34993Labels permutation581 permutation7
    mixedMoment B raw34993step0 raw34993step0Labels = mixedMoment B raw34993step1 raw34993step1Labels := by
      have ha : raw34993step1 = raw34993step0 := by apply Matrix.ext; unfold raw34993step1 raw34993step0; decide +kernel
      have hl : raw34993step0Labels = labelEmbedding1 ∘ raw34993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34993step0 raw34993step0Labels raw34993step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

theorem canonical34994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34994 raw34994Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw34994 raw34994Labels = mixedMoment B raw34994step0 raw34994step0Labels := by
      have hz : ∀ j, raw34994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34994step0 = (fun i j => raw34994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34994step0 raw34994; decide +kernel
      have hl : raw34994step0Labels = raw34994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34994 raw34994Labels permutation346 hz
    mixedMoment B raw34994step0 raw34994step0Labels = mixedMoment B raw34994step1 raw34994step1Labels := by
      have ha : raw34994step1 = (fun i j => raw34994step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34994step1 raw34994step0; decide +kernel
      have hl : raw34994step1Labels = raw34994step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34994step0 raw34994step0Labels permutation35 permutation5
    mixedMoment B raw34994step1 raw34994step1Labels = mixedMoment B raw34994step2 raw34994step2Labels := by
      have ha : raw34994step2 = -raw34994step1 := by apply Matrix.ext; change ∀ i j, raw34994step2 i j = -(raw34994step1 i j); unfold raw34994step2 raw34994step1; decide +kernel
      have hl : raw34994step2Labels = raw34994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34994step2 raw34994step2Labels = mixedMoment B raw34994step3 raw34994step3Labels := by
      have ha : raw34994step3 = raw34994step2 := by apply Matrix.ext; unfold raw34994step3 raw34994step2; decide +kernel
      have hl : raw34994step2Labels = labelEmbedding1 ∘ raw34994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34994step2 raw34994step2Labels raw34994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

theorem canonical34995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34995 raw34995Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw34995 raw34995Labels = mixedMoment B raw34995step0 raw34995step0Labels := by
      have hz : ∀ j, raw34995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34995step0 = (fun i j => raw34995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34995step0 raw34995; decide +kernel
      have hl : raw34995step0Labels = raw34995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34995 raw34995Labels permutation346 hz
    mixedMoment B raw34995step0 raw34995step0Labels = mixedMoment B raw34995step1 raw34995step1Labels := by
      have ha : raw34995step1 = (fun i j => raw34995step0 (permutation63 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34995step1 raw34995step0; decide +kernel
      have hl : raw34995step1Labels = raw34995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34995step0 raw34995step0Labels permutation63 permutation7
    mixedMoment B raw34995step1 raw34995step1Labels = mixedMoment B raw34995step2 raw34995step2Labels := by
      have ha : raw34995step2 = -raw34995step1 := by apply Matrix.ext; change ∀ i j, raw34995step2 i j = -(raw34995step1 i j); unfold raw34995step2 raw34995step1; decide +kernel
      have hl : raw34995step2Labels = raw34995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34995step2 raw34995step2Labels = mixedMoment B raw34995step3 raw34995step3Labels := by
      have ha : raw34995step3 = raw34995step2 := by apply Matrix.ext; unfold raw34995step3 raw34995step2; decide +kernel
      have hl : raw34995step2Labels = labelEmbedding1 ∘ raw34995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34995step2 raw34995step2Labels raw34995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

theorem canonical34996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34996 raw34996Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw34996 raw34996Labels = mixedMoment B raw34996step0 raw34996step0Labels := by
      have ha : raw34996step0 = (fun i j => raw34996 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34996step0 raw34996; decide +kernel
      have hl : raw34996step0Labels = raw34996Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34996 raw34996Labels permutation581 permutation7
    mixedMoment B raw34996step0 raw34996step0Labels = mixedMoment B raw34996step1 raw34996step1Labels := by
      have ha : raw34996step1 = raw34996step0 := by apply Matrix.ext; unfold raw34996step1 raw34996step0; decide +kernel
      have hl : raw34996step0Labels = labelEmbedding1 ∘ raw34996step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34996step0 raw34996step0Labels raw34996step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

theorem canonical34997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34997 raw34997Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw34997 raw34997Labels = mixedMoment B raw34997step0 raw34997step0Labels := by
      have hz : ∀ j, raw34997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34997step0 = (fun i j => raw34997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34997step0 raw34997; decide +kernel
      have hl : raw34997step0Labels = raw34997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34997 raw34997Labels permutation346 hz
    mixedMoment B raw34997step0 raw34997step0Labels = mixedMoment B raw34997step1 raw34997step1Labels := by
      have ha : raw34997step1 = (fun i j => raw34997step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34997step1 raw34997step0; decide +kernel
      have hl : raw34997step1Labels = raw34997step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34997step0 raw34997step0Labels permutation123 permutation7
    mixedMoment B raw34997step1 raw34997step1Labels = mixedMoment B raw34997step2 raw34997step2Labels := by
      have ha : raw34997step2 = raw34997step1 := by apply Matrix.ext; unfold raw34997step2 raw34997step1; decide +kernel
      have hl : raw34997step1Labels = labelEmbedding1 ∘ raw34997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34997step1 raw34997step1Labels raw34997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

theorem canonical34998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34998 raw34998Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw34998 raw34998Labels = mixedMoment B raw34998step0 raw34998step0Labels := by
      have hz : ∀ j, raw34998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34998step0 = (fun i j => raw34998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34998step0 raw34998; decide +kernel
      have hl : raw34998step0Labels = raw34998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34998 raw34998Labels permutation346 hz
    mixedMoment B raw34998step0 raw34998step0Labels = mixedMoment B raw34998step1 raw34998step1Labels := by
      have ha : raw34998step1 = (fun i j => raw34998step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34998step1 raw34998step0; decide +kernel
      have hl : raw34998step1Labels = raw34998step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34998step0 raw34998step0Labels permutation33 permutation5
    mixedMoment B raw34998step1 raw34998step1Labels = mixedMoment B raw34998step2 raw34998step2Labels := by
      have ha : raw34998step2 = -raw34998step1 := by apply Matrix.ext; change ∀ i j, raw34998step2 i j = -(raw34998step1 i j); unfold raw34998step2 raw34998step1; decide +kernel
      have hl : raw34998step2Labels = raw34998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34998step2 raw34998step2Labels = mixedMoment B raw34998step3 raw34998step3Labels := by
      have ha : raw34998step3 = raw34998step2 := by apply Matrix.ext; unfold raw34998step3 raw34998step2; decide +kernel
      have hl : raw34998step2Labels = labelEmbedding1 ∘ raw34998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34998step2 raw34998step2Labels raw34998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical34999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34999 raw34999Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw34999 raw34999Labels = mixedMoment B raw34999step0 raw34999step0Labels := by
      have hz : ∀ j, raw34999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34999step0 = (fun i j => raw34999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34999step0 raw34999; decide +kernel
      have hl : raw34999step0Labels = raw34999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34999 raw34999Labels permutation346 hz
    mixedMoment B raw34999step0 raw34999step0Labels = mixedMoment B raw34999step1 raw34999step1Labels := by
      have ha : raw34999step1 = (fun i j => raw34999step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34999step1 raw34999step0; decide +kernel
      have hl : raw34999step1Labels = raw34999step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34999step0 raw34999step0Labels permutation123 permutation7
    mixedMoment B raw34999step1 raw34999step1Labels = mixedMoment B raw34999step2 raw34999step2Labels := by
      have ha : raw34999step2 = raw34999step1 := by apply Matrix.ext; unfold raw34999step2 raw34999step1; decide +kernel
      have hl : raw34999step1Labels = labelEmbedding1 ∘ raw34999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34999step1 raw34999step1Labels raw34999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

theorem canonical35000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35000 raw35000Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw35000 raw35000Labels = mixedMoment B raw35000step0 raw35000step0Labels := by
      have ha : raw35000step0 = (fun i j => raw35000 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35000step0 raw35000; decide +kernel
      have hl : raw35000step0Labels = raw35000Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35000 raw35000Labels permutation581 permutation7
    mixedMoment B raw35000step0 raw35000step0Labels = mixedMoment B raw35000step1 raw35000step1Labels := by
      have ha : raw35000step1 = raw35000step0 := by apply Matrix.ext; unfold raw35000step1 raw35000step0; decide +kernel
      have hl : raw35000step0Labels = labelEmbedding1 ∘ raw35000step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35000step0 raw35000step0Labels raw35000step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical35001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35001 raw35001Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw35001 raw35001Labels = mixedMoment B raw35001step0 raw35001step0Labels := by
      have hz : ∀ j, raw35001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35001step0 = (fun i j => raw35001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35001step0 raw35001; decide +kernel
      have hl : raw35001step0Labels = raw35001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35001 raw35001Labels permutation346 hz
    mixedMoment B raw35001step0 raw35001step0Labels = mixedMoment B raw35001step1 raw35001step1Labels := by
      have ha : raw35001step1 = (fun i j => raw35001step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35001step1 raw35001step0; decide +kernel
      have hl : raw35001step1Labels = raw35001step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35001step0 raw35001step0Labels permutation123 permutation7
    mixedMoment B raw35001step1 raw35001step1Labels = mixedMoment B raw35001step2 raw35001step2Labels := by
      have ha : raw35001step2 = raw35001step1 := by apply Matrix.ext; unfold raw35001step2 raw35001step1; decide +kernel
      have hl : raw35001step1Labels = labelEmbedding1 ∘ raw35001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35001step1 raw35001step1Labels raw35001step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

theorem canonical35002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35002 raw35002Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw35002 raw35002Labels = mixedMoment B raw35002step0 raw35002step0Labels := by
      have hz : ∀ j, raw35002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35002step0 = (fun i j => raw35002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35002step0 raw35002; decide +kernel
      have hl : raw35002step0Labels = raw35002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35002 raw35002Labels permutation346 hz
    mixedMoment B raw35002step0 raw35002step0Labels = mixedMoment B raw35002step1 raw35002step1Labels := by
      have ha : raw35002step1 = (fun i j => raw35002step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35002step1 raw35002step0; decide +kernel
      have hl : raw35002step1Labels = raw35002step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35002step0 raw35002step0Labels permutation123 permutation7
    mixedMoment B raw35002step1 raw35002step1Labels = mixedMoment B raw35002step2 raw35002step2Labels := by
      have ha : raw35002step2 = raw35002step1 := by apply Matrix.ext; unfold raw35002step2 raw35002step1; decide +kernel
      have hl : raw35002step1Labels = labelEmbedding1 ∘ raw35002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35002step1 raw35002step1Labels raw35002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical35003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35003 raw35003Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw35003 raw35003Labels = mixedMoment B raw35003step0 raw35003step0Labels := by
      have hz : ∀ j, raw35003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35003step0 = (fun i j => raw35003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35003step0 raw35003; decide +kernel
      have hl : raw35003step0Labels = raw35003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35003 raw35003Labels permutation346 hz
    mixedMoment B raw35003step0 raw35003step0Labels = mixedMoment B raw35003step1 raw35003step1Labels := by
      have ha : raw35003step1 = (fun i j => raw35003step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35003step1 raw35003step0; decide +kernel
      have hl : raw35003step1Labels = raw35003step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35003step0 raw35003step0Labels permutation34 permutation5
    mixedMoment B raw35003step1 raw35003step1Labels = mixedMoment B raw35003step2 raw35003step2Labels := by
      have ha : raw35003step2 = -raw35003step1 := by apply Matrix.ext; change ∀ i j, raw35003step2 i j = -(raw35003step1 i j); unfold raw35003step2 raw35003step1; decide +kernel
      have hl : raw35003step2Labels = raw35003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35003step2 raw35003step2Labels = mixedMoment B raw35003step3 raw35003step3Labels := by
      have ha : raw35003step3 = raw35003step2 := by apply Matrix.ext; unfold raw35003step3 raw35003step2; decide +kernel
      have hl : raw35003step2Labels = labelEmbedding1 ∘ raw35003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35003step2 raw35003step2Labels raw35003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

theorem canonical35004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35004 raw35004Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw35004 raw35004Labels = mixedMoment B raw35004step0 raw35004step0Labels := by
      have hz : ∀ j, raw35004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35004step0 = (fun i j => raw35004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35004step0 raw35004; decide +kernel
      have hl : raw35004step0Labels = raw35004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35004 raw35004Labels permutation346 hz
    mixedMoment B raw35004step0 raw35004step0Labels = mixedMoment B raw35004step1 raw35004step1Labels := by
      have ha : raw35004step1 = (fun i j => raw35004step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35004step1 raw35004step0; decide +kernel
      have hl : raw35004step1Labels = raw35004step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35004step0 raw35004step0Labels permutation145 permutation5
    mixedMoment B raw35004step1 raw35004step1Labels = mixedMoment B raw35004step2 raw35004step2Labels := by
      have ha : raw35004step2 = raw35004step1 := by apply Matrix.ext; unfold raw35004step2 raw35004step1; decide +kernel
      have hl : raw35004step1Labels = labelEmbedding1 ∘ raw35004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35004step1 raw35004step1Labels raw35004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3512 node3512Labels := by rfl

theorem canonical35005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35005 raw35005Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw35005 raw35005Labels = mixedMoment B raw35005step0 raw35005step0Labels := by
      have ha : raw35005step0 = (fun i j => raw35005 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35005step0 raw35005; decide +kernel
      have hl : raw35005step0Labels = raw35005Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35005 raw35005Labels permutation662 permutation5
    mixedMoment B raw35005step0 raw35005step0Labels = mixedMoment B raw35005step1 raw35005step1Labels := by
      have ha : raw35005step1 = raw35005step0 := by apply Matrix.ext; unfold raw35005step1 raw35005step0; decide +kernel
      have hl : raw35005step0Labels = labelEmbedding1 ∘ raw35005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35005step0 raw35005step0Labels raw35005step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

theorem canonical35006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35006 raw35006Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw35006 raw35006Labels = mixedMoment B raw35006step0 raw35006step0Labels := by
      have hz : ∀ j, raw35006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35006step0 = (fun i j => raw35006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35006step0 raw35006; decide +kernel
      have hl : raw35006step0Labels = raw35006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35006 raw35006Labels permutation346 hz
    mixedMoment B raw35006step0 raw35006step0Labels = mixedMoment B raw35006step1 raw35006step1Labels := by
      have ha : raw35006step1 = (fun i j => raw35006step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35006step1 raw35006step0; decide +kernel
      have hl : raw35006step1Labels = raw35006step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35006step0 raw35006step0Labels permutation151 permutation5
    mixedMoment B raw35006step1 raw35006step1Labels = mixedMoment B raw35006step2 raw35006step2Labels := by
      have ha : raw35006step2 = raw35006step1 := by apply Matrix.ext; unfold raw35006step2 raw35006step1; decide +kernel
      have hl : raw35006step1Labels = labelEmbedding1 ∘ raw35006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35006step1 raw35006step1Labels raw35006step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

theorem canonical35007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35007 raw35007Labels = mixedMoment B node2348 node2348Labels := by
  calc
    mixedMoment B raw35007 raw35007Labels = mixedMoment B raw35007step0 raw35007step0Labels := by
      have ha : raw35007step0 = (fun i j => raw35007 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35007step0 raw35007; decide +kernel
      have hl : raw35007step0Labels = raw35007Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35007 raw35007Labels permutation272 permutation2
    _ = mixedMoment B node2348 node2348Labels := by rfl

theorem canonical35008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35008 raw35008Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw35008 raw35008Labels = mixedMoment B raw35008step0 raw35008step0Labels := by
      have ha : raw35008step0 = (fun i j => raw35008 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35008step0 raw35008; decide +kernel
      have hl : raw35008step0Labels = raw35008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35008 raw35008Labels permutation583 permutation2
    mixedMoment B raw35008step0 raw35008step0Labels = mixedMoment B raw35008step1 raw35008step1Labels := by
      have ha : raw35008step1 = -raw35008step0 := by apply Matrix.ext; change ∀ i j, raw35008step1 i j = -(raw35008step0 i j); unfold raw35008step1 raw35008step0; decide +kernel
      have hl : raw35008step1Labels = raw35008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3671 node3671Labels := by rfl

theorem canonical35009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35009 raw35009Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw35009 raw35009Labels = mixedMoment B raw35009step0 raw35009step0Labels := by
      have ha : raw35009step0 = (fun i j => raw35009 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35009step0 raw35009; decide +kernel
      have hl : raw35009step0Labels = raw35009Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35009 raw35009Labels permutation272 permutation2
    _ = mixedMoment B node3719 node3719Labels := by rfl

theorem canonical35010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35010 raw35010Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw35010 raw35010Labels = mixedMoment B raw35010step0 raw35010step0Labels := by
      have ha : raw35010step0 = (fun i j => raw35010 (permutation585 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35010step0 raw35010; decide +kernel
      have hl : raw35010step0Labels = raw35010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35010 raw35010Labels permutation585 permutation2
    mixedMoment B raw35010step0 raw35010step0Labels = mixedMoment B raw35010step1 raw35010step1Labels := by
      have ha : raw35010step1 = -raw35010step0 := by apply Matrix.ext; change ∀ i j, raw35010step1 i j = -(raw35010step0 i j); unfold raw35010step1 raw35010step0; decide +kernel
      have hl : raw35010step1Labels = raw35010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical35011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35011 raw35011Labels = mixedMoment B node3674 node3674Labels := by
  calc
    mixedMoment B raw35011 raw35011Labels = mixedMoment B raw35011step0 raw35011step0Labels := by
      have ha : raw35011step0 = (fun i j => raw35011 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35011step0 raw35011; decide +kernel
      have hl : raw35011step0Labels = raw35011Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35011 raw35011Labels permutation588 permutation2
    mixedMoment B raw35011step0 raw35011step0Labels = mixedMoment B raw35011step1 raw35011step1Labels := by
      have ha : raw35011step1 = -raw35011step0 := by apply Matrix.ext; change ∀ i j, raw35011step1 i j = -(raw35011step0 i j); unfold raw35011step1 raw35011step0; decide +kernel
      have hl : raw35011step1Labels = raw35011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3674 node3674Labels := by rfl

theorem canonical35012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35012 raw35012Labels = mixedMoment B node2321 node2321Labels := by
  calc
    mixedMoment B raw35012 raw35012Labels = mixedMoment B raw35012step0 raw35012step0Labels := by
      have ha : raw35012step0 = (fun i j => raw35012 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35012step0 raw35012; decide +kernel
      have hl : raw35012step0Labels = raw35012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35012 raw35012Labels permutation588 permutation2
    mixedMoment B raw35012step0 raw35012step0Labels = mixedMoment B raw35012step1 raw35012step1Labels := by
      have ha : raw35012step1 = -raw35012step0 := by apply Matrix.ext; change ∀ i j, raw35012step1 i j = -(raw35012step0 i j); unfold raw35012step1 raw35012step0; decide +kernel
      have hl : raw35012step1Labels = raw35012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2321 node2321Labels := by rfl

theorem canonical35013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35013 raw35013Labels = mixedMoment B node2798 node2798Labels := by
  calc
    mixedMoment B raw35013 raw35013Labels = mixedMoment B raw35013step0 raw35013step0Labels := by
      have ha : raw35013step0 = (fun i j => raw35013 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35013step0 raw35013; decide +kernel
      have hl : raw35013step0Labels = raw35013Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35013 raw35013Labels permutation687 permutation2
    mixedMoment B raw35013step0 raw35013step0Labels = mixedMoment B raw35013step1 raw35013step1Labels := by
      have ha : raw35013step1 = -raw35013step0 := by apply Matrix.ext; change ∀ i j, raw35013step1 i j = -(raw35013step0 i j); unfold raw35013step1 raw35013step0; decide +kernel
      have hl : raw35013step1Labels = raw35013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2798 node2798Labels := by rfl

theorem canonical35014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35014 raw35014Labels = mixedMoment B node2356 node2356Labels := by
  calc
    mixedMoment B raw35014 raw35014Labels = mixedMoment B raw35014step0 raw35014step0Labels := by
      have hz : ∀ j, raw35014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35014step0 = (fun i j => raw35014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35014step0 raw35014; decide +kernel
      have hl : raw35014step0Labels = raw35014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35014 raw35014Labels permutation346 hz
    mixedMoment B raw35014step0 raw35014step0Labels = mixedMoment B raw35014step1 raw35014step1Labels := by
      have ha : raw35014step1 = (fun i j => raw35014step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35014step1 raw35014step0; decide +kernel
      have hl : raw35014step1Labels = raw35014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35014step0 raw35014step0Labels permutation57 permutation2
    _ = mixedMoment B node2356 node2356Labels := by rfl

theorem canonical35015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35015 raw35015Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw35015 raw35015Labels = mixedMoment B raw35015step0 raw35015step0Labels := by
      have hz : ∀ j, raw35015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35015step0 = (fun i j => raw35015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35015step0 raw35015; decide +kernel
      have hl : raw35015step0Labels = raw35015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35015 raw35015Labels permutation346 hz
    mixedMoment B raw35015step0 raw35015step0Labels = mixedMoment B raw35015step1 raw35015step1Labels := by
      have ha : raw35015step1 = (fun i j => raw35015step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35015step1 raw35015step0; decide +kernel
      have hl : raw35015step1Labels = raw35015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35015step0 raw35015step0Labels permutation57 permutation2
    _ = mixedMoment B node3732 node3732Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35115 raw35115Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw35115 raw35115Labels = mixedMoment B raw35115step0 raw35115step0Labels := by
      have hz : ∀ j, raw35115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35115step0 = (fun i j => raw35115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35115step0 raw35115; decide +kernel
      have hl : raw35115step0Labels = raw35115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35115 raw35115Labels permutation434 hz
    mixedMoment B raw35115step0 raw35115step0Labels = mixedMoment B raw35115step1 raw35115step1Labels := by
      have hz : ∀ j, raw35115step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35115step1 = (fun i j => raw35115step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35115step1 raw35115step0; decide +kernel
      have hl : raw35115step1Labels = raw35115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35115step0 raw35115step0Labels permutation80 hz
    mixedMoment B raw35115step1 raw35115step1Labels = mixedMoment B raw35115step2 raw35115step2Labels := by
      have ha : raw35115step2 = (fun i j => raw35115step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35115step2 raw35115step1; decide +kernel
      have hl : raw35115step2Labels = raw35115step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35115step1 raw35115step1Labels permutation15 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical35116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35116 raw35116Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw35116 raw35116Labels = mixedMoment B raw35116step0 raw35116step0Labels := by
      have hz : ∀ j, raw35116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35116step0 = (fun i j => raw35116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35116step0 raw35116; decide +kernel
      have hl : raw35116step0Labels = raw35116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35116 raw35116Labels permutation434 hz
    mixedMoment B raw35116step0 raw35116step0Labels = mixedMoment B raw35116step1 raw35116step1Labels := by
      have ha : raw35116step1 = (fun i j => raw35116step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35116step1 raw35116step0; decide +kernel
      have hl : raw35116step1Labels = raw35116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35116step0 raw35116step0Labels permutation57 permutation7
    mixedMoment B raw35116step1 raw35116step1Labels = mixedMoment B raw35116step2 raw35116step2Labels := by
      have ha : raw35116step2 = -raw35116step1 := by apply Matrix.ext; change ∀ i j, raw35116step2 i j = -(raw35116step1 i j); unfold raw35116step2 raw35116step1; decide +kernel
      have hl : raw35116step2Labels = raw35116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35116step2 raw35116step2Labels = mixedMoment B raw35116step3 raw35116step3Labels := by
      have ha : raw35116step3 = raw35116step2 := by apply Matrix.ext; unfold raw35116step3 raw35116step2; decide +kernel
      have hl : raw35116step2Labels = labelEmbedding10 ∘ raw35116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35116step2 raw35116step2Labels raw35116step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical35117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35117 raw35117Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw35117 raw35117Labels = mixedMoment B raw35117step0 raw35117step0Labels := by
      have hz : ∀ j, raw35117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35117step0 = (fun i j => raw35117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35117step0 raw35117; decide +kernel
      have hl : raw35117step0Labels = raw35117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35117 raw35117Labels permutation346 hz
    mixedMoment B raw35117step0 raw35117step0Labels = mixedMoment B raw35117step1 raw35117step1Labels := by
      have ha : raw35117step1 = (fun i j => raw35117step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35117step1 raw35117step0; decide +kernel
      have hl : raw35117step1Labels = raw35117step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35117step0 raw35117step0Labels permutation57 permutation7
    mixedMoment B raw35117step1 raw35117step1Labels = mixedMoment B raw35117step2 raw35117step2Labels := by
      have ha : raw35117step2 = -raw35117step1 := by apply Matrix.ext; change ∀ i j, raw35117step2 i j = -(raw35117step1 i j); unfold raw35117step2 raw35117step1; decide +kernel
      have hl : raw35117step2Labels = raw35117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35117step2 raw35117step2Labels = mixedMoment B raw35117step3 raw35117step3Labels := by
      have ha : raw35117step3 = raw35117step2 := by apply Matrix.ext; unfold raw35117step3 raw35117step2; decide +kernel
      have hl : raw35117step2Labels = labelEmbedding10 ∘ raw35117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35117step2 raw35117step2Labels raw35117step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical35118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35118 raw35118Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw35118 raw35118Labels = mixedMoment B raw35118step0 raw35118step0Labels := by
      have hz : ∀ j, raw35118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35118step0 = (fun i j => raw35118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35118step0 raw35118; decide +kernel
      have hl : raw35118step0Labels = raw35118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35118 raw35118Labels permutation434 hz
    mixedMoment B raw35118step0 raw35118step0Labels = mixedMoment B raw35118step1 raw35118step1Labels := by
      have hz : ∀ j, raw35118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35118step1 = (fun i j => raw35118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35118step1 raw35118step0; decide +kernel
      have hl : raw35118step1Labels = raw35118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35118step0 raw35118step0Labels permutation80 hz
    mixedMoment B raw35118step1 raw35118step1Labels = mixedMoment B raw35118step2 raw35118step2Labels := by
      have ha : raw35118step2 = (fun i j => raw35118step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35118step2 raw35118step1; decide +kernel
      have hl : raw35118step2Labels = raw35118step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35118step1 raw35118step1Labels permutation15 permutation7
    mixedMoment B raw35118step2 raw35118step2Labels = mixedMoment B raw35118step3 raw35118step3Labels := by
      have ha : raw35118step3 = -raw35118step2 := by apply Matrix.ext; change ∀ i j, raw35118step3 i j = -(raw35118step2 i j); unfold raw35118step3 raw35118step2; decide +kernel
      have hl : raw35118step3Labels = raw35118step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35118step3 raw35118step3Labels = mixedMoment B raw35118step4 raw35118step4Labels := by
      have ha : raw35118step4 = raw35118step3 := by apply Matrix.ext; unfold raw35118step4 raw35118step3; decide +kernel
      have hl : raw35118step3Labels = labelEmbedding10 ∘ raw35118step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35118step3 raw35118step3Labels raw35118step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical35119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35119 raw35119Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw35119 raw35119Labels = mixedMoment B raw35119step0 raw35119step0Labels := by
      have hz : ∀ j, raw35119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35119step0 = (fun i j => raw35119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35119step0 raw35119; decide +kernel
      have hl : raw35119step0Labels = raw35119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35119 raw35119Labels permutation434 hz
    mixedMoment B raw35119step0 raw35119step0Labels = mixedMoment B raw35119step1 raw35119step1Labels := by
      have hz : ∀ j, raw35119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35119step1 = (fun i j => raw35119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35119step1 raw35119step0; decide +kernel
      have hl : raw35119step1Labels = raw35119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35119step0 raw35119step0Labels permutation80 hz
    mixedMoment B raw35119step1 raw35119step1Labels = mixedMoment B raw35119step2 raw35119step2Labels := by
      have ha : raw35119step2 = (fun i j => raw35119step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35119step2 raw35119step1; decide +kernel
      have hl : raw35119step2Labels = raw35119step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35119step1 raw35119step1Labels permutation15 permutation7
    mixedMoment B raw35119step2 raw35119step2Labels = mixedMoment B raw35119step3 raw35119step3Labels := by
      have ha : raw35119step3 = -raw35119step2 := by apply Matrix.ext; change ∀ i j, raw35119step3 i j = -(raw35119step2 i j); unfold raw35119step3 raw35119step2; decide +kernel
      have hl : raw35119step3Labels = raw35119step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35119step3 raw35119step3Labels = mixedMoment B raw35119step4 raw35119step4Labels := by
      have ha : raw35119step4 = raw35119step3 := by apply Matrix.ext; unfold raw35119step4 raw35119step3; decide +kernel
      have hl : raw35119step3Labels = labelEmbedding10 ∘ raw35119step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35119step3 raw35119step3Labels raw35119step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical35120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35120 raw35120Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw35120 raw35120Labels = mixedMoment B raw35120step0 raw35120step0Labels := by
      have hz : ∀ j, raw35120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35120step0 = (fun i j => raw35120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35120step0 raw35120; decide +kernel
      have hl : raw35120step0Labels = raw35120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35120 raw35120Labels permutation434 hz
    mixedMoment B raw35120step0 raw35120step0Labels = mixedMoment B raw35120step1 raw35120step1Labels := by
      have hz : ∀ j, raw35120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35120step1 = (fun i j => raw35120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35120step1 raw35120step0; decide +kernel
      have hl : raw35120step1Labels = raw35120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35120step0 raw35120step0Labels permutation80 hz
    mixedMoment B raw35120step1 raw35120step1Labels = mixedMoment B raw35120step2 raw35120step2Labels := by
      have ha : raw35120step2 = (fun i j => raw35120step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35120step2 raw35120step1; decide +kernel
      have hl : raw35120step2Labels = raw35120step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35120step1 raw35120step1Labels permutation8 permutation3
    mixedMoment B raw35120step2 raw35120step2Labels = mixedMoment B raw35120step3 raw35120step3Labels := by
      have ha : raw35120step3 = raw35120step2 := by apply Matrix.ext; unfold raw35120step3 raw35120step2; decide +kernel
      have hl : raw35120step2Labels = labelEmbedding6 ∘ raw35120step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35120step2 raw35120step2Labels raw35120step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

theorem canonical35121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35121 raw35121Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw35121 raw35121Labels = mixedMoment B raw35121step0 raw35121step0Labels := by
      have hz : ∀ j, raw35121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35121step0 = (fun i j => raw35121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35121step0 raw35121; decide +kernel
      have hl : raw35121step0Labels = raw35121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35121 raw35121Labels permutation434 hz
    mixedMoment B raw35121step0 raw35121step0Labels = mixedMoment B raw35121step1 raw35121step1Labels := by
      have ha : raw35121step1 = (fun i j => raw35121step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35121step1 raw35121step0; decide +kernel
      have hl : raw35121step1Labels = raw35121step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35121step0 raw35121step0Labels permutation63 permutation6
    mixedMoment B raw35121step1 raw35121step1Labels = mixedMoment B raw35121step2 raw35121step2Labels := by
      have ha : raw35121step2 = -raw35121step1 := by apply Matrix.ext; change ∀ i j, raw35121step2 i j = -(raw35121step1 i j); unfold raw35121step2 raw35121step1; decide +kernel
      have hl : raw35121step2Labels = raw35121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35121step2 raw35121step2Labels = mixedMoment B raw35121step3 raw35121step3Labels := by
      have ha : raw35121step3 = raw35121step2 := by apply Matrix.ext; unfold raw35121step3 raw35121step2; decide +kernel
      have hl : raw35121step2Labels = labelEmbedding9 ∘ raw35121step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35121step2 raw35121step2Labels raw35121step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

theorem canonical35122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35122 raw35122Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw35122 raw35122Labels = mixedMoment B raw35122step0 raw35122step0Labels := by
      have hz : ∀ j, raw35122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35122step0 = (fun i j => raw35122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35122step0 raw35122; decide +kernel
      have hl : raw35122step0Labels = raw35122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35122 raw35122Labels permutation346 hz
    mixedMoment B raw35122step0 raw35122step0Labels = mixedMoment B raw35122step1 raw35122step1Labels := by
      have ha : raw35122step1 = (fun i j => raw35122step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35122step1 raw35122step0; decide +kernel
      have hl : raw35122step1Labels = raw35122step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35122step0 raw35122step0Labels permutation63 permutation6
    mixedMoment B raw35122step1 raw35122step1Labels = mixedMoment B raw35122step2 raw35122step2Labels := by
      have ha : raw35122step2 = -raw35122step1 := by apply Matrix.ext; change ∀ i j, raw35122step2 i j = -(raw35122step1 i j); unfold raw35122step2 raw35122step1; decide +kernel
      have hl : raw35122step2Labels = raw35122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35122step2 raw35122step2Labels = mixedMoment B raw35122step3 raw35122step3Labels := by
      have ha : raw35122step3 = raw35122step2 := by apply Matrix.ext; unfold raw35122step3 raw35122step2; decide +kernel
      have hl : raw35122step2Labels = labelEmbedding9 ∘ raw35122step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35122step2 raw35122step2Labels raw35122step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

theorem canonical35123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35123 raw35123Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw35123 raw35123Labels = mixedMoment B raw35123step0 raw35123step0Labels := by
      have hz : ∀ j, raw35123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35123step0 = (fun i j => raw35123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35123step0 raw35123; decide +kernel
      have hl : raw35123step0Labels = raw35123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35123 raw35123Labels permutation434 hz
    mixedMoment B raw35123step0 raw35123step0Labels = mixedMoment B raw35123step1 raw35123step1Labels := by
      have hz : ∀ j, raw35123step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35123step1 = (fun i j => raw35123step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35123step1 raw35123step0; decide +kernel
      have hl : raw35123step1Labels = raw35123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35123step0 raw35123step0Labels permutation80 hz
    mixedMoment B raw35123step1 raw35123step1Labels = mixedMoment B raw35123step2 raw35123step2Labels := by
      have ha : raw35123step2 = (fun i j => raw35123step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35123step2 raw35123step1; decide +kernel
      have hl : raw35123step2Labels = raw35123step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35123step1 raw35123step1Labels permutation15 permutation6
    mixedMoment B raw35123step2 raw35123step2Labels = mixedMoment B raw35123step3 raw35123step3Labels := by
      have ha : raw35123step3 = -raw35123step2 := by apply Matrix.ext; change ∀ i j, raw35123step3 i j = -(raw35123step2 i j); unfold raw35123step3 raw35123step2; decide +kernel
      have hl : raw35123step3Labels = raw35123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35123step3 raw35123step3Labels = mixedMoment B raw35123step4 raw35123step4Labels := by
      have ha : raw35123step4 = raw35123step3 := by apply Matrix.ext; unfold raw35123step4 raw35123step3; decide +kernel
      have hl : raw35123step3Labels = labelEmbedding9 ∘ raw35123step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35123step3 raw35123step3Labels raw35123step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical35124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35124 raw35124Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw35124 raw35124Labels = mixedMoment B raw35124step0 raw35124step0Labels := by
      have hz : ∀ j, raw35124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35124step0 = (fun i j => raw35124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35124step0 raw35124; decide +kernel
      have hl : raw35124step0Labels = raw35124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35124 raw35124Labels permutation434 hz
    mixedMoment B raw35124step0 raw35124step0Labels = mixedMoment B raw35124step1 raw35124step1Labels := by
      have hz : ∀ j, raw35124step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35124step1 = (fun i j => raw35124step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35124step1 raw35124step0; decide +kernel
      have hl : raw35124step1Labels = raw35124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35124step0 raw35124step0Labels permutation80 hz
    mixedMoment B raw35124step1 raw35124step1Labels = mixedMoment B raw35124step2 raw35124step2Labels := by
      have ha : raw35124step2 = (fun i j => raw35124step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35124step2 raw35124step1; decide +kernel
      have hl : raw35124step2Labels = raw35124step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35124step1 raw35124step1Labels permutation15 permutation6
    mixedMoment B raw35124step2 raw35124step2Labels = mixedMoment B raw35124step3 raw35124step3Labels := by
      have ha : raw35124step3 = -raw35124step2 := by apply Matrix.ext; change ∀ i j, raw35124step3 i j = -(raw35124step2 i j); unfold raw35124step3 raw35124step2; decide +kernel
      have hl : raw35124step3Labels = raw35124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35124step3 raw35124step3Labels = mixedMoment B raw35124step4 raw35124step4Labels := by
      have ha : raw35124step4 = raw35124step3 := by apply Matrix.ext; unfold raw35124step4 raw35124step3; decide +kernel
      have hl : raw35124step3Labels = labelEmbedding9 ∘ raw35124step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35124step3 raw35124step3Labels raw35124step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical35125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35125 raw35125Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw35125 raw35125Labels = mixedMoment B raw35125step0 raw35125step0Labels := by
      have hz : ∀ j, raw35125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35125step0 = (fun i j => raw35125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35125step0 raw35125; decide +kernel
      have hl : raw35125step0Labels = raw35125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35125 raw35125Labels permutation434 hz
    mixedMoment B raw35125step0 raw35125step0Labels = mixedMoment B raw35125step1 raw35125step1Labels := by
      have ha : raw35125step1 = (fun i j => raw35125step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35125step1 raw35125step0; decide +kernel
      have hl : raw35125step1Labels = raw35125step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35125step0 raw35125step0Labels permutation32 permutation3
    mixedMoment B raw35125step1 raw35125step1Labels = mixedMoment B raw35125step2 raw35125step2Labels := by
      have ha : raw35125step2 = raw35125step1 := by apply Matrix.ext; unfold raw35125step2 raw35125step1; decide +kernel
      have hl : raw35125step1Labels = labelEmbedding6 ∘ raw35125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35125step1 raw35125step1Labels raw35125step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4703 node4703Labels := by rfl

theorem canonical35126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35126 raw35126Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw35126 raw35126Labels = mixedMoment B raw35126step0 raw35126step0Labels := by
      have hz : ∀ j, raw35126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35126step0 = (fun i j => raw35126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35126step0 raw35126; decide +kernel
      have hl : raw35126step0Labels = raw35126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35126 raw35126Labels permutation434 hz
    mixedMoment B raw35126step0 raw35126step0Labels = mixedMoment B raw35126step1 raw35126step1Labels := by
      have ha : raw35126step1 = (fun i j => raw35126step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35126step1 raw35126step0; decide +kernel
      have hl : raw35126step1Labels = raw35126step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35126step0 raw35126step0Labels permutation57 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical35127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35127 raw35127Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw35127 raw35127Labels = mixedMoment B raw35127step0 raw35127step0Labels := by
      have ha : raw35127step0 = (fun i j => raw35127 (permutation272 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35127step0 raw35127; decide +kernel
      have hl : raw35127step0Labels = raw35127Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35127 raw35127Labels permutation272 permutation7
    mixedMoment B raw35127step0 raw35127step0Labels = mixedMoment B raw35127step1 raw35127step1Labels := by
      have ha : raw35127step1 = -raw35127step0 := by apply Matrix.ext; change ∀ i j, raw35127step1 i j = -(raw35127step0 i j); unfold raw35127step1 raw35127step0; decide +kernel
      have hl : raw35127step1Labels = raw35127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35127step1 raw35127step1Labels = mixedMoment B raw35127step2 raw35127step2Labels := by
      have ha : raw35127step2 = raw35127step1 := by apply Matrix.ext; unfold raw35127step2 raw35127step1; decide +kernel
      have hl : raw35127step1Labels = labelEmbedding10 ∘ raw35127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35127step1 raw35127step1Labels raw35127step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

theorem canonical35128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35128 raw35128Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw35128 raw35128Labels = mixedMoment B raw35128step0 raw35128step0Labels := by
      have hz : ∀ j, raw35128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35128step0 = (fun i j => raw35128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35128step0 raw35128; decide +kernel
      have hl : raw35128step0Labels = raw35128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35128 raw35128Labels permutation434 hz
    mixedMoment B raw35128step0 raw35128step0Labels = mixedMoment B raw35128step1 raw35128step1Labels := by
      have ha : raw35128step1 = (fun i j => raw35128step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35128step1 raw35128step0; decide +kernel
      have hl : raw35128step1Labels = raw35128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35128step0 raw35128step0Labels permutation57 permutation7
    mixedMoment B raw35128step1 raw35128step1Labels = mixedMoment B raw35128step2 raw35128step2Labels := by
      have ha : raw35128step2 = -raw35128step1 := by apply Matrix.ext; change ∀ i j, raw35128step2 i j = -(raw35128step1 i j); unfold raw35128step2 raw35128step1; decide +kernel
      have hl : raw35128step2Labels = raw35128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35128step2 raw35128step2Labels = mixedMoment B raw35128step3 raw35128step3Labels := by
      have ha : raw35128step3 = raw35128step2 := by apply Matrix.ext; unfold raw35128step3 raw35128step2; decide +kernel
      have hl : raw35128step2Labels = labelEmbedding10 ∘ raw35128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35128step2 raw35128step2Labels raw35128step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

theorem canonical35129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35129 raw35129Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35129 raw35129Labels = mixedMoment B raw35129step0 raw35129step0Labels := by
      have hz : ∀ j, raw35129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35129step0 = (fun i j => raw35129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35129step0 raw35129; decide +kernel
      have hl : raw35129step0Labels = raw35129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35129 raw35129Labels permutation434 hz
    mixedMoment B raw35129step0 raw35129step0Labels = mixedMoment B raw35129step1 raw35129step1Labels := by
      have ha : raw35129step1 = (fun i j => raw35129step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35129step1 raw35129step0; decide +kernel
      have hl : raw35129step1Labels = raw35129step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35129step0 raw35129step0Labels permutation57 permutation7
    mixedMoment B raw35129step1 raw35129step1Labels = mixedMoment B raw35129step2 raw35129step2Labels := by
      have ha : raw35129step2 = -raw35129step1 := by apply Matrix.ext; change ∀ i j, raw35129step2 i j = -(raw35129step1 i j); unfold raw35129step2 raw35129step1; decide +kernel
      have hl : raw35129step2Labels = raw35129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35129step2 raw35129step2Labels = mixedMoment B raw35129step3 raw35129step3Labels := by
      have ha : raw35129step3 = raw35129step2 := by apply Matrix.ext; unfold raw35129step3 raw35129step2; decide +kernel
      have hl : raw35129step2Labels = labelEmbedding10 ∘ raw35129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35129step2 raw35129step2Labels raw35129step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical35130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35130 raw35130Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw35130 raw35130Labels = mixedMoment B raw35130step0 raw35130step0Labels := by
      have hz : ∀ j, raw35130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35130step0 = (fun i j => raw35130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35130step0 raw35130; decide +kernel
      have hl : raw35130step0Labels = raw35130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35130 raw35130Labels permutation346 hz
    mixedMoment B raw35130step0 raw35130step0Labels = mixedMoment B raw35130step1 raw35130step1Labels := by
      have ha : raw35130step1 = (fun i j => raw35130step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35130step1 raw35130step0; decide +kernel
      have hl : raw35130step1Labels = raw35130step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35130step0 raw35130step0Labels permutation32 permutation3
    mixedMoment B raw35130step1 raw35130step1Labels = mixedMoment B raw35130step2 raw35130step2Labels := by
      have ha : raw35130step2 = raw35130step1 := by apply Matrix.ext; unfold raw35130step2 raw35130step1; decide +kernel
      have hl : raw35130step1Labels = labelEmbedding6 ∘ raw35130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35130step1 raw35130step1Labels raw35130step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4703 node4703Labels := by rfl

theorem canonical35131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35131 raw35131Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw35131 raw35131Labels = mixedMoment B raw35131step0 raw35131step0Labels := by
      have hz : ∀ j, raw35131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35131step0 = (fun i j => raw35131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35131step0 raw35131; decide +kernel
      have hl : raw35131step0Labels = raw35131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35131 raw35131Labels permutation346 hz
    mixedMoment B raw35131step0 raw35131step0Labels = mixedMoment B raw35131step1 raw35131step1Labels := by
      have ha : raw35131step1 = (fun i j => raw35131step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35131step1 raw35131step0; decide +kernel
      have hl : raw35131step1Labels = raw35131step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35131step0 raw35131step0Labels permutation57 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical35132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35132 raw35132Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw35132 raw35132Labels = mixedMoment B raw35132step0 raw35132step0Labels := by
      have ha : raw35132step0 = (fun i j => raw35132 (permutation266 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35132step0 raw35132; decide +kernel
      have hl : raw35132step0Labels = raw35132Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35132 raw35132Labels permutation266 permutation7
    mixedMoment B raw35132step0 raw35132step0Labels = mixedMoment B raw35132step1 raw35132step1Labels := by
      have ha : raw35132step1 = -raw35132step0 := by apply Matrix.ext; change ∀ i j, raw35132step1 i j = -(raw35132step0 i j); unfold raw35132step1 raw35132step0; decide +kernel
      have hl : raw35132step1Labels = raw35132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35132step1 raw35132step1Labels = mixedMoment B raw35132step2 raw35132step2Labels := by
      have ha : raw35132step2 = raw35132step1 := by apply Matrix.ext; unfold raw35132step2 raw35132step1; decide +kernel
      have hl : raw35132step1Labels = labelEmbedding10 ∘ raw35132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35132step1 raw35132step1Labels raw35132step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

theorem canonical35133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35133 raw35133Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw35133 raw35133Labels = mixedMoment B raw35133step0 raw35133step0Labels := by
      have hz : ∀ j, raw35133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35133step0 = (fun i j => raw35133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35133step0 raw35133; decide +kernel
      have hl : raw35133step0Labels = raw35133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35133 raw35133Labels permutation346 hz
    mixedMoment B raw35133step0 raw35133step0Labels = mixedMoment B raw35133step1 raw35133step1Labels := by
      have ha : raw35133step1 = (fun i j => raw35133step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35133step1 raw35133step0; decide +kernel
      have hl : raw35133step1Labels = raw35133step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35133step0 raw35133step0Labels permutation57 permutation7
    mixedMoment B raw35133step1 raw35133step1Labels = mixedMoment B raw35133step2 raw35133step2Labels := by
      have ha : raw35133step2 = -raw35133step1 := by apply Matrix.ext; change ∀ i j, raw35133step2 i j = -(raw35133step1 i j); unfold raw35133step2 raw35133step1; decide +kernel
      have hl : raw35133step2Labels = raw35133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35133step2 raw35133step2Labels = mixedMoment B raw35133step3 raw35133step3Labels := by
      have ha : raw35133step3 = raw35133step2 := by apply Matrix.ext; unfold raw35133step3 raw35133step2; decide +kernel
      have hl : raw35133step2Labels = labelEmbedding10 ∘ raw35133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35133step2 raw35133step2Labels raw35133step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

theorem canonical35134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35134 raw35134Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35134 raw35134Labels = mixedMoment B raw35134step0 raw35134step0Labels := by
      have hz : ∀ j, raw35134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35134step0 = (fun i j => raw35134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35134step0 raw35134; decide +kernel
      have hl : raw35134step0Labels = raw35134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35134 raw35134Labels permutation346 hz
    mixedMoment B raw35134step0 raw35134step0Labels = mixedMoment B raw35134step1 raw35134step1Labels := by
      have ha : raw35134step1 = (fun i j => raw35134step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35134step1 raw35134step0; decide +kernel
      have hl : raw35134step1Labels = raw35134step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35134step0 raw35134step0Labels permutation57 permutation7
    mixedMoment B raw35134step1 raw35134step1Labels = mixedMoment B raw35134step2 raw35134step2Labels := by
      have ha : raw35134step2 = -raw35134step1 := by apply Matrix.ext; change ∀ i j, raw35134step2 i j = -(raw35134step1 i j); unfold raw35134step2 raw35134step1; decide +kernel
      have hl : raw35134step2Labels = raw35134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35134step2 raw35134step2Labels = mixedMoment B raw35134step3 raw35134step3Labels := by
      have ha : raw35134step3 = raw35134step2 := by apply Matrix.ext; unfold raw35134step3 raw35134step2; decide +kernel
      have hl : raw35134step2Labels = labelEmbedding10 ∘ raw35134step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35134step2 raw35134step2Labels raw35134step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical35135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35135 raw35135Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw35135 raw35135Labels = mixedMoment B raw35135step0 raw35135step0Labels := by
      have hz : ∀ j, raw35135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35135step0 = (fun i j => raw35135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35135step0 raw35135; decide +kernel
      have hl : raw35135step0Labels = raw35135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35135 raw35135Labels permutation434 hz
    mixedMoment B raw35135step0 raw35135step0Labels = mixedMoment B raw35135step1 raw35135step1Labels := by
      have hz : ∀ j, raw35135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35135step1 = (fun i j => raw35135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35135step1 raw35135step0; decide +kernel
      have hl : raw35135step1Labels = raw35135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35135step0 raw35135step0Labels permutation80 hz
    mixedMoment B raw35135step1 raw35135step1Labels = mixedMoment B raw35135step2 raw35135step2Labels := by
      have ha : raw35135step2 = (fun i j => raw35135step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35135step2 raw35135step1; decide +kernel
      have hl : raw35135step2Labels = raw35135step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35135step1 raw35135step1Labels permutation9 permutation3
    mixedMoment B raw35135step2 raw35135step2Labels = mixedMoment B raw35135step3 raw35135step3Labels := by
      have ha : raw35135step3 = raw35135step2 := by apply Matrix.ext; unfold raw35135step3 raw35135step2; decide +kernel
      have hl : raw35135step2Labels = labelEmbedding6 ∘ raw35135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35135step2 raw35135step2Labels raw35135step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4705 node4705Labels := by rfl

theorem canonical35136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35136 raw35136Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw35136 raw35136Labels = mixedMoment B raw35136step0 raw35136step0Labels := by
      have hz : ∀ j, raw35136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35136step0 = (fun i j => raw35136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35136step0 raw35136; decide +kernel
      have hl : raw35136step0Labels = raw35136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35136 raw35136Labels permutation434 hz
    mixedMoment B raw35136step0 raw35136step0Labels = mixedMoment B raw35136step1 raw35136step1Labels := by
      have hz : ∀ j, raw35136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35136step1 = (fun i j => raw35136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35136step1 raw35136step0; decide +kernel
      have hl : raw35136step1Labels = raw35136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35136step0 raw35136step0Labels permutation80 hz
    mixedMoment B raw35136step1 raw35136step1Labels = mixedMoment B raw35136step2 raw35136step2Labels := by
      have ha : raw35136step2 = (fun i j => raw35136step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35136step2 raw35136step1; decide +kernel
      have hl : raw35136step2Labels = raw35136step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35136step1 raw35136step1Labels permutation15 permutation2
    _ = mixedMoment B node4692 node4692Labels := by rfl

theorem canonical35137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35137 raw35137Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw35137 raw35137Labels = mixedMoment B raw35137step0 raw35137step0Labels := by
      have hz : ∀ j, raw35137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35137step0 = (fun i j => raw35137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35137step0 raw35137; decide +kernel
      have hl : raw35137step0Labels = raw35137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35137 raw35137Labels permutation434 hz
    mixedMoment B raw35137step0 raw35137step0Labels = mixedMoment B raw35137step1 raw35137step1Labels := by
      have ha : raw35137step1 = (fun i j => raw35137step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35137step1 raw35137step0; decide +kernel
      have hl : raw35137step1Labels = raw35137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35137step0 raw35137step0Labels permutation126 permutation2
    mixedMoment B raw35137step1 raw35137step1Labels = mixedMoment B raw35137step2 raw35137step2Labels := by
      have ha : raw35137step2 = -raw35137step1 := by apply Matrix.ext; change ∀ i j, raw35137step2 i j = -(raw35137step1 i j); unfold raw35137step2 raw35137step1; decide +kernel
      have hl : raw35137step2Labels = raw35137step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4945 node4945Labels := by rfl

theorem canonical35138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35138 raw35138Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw35138 raw35138Labels = mixedMoment B raw35138step0 raw35138step0Labels := by
      have hz : ∀ j, raw35138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35138step0 = (fun i j => raw35138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35138step0 raw35138; decide +kernel
      have hl : raw35138step0Labels = raw35138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35138 raw35138Labels permutation346 hz
    mixedMoment B raw35138step0 raw35138step0Labels = mixedMoment B raw35138step1 raw35138step1Labels := by
      have ha : raw35138step1 = (fun i j => raw35138step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35138step1 raw35138step0; decide +kernel
      have hl : raw35138step1Labels = raw35138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35138step0 raw35138step0Labels permutation126 permutation2
    mixedMoment B raw35138step1 raw35138step1Labels = mixedMoment B raw35138step2 raw35138step2Labels := by
      have ha : raw35138step2 = -raw35138step1 := by apply Matrix.ext; change ∀ i j, raw35138step2 i j = -(raw35138step1 i j); unfold raw35138step2 raw35138step1; decide +kernel
      have hl : raw35138step2Labels = raw35138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4945 node4945Labels := by rfl

theorem canonical35139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35139 raw35139Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw35139 raw35139Labels = mixedMoment B raw35139step0 raw35139step0Labels := by
      have hz : ∀ j, raw35139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35139step0 = (fun i j => raw35139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35139step0 raw35139; decide +kernel
      have hl : raw35139step0Labels = raw35139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35139 raw35139Labels permutation434 hz
    mixedMoment B raw35139step0 raw35139step0Labels = mixedMoment B raw35139step1 raw35139step1Labels := by
      have hz : ∀ j, raw35139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35139step1 = (fun i j => raw35139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35139step1 raw35139step0; decide +kernel
      have hl : raw35139step1Labels = raw35139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35139step0 raw35139step0Labels permutation80 hz
    mixedMoment B raw35139step1 raw35139step1Labels = mixedMoment B raw35139step2 raw35139step2Labels := by
      have ha : raw35139step2 = (fun i j => raw35139step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35139step2 raw35139step1; decide +kernel
      have hl : raw35139step2Labels = raw35139step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35139step1 raw35139step1Labels permutation24 permutation2
    mixedMoment B raw35139step2 raw35139step2Labels = mixedMoment B raw35139step3 raw35139step3Labels := by
      have ha : raw35139step3 = -raw35139step2 := by apply Matrix.ext; change ∀ i j, raw35139step3 i j = -(raw35139step2 i j); unfold raw35139step3 raw35139step2; decide +kernel
      have hl : raw35139step3Labels = raw35139step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5110 node5110Labels := by rfl

theorem canonical35140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35140 raw35140Labels = mixedMoment B node4704 node4704Labels := by
  calc
    mixedMoment B raw35140 raw35140Labels = mixedMoment B raw35140step0 raw35140step0Labels := by
      have hz : ∀ j, raw35140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35140step0 = (fun i j => raw35140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35140step0 raw35140; decide +kernel
      have hl : raw35140step0Labels = raw35140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35140 raw35140Labels permutation434 hz
    mixedMoment B raw35140step0 raw35140step0Labels = mixedMoment B raw35140step1 raw35140step1Labels := by
      have hz : ∀ j, raw35140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35140step1 = (fun i j => raw35140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35140step1 raw35140step0; decide +kernel
      have hl : raw35140step1Labels = raw35140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35140step0 raw35140step0Labels permutation80 hz
    mixedMoment B raw35140step1 raw35140step1Labels = mixedMoment B raw35140step2 raw35140step2Labels := by
      have ha : raw35140step2 = (fun i j => raw35140step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35140step2 raw35140step1; decide +kernel
      have hl : raw35140step2Labels = raw35140step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35140step1 raw35140step1Labels permutation8 permutation3
    mixedMoment B raw35140step2 raw35140step2Labels = mixedMoment B raw35140step3 raw35140step3Labels := by
      have ha : raw35140step3 = raw35140step2 := by apply Matrix.ext; unfold raw35140step3 raw35140step2; decide +kernel
      have hl : raw35140step2Labels = labelEmbedding6 ∘ raw35140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35140step2 raw35140step2Labels raw35140step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4704 node4704Labels := by rfl

theorem canonical35141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35141 raw35141Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw35141 raw35141Labels = mixedMoment B raw35141step0 raw35141step0Labels := by
      have hz : ∀ j, raw35141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35141step0 = (fun i j => raw35141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35141step0 raw35141; decide +kernel
      have hl : raw35141step0Labels = raw35141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35141 raw35141Labels permutation434 hz
    mixedMoment B raw35141step0 raw35141step0Labels = mixedMoment B raw35141step1 raw35141step1Labels := by
      have hz : ∀ j, raw35141step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35141step1 = (fun i j => raw35141step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35141step1 raw35141step0; decide +kernel
      have hl : raw35141step1Labels = raw35141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35141step0 raw35141step0Labels permutation80 hz
    mixedMoment B raw35141step1 raw35141step1Labels = mixedMoment B raw35141step2 raw35141step2Labels := by
      have ha : raw35141step2 = (fun i j => raw35141step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35141step2 raw35141step1; decide +kernel
      have hl : raw35141step2Labels = raw35141step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35141step1 raw35141step1Labels permutation14 permutation2
    _ = mixedMoment B node4693 node4693Labels := by rfl

theorem canonical35142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35142 raw35142Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw35142 raw35142Labels = mixedMoment B raw35142step0 raw35142step0Labels := by
      have hz : ∀ j, raw35142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35142step0 = (fun i j => raw35142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35142step0 raw35142; decide +kernel
      have hl : raw35142step0Labels = raw35142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35142 raw35142Labels permutation434 hz
    mixedMoment B raw35142step0 raw35142step0Labels = mixedMoment B raw35142step1 raw35142step1Labels := by
      have ha : raw35142step1 = (fun i j => raw35142step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35142step1 raw35142step0; decide +kernel
      have hl : raw35142step1Labels = raw35142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35142step0 raw35142step0Labels permutation151 permutation3
    mixedMoment B raw35142step1 raw35142step1Labels = mixedMoment B raw35142step2 raw35142step2Labels := by
      have ha : raw35142step2 = -raw35142step1 := by apply Matrix.ext; change ∀ i j, raw35142step2 i j = -(raw35142step1 i j); unfold raw35142step2 raw35142step1; decide +kernel
      have hl : raw35142step2Labels = raw35142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35142step2 raw35142step2Labels = mixedMoment B raw35142step3 raw35142step3Labels := by
      have ha : raw35142step3 = raw35142step2 := by apply Matrix.ext; unfold raw35142step3 raw35142step2; decide +kernel
      have hl : raw35142step2Labels = labelEmbedding6 ∘ raw35142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35142step2 raw35142step2Labels raw35142step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

theorem canonical35143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35143 raw35143Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw35143 raw35143Labels = mixedMoment B raw35143step0 raw35143step0Labels := by
      have hz : ∀ j, raw35143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35143step0 = (fun i j => raw35143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35143step0 raw35143; decide +kernel
      have hl : raw35143step0Labels = raw35143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35143 raw35143Labels permutation346 hz
    mixedMoment B raw35143step0 raw35143step0Labels = mixedMoment B raw35143step1 raw35143step1Labels := by
      have ha : raw35143step1 = (fun i j => raw35143step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35143step1 raw35143step0; decide +kernel
      have hl : raw35143step1Labels = raw35143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35143step0 raw35143step0Labels permutation151 permutation3
    mixedMoment B raw35143step1 raw35143step1Labels = mixedMoment B raw35143step2 raw35143step2Labels := by
      have ha : raw35143step2 = -raw35143step1 := by apply Matrix.ext; change ∀ i j, raw35143step2 i j = -(raw35143step1 i j); unfold raw35143step2 raw35143step1; decide +kernel
      have hl : raw35143step2Labels = raw35143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35143step2 raw35143step2Labels = mixedMoment B raw35143step3 raw35143step3Labels := by
      have ha : raw35143step3 = raw35143step2 := by apply Matrix.ext; unfold raw35143step3 raw35143step2; decide +kernel
      have hl : raw35143step2Labels = labelEmbedding6 ∘ raw35143step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35143step2 raw35143step2Labels raw35143step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

theorem canonical35144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35144 raw35144Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw35144 raw35144Labels = mixedMoment B raw35144step0 raw35144step0Labels := by
      have hz : ∀ j, raw35144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35144step0 = (fun i j => raw35144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35144step0 raw35144; decide +kernel
      have hl : raw35144step0Labels = raw35144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35144 raw35144Labels permutation434 hz
    mixedMoment B raw35144step0 raw35144step0Labels = mixedMoment B raw35144step1 raw35144step1Labels := by
      have hz : ∀ j, raw35144step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35144step1 = (fun i j => raw35144step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35144step1 raw35144step0; decide +kernel
      have hl : raw35144step1Labels = raw35144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35144step0 raw35144step0Labels permutation80 hz
    mixedMoment B raw35144step1 raw35144step1Labels = mixedMoment B raw35144step2 raw35144step2Labels := by
      have ha : raw35144step2 = (fun i j => raw35144step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35144step2 raw35144step1; decide +kernel
      have hl : raw35144step2Labels = raw35144step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35144step1 raw35144step1Labels permutation31 permutation3
    mixedMoment B raw35144step2 raw35144step2Labels = mixedMoment B raw35144step3 raw35144step3Labels := by
      have ha : raw35144step3 = -raw35144step2 := by apply Matrix.ext; change ∀ i j, raw35144step3 i j = -(raw35144step2 i j); unfold raw35144step3 raw35144step2; decide +kernel
      have hl : raw35144step3Labels = raw35144step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35144step3 raw35144step3Labels = mixedMoment B raw35144step4 raw35144step4Labels := by
      have ha : raw35144step4 = raw35144step3 := by apply Matrix.ext; unfold raw35144step4 raw35144step3; decide +kernel
      have hl : raw35144step3Labels = labelEmbedding6 ∘ raw35144step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35144step3 raw35144step3Labels raw35144step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

theorem canonical35175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35175 raw35175Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw35175 raw35175Labels = mixedMoment B raw35175step0 raw35175step0Labels := by
      have hz : ∀ j, raw35175 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35175step0 = (fun i j => raw35175 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35175step0 raw35175; decide +kernel
      have hl : raw35175step0Labels = raw35175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35175 raw35175Labels permutation434 hz
    mixedMoment B raw35175step0 raw35175step0Labels = mixedMoment B raw35175step1 raw35175step1Labels := by
      have hz : ∀ j, raw35175step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35175step1 = (fun i j => raw35175step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35175step1 raw35175step0; decide +kernel
      have hl : raw35175step1Labels = raw35175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35175step0 raw35175step0Labels permutation80 hz
    mixedMoment B raw35175step1 raw35175step1Labels = mixedMoment B raw35175step2 raw35175step2Labels := by
      have ha : raw35175step2 = (fun i j => raw35175step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35175step2 raw35175step1; decide +kernel
      have hl : raw35175step2Labels = raw35175step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35175step1 raw35175step1Labels permutation15 permutation7
    mixedMoment B raw35175step2 raw35175step2Labels = mixedMoment B raw35175step3 raw35175step3Labels := by
      have ha : raw35175step3 = -raw35175step2 := by apply Matrix.ext; change ∀ i j, raw35175step3 i j = -(raw35175step2 i j); unfold raw35175step3 raw35175step2; decide +kernel
      have hl : raw35175step3Labels = raw35175step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35175step3 raw35175step3Labels = mixedMoment B raw35175step4 raw35175step4Labels := by
      have ha : raw35175step4 = raw35175step3 := by apply Matrix.ext; unfold raw35175step4 raw35175step3; decide +kernel
      have hl : raw35175step3Labels = labelEmbedding1 ∘ raw35175step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35175step3 raw35175step3Labels raw35175step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical35176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35176 raw35176Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw35176 raw35176Labels = mixedMoment B raw35176step0 raw35176step0Labels := by
      have hz : ∀ j, raw35176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35176step0 = (fun i j => raw35176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35176step0 raw35176; decide +kernel
      have hl : raw35176step0Labels = raw35176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35176 raw35176Labels permutation434 hz
    mixedMoment B raw35176step0 raw35176step0Labels = mixedMoment B raw35176step1 raw35176step1Labels := by
      have ha : raw35176step1 = (fun i j => raw35176step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35176step1 raw35176step0; decide +kernel
      have hl : raw35176step1Labels = raw35176step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35176step0 raw35176step0Labels permutation57 permutation7
    mixedMoment B raw35176step1 raw35176step1Labels = mixedMoment B raw35176step2 raw35176step2Labels := by
      have ha : raw35176step2 = -raw35176step1 := by apply Matrix.ext; change ∀ i j, raw35176step2 i j = -(raw35176step1 i j); unfold raw35176step2 raw35176step1; decide +kernel
      have hl : raw35176step2Labels = raw35176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35176step2 raw35176step2Labels = mixedMoment B raw35176step3 raw35176step3Labels := by
      have ha : raw35176step3 = raw35176step2 := by apply Matrix.ext; unfold raw35176step3 raw35176step2; decide +kernel
      have hl : raw35176step2Labels = labelEmbedding1 ∘ raw35176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35176step2 raw35176step2Labels raw35176step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical35177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35177 raw35177Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw35177 raw35177Labels = mixedMoment B raw35177step0 raw35177step0Labels := by
      have hz : ∀ j, raw35177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35177step0 = (fun i j => raw35177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35177step0 raw35177; decide +kernel
      have hl : raw35177step0Labels = raw35177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35177 raw35177Labels permutation346 hz
    mixedMoment B raw35177step0 raw35177step0Labels = mixedMoment B raw35177step1 raw35177step1Labels := by
      have ha : raw35177step1 = (fun i j => raw35177step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35177step1 raw35177step0; decide +kernel
      have hl : raw35177step1Labels = raw35177step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35177step0 raw35177step0Labels permutation57 permutation7
    mixedMoment B raw35177step1 raw35177step1Labels = mixedMoment B raw35177step2 raw35177step2Labels := by
      have ha : raw35177step2 = -raw35177step1 := by apply Matrix.ext; change ∀ i j, raw35177step2 i j = -(raw35177step1 i j); unfold raw35177step2 raw35177step1; decide +kernel
      have hl : raw35177step2Labels = raw35177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35177step2 raw35177step2Labels = mixedMoment B raw35177step3 raw35177step3Labels := by
      have ha : raw35177step3 = raw35177step2 := by apply Matrix.ext; unfold raw35177step3 raw35177step2; decide +kernel
      have hl : raw35177step2Labels = labelEmbedding1 ∘ raw35177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35177step2 raw35177step2Labels raw35177step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical35178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35178 raw35178Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw35178 raw35178Labels = mixedMoment B raw35178step0 raw35178step0Labels := by
      have hz : ∀ j, raw35178 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35178step0 = (fun i j => raw35178 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35178step0 raw35178; decide +kernel
      have hl : raw35178step0Labels = raw35178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35178 raw35178Labels permutation434 hz
    mixedMoment B raw35178step0 raw35178step0Labels = mixedMoment B raw35178step1 raw35178step1Labels := by
      have hz : ∀ j, raw35178step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35178step1 = (fun i j => raw35178step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35178step1 raw35178step0; decide +kernel
      have hl : raw35178step1Labels = raw35178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35178step0 raw35178step0Labels permutation80 hz
    mixedMoment B raw35178step1 raw35178step1Labels = mixedMoment B raw35178step2 raw35178step2Labels := by
      have ha : raw35178step2 = (fun i j => raw35178step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35178step2 raw35178step1; decide +kernel
      have hl : raw35178step2Labels = raw35178step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35178step1 raw35178step1Labels permutation15 permutation7
    mixedMoment B raw35178step2 raw35178step2Labels = mixedMoment B raw35178step3 raw35178step3Labels := by
      have ha : raw35178step3 = -raw35178step2 := by apply Matrix.ext; change ∀ i j, raw35178step3 i j = -(raw35178step2 i j); unfold raw35178step3 raw35178step2; decide +kernel
      have hl : raw35178step3Labels = raw35178step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35178step3 raw35178step3Labels = mixedMoment B raw35178step4 raw35178step4Labels := by
      have ha : raw35178step4 = raw35178step3 := by apply Matrix.ext; unfold raw35178step4 raw35178step3; decide +kernel
      have hl : raw35178step3Labels = labelEmbedding1 ∘ raw35178step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35178step3 raw35178step3Labels raw35178step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical35179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35179 raw35179Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw35179 raw35179Labels = mixedMoment B raw35179step0 raw35179step0Labels := by
      have hz : ∀ j, raw35179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35179step0 = (fun i j => raw35179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35179step0 raw35179; decide +kernel
      have hl : raw35179step0Labels = raw35179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35179 raw35179Labels permutation434 hz
    mixedMoment B raw35179step0 raw35179step0Labels = mixedMoment B raw35179step1 raw35179step1Labels := by
      have hz : ∀ j, raw35179step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35179step1 = (fun i j => raw35179step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35179step1 raw35179step0; decide +kernel
      have hl : raw35179step1Labels = raw35179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35179step0 raw35179step0Labels permutation80 hz
    mixedMoment B raw35179step1 raw35179step1Labels = mixedMoment B raw35179step2 raw35179step2Labels := by
      have ha : raw35179step2 = (fun i j => raw35179step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35179step2 raw35179step1; decide +kernel
      have hl : raw35179step2Labels = raw35179step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35179step1 raw35179step1Labels permutation15 permutation7
    mixedMoment B raw35179step2 raw35179step2Labels = mixedMoment B raw35179step3 raw35179step3Labels := by
      have ha : raw35179step3 = -raw35179step2 := by apply Matrix.ext; change ∀ i j, raw35179step3 i j = -(raw35179step2 i j); unfold raw35179step3 raw35179step2; decide +kernel
      have hl : raw35179step3Labels = raw35179step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35179step3 raw35179step3Labels = mixedMoment B raw35179step4 raw35179step4Labels := by
      have ha : raw35179step4 = raw35179step3 := by apply Matrix.ext; unfold raw35179step4 raw35179step3; decide +kernel
      have hl : raw35179step3Labels = labelEmbedding1 ∘ raw35179step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35179step3 raw35179step3Labels raw35179step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

theorem canonical35180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35180 raw35180Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw35180 raw35180Labels = mixedMoment B raw35180step0 raw35180step0Labels := by
      have hz : ∀ j, raw35180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35180step0 = (fun i j => raw35180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35180step0 raw35180; decide +kernel
      have hl : raw35180step0Labels = raw35180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35180 raw35180Labels permutation434 hz
    mixedMoment B raw35180step0 raw35180step0Labels = mixedMoment B raw35180step1 raw35180step1Labels := by
      have hz : ∀ j, raw35180step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35180step1 = (fun i j => raw35180step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35180step1 raw35180step0; decide +kernel
      have hl : raw35180step1Labels = raw35180step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35180step0 raw35180step0Labels permutation80 hz
    mixedMoment B raw35180step1 raw35180step1Labels = mixedMoment B raw35180step2 raw35180step2Labels := by
      have ha : raw35180step2 = (fun i j => raw35180step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35180step2 raw35180step1; decide +kernel
      have hl : raw35180step2Labels = raw35180step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35180step1 raw35180step1Labels permutation11 permutation5
    mixedMoment B raw35180step2 raw35180step2Labels = mixedMoment B raw35180step3 raw35180step3Labels := by
      have ha : raw35180step3 = -raw35180step2 := by apply Matrix.ext; change ∀ i j, raw35180step3 i j = -(raw35180step2 i j); unfold raw35180step3 raw35180step2; decide +kernel
      have hl : raw35180step3Labels = raw35180step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35180step3 raw35180step3Labels = mixedMoment B raw35180step4 raw35180step4Labels := by
      have ha : raw35180step4 = raw35180step3 := by apply Matrix.ext; unfold raw35180step4 raw35180step3; decide +kernel
      have hl : raw35180step3Labels = labelEmbedding1 ∘ raw35180step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35180step3 raw35180step3Labels raw35180step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2280 node2280Labels := by rfl

theorem canonical35181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35181 raw35181Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw35181 raw35181Labels = mixedMoment B raw35181step0 raw35181step0Labels := by
      have hz : ∀ j, raw35181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35181step0 = (fun i j => raw35181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35181step0 raw35181; decide +kernel
      have hl : raw35181step0Labels = raw35181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35181 raw35181Labels permutation434 hz
    mixedMoment B raw35181step0 raw35181step0Labels = mixedMoment B raw35181step1 raw35181step1Labels := by
      have ha : raw35181step1 = (fun i j => raw35181step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35181step1 raw35181step0; decide +kernel
      have hl : raw35181step1Labels = raw35181step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35181step0 raw35181step0Labels permutation57 permutation7
    mixedMoment B raw35181step1 raw35181step1Labels = mixedMoment B raw35181step2 raw35181step2Labels := by
      have ha : raw35181step2 = -raw35181step1 := by apply Matrix.ext; change ∀ i j, raw35181step2 i j = -(raw35181step1 i j); unfold raw35181step2 raw35181step1; decide +kernel
      have hl : raw35181step2Labels = raw35181step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35181step2 raw35181step2Labels = mixedMoment B raw35181step3 raw35181step3Labels := by
      have ha : raw35181step3 = raw35181step2 := by apply Matrix.ext; unfold raw35181step3 raw35181step2; decide +kernel
      have hl : raw35181step2Labels = labelEmbedding1 ∘ raw35181step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35181step2 raw35181step2Labels raw35181step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

theorem canonical35182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35182 raw35182Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw35182 raw35182Labels = mixedMoment B raw35182step0 raw35182step0Labels := by
      have hz : ∀ j, raw35182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35182step0 = (fun i j => raw35182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35182step0 raw35182; decide +kernel
      have hl : raw35182step0Labels = raw35182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35182 raw35182Labels permutation346 hz
    mixedMoment B raw35182step0 raw35182step0Labels = mixedMoment B raw35182step1 raw35182step1Labels := by
      have ha : raw35182step1 = (fun i j => raw35182step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35182step1 raw35182step0; decide +kernel
      have hl : raw35182step1Labels = raw35182step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35182step0 raw35182step0Labels permutation57 permutation7
    mixedMoment B raw35182step1 raw35182step1Labels = mixedMoment B raw35182step2 raw35182step2Labels := by
      have ha : raw35182step2 = -raw35182step1 := by apply Matrix.ext; change ∀ i j, raw35182step2 i j = -(raw35182step1 i j); unfold raw35182step2 raw35182step1; decide +kernel
      have hl : raw35182step2Labels = raw35182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35182step2 raw35182step2Labels = mixedMoment B raw35182step3 raw35182step3Labels := by
      have ha : raw35182step3 = raw35182step2 := by apply Matrix.ext; unfold raw35182step3 raw35182step2; decide +kernel
      have hl : raw35182step2Labels = labelEmbedding1 ∘ raw35182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35182step2 raw35182step2Labels raw35182step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

theorem canonical35183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35183 raw35183Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw35183 raw35183Labels = mixedMoment B raw35183step0 raw35183step0Labels := by
      have hz : ∀ j, raw35183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35183step0 = (fun i j => raw35183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35183step0 raw35183; decide +kernel
      have hl : raw35183step0Labels = raw35183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35183 raw35183Labels permutation434 hz
    mixedMoment B raw35183step0 raw35183step0Labels = mixedMoment B raw35183step1 raw35183step1Labels := by
      have hz : ∀ j, raw35183step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35183step1 = (fun i j => raw35183step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35183step1 raw35183step0; decide +kernel
      have hl : raw35183step1Labels = raw35183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35183step0 raw35183step0Labels permutation80 hz
    mixedMoment B raw35183step1 raw35183step1Labels = mixedMoment B raw35183step2 raw35183step2Labels := by
      have ha : raw35183step2 = (fun i j => raw35183step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35183step2 raw35183step1; decide +kernel
      have hl : raw35183step2Labels = raw35183step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35183step1 raw35183step1Labels permutation15 permutation7
    mixedMoment B raw35183step2 raw35183step2Labels = mixedMoment B raw35183step3 raw35183step3Labels := by
      have ha : raw35183step3 = -raw35183step2 := by apply Matrix.ext; change ∀ i j, raw35183step3 i j = -(raw35183step2 i j); unfold raw35183step3 raw35183step2; decide +kernel
      have hl : raw35183step3Labels = raw35183step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35183step3 raw35183step3Labels = mixedMoment B raw35183step4 raw35183step4Labels := by
      have ha : raw35183step4 = raw35183step3 := by apply Matrix.ext; unfold raw35183step4 raw35183step3; decide +kernel
      have hl : raw35183step3Labels = labelEmbedding1 ∘ raw35183step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35183step3 raw35183step3Labels raw35183step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical35184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35184 raw35184Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw35184 raw35184Labels = mixedMoment B raw35184step0 raw35184step0Labels := by
      have hz : ∀ j, raw35184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35184step0 = (fun i j => raw35184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35184step0 raw35184; decide +kernel
      have hl : raw35184step0Labels = raw35184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35184 raw35184Labels permutation434 hz
    mixedMoment B raw35184step0 raw35184step0Labels = mixedMoment B raw35184step1 raw35184step1Labels := by
      have hz : ∀ j, raw35184step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35184step1 = (fun i j => raw35184step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35184step1 raw35184step0; decide +kernel
      have hl : raw35184step1Labels = raw35184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35184step0 raw35184step0Labels permutation80 hz
    mixedMoment B raw35184step1 raw35184step1Labels = mixedMoment B raw35184step2 raw35184step2Labels := by
      have ha : raw35184step2 = (fun i j => raw35184step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35184step2 raw35184step1; decide +kernel
      have hl : raw35184step2Labels = raw35184step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35184step1 raw35184step1Labels permutation15 permutation7
    mixedMoment B raw35184step2 raw35184step2Labels = mixedMoment B raw35184step3 raw35184step3Labels := by
      have ha : raw35184step3 = -raw35184step2 := by apply Matrix.ext; change ∀ i j, raw35184step3 i j = -(raw35184step2 i j); unfold raw35184step3 raw35184step2; decide +kernel
      have hl : raw35184step3Labels = raw35184step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35184step3 raw35184step3Labels = mixedMoment B raw35184step4 raw35184step4Labels := by
      have ha : raw35184step4 = raw35184step3 := by apply Matrix.ext; unfold raw35184step4 raw35184step3; decide +kernel
      have hl : raw35184step3Labels = labelEmbedding1 ∘ raw35184step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35184step3 raw35184step3Labels raw35184step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical35185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35185 raw35185Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw35185 raw35185Labels = mixedMoment B raw35185step0 raw35185step0Labels := by
      have hz : ∀ j, raw35185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35185step0 = (fun i j => raw35185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35185step0 raw35185; decide +kernel
      have hl : raw35185step0Labels = raw35185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35185 raw35185Labels permutation434 hz
    mixedMoment B raw35185step0 raw35185step0Labels = mixedMoment B raw35185step1 raw35185step1Labels := by
      have ha : raw35185step1 = (fun i j => raw35185step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35185step1 raw35185step0; decide +kernel
      have hl : raw35185step1Labels = raw35185step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35185step0 raw35185step0Labels permutation44 permutation5
    mixedMoment B raw35185step1 raw35185step1Labels = mixedMoment B raw35185step2 raw35185step2Labels := by
      have ha : raw35185step2 = -raw35185step1 := by apply Matrix.ext; change ∀ i j, raw35185step2 i j = -(raw35185step1 i j); unfold raw35185step2 raw35185step1; decide +kernel
      have hl : raw35185step2Labels = raw35185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35185step2 raw35185step2Labels = mixedMoment B raw35185step3 raw35185step3Labels := by
      have ha : raw35185step3 = raw35185step2 := by apply Matrix.ext; unfold raw35185step3 raw35185step2; decide +kernel
      have hl : raw35185step2Labels = labelEmbedding1 ∘ raw35185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35185step2 raw35185step2Labels raw35185step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

theorem canonical35186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35186 raw35186Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw35186 raw35186Labels = mixedMoment B raw35186step0 raw35186step0Labels := by
      have hz : ∀ j, raw35186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35186step0 = (fun i j => raw35186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35186step0 raw35186; decide +kernel
      have hl : raw35186step0Labels = raw35186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35186 raw35186Labels permutation434 hz
    mixedMoment B raw35186step0 raw35186step0Labels = mixedMoment B raw35186step1 raw35186step1Labels := by
      have ha : raw35186step1 = (fun i j => raw35186step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35186step1 raw35186step0; decide +kernel
      have hl : raw35186step1Labels = raw35186step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35186step0 raw35186step0Labels permutation57 permutation7
    mixedMoment B raw35186step1 raw35186step1Labels = mixedMoment B raw35186step2 raw35186step2Labels := by
      have ha : raw35186step2 = -raw35186step1 := by apply Matrix.ext; change ∀ i j, raw35186step2 i j = -(raw35186step1 i j); unfold raw35186step2 raw35186step1; decide +kernel
      have hl : raw35186step2Labels = raw35186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35186step2 raw35186step2Labels = mixedMoment B raw35186step3 raw35186step3Labels := by
      have ha : raw35186step3 = raw35186step2 := by apply Matrix.ext; unfold raw35186step3 raw35186step2; decide +kernel
      have hl : raw35186step2Labels = labelEmbedding1 ∘ raw35186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35186step2 raw35186step2Labels raw35186step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical35187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35187 raw35187Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw35187 raw35187Labels = mixedMoment B raw35187step0 raw35187step0Labels := by
      have ha : raw35187step0 = (fun i j => raw35187 (permutation272 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35187step0 raw35187; decide +kernel
      have hl : raw35187step0Labels = raw35187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35187 raw35187Labels permutation272 permutation7
    mixedMoment B raw35187step0 raw35187step0Labels = mixedMoment B raw35187step1 raw35187step1Labels := by
      have ha : raw35187step1 = -raw35187step0 := by apply Matrix.ext; change ∀ i j, raw35187step1 i j = -(raw35187step0 i j); unfold raw35187step1 raw35187step0; decide +kernel
      have hl : raw35187step1Labels = raw35187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35187step1 raw35187step1Labels = mixedMoment B raw35187step2 raw35187step2Labels := by
      have ha : raw35187step2 = raw35187step1 := by apply Matrix.ext; unfold raw35187step2 raw35187step1; decide +kernel
      have hl : raw35187step1Labels = labelEmbedding1 ∘ raw35187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35187step1 raw35187step1Labels raw35187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

theorem canonical35188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35188 raw35188Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw35188 raw35188Labels = mixedMoment B raw35188step0 raw35188step0Labels := by
      have hz : ∀ j, raw35188 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35188step0 = (fun i j => raw35188 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35188step0 raw35188; decide +kernel
      have hl : raw35188step0Labels = raw35188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35188 raw35188Labels permutation434 hz
    mixedMoment B raw35188step0 raw35188step0Labels = mixedMoment B raw35188step1 raw35188step1Labels := by
      have ha : raw35188step1 = (fun i j => raw35188step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35188step1 raw35188step0; decide +kernel
      have hl : raw35188step1Labels = raw35188step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35188step0 raw35188step0Labels permutation57 permutation7
    mixedMoment B raw35188step1 raw35188step1Labels = mixedMoment B raw35188step2 raw35188step2Labels := by
      have ha : raw35188step2 = -raw35188step1 := by apply Matrix.ext; change ∀ i j, raw35188step2 i j = -(raw35188step1 i j); unfold raw35188step2 raw35188step1; decide +kernel
      have hl : raw35188step2Labels = raw35188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35188step2 raw35188step2Labels = mixedMoment B raw35188step3 raw35188step3Labels := by
      have ha : raw35188step3 = raw35188step2 := by apply Matrix.ext; unfold raw35188step3 raw35188step2; decide +kernel
      have hl : raw35188step2Labels = labelEmbedding1 ∘ raw35188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35188step2 raw35188step2Labels raw35188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

theorem canonical35189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35189 raw35189Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw35189 raw35189Labels = mixedMoment B raw35189step0 raw35189step0Labels := by
      have hz : ∀ j, raw35189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35189step0 = (fun i j => raw35189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35189step0 raw35189; decide +kernel
      have hl : raw35189step0Labels = raw35189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35189 raw35189Labels permutation434 hz
    mixedMoment B raw35189step0 raw35189step0Labels = mixedMoment B raw35189step1 raw35189step1Labels := by
      have ha : raw35189step1 = (fun i j => raw35189step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35189step1 raw35189step0; decide +kernel
      have hl : raw35189step1Labels = raw35189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35189step0 raw35189step0Labels permutation57 permutation7
    mixedMoment B raw35189step1 raw35189step1Labels = mixedMoment B raw35189step2 raw35189step2Labels := by
      have ha : raw35189step2 = -raw35189step1 := by apply Matrix.ext; change ∀ i j, raw35189step2 i j = -(raw35189step1 i j); unfold raw35189step2 raw35189step1; decide +kernel
      have hl : raw35189step2Labels = raw35189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35189step2 raw35189step2Labels = mixedMoment B raw35189step3 raw35189step3Labels := by
      have ha : raw35189step3 = raw35189step2 := by apply Matrix.ext; unfold raw35189step3 raw35189step2; decide +kernel
      have hl : raw35189step2Labels = labelEmbedding1 ∘ raw35189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35189step2 raw35189step2Labels raw35189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical35190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35190 raw35190Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw35190 raw35190Labels = mixedMoment B raw35190step0 raw35190step0Labels := by
      have hz : ∀ j, raw35190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35190step0 = (fun i j => raw35190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35190step0 raw35190; decide +kernel
      have hl : raw35190step0Labels = raw35190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35190 raw35190Labels permutation346 hz
    mixedMoment B raw35190step0 raw35190step0Labels = mixedMoment B raw35190step1 raw35190step1Labels := by
      have ha : raw35190step1 = (fun i j => raw35190step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35190step1 raw35190step0; decide +kernel
      have hl : raw35190step1Labels = raw35190step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35190step0 raw35190step0Labels permutation44 permutation5
    mixedMoment B raw35190step1 raw35190step1Labels = mixedMoment B raw35190step2 raw35190step2Labels := by
      have ha : raw35190step2 = -raw35190step1 := by apply Matrix.ext; change ∀ i j, raw35190step2 i j = -(raw35190step1 i j); unfold raw35190step2 raw35190step1; decide +kernel
      have hl : raw35190step2Labels = raw35190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35190step2 raw35190step2Labels = mixedMoment B raw35190step3 raw35190step3Labels := by
      have ha : raw35190step3 = raw35190step2 := by apply Matrix.ext; unfold raw35190step3 raw35190step2; decide +kernel
      have hl : raw35190step2Labels = labelEmbedding1 ∘ raw35190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35190step2 raw35190step2Labels raw35190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

theorem canonical35191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35191 raw35191Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw35191 raw35191Labels = mixedMoment B raw35191step0 raw35191step0Labels := by
      have hz : ∀ j, raw35191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35191step0 = (fun i j => raw35191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35191step0 raw35191; decide +kernel
      have hl : raw35191step0Labels = raw35191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35191 raw35191Labels permutation346 hz
    mixedMoment B raw35191step0 raw35191step0Labels = mixedMoment B raw35191step1 raw35191step1Labels := by
      have ha : raw35191step1 = (fun i j => raw35191step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35191step1 raw35191step0; decide +kernel
      have hl : raw35191step1Labels = raw35191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35191step0 raw35191step0Labels permutation57 permutation7
    mixedMoment B raw35191step1 raw35191step1Labels = mixedMoment B raw35191step2 raw35191step2Labels := by
      have ha : raw35191step2 = -raw35191step1 := by apply Matrix.ext; change ∀ i j, raw35191step2 i j = -(raw35191step1 i j); unfold raw35191step2 raw35191step1; decide +kernel
      have hl : raw35191step2Labels = raw35191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35191step2 raw35191step2Labels = mixedMoment B raw35191step3 raw35191step3Labels := by
      have ha : raw35191step3 = raw35191step2 := by apply Matrix.ext; unfold raw35191step3 raw35191step2; decide +kernel
      have hl : raw35191step2Labels = labelEmbedding1 ∘ raw35191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35191step2 raw35191step2Labels raw35191step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical35192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35192 raw35192Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw35192 raw35192Labels = mixedMoment B raw35192step0 raw35192step0Labels := by
      have ha : raw35192step0 = (fun i j => raw35192 (permutation266 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35192step0 raw35192; decide +kernel
      have hl : raw35192step0Labels = raw35192Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35192 raw35192Labels permutation266 permutation7
    mixedMoment B raw35192step0 raw35192step0Labels = mixedMoment B raw35192step1 raw35192step1Labels := by
      have ha : raw35192step1 = -raw35192step0 := by apply Matrix.ext; change ∀ i j, raw35192step1 i j = -(raw35192step0 i j); unfold raw35192step1 raw35192step0; decide +kernel
      have hl : raw35192step1Labels = raw35192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35192step1 raw35192step1Labels = mixedMoment B raw35192step2 raw35192step2Labels := by
      have ha : raw35192step2 = raw35192step1 := by apply Matrix.ext; unfold raw35192step2 raw35192step1; decide +kernel
      have hl : raw35192step1Labels = labelEmbedding1 ∘ raw35192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35192step1 raw35192step1Labels raw35192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

theorem canonical35193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35193 raw35193Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw35193 raw35193Labels = mixedMoment B raw35193step0 raw35193step0Labels := by
      have hz : ∀ j, raw35193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35193step0 = (fun i j => raw35193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35193step0 raw35193; decide +kernel
      have hl : raw35193step0Labels = raw35193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35193 raw35193Labels permutation346 hz
    mixedMoment B raw35193step0 raw35193step0Labels = mixedMoment B raw35193step1 raw35193step1Labels := by
      have ha : raw35193step1 = (fun i j => raw35193step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35193step1 raw35193step0; decide +kernel
      have hl : raw35193step1Labels = raw35193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35193step0 raw35193step0Labels permutation57 permutation7
    mixedMoment B raw35193step1 raw35193step1Labels = mixedMoment B raw35193step2 raw35193step2Labels := by
      have ha : raw35193step2 = -raw35193step1 := by apply Matrix.ext; change ∀ i j, raw35193step2 i j = -(raw35193step1 i j); unfold raw35193step2 raw35193step1; decide +kernel
      have hl : raw35193step2Labels = raw35193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35193step2 raw35193step2Labels = mixedMoment B raw35193step3 raw35193step3Labels := by
      have ha : raw35193step3 = raw35193step2 := by apply Matrix.ext; unfold raw35193step3 raw35193step2; decide +kernel
      have hl : raw35193step2Labels = labelEmbedding1 ∘ raw35193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35193step2 raw35193step2Labels raw35193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

theorem canonical35194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35194 raw35194Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw35194 raw35194Labels = mixedMoment B raw35194step0 raw35194step0Labels := by
      have hz : ∀ j, raw35194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35194step0 = (fun i j => raw35194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35194step0 raw35194; decide +kernel
      have hl : raw35194step0Labels = raw35194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35194 raw35194Labels permutation346 hz
    mixedMoment B raw35194step0 raw35194step0Labels = mixedMoment B raw35194step1 raw35194step1Labels := by
      have ha : raw35194step1 = (fun i j => raw35194step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35194step1 raw35194step0; decide +kernel
      have hl : raw35194step1Labels = raw35194step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35194step0 raw35194step0Labels permutation57 permutation7
    mixedMoment B raw35194step1 raw35194step1Labels = mixedMoment B raw35194step2 raw35194step2Labels := by
      have ha : raw35194step2 = -raw35194step1 := by apply Matrix.ext; change ∀ i j, raw35194step2 i j = -(raw35194step1 i j); unfold raw35194step2 raw35194step1; decide +kernel
      have hl : raw35194step2Labels = raw35194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35194step2 raw35194step2Labels = mixedMoment B raw35194step3 raw35194step3Labels := by
      have ha : raw35194step3 = raw35194step2 := by apply Matrix.ext; unfold raw35194step3 raw35194step2; decide +kernel
      have hl : raw35194step2Labels = labelEmbedding1 ∘ raw35194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35194step2 raw35194step2Labels raw35194step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical35195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35195 raw35195Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw35195 raw35195Labels = mixedMoment B raw35195step0 raw35195step0Labels := by
      have hz : ∀ j, raw35195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35195step0 = (fun i j => raw35195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35195step0 raw35195; decide +kernel
      have hl : raw35195step0Labels = raw35195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35195 raw35195Labels permutation434 hz
    mixedMoment B raw35195step0 raw35195step0Labels = mixedMoment B raw35195step1 raw35195step1Labels := by
      have hz : ∀ j, raw35195step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35195step1 = (fun i j => raw35195step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35195step1 raw35195step0; decide +kernel
      have hl : raw35195step1Labels = raw35195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35195step0 raw35195step0Labels permutation80 hz
    mixedMoment B raw35195step1 raw35195step1Labels = mixedMoment B raw35195step2 raw35195step2Labels := by
      have ha : raw35195step2 = (fun i j => raw35195step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35195step2 raw35195step1; decide +kernel
      have hl : raw35195step2Labels = raw35195step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35195step1 raw35195step1Labels permutation9 permutation5
    mixedMoment B raw35195step2 raw35195step2Labels = mixedMoment B raw35195step3 raw35195step3Labels := by
      have ha : raw35195step3 = -raw35195step2 := by apply Matrix.ext; change ∀ i j, raw35195step3 i j = -(raw35195step2 i j); unfold raw35195step3 raw35195step2; decide +kernel
      have hl : raw35195step3Labels = raw35195step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35195step3 raw35195step3Labels = mixedMoment B raw35195step4 raw35195step4Labels := by
      have ha : raw35195step4 = raw35195step3 := by apply Matrix.ext; unfold raw35195step4 raw35195step3; decide +kernel
      have hl : raw35195step3Labels = labelEmbedding1 ∘ raw35195step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35195step3 raw35195step3Labels raw35195step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

theorem canonical35196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35196 raw35196Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw35196 raw35196Labels = mixedMoment B raw35196step0 raw35196step0Labels := by
      have hz : ∀ j, raw35196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35196step0 = (fun i j => raw35196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35196step0 raw35196; decide +kernel
      have hl : raw35196step0Labels = raw35196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35196 raw35196Labels permutation434 hz
    mixedMoment B raw35196step0 raw35196step0Labels = mixedMoment B raw35196step1 raw35196step1Labels := by
      have hz : ∀ j, raw35196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35196step1 = (fun i j => raw35196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35196step1 raw35196step0; decide +kernel
      have hl : raw35196step1Labels = raw35196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35196step0 raw35196step0Labels permutation80 hz
    mixedMoment B raw35196step1 raw35196step1Labels = mixedMoment B raw35196step2 raw35196step2Labels := by
      have ha : raw35196step2 = (fun i j => raw35196step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35196step2 raw35196step1; decide +kernel
      have hl : raw35196step2Labels = raw35196step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35196step1 raw35196step1Labels permutation15 permutation7
    mixedMoment B raw35196step2 raw35196step2Labels = mixedMoment B raw35196step3 raw35196step3Labels := by
      have ha : raw35196step3 = -raw35196step2 := by apply Matrix.ext; change ∀ i j, raw35196step3 i j = -(raw35196step2 i j); unfold raw35196step3 raw35196step2; decide +kernel
      have hl : raw35196step3Labels = raw35196step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35196step3 raw35196step3Labels = mixedMoment B raw35196step4 raw35196step4Labels := by
      have ha : raw35196step4 = raw35196step3 := by apply Matrix.ext; unfold raw35196step4 raw35196step3; decide +kernel
      have hl : raw35196step3Labels = labelEmbedding1 ∘ raw35196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35196step3 raw35196step3Labels raw35196step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

theorem canonical35197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35197 raw35197Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw35197 raw35197Labels = mixedMoment B raw35197step0 raw35197step0Labels := by
      have hz : ∀ j, raw35197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35197step0 = (fun i j => raw35197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35197step0 raw35197; decide +kernel
      have hl : raw35197step0Labels = raw35197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35197 raw35197Labels permutation434 hz
    mixedMoment B raw35197step0 raw35197step0Labels = mixedMoment B raw35197step1 raw35197step1Labels := by
      have ha : raw35197step1 = (fun i j => raw35197step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35197step1 raw35197step0; decide +kernel
      have hl : raw35197step1Labels = raw35197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35197step0 raw35197step0Labels permutation57 permutation7
    mixedMoment B raw35197step1 raw35197step1Labels = mixedMoment B raw35197step2 raw35197step2Labels := by
      have ha : raw35197step2 = -raw35197step1 := by apply Matrix.ext; change ∀ i j, raw35197step2 i j = -(raw35197step1 i j); unfold raw35197step2 raw35197step1; decide +kernel
      have hl : raw35197step2Labels = raw35197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35197step2 raw35197step2Labels = mixedMoment B raw35197step3 raw35197step3Labels := by
      have ha : raw35197step3 = raw35197step2 := by apply Matrix.ext; unfold raw35197step3 raw35197step2; decide +kernel
      have hl : raw35197step2Labels = labelEmbedding1 ∘ raw35197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35197step2 raw35197step2Labels raw35197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical35198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35198 raw35198Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw35198 raw35198Labels = mixedMoment B raw35198step0 raw35198step0Labels := by
      have hz : ∀ j, raw35198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35198step0 = (fun i j => raw35198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35198step0 raw35198; decide +kernel
      have hl : raw35198step0Labels = raw35198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35198 raw35198Labels permutation346 hz
    mixedMoment B raw35198step0 raw35198step0Labels = mixedMoment B raw35198step1 raw35198step1Labels := by
      have ha : raw35198step1 = (fun i j => raw35198step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35198step1 raw35198step0; decide +kernel
      have hl : raw35198step1Labels = raw35198step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35198step0 raw35198step0Labels permutation57 permutation7
    mixedMoment B raw35198step1 raw35198step1Labels = mixedMoment B raw35198step2 raw35198step2Labels := by
      have ha : raw35198step2 = -raw35198step1 := by apply Matrix.ext; change ∀ i j, raw35198step2 i j = -(raw35198step1 i j); unfold raw35198step2 raw35198step1; decide +kernel
      have hl : raw35198step2Labels = raw35198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35198step2 raw35198step2Labels = mixedMoment B raw35198step3 raw35198step3Labels := by
      have ha : raw35198step3 = raw35198step2 := by apply Matrix.ext; unfold raw35198step3 raw35198step2; decide +kernel
      have hl : raw35198step2Labels = labelEmbedding1 ∘ raw35198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35198step2 raw35198step2Labels raw35198step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical35199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35199 raw35199Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw35199 raw35199Labels = mixedMoment B raw35199step0 raw35199step0Labels := by
      have hz : ∀ j, raw35199 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35199step0 = (fun i j => raw35199 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35199step0 raw35199; decide +kernel
      have hl : raw35199step0Labels = raw35199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35199 raw35199Labels permutation434 hz
    mixedMoment B raw35199step0 raw35199step0Labels = mixedMoment B raw35199step1 raw35199step1Labels := by
      have hz : ∀ j, raw35199step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35199step1 = (fun i j => raw35199step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35199step1 raw35199step0; decide +kernel
      have hl : raw35199step1Labels = raw35199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35199step0 raw35199step0Labels permutation80 hz
    mixedMoment B raw35199step1 raw35199step1Labels = mixedMoment B raw35199step2 raw35199step2Labels := by
      have ha : raw35199step2 = (fun i j => raw35199step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35199step2 raw35199step1; decide +kernel
      have hl : raw35199step2Labels = raw35199step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35199step1 raw35199step1Labels permutation15 permutation7
    mixedMoment B raw35199step2 raw35199step2Labels = mixedMoment B raw35199step3 raw35199step3Labels := by
      have ha : raw35199step3 = -raw35199step2 := by apply Matrix.ext; change ∀ i j, raw35199step3 i j = -(raw35199step2 i j); unfold raw35199step3 raw35199step2; decide +kernel
      have hl : raw35199step3Labels = raw35199step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35199step3 raw35199step3Labels = mixedMoment B raw35199step4 raw35199step4Labels := by
      have ha : raw35199step4 = raw35199step3 := by apply Matrix.ext; unfold raw35199step4 raw35199step3; decide +kernel
      have hl : raw35199step3Labels = labelEmbedding1 ∘ raw35199step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35199step3 raw35199step3Labels raw35199step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical275
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35200 raw35200Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw35200 raw35200Labels = mixedMoment B raw35200step0 raw35200step0Labels := by
      have hz : ∀ j, raw35200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35200step0 = (fun i j => raw35200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35200step0 raw35200; decide +kernel
      have hl : raw35200step0Labels = raw35200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35200 raw35200Labels permutation434 hz
    mixedMoment B raw35200step0 raw35200step0Labels = mixedMoment B raw35200step1 raw35200step1Labels := by
      have hz : ∀ j, raw35200step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35200step1 = (fun i j => raw35200step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35200step1 raw35200step0; decide +kernel
      have hl : raw35200step1Labels = raw35200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35200step0 raw35200step0Labels permutation80 hz
    mixedMoment B raw35200step1 raw35200step1Labels = mixedMoment B raw35200step2 raw35200step2Labels := by
      have ha : raw35200step2 = (fun i j => raw35200step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35200step2 raw35200step1; decide +kernel
      have hl : raw35200step2Labels = raw35200step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35200step1 raw35200step1Labels permutation10 permutation5
    mixedMoment B raw35200step2 raw35200step2Labels = mixedMoment B raw35200step3 raw35200step3Labels := by
      have ha : raw35200step3 = -raw35200step2 := by apply Matrix.ext; change ∀ i j, raw35200step3 i j = -(raw35200step2 i j); unfold raw35200step3 raw35200step2; decide +kernel
      have hl : raw35200step3Labels = raw35200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35200step3 raw35200step3Labels = mixedMoment B raw35200step4 raw35200step4Labels := by
      have ha : raw35200step4 = raw35200step3 := by apply Matrix.ext; unfold raw35200step4 raw35200step3; decide +kernel
      have hl : raw35200step3Labels = labelEmbedding1 ∘ raw35200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35200step3 raw35200step3Labels raw35200step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2273 node2273Labels := by rfl

theorem canonical35201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35201 raw35201Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw35201 raw35201Labels = mixedMoment B raw35201step0 raw35201step0Labels := by
      have hz : ∀ j, raw35201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35201step0 = (fun i j => raw35201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35201step0 raw35201; decide +kernel
      have hl : raw35201step0Labels = raw35201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35201 raw35201Labels permutation434 hz
    mixedMoment B raw35201step0 raw35201step0Labels = mixedMoment B raw35201step1 raw35201step1Labels := by
      have hz : ∀ j, raw35201step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35201step1 = (fun i j => raw35201step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35201step1 raw35201step0; decide +kernel
      have hl : raw35201step1Labels = raw35201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35201step0 raw35201step0Labels permutation80 hz
    mixedMoment B raw35201step1 raw35201step1Labels = mixedMoment B raw35201step2 raw35201step2Labels := by
      have ha : raw35201step2 = (fun i j => raw35201step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35201step2 raw35201step1; decide +kernel
      have hl : raw35201step2Labels = raw35201step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35201step1 raw35201step1Labels permutation15 permutation7
    mixedMoment B raw35201step2 raw35201step2Labels = mixedMoment B raw35201step3 raw35201step3Labels := by
      have ha : raw35201step3 = -raw35201step2 := by apply Matrix.ext; change ∀ i j, raw35201step3 i j = -(raw35201step2 i j); unfold raw35201step3 raw35201step2; decide +kernel
      have hl : raw35201step3Labels = raw35201step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35201step3 raw35201step3Labels = mixedMoment B raw35201step4 raw35201step4Labels := by
      have ha : raw35201step4 = raw35201step3 := by apply Matrix.ext; unfold raw35201step4 raw35201step3; decide +kernel
      have hl : raw35201step3Labels = labelEmbedding1 ∘ raw35201step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35201step3 raw35201step3Labels raw35201step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

theorem canonical35202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35202 raw35202Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw35202 raw35202Labels = mixedMoment B raw35202step0 raw35202step0Labels := by
      have hz : ∀ j, raw35202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35202step0 = (fun i j => raw35202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35202step0 raw35202; decide +kernel
      have hl : raw35202step0Labels = raw35202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35202 raw35202Labels permutation434 hz
    mixedMoment B raw35202step0 raw35202step0Labels = mixedMoment B raw35202step1 raw35202step1Labels := by
      have ha : raw35202step1 = (fun i j => raw35202step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35202step1 raw35202step0; decide +kernel
      have hl : raw35202step1Labels = raw35202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35202step0 raw35202step0Labels permutation57 permutation7
    mixedMoment B raw35202step1 raw35202step1Labels = mixedMoment B raw35202step2 raw35202step2Labels := by
      have ha : raw35202step2 = -raw35202step1 := by apply Matrix.ext; change ∀ i j, raw35202step2 i j = -(raw35202step1 i j); unfold raw35202step2 raw35202step1; decide +kernel
      have hl : raw35202step2Labels = raw35202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35202step2 raw35202step2Labels = mixedMoment B raw35202step3 raw35202step3Labels := by
      have ha : raw35202step3 = raw35202step2 := by apply Matrix.ext; unfold raw35202step3 raw35202step2; decide +kernel
      have hl : raw35202step2Labels = labelEmbedding1 ∘ raw35202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35202step2 raw35202step2Labels raw35202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

theorem canonical35203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35203 raw35203Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw35203 raw35203Labels = mixedMoment B raw35203step0 raw35203step0Labels := by
      have hz : ∀ j, raw35203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35203step0 = (fun i j => raw35203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35203step0 raw35203; decide +kernel
      have hl : raw35203step0Labels = raw35203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35203 raw35203Labels permutation346 hz
    mixedMoment B raw35203step0 raw35203step0Labels = mixedMoment B raw35203step1 raw35203step1Labels := by
      have ha : raw35203step1 = (fun i j => raw35203step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35203step1 raw35203step0; decide +kernel
      have hl : raw35203step1Labels = raw35203step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35203step0 raw35203step0Labels permutation57 permutation7
    mixedMoment B raw35203step1 raw35203step1Labels = mixedMoment B raw35203step2 raw35203step2Labels := by
      have ha : raw35203step2 = -raw35203step1 := by apply Matrix.ext; change ∀ i j, raw35203step2 i j = -(raw35203step1 i j); unfold raw35203step2 raw35203step1; decide +kernel
      have hl : raw35203step2Labels = raw35203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35203step2 raw35203step2Labels = mixedMoment B raw35203step3 raw35203step3Labels := by
      have ha : raw35203step3 = raw35203step2 := by apply Matrix.ext; unfold raw35203step3 raw35203step2; decide +kernel
      have hl : raw35203step2Labels = labelEmbedding1 ∘ raw35203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35203step2 raw35203step2Labels raw35203step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

theorem canonical35204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35204 raw35204Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw35204 raw35204Labels = mixedMoment B raw35204step0 raw35204step0Labels := by
      have hz : ∀ j, raw35204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35204step0 = (fun i j => raw35204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35204step0 raw35204; decide +kernel
      have hl : raw35204step0Labels = raw35204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35204 raw35204Labels permutation434 hz
    mixedMoment B raw35204step0 raw35204step0Labels = mixedMoment B raw35204step1 raw35204step1Labels := by
      have hz : ∀ j, raw35204step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35204step1 = (fun i j => raw35204step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35204step1 raw35204step0; decide +kernel
      have hl : raw35204step1Labels = raw35204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35204step0 raw35204step0Labels permutation80 hz
    mixedMoment B raw35204step1 raw35204step1Labels = mixedMoment B raw35204step2 raw35204step2Labels := by
      have ha : raw35204step2 = (fun i j => raw35204step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35204step2 raw35204step1; decide +kernel
      have hl : raw35204step2Labels = raw35204step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35204step1 raw35204step1Labels permutation15 permutation7
    mixedMoment B raw35204step2 raw35204step2Labels = mixedMoment B raw35204step3 raw35204step3Labels := by
      have ha : raw35204step3 = -raw35204step2 := by apply Matrix.ext; change ∀ i j, raw35204step3 i j = -(raw35204step2 i j); unfold raw35204step3 raw35204step2; decide +kernel
      have hl : raw35204step3Labels = raw35204step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35204step3 raw35204step3Labels = mixedMoment B raw35204step4 raw35204step4Labels := by
      have ha : raw35204step4 = raw35204step3 := by apply Matrix.ext; unfold raw35204step4 raw35204step3; decide +kernel
      have hl : raw35204step3Labels = labelEmbedding1 ∘ raw35204step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35204step3 raw35204step3Labels raw35204step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4684 node4684Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1810 node1810Labels + mixedMoment B node2152 node2152Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1566 singletonSmall4684
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4684) = raw1566Labels := by decide +kernel
  rw [hl, canonical1566 B hB] at h
  have hc0 : mixedMoment B raw1566 (Fin.cases (0 : Fin 2) singletonSmall4684) =
      mixedMoment B node1810 node1810Labels := by
    have ha : raw1566 = raw1567 := by apply Matrix.ext; unfold raw1566 raw1567; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4684 = raw1567Labels := by decide +kernel
    rw [ha, hj, canonical1567 B hB]
  have hc1 : mixedMoment B raw1566 (Fin.cases (1 : Fin 2) singletonSmall4684) =
      mixedMoment B node2152 node2152Labels := by
    have ha : raw1566 = raw1568 := by apply Matrix.ext; unfold raw1566 raw1568; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4684 = raw1568Labels := by decide +kernel
    rw [ha, hj, canonical1568 B hB]
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

theorem singleton4693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4693 node4693Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1819 node1819Labels + mixedMoment B node2169 node2169Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1587 singletonSmall4693
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4693) = raw1587Labels := by decide +kernel
  rw [hl, canonical1587 B hB] at h
  have hc0 : mixedMoment B raw1587 (Fin.cases (0 : Fin 2) singletonSmall4693) =
      mixedMoment B node1819 node1819Labels := by
    have ha : raw1587 = raw1588 := by apply Matrix.ext; unfold raw1587 raw1588; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4693 = raw1588Labels := by decide +kernel
    rw [ha, hj, canonical1588 B hB]
  have hc1 : mixedMoment B raw1587 (Fin.cases (1 : Fin 2) singletonSmall4693) =
      mixedMoment B node2169 node2169Labels := by
    have ha : raw1587 = raw1589 := by apply Matrix.ext; unfold raw1587 raw1589; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4693 = raw1589Labels := by decide +kernel
    rw [ha, hj, canonical1589 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5228 node5228Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2672 node2672Labels + mixedMoment B node3391 node3391Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2250 singletonSmall5228
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5228) = raw2250Labels := by decide +kernel
  rw [hl, canonical2250 B hB] at h
  have hc0 : mixedMoment B raw2250 (Fin.cases (0 : Fin 2) singletonSmall5228) =
      mixedMoment B node2672 node2672Labels := by
    have ha : raw2250 = raw2251 := by apply Matrix.ext; unfold raw2250 raw2251; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5228 = raw2251Labels := by decide +kernel
    rw [ha, hj, canonical2251 B hB]
  have hc1 : mixedMoment B raw2250 (Fin.cases (1 : Fin 2) singletonSmall5228) =
      mixedMoment B node3391 node3391Labels := by
    have ha : raw2250 = raw2252 := by apply Matrix.ext; unfold raw2250 raw2252; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5228 = raw2252Labels := by decide +kernel
    rw [ha, hj, canonical2252 B hB]
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

theorem singleton5248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5248 node5248Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2705 node2705Labels + mixedMoment B node3498 node3498Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2265 singletonSmall5248
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5248) = raw2265Labels := by decide +kernel
  rw [hl, canonical2265 B hB] at h
  have hc0 : mixedMoment B raw2265 (Fin.cases (0 : Fin 2) singletonSmall5248) =
      mixedMoment B node2705 node2705Labels := by
    have ha : raw2265 = raw2266 := by apply Matrix.ext; unfold raw2265 raw2266; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5248 = raw2266Labels := by decide +kernel
    rw [ha, hj, canonical2266 B hB]
  have hc1 : mixedMoment B raw2265 (Fin.cases (1 : Fin 2) singletonSmall5248) =
      mixedMoment B node3498 node3498Labels := by
    have ha : raw2265 = raw2267 := by apply Matrix.ext; unfold raw2265 raw2267; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5248 = raw2267Labels := by decide +kernel
    rw [ha, hj, canonical2267 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5302 node5302Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3054 node3054Labels + mixedMoment B node3626 node3626Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2313 singletonSmall5302
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5302) = raw2313Labels := by decide +kernel
  rw [hl, canonical2313 B hB] at h
  have hc0 : mixedMoment B raw2313 (Fin.cases (0 : Fin 2) singletonSmall5302) =
      mixedMoment B node3054 node3054Labels := by
    have ha : raw2313 = raw2314 := by apply Matrix.ext; unfold raw2313 raw2314; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5302 = raw2314Labels := by decide +kernel
    rw [ha, hj, canonical2314 B hB]
  have hc1 : mixedMoment B raw2313 (Fin.cases (1 : Fin 2) singletonSmall5302) =
      mixedMoment B node3626 node3626Labels := by
    have ha : raw2313 = raw2315 := by apply Matrix.ext; unfold raw2313 raw2315; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5302 = raw2315Labels := by decide +kernel
    rw [ha, hj, canonical2315 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound5302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5302 node5302Labels = Sparse.eval nodeValue5302 (mixedVector B) := by
  have h := singleton5302 B _hB
  rw [sound3054 B _hB _hF, sound3626 B _hB _hF] at h
  norm_num [nodeValue5302, nodeValue3054, nodeValue3626, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1810 node1810Labels = Sparse.eval nodeValue1810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1810) = mixedMoment B node1810 node1810Labels := rfl
  simpa [nodeValue1810, Sparse.eval] using hc.symm

theorem sound1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1818 node1818Labels = Sparse.eval nodeValue1818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1818) = mixedMoment B node1818 node1818Labels := rfl
  simpa [nodeValue1818, Sparse.eval] using hc.symm

theorem sound1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1819 node1819Labels = Sparse.eval nodeValue1819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1819) = mixedMoment B node1819 node1819Labels := rfl
  simpa [nodeValue1819, Sparse.eval] using hc.symm

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

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

theorem sound2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2154 node2154Labels = Sparse.eval nodeValue2154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2154) = mixedMoment B node2154 node2154Labels := rfl
  simpa [nodeValue2154, Sparse.eval] using hc.symm

theorem sound2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2155 node2155Labels = Sparse.eval nodeValue2155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2155) = mixedMoment B node2155 node2155Labels := rfl
  simpa [nodeValue2155, Sparse.eval] using hc.symm

theorem sound2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2158 node2158Labels = Sparse.eval nodeValue2158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2158) = mixedMoment B node2158 node2158Labels := rfl
  simpa [nodeValue2158, Sparse.eval] using hc.symm

theorem sound2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2164 node2164Labels = Sparse.eval nodeValue2164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2164) = mixedMoment B node2164 node2164Labels := rfl
  simpa [nodeValue2164, Sparse.eval] using hc.symm

theorem sound2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2168 node2168Labels = Sparse.eval nodeValue2168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2168) = mixedMoment B node2168 node2168Labels := rfl
  simpa [nodeValue2168, Sparse.eval] using hc.symm

theorem sound2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2169 node2169Labels = Sparse.eval nodeValue2169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2169) = mixedMoment B node2169 node2169Labels := rfl
  simpa [nodeValue2169, Sparse.eval] using hc.symm

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

theorem zero2229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = 0 := by
  exact mixedMoment_order_one B hB node2229 node2229Labels 1
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

theorem sound2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = Sparse.eval nodeValue2229 (mixedVector B) := by
  simpa only [nodeValue2229, Sparse.eval_nil] using zero2229 B _hB _hF

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

theorem sound2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2272 node2272Labels = Sparse.eval nodeValue2272 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2272) = mixedMoment B node2272 node2272Labels := rfl
  simpa [nodeValue2272, Sparse.eval] using hc.symm

theorem sound2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2273 node2273Labels = Sparse.eval nodeValue2273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2273) = mixedMoment B node2273 node2273Labels := rfl
  simpa [nodeValue2273, Sparse.eval] using hc.symm

theorem sound2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2274 node2274Labels = Sparse.eval nodeValue2274 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2274) = mixedMoment B node2274 node2274Labels := rfl
  simpa [nodeValue2274, Sparse.eval] using hc.symm

theorem sound2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2280 node2280Labels = Sparse.eval nodeValue2280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2280) = mixedMoment B node2280 node2280Labels := rfl
  simpa [nodeValue2280, Sparse.eval] using hc.symm

theorem sound2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2286 node2286Labels = Sparse.eval nodeValue2286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2286) = mixedMoment B node2286 node2286Labels := rfl
  simpa [nodeValue2286, Sparse.eval] using hc.symm

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

theorem sound2321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2321 node2321Labels = Sparse.eval nodeValue2321 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2321) = mixedMoment B node2321 node2321Labels := rfl
  simpa [nodeValue2321, Sparse.eval] using hc.symm

theorem sound2348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2348 node2348Labels = Sparse.eval nodeValue2348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2348) = mixedMoment B node2348 node2348Labels := rfl
  simpa [nodeValue2348, Sparse.eval] using hc.symm

theorem sound2351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2351 node2351Labels = Sparse.eval nodeValue2351 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2351) = mixedMoment B node2351 node2351Labels := rfl
  simpa [nodeValue2351, Sparse.eval] using hc.symm

theorem sound2356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2356 node2356Labels = Sparse.eval nodeValue2356 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2356) = mixedMoment B node2356 node2356Labels := rfl
  simpa [nodeValue2356, Sparse.eval] using hc.symm

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

theorem sound2653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2653 node2653Labels = Sparse.eval nodeValue2653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2653) = mixedMoment B node2653 node2653Labels := rfl
  simpa [nodeValue2653, Sparse.eval] using hc.symm

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

theorem sound2659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2659 node2659Labels = Sparse.eval nodeValue2659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2659) = mixedMoment B node2659 node2659Labels := rfl
  simpa [nodeValue2659, Sparse.eval] using hc.symm

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

theorem sound2673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2673 node2673Labels = Sparse.eval nodeValue2673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2673) = mixedMoment B node2673 node2673Labels := rfl
  simpa [nodeValue2673, Sparse.eval] using hc.symm

theorem sound2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2685 node2685Labels = Sparse.eval nodeValue2685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2685) = mixedMoment B node2685 node2685Labels := rfl
  simpa [nodeValue2685, Sparse.eval] using hc.symm

theorem sound2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2687 node2687Labels = Sparse.eval nodeValue2687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2687) = mixedMoment B node2687 node2687Labels := rfl
  simpa [nodeValue2687, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2742 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = 0 := by
  exact mixedMoment_order_one B hB node2742 node2742Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

theorem sound2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2742 node2742Labels = Sparse.eval nodeValue2742 (mixedVector B) := by
  simpa only [nodeValue2742, Sparse.eval_nil] using zero2742 B _hB _hF

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

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

theorem sound2798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2798 node2798Labels = Sparse.eval nodeValue2798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2798) = mixedMoment B node2798 node2798Labels := rfl
  simpa [nodeValue2798, Sparse.eval] using hc.symm

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

theorem sound3025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3025 node3025Labels = Sparse.eval nodeValue3025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3025) = mixedMoment B node3025 node3025Labels := rfl
  simpa [nodeValue3025, Sparse.eval] using hc.symm

theorem sound3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3055 node3055Labels = Sparse.eval nodeValue3055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3055) = mixedMoment B node3055 node3055Labels := rfl
  simpa [nodeValue3055, Sparse.eval] using hc.symm

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

theorem sound3133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3133 node3133Labels = Sparse.eval nodeValue3133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3133) = mixedMoment B node3133 node3133Labels := rfl
  simpa [nodeValue3133, Sparse.eval] using hc.symm

theorem sound3135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3135 node3135Labels = Sparse.eval nodeValue3135 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3135) = mixedMoment B node3135 node3135Labels := rfl
  simpa [nodeValue3135, Sparse.eval] using hc.symm

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

theorem sound3138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3138 node3138Labels = Sparse.eval nodeValue3138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3138) = mixedMoment B node3138 node3138Labels := rfl
  simpa [nodeValue3138, Sparse.eval] using hc.symm

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

theorem sound3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3391 node3391Labels = Sparse.eval nodeValue3391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3391) = mixedMoment B node3391 node3391Labels := rfl
  simpa [nodeValue3391, Sparse.eval] using hc.symm

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

theorem sound3406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3406 node3406Labels = Sparse.eval nodeValue3406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3406) = mixedMoment B node3406 node3406Labels := rfl
  simpa [nodeValue3406, Sparse.eval] using hc.symm

theorem sound3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3415 node3415Labels = Sparse.eval nodeValue3415 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3415) = mixedMoment B node3415 node3415Labels := rfl
  simpa [nodeValue3415, Sparse.eval] using hc.symm

theorem sound3417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3417 node3417Labels = Sparse.eval nodeValue3417 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3417) = mixedMoment B node3417 node3417Labels := rfl
  simpa [nodeValue3417, Sparse.eval] using hc.symm

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

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

theorem sound3508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3508 node3508Labels = Sparse.eval nodeValue3508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3508) = mixedMoment B node3508 node3508Labels := rfl
  simpa [nodeValue3508, Sparse.eval] using hc.symm

theorem sound3509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3509 node3509Labels = Sparse.eval nodeValue3509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3509) = mixedMoment B node3509 node3509Labels := rfl
  simpa [nodeValue3509, Sparse.eval] using hc.symm

theorem sound3512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3512 node3512Labels = Sparse.eval nodeValue3512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3512) = mixedMoment B node3512 node3512Labels := rfl
  simpa [nodeValue3512, Sparse.eval] using hc.symm

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

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3555 node3555Labels = Sparse.eval nodeValue3555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3555) = mixedMoment B node3555 node3555Labels := rfl
  simpa [nodeValue3555, Sparse.eval] using hc.symm

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

theorem sound3591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3591 node3591Labels = Sparse.eval nodeValue3591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3591) = mixedMoment B node3591 node3591Labels := rfl
  simpa [nodeValue3591, Sparse.eval] using hc.symm

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

theorem sound3671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3671 node3671Labels = Sparse.eval nodeValue3671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3671) = mixedMoment B node3671 node3671Labels := rfl
  simpa [nodeValue3671, Sparse.eval] using hc.symm

theorem sound3674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3674 node3674Labels = Sparse.eval nodeValue3674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3674) = mixedMoment B node3674 node3674Labels := rfl
  simpa [nodeValue3674, Sparse.eval] using hc.symm

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

theorem sound3691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3691 node3691Labels = Sparse.eval nodeValue3691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3691) = mixedMoment B node3691 node3691Labels := rfl
  simpa [nodeValue3691, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

theorem sound3709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3709 node3709Labels = Sparse.eval nodeValue3709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3709) = mixedMoment B node3709 node3709Labels := rfl
  simpa [nodeValue3709, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = 0 := by
  exact mixedMoment_order_one B hB node3766 node3766Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3720 node3720Labels = Sparse.eval nodeValue3720 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3720) = mixedMoment B node3720 node3720Labels := rfl
  simpa [nodeValue3720, Sparse.eval] using hc.symm

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3733 node3733Labels = Sparse.eval nodeValue3733 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3733) = mixedMoment B node3733 node3733Labels := rfl
  simpa [nodeValue3733, Sparse.eval] using hc.symm

theorem sound3754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3754 node3754Labels = Sparse.eval nodeValue3754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3754) = mixedMoment B node3754 node3754Labels := rfl
  simpa [nodeValue3754, Sparse.eval] using hc.symm

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3760 node3760Labels = Sparse.eval nodeValue3760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3760) = mixedMoment B node3760 node3760Labels := rfl
  simpa [nodeValue3760, Sparse.eval] using hc.symm

theorem sound3761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3761 node3761Labels = Sparse.eval nodeValue3761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3761) = mixedMoment B node3761 node3761Labels := rfl
  simpa [nodeValue3761, Sparse.eval] using hc.symm

theorem sound3766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3766 node3766Labels = Sparse.eval nodeValue3766 (mixedVector B) := by
  simpa only [nodeValue3766, Sparse.eval_nil] using zero3766 B _hB _hF

theorem sound3771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3771 node3771Labels = Sparse.eval nodeValue3771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3771) = mixedMoment B node3771 node3771Labels := rfl
  simpa [nodeValue3771, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3811 node3811Labels = Sparse.eval nodeValue3811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3811) = mixedMoment B node3811 node3811Labels := rfl
  simpa [nodeValue3811, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3832 node3832Labels = Sparse.eval nodeValue3832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3832) = mixedMoment B node3832 node3832Labels := rfl
  simpa [nodeValue3832, Sparse.eval] using hc.symm

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

theorem sound3868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3868 node3868Labels = Sparse.eval nodeValue3868 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3868) = mixedMoment B node3868 node3868Labels := rfl
  simpa [nodeValue3868, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4684 node4684Labels = Sparse.eval nodeValue4684 (mixedVector B) := by
  have h := singleton4684 B _hB
  rw [sound1810 B _hB _hF, sound2152 B _hB _hF] at h
  norm_num [nodeValue4684, nodeValue1810, nodeValue2152, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4692 node4692Labels = Sparse.eval nodeValue4692 (mixedVector B) := by
  have h := singleton4692 B _hB
  rw [sound1818 B _hB _hF, sound2168 B _hB _hF] at h
  norm_num [nodeValue4692, nodeValue1818, nodeValue2168, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4693 node4693Labels = Sparse.eval nodeValue4693 (mixedVector B) := by
  have h := singleton4693 B _hB
  rw [sound1819 B _hB _hF, sound2169 B _hB _hF] at h
  norm_num [nodeValue4693, nodeValue1819, nodeValue2169, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4703 node4703Labels = Sparse.eval nodeValue4703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4703) = mixedMoment B node4703 node4703Labels := rfl
  simpa [nodeValue4703, Sparse.eval] using hc.symm

theorem sound4704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4704 node4704Labels = Sparse.eval nodeValue4704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4704) = mixedMoment B node4704 node4704Labels := rfl
  simpa [nodeValue4704, Sparse.eval] using hc.symm

theorem sound4705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4705 node4705Labels = Sparse.eval nodeValue4705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4705) = mixedMoment B node4705 node4705Labels := rfl
  simpa [nodeValue4705, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4884 node4884Labels = Sparse.eval nodeValue4884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4884) = mixedMoment B node4884 node4884Labels := rfl
  simpa [nodeValue4884, Sparse.eval] using hc.symm

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

theorem sound4945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4945 node4945Labels = Sparse.eval nodeValue4945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4945) = mixedMoment B node4945 node4945Labels := rfl
  simpa [nodeValue4945, Sparse.eval] using hc.symm

theorem sound4976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4976 node4976Labels = Sparse.eval nodeValue4976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4976) = mixedMoment B node4976 node4976Labels := rfl
  simpa [nodeValue4976, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5206 node5206Labels = Sparse.eval nodeValue5206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5206) = mixedMoment B node5206 node5206Labels := rfl
  simpa [nodeValue5206, Sparse.eval] using hc.symm

theorem sound5215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5215 node5215Labels = Sparse.eval nodeValue5215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5215) = mixedMoment B node5215 node5215Labels := rfl
  simpa [nodeValue5215, Sparse.eval] using hc.symm

theorem sound5228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5228 node5228Labels = Sparse.eval nodeValue5228 (mixedVector B) := by
  have h := singleton5228 B _hB
  rw [sound2672 B _hB _hF, sound3391 B _hB _hF] at h
  norm_num [nodeValue5228, nodeValue2672, nodeValue3391, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5229 node5229Labels = Sparse.eval nodeValue5229 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5229) = mixedMoment B node5229 node5229Labels := rfl
  simpa [nodeValue5229, Sparse.eval] using hc.symm

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

theorem sound5248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5248 node5248Labels = Sparse.eval nodeValue5248 (mixedVector B) := by
  have h := singleton5248 B _hB
  rw [sound2705 B _hB _hF, sound3498 B _hB _hF] at h
  norm_num [nodeValue5248, nodeValue2705, nodeValue3498, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5287 node5287Labels = Sparse.eval nodeValue5287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5287) = mixedMoment B node5287 node5287Labels := rfl
  simpa [nodeValue5287, Sparse.eval] using hc.symm

theorem sound5300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5300 node5300Labels = Sparse.eval nodeValue5300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5300) = mixedMoment B node5300 node5300Labels := rfl
  simpa [nodeValue5300, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources78
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2523 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2523 + difference 3 0) (sourceB2523 + difference 0 3) sourceC2523) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2351) := by
    have ha : (tripleCharges (sourceA2523 + difference 3 0) (sourceB2523 + difference 0 3) sourceC2523) = raw29487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2523 sourceB2523 sourceC2523 difference raw29487; decide +kernel
    rw [ha]
    exact (canonical29487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2523 + difference 3 1) (sourceB2523 + difference 1 3) sourceC2523) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3135) := by
    have ha : (tripleCharges (sourceA2523 + difference 3 1) (sourceB2523 + difference 1 3) sourceC2523) = raw34780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2523 sourceB2523 sourceC2523 difference raw34780; decide +kernel
    rw [ha]
    exact (canonical34780 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2523 + difference 3 2) (sourceB2523 + difference 2 3) sourceC2523) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3709) := by
    have ha : (tripleCharges (sourceA2523 + difference 3 2) (sourceB2523 + difference 2 3) sourceC2523) = raw34777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2523 sourceB2523 sourceC2523 difference raw34777; decide +kernel
    rw [ha]
    exact (canonical34777 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2523 + difference 3 3) (sourceB2523 + difference 3 3) sourceC2523) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3716) := by
    have ha : (tripleCharges (sourceA2523 + difference 3 3) (sourceB2523 + difference 3 3) sourceC2523) = raw34776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2523 sourceB2523 sourceC2523 difference raw34776; decide +kernel
    rw [ha]
    exact (canonical34776 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2523 + difference 3 4) (sourceB2523 + difference 4 3) sourceC2523) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2523 + difference 3 4) (sourceB2523 + difference 4 3) sourceC2523) = raw32878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2523 sourceB2523 sourceC2523 difference raw32878; decide +kernel
    rw [ha]
    exact (canonical32878 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2523 + difference 3 5) (sourceB2523 + difference 5 3) sourceC2523) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2523 + difference 3 5) (sourceB2523 + difference 5 3) sourceC2523) = raw34781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2523 sourceB2523 sourceC2523 difference raw34781; decide +kernel
    rw [ha]
    exact (canonical34781 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2523 + sourceB2523) sourceC2523) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2523 + sourceB2523) sourceC2523) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA2523 sourceB2523 sourceC2523 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2523 sourceB2523 sourceC2523
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2523, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources79
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2534 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2534 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 1) (sourceB2534 + difference 1 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 1) (sourceB2534 + difference 1 0) sourceC2534) = raw34985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34985; decide +kernel
    rw [ha]
    exact (canonical34985 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 2) (sourceB2534 + difference 2 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 2) (sourceB2534 + difference 2 0) sourceC2534) = raw34986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34986; decide +kernel
    rw [ha]
    exact (canonical34986 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 3) (sourceB2534 + difference 3 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 3) (sourceB2534 + difference 3 0) sourceC2534) = raw34987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34987; decide +kernel
    rw [ha]
    exact (canonical34987 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 4) (sourceB2534 + difference 4 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 4) (sourceB2534 + difference 4 0) sourceC2534) = raw16502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16502; decide +kernel
    rw [ha]
    exact (canonical16502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2534 + difference 0 5) (sourceB2534 + difference 5 0) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2534 + difference 0 5) (sourceB2534 + difference 5 0) sourceC2534) = raw34988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34988; decide +kernel
    rw [ha]
    exact (canonical34988 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 0) (sourceB2534 + difference 0 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 0) (sourceB2534 + difference 0 1) sourceC2534) = raw16522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16522; decide +kernel
    rw [ha]
    exact (canonical16522 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 2) (sourceB2534 + difference 2 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 2) (sourceB2534 + difference 2 1) sourceC2534) = raw16524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16524; decide +kernel
    rw [ha]
    exact (canonical16524 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 3) (sourceB2534 + difference 3 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 3) (sourceB2534 + difference 3 1) sourceC2534) = raw16525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16525; decide +kernel
    rw [ha]
    exact (canonical16525 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 4) (sourceB2534 + difference 4 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 4) (sourceB2534 + difference 4 1) sourceC2534) = raw34989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34989; decide +kernel
    rw [ha]
    exact (canonical34989 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2534 + difference 1 5) (sourceB2534 + difference 5 1) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2534 + difference 1 5) (sourceB2534 + difference 5 1) sourceC2534) = raw16526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16526; decide +kernel
    rw [ha]
    exact (canonical16526 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 0) (sourceB2534 + difference 0 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 0) (sourceB2534 + difference 0 2) sourceC2534) = raw34990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34990; decide +kernel
    rw [ha]
    exact (canonical34990 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 1) (sourceB2534 + difference 1 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 1) (sourceB2534 + difference 1 2) sourceC2534) = raw34991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34991; decide +kernel
    rw [ha]
    exact (canonical34991 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 3) (sourceB2534 + difference 3 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3754) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 3) (sourceB2534 + difference 3 2) sourceC2534) = raw34992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34992; decide +kernel
    rw [ha]
    exact (canonical34992 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 4) (sourceB2534 + difference 4 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 4) (sourceB2534 + difference 4 2) sourceC2534) = raw16513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16513; decide +kernel
    rw [ha]
    exact (canonical16513 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2534 + difference 2 5) (sourceB2534 + difference 5 2) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2534 + difference 2 5) (sourceB2534 + difference 5 2) sourceC2534) = raw34993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34993; decide +kernel
    rw [ha]
    exact (canonical34993 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 0) (sourceB2534 + difference 0 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 0) (sourceB2534 + difference 0 3) sourceC2534) = raw34994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34994; decide +kernel
    rw [ha]
    exact (canonical34994 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 1) (sourceB2534 + difference 1 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 1) (sourceB2534 + difference 1 3) sourceC2534) = raw34995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34995; decide +kernel
    rw [ha]
    exact (canonical34995 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 2) (sourceB2534 + difference 2 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3760) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 2) (sourceB2534 + difference 2 3) sourceC2534) = raw34996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34996; decide +kernel
    rw [ha]
    exact (canonical34996 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 4) (sourceB2534 + difference 4 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 4) (sourceB2534 + difference 4 3) sourceC2534) = raw16518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16518; decide +kernel
    rw [ha]
    exact (canonical16518 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2534 + difference 3 5) (sourceB2534 + difference 5 3) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2534 + difference 3 5) (sourceB2534 + difference 5 3) sourceC2534) = raw34997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34997; decide +kernel
    rw [ha]
    exact (canonical34997 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 0) (sourceB2534 + difference 0 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 0) (sourceB2534 + difference 0 4) sourceC2534) = raw34998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34998; decide +kernel
    rw [ha]
    exact (canonical34998 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 1) (sourceB2534 + difference 1 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 1) (sourceB2534 + difference 1 4) sourceC2534) = raw34999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw34999; decide +kernel
    rw [ha]
    exact (canonical34999 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 2) (sourceB2534 + difference 2 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 2) (sourceB2534 + difference 2 4) sourceC2534) = raw35000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35000; decide +kernel
    rw [ha]
    exact (canonical35000 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 3) (sourceB2534 + difference 3 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 3) (sourceB2534 + difference 3 4) sourceC2534) = raw35001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35001; decide +kernel
    rw [ha]
    exact (canonical35001 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2534 + difference 4 5) (sourceB2534 + difference 5 4) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2534 + difference 4 5) (sourceB2534 + difference 5 4) sourceC2534) = raw35002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35002; decide +kernel
    rw [ha]
    exact (canonical35002 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 0) (sourceB2534 + difference 0 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 0) (sourceB2534 + difference 0 5) sourceC2534) = raw35003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35003; decide +kernel
    rw [ha]
    exact (canonical35003 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 1) (sourceB2534 + difference 1 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3512) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 1) (sourceB2534 + difference 1 5) sourceC2534) = raw35004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35004; decide +kernel
    rw [ha]
    exact (canonical35004 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 2) (sourceB2534 + difference 2 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 2) (sourceB2534 + difference 2 5) sourceC2534) = raw35005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35005; decide +kernel
    rw [ha]
    exact (canonical35005 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 3) (sourceB2534 + difference 3 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 3) (sourceB2534 + difference 3 5) sourceC2534) = raw35006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw35006; decide +kernel
    rw [ha]
    exact (canonical35006 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2534 + difference 5 4) (sourceB2534 + difference 4 5) sourceC2534) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2534 + difference 5 4) (sourceB2534 + difference 4 5) sourceC2534) = raw16528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2534 sourceB2534 sourceC2534 difference raw16528; decide +kernel
    rw [ha]
    exact (canonical16528 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2534 sourceB2534 sourceC2534
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2534, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2535 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2535 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 0) (sourceB2535 + difference 0 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3133) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 0) (sourceB2535 + difference 0 2) sourceC2535) = raw29347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw29347; decide +kernel
    rw [ha]
    exact (canonical29347 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 1) (sourceB2535 + difference 1 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2348) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 1) (sourceB2535 + difference 1 2) sourceC2535) = raw35007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw35007; decide +kernel
    rw [ha]
    exact (canonical35007 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 2) (sourceB2535 + difference 2 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 2) (sourceB2535 + difference 2 2) sourceC2535) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 3) (sourceB2535 + difference 3 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3671) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 3) (sourceB2535 + difference 3 2) sourceC2535) = raw35008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw35008; decide +kernel
    rw [ha]
    exact (canonical35008 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 4) (sourceB2535 + difference 4 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 4) (sourceB2535 + difference 4 2) sourceC2535) = raw16540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw16540; decide +kernel
    rw [ha]
    exact (canonical16540 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2535 + difference 2 5) (sourceB2535 + difference 5 2) sourceC2535) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2535 + difference 2 5) (sourceB2535 + difference 5 2) sourceC2535) = raw35009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2535 sourceB2535 sourceC2535 difference raw35009; decide +kernel
    rw [ha]
    exact (canonical35009 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2535 + sourceB2535) sourceC2535) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2535 + sourceB2535) sourceC2535) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA2535 sourceB2535 sourceC2535 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2535 sourceB2535 sourceC2535
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2535, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2536 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2536 + difference 0 2) (sourceB2536 + difference 2 0) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA2536 + difference 0 2) (sourceB2536 + difference 2 0) sourceC2536) = raw35010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw35010; decide +kernel
    rw [ha]
    exact (canonical35010 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2536 + difference 1 2) (sourceB2536 + difference 2 1) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA2536 + difference 1 2) (sourceB2536 + difference 2 1) sourceC2536) = raw16550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw16550; decide +kernel
    rw [ha]
    exact (canonical16550 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2536 + difference 2 2) (sourceB2536 + difference 2 2) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2536 + difference 2 2) (sourceB2536 + difference 2 2) sourceC2536) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2536 + difference 3 2) (sourceB2536 + difference 2 3) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3674) := by
    have ha : (tripleCharges (sourceA2536 + difference 3 2) (sourceB2536 + difference 2 3) sourceC2536) = raw35011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw35011; decide +kernel
    rw [ha]
    exact (canonical35011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2536 + difference 4 2) (sourceB2536 + difference 2 4) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2321) := by
    have ha : (tripleCharges (sourceA2536 + difference 4 2) (sourceB2536 + difference 2 4) sourceC2536) = raw35012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw35012; decide +kernel
    rw [ha]
    exact (canonical35012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2536 + difference 5 2) (sourceB2536 + difference 2 5) sourceC2536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2798) := by
    have ha : (tripleCharges (sourceA2536 + difference 5 2) (sourceB2536 + difference 2 5) sourceC2536) = raw35013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2536 sourceB2536 sourceC2536 difference raw35013; decide +kernel
    rw [ha]
    exact (canonical35013 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2536 + sourceB2536) sourceC2536) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2536 + sourceB2536) sourceC2536) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA2536 sourceB2536 sourceC2536 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2536 sourceB2536 sourceC2536
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2536, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2537 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 0) (sourceB2537 + difference 0 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3138) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 0) (sourceB2537 + difference 0 3) sourceC2537) = raw29348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw29348; decide +kernel
    rw [ha]
    exact (canonical29348 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 1) (sourceB2537 + difference 1 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2356) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 1) (sourceB2537 + difference 1 3) sourceC2537) = raw35014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw35014; decide +kernel
    rw [ha]
    exact (canonical35014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 2) (sourceB2537 + difference 2 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3674) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 2) (sourceB2537 + difference 2 3) sourceC2537) = raw35011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw35011; decide +kernel
    rw [ha]
    exact (canonical35011 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 3) (sourceB2537 + difference 3 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 3) (sourceB2537 + difference 3 3) sourceC2537) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 4) (sourceB2537 + difference 4 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 4) (sourceB2537 + difference 4 3) sourceC2537) = raw16541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw16541; decide +kernel
    rw [ha]
    exact (canonical16541 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2537 + difference 3 5) (sourceB2537 + difference 5 3) sourceC2537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2537 + difference 3 5) (sourceB2537 + difference 5 3) sourceC2537) = raw35015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2537 sourceB2537 sourceC2537 difference raw35015; decide +kernel
    rw [ha]
    exact (canonical35015 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2537 + sourceB2537) sourceC2537) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2537 + sourceB2537) sourceC2537) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA2537 sourceB2537 sourceC2537 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2537 sourceB2537 sourceC2537
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2537, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2545 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 1) (sourceB2545 + difference 1 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 1) (sourceB2545 + difference 1 0) sourceC2545) = raw35115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35115; decide +kernel
    rw [ha]
    exact (canonical35115 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 2) (sourceB2545 + difference 2 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 2) (sourceB2545 + difference 2 0) sourceC2545) = raw35116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35116; decide +kernel
    rw [ha]
    exact (canonical35116 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 3) (sourceB2545 + difference 3 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 3) (sourceB2545 + difference 3 0) sourceC2545) = raw35117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35117; decide +kernel
    rw [ha]
    exact (canonical35117 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 4) (sourceB2545 + difference 4 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 4) (sourceB2545 + difference 4 0) sourceC2545) = raw35118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35118; decide +kernel
    rw [ha]
    exact (canonical35118 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2545 + difference 0 5) (sourceB2545 + difference 5 0) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2545 + difference 0 5) (sourceB2545 + difference 5 0) sourceC2545) = raw35119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35119; decide +kernel
    rw [ha]
    exact (canonical35119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 0) (sourceB2545 + difference 0 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 0) (sourceB2545 + difference 0 1) sourceC2545) = raw35120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35120; decide +kernel
    rw [ha]
    exact (canonical35120 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 2) (sourceB2545 + difference 2 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 2) (sourceB2545 + difference 2 1) sourceC2545) = raw35121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35121; decide +kernel
    rw [ha]
    exact (canonical35121 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 3) (sourceB2545 + difference 3 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 3) (sourceB2545 + difference 3 1) sourceC2545) = raw35122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35122; decide +kernel
    rw [ha]
    exact (canonical35122 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 4) (sourceB2545 + difference 4 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 4) (sourceB2545 + difference 4 1) sourceC2545) = raw35123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35123; decide +kernel
    rw [ha]
    exact (canonical35123 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2545 + difference 1 5) (sourceB2545 + difference 5 1) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2545 + difference 1 5) (sourceB2545 + difference 5 1) sourceC2545) = raw35124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35124; decide +kernel
    rw [ha]
    exact (canonical35124 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 0) (sourceB2545 + difference 0 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 0) (sourceB2545 + difference 0 2) sourceC2545) = raw35125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35125; decide +kernel
    rw [ha]
    exact (canonical35125 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 1) (sourceB2545 + difference 1 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 1) (sourceB2545 + difference 1 2) sourceC2545) = raw35126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35126; decide +kernel
    rw [ha]
    exact (canonical35126 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 3) (sourceB2545 + difference 3 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 3) (sourceB2545 + difference 3 2) sourceC2545) = raw35127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35127; decide +kernel
    rw [ha]
    exact (canonical35127 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 4) (sourceB2545 + difference 4 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 4) (sourceB2545 + difference 4 2) sourceC2545) = raw35128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35128; decide +kernel
    rw [ha]
    exact (canonical35128 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2545 + difference 2 5) (sourceB2545 + difference 5 2) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2545 + difference 2 5) (sourceB2545 + difference 5 2) sourceC2545) = raw35129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35129; decide +kernel
    rw [ha]
    exact (canonical35129 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 0) (sourceB2545 + difference 0 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 0) (sourceB2545 + difference 0 3) sourceC2545) = raw35130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35130; decide +kernel
    rw [ha]
    exact (canonical35130 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 1) (sourceB2545 + difference 1 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 1) (sourceB2545 + difference 1 3) sourceC2545) = raw35131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35131; decide +kernel
    rw [ha]
    exact (canonical35131 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 2) (sourceB2545 + difference 2 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 2) (sourceB2545 + difference 2 3) sourceC2545) = raw35132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35132; decide +kernel
    rw [ha]
    exact (canonical35132 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 4) (sourceB2545 + difference 4 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 4) (sourceB2545 + difference 4 3) sourceC2545) = raw35133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35133; decide +kernel
    rw [ha]
    exact (canonical35133 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2545 + difference 3 5) (sourceB2545 + difference 5 3) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2545 + difference 3 5) (sourceB2545 + difference 5 3) sourceC2545) = raw35134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35134; decide +kernel
    rw [ha]
    exact (canonical35134 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 0) (sourceB2545 + difference 0 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 0) (sourceB2545 + difference 0 4) sourceC2545) = raw35135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35135; decide +kernel
    rw [ha]
    exact (canonical35135 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 1) (sourceB2545 + difference 1 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 1) (sourceB2545 + difference 1 4) sourceC2545) = raw35136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35136; decide +kernel
    rw [ha]
    exact (canonical35136 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 2) (sourceB2545 + difference 2 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 2) (sourceB2545 + difference 2 4) sourceC2545) = raw35137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35137; decide +kernel
    rw [ha]
    exact (canonical35137 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 3) (sourceB2545 + difference 3 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 3) (sourceB2545 + difference 3 4) sourceC2545) = raw35138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35138; decide +kernel
    rw [ha]
    exact (canonical35138 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2545 + difference 4 5) (sourceB2545 + difference 5 4) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2545 + difference 4 5) (sourceB2545 + difference 5 4) sourceC2545) = raw35139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35139; decide +kernel
    rw [ha]
    exact (canonical35139 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 0) (sourceB2545 + difference 0 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4704) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 0) (sourceB2545 + difference 0 5) sourceC2545) = raw35140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35140; decide +kernel
    rw [ha]
    exact (canonical35140 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 1) (sourceB2545 + difference 1 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 1) (sourceB2545 + difference 1 5) sourceC2545) = raw35141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35141; decide +kernel
    rw [ha]
    exact (canonical35141 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 2) (sourceB2545 + difference 2 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 2) (sourceB2545 + difference 2 5) sourceC2545) = raw35142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35142; decide +kernel
    rw [ha]
    exact (canonical35142 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 3) (sourceB2545 + difference 3 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4976) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 3) (sourceB2545 + difference 3 5) sourceC2545) = raw35143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35143; decide +kernel
    rw [ha]
    exact (canonical35143 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2545 + difference 5 4) (sourceB2545 + difference 4 5) sourceC2545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA2545 + difference 5 4) (sourceB2545 + difference 4 5) sourceC2545) = raw35144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2545 sourceB2545 sourceC2545 difference raw35144; decide +kernel
    rw [ha]
    exact (canonical35144 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2545 sourceB2545 sourceC2545
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2545, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2547 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 1) (sourceB2547 + difference 1 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 1) (sourceB2547 + difference 1 0) sourceC2547) = raw35175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35175; decide +kernel
    rw [ha]
    exact (canonical35175 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 2) (sourceB2547 + difference 2 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 2) (sourceB2547 + difference 2 0) sourceC2547) = raw35176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35176; decide +kernel
    rw [ha]
    exact (canonical35176 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 3) (sourceB2547 + difference 3 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 3) (sourceB2547 + difference 3 0) sourceC2547) = raw35177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35177; decide +kernel
    rw [ha]
    exact (canonical35177 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 4) (sourceB2547 + difference 4 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 4) (sourceB2547 + difference 4 0) sourceC2547) = raw35178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35178; decide +kernel
    rw [ha]
    exact (canonical35178 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2547 + difference 0 5) (sourceB2547 + difference 5 0) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2547 + difference 0 5) (sourceB2547 + difference 5 0) sourceC2547) = raw35179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35179; decide +kernel
    rw [ha]
    exact (canonical35179 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 0) (sourceB2547 + difference 0 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 0) (sourceB2547 + difference 0 1) sourceC2547) = raw35180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35180; decide +kernel
    rw [ha]
    exact (canonical35180 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 2) (sourceB2547 + difference 2 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 2) (sourceB2547 + difference 2 1) sourceC2547) = raw35181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35181; decide +kernel
    rw [ha]
    exact (canonical35181 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 3) (sourceB2547 + difference 3 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 3) (sourceB2547 + difference 3 1) sourceC2547) = raw35182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35182; decide +kernel
    rw [ha]
    exact (canonical35182 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 4) (sourceB2547 + difference 4 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 4) (sourceB2547 + difference 4 1) sourceC2547) = raw35183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35183; decide +kernel
    rw [ha]
    exact (canonical35183 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2547 + difference 1 5) (sourceB2547 + difference 5 1) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA2547 + difference 1 5) (sourceB2547 + difference 5 1) sourceC2547) = raw35184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35184; decide +kernel
    rw [ha]
    exact (canonical35184 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 0) (sourceB2547 + difference 0 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 0) (sourceB2547 + difference 0 2) sourceC2547) = raw35185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35185; decide +kernel
    rw [ha]
    exact (canonical35185 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 1) (sourceB2547 + difference 1 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 1) (sourceB2547 + difference 1 2) sourceC2547) = raw35186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35186; decide +kernel
    rw [ha]
    exact (canonical35186 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 3) (sourceB2547 + difference 3 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 3) (sourceB2547 + difference 3 2) sourceC2547) = raw35187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35187; decide +kernel
    rw [ha]
    exact (canonical35187 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 4) (sourceB2547 + difference 4 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 4) (sourceB2547 + difference 4 2) sourceC2547) = raw35188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35188; decide +kernel
    rw [ha]
    exact (canonical35188 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2547 + difference 2 5) (sourceB2547 + difference 5 2) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2547 + difference 2 5) (sourceB2547 + difference 5 2) sourceC2547) = raw35189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35189; decide +kernel
    rw [ha]
    exact (canonical35189 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 0) (sourceB2547 + difference 0 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 0) (sourceB2547 + difference 0 3) sourceC2547) = raw35190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35190; decide +kernel
    rw [ha]
    exact (canonical35190 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 1) (sourceB2547 + difference 1 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 1) (sourceB2547 + difference 1 3) sourceC2547) = raw35191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35191; decide +kernel
    rw [ha]
    exact (canonical35191 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 2) (sourceB2547 + difference 2 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 2) (sourceB2547 + difference 2 3) sourceC2547) = raw35192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35192; decide +kernel
    rw [ha]
    exact (canonical35192 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 4) (sourceB2547 + difference 4 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 4) (sourceB2547 + difference 4 3) sourceC2547) = raw35193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35193; decide +kernel
    rw [ha]
    exact (canonical35193 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2547 + difference 3 5) (sourceB2547 + difference 5 3) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2547 + difference 3 5) (sourceB2547 + difference 5 3) sourceC2547) = raw35194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35194; decide +kernel
    rw [ha]
    exact (canonical35194 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 0) (sourceB2547 + difference 0 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 0) (sourceB2547 + difference 0 4) sourceC2547) = raw35195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35195; decide +kernel
    rw [ha]
    exact (canonical35195 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 1) (sourceB2547 + difference 1 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 1) (sourceB2547 + difference 1 4) sourceC2547) = raw35196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35196; decide +kernel
    rw [ha]
    exact (canonical35196 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 2) (sourceB2547 + difference 2 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 2) (sourceB2547 + difference 2 4) sourceC2547) = raw35197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35197; decide +kernel
    rw [ha]
    exact (canonical35197 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 3) (sourceB2547 + difference 3 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 3) (sourceB2547 + difference 3 4) sourceC2547) = raw35198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35198; decide +kernel
    rw [ha]
    exact (canonical35198 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2547 + difference 4 5) (sourceB2547 + difference 5 4) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2547 + difference 4 5) (sourceB2547 + difference 5 4) sourceC2547) = raw35199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35199; decide +kernel
    rw [ha]
    exact (canonical35199 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 0) (sourceB2547 + difference 0 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2273) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 0) (sourceB2547 + difference 0 5) sourceC2547) = raw35200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35200; decide +kernel
    rw [ha]
    exact (canonical35200 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 1) (sourceB2547 + difference 1 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 1) (sourceB2547 + difference 1 5) sourceC2547) = raw35201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35201; decide +kernel
    rw [ha]
    exact (canonical35201 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 2) (sourceB2547 + difference 2 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 2) (sourceB2547 + difference 2 5) sourceC2547) = raw35202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35202; decide +kernel
    rw [ha]
    exact (canonical35202 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 3) (sourceB2547 + difference 3 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2659) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 3) (sourceB2547 + difference 3 5) sourceC2547) = raw35203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35203; decide +kernel
    rw [ha]
    exact (canonical35203 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2547 + difference 5 4) (sourceB2547 + difference 4 5) sourceC2547) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA2547 + difference 5 4) (sourceB2547 + difference 4 5) sourceC2547) = raw35204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2547 sourceB2547 sourceC2547 difference raw35204; decide +kernel
    rw [ha]
    exact (canonical35204 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2547 sourceB2547 sourceC2547
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2547, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2032 : Integer.Sparse.reindex keyMap MixedData.row2032 = numericRow2032 := by decide +kernel

theorem numericCheck2032 (x : Master → ℝ) : Integer.Sparse.eval numericRow2032 x =
    (1 : ℝ) * reducedSource2032 x := by
  norm_num [numericRow2032, reducedSource2032, Integer.Sparse.eval, Sparse.eval, nodeValue2351, nodeValue3135, nodeValue3709, nodeValue3716, nodeValue3721, nodeValue4091]

theorem reindexCheck2041 : Integer.Sparse.reindex keyMap MixedData.row2041 = numericRow2041 := by decide +kernel

theorem numericCheck2041 (x : Master → ℝ) : Integer.Sparse.eval numericRow2041 x =
    (1 : ℝ) * reducedSource2041 x := by
  norm_num [numericRow2041, reducedSource2041, Integer.Sparse.eval, Sparse.eval, nodeValue2154, nodeValue2155, nodeValue2158, nodeValue2164, nodeValue2274, nodeValue3406, nodeValue3415, nodeValue3417, nodeValue3478, nodeValue3508, nodeValue3509, nodeValue3512, nodeValue3522, nodeValue3538, nodeValue3555, nodeValue3591, nodeValue3754, nodeValue3757, nodeValue3760, nodeValue3761, nodeValue3766, nodeValue3771, nodeValue3795, nodeValue3807, nodeValue3811, nodeValue3813, nodeValue3832, nodeValue3845, nodeValue3868, nodeValue3884]

theorem reindexCheck2042 : Integer.Sparse.reindex keyMap MixedData.row2042 = numericRow2042 := by decide +kernel

theorem numericCheck2042 (x : Master → ℝ) : Integer.Sparse.eval numericRow2042 x =
    (1 : ℝ) * reducedSource2042 x := by
  norm_num [numericRow2042, reducedSource2042, Integer.Sparse.eval, Sparse.eval, nodeValue2348, nodeValue3133, nodeValue3671, nodeValue3693, nodeValue3719, nodeValue3720, nodeValue4092]

theorem reindexCheck2043 : Integer.Sparse.reindex keyMap MixedData.row2043 = numericRow2043 := by decide +kernel

theorem numericCheck2043 (x : Master → ℝ) : Integer.Sparse.eval numericRow2043 x =
    (1 : ℝ) * reducedSource2043 x := by
  norm_num [numericRow2043, reducedSource2043, Integer.Sparse.eval, Sparse.eval, nodeValue2321, nodeValue2798, nodeValue3674, nodeValue3689, nodeValue3691, nodeValue3693, nodeValue4092]

theorem reindexCheck2044 : Integer.Sparse.reindex keyMap MixedData.row2044 = numericRow2044 := by decide +kernel

theorem numericCheck2044 (x : Master → ℝ) : Integer.Sparse.eval numericRow2044 x =
    (1 : ℝ) * reducedSource2044 x := by
  norm_num [numericRow2044, reducedSource2044, Integer.Sparse.eval, Sparse.eval, nodeValue2356, nodeValue3138, nodeValue3674, nodeValue3693, nodeValue3732, nodeValue3733, nodeValue4092]

theorem reindexCheck2045 : Integer.Sparse.reindex keyMap MixedData.row2045 = numericRow2045 := by decide +kernel

theorem numericCheck2045 (x : Master → ℝ) : Integer.Sparse.eval numericRow2045 x =
    (4 : ℝ) * reducedSource2045 x := by
  norm_num [numericRow2045, reducedSource2045, Integer.Sparse.eval, Sparse.eval, nodeValue4684, nodeValue4692, nodeValue4693, nodeValue4703, nodeValue4704, nodeValue4705, nodeValue4846, nodeValue4884, nodeValue4945, nodeValue4976, nodeValue5110, nodeValue5206, nodeValue5215, nodeValue5228, nodeValue5229, nodeValue5248, nodeValue5274, nodeValue5275, nodeValue5287, nodeValue5300, nodeValue5302] <;> ring

theorem reindexCheck2047 : Integer.Sparse.reindex keyMap MixedData.row2047 = numericRow2047 := by decide +kernel

theorem numericCheck2047 (x : Master → ℝ) : Integer.Sparse.eval numericRow2047 x =
    (1 : ℝ) * reducedSource2047 x := by
  norm_num [numericRow2047, reducedSource2047, Integer.Sparse.eval, Sparse.eval, nodeValue2152, nodeValue2168, nodeValue2169, nodeValue2229, nodeValue2272, nodeValue2273, nodeValue2280, nodeValue2286, nodeValue2653, nodeValue2658, nodeValue2659, nodeValue2672, nodeValue2673, nodeValue2685, nodeValue2687, nodeValue2705, nodeValue2742, nodeValue2743, nodeValue3025, nodeValue3054, nodeValue3055]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows127
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2032 (mixedVector B) = 0 := by
  have h2351 : mixedVector B (Sum.inr 2351) = Sparse.eval nodeValue2351 (mixedVector B) := by
    change mixedMoment B node2351 node2351Labels = _
    exact sound2351 B hB hF
  have h3135 : mixedVector B (Sum.inr 3135) = Sparse.eval nodeValue3135 (mixedVector B) := by
    change mixedMoment B node3135 node3135Labels = _
    exact sound3135 B hB hF
  have h3709 : mixedVector B (Sum.inr 3709) = Sparse.eval nodeValue3709 (mixedVector B) := by
    change mixedMoment B node3709 node3709Labels = _
    exact sound3709 B hB hF
  have h3716 : mixedVector B (Sum.inr 3716) = Sparse.eval nodeValue3716 (mixedVector B) := by
    change mixedMoment B node3716 node3716Labels = _
    exact sound3716 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2523, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2351, h3135, h3709, h3716, h3721, h4091, reducedSource2032] using sourceEq2523 B hB

theorem rowSound2032 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2032 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2032, numericCheck2032, reducedZero2032 B hB hF, mul_zero]

theorem reducedZero2041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2041 (mixedVector B) = 0 := by
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2155 : mixedVector B (Sum.inr 2155) = Sparse.eval nodeValue2155 (mixedVector B) := by
    change mixedMoment B node2155 node2155Labels = _
    exact sound2155 B hB hF
  have h2158 : mixedVector B (Sum.inr 2158) = Sparse.eval nodeValue2158 (mixedVector B) := by
    change mixedMoment B node2158 node2158Labels = _
    exact sound2158 B hB hF
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2274 : mixedVector B (Sum.inr 2274) = Sparse.eval nodeValue2274 (mixedVector B) := by
    change mixedMoment B node2274 node2274Labels = _
    exact sound2274 B hB hF
  have h3406 : mixedVector B (Sum.inr 3406) = Sparse.eval nodeValue3406 (mixedVector B) := by
    change mixedMoment B node3406 node3406Labels = _
    exact sound3406 B hB hF
  have h3415 : mixedVector B (Sum.inr 3415) = Sparse.eval nodeValue3415 (mixedVector B) := by
    change mixedMoment B node3415 node3415Labels = _
    exact sound3415 B hB hF
  have h3417 : mixedVector B (Sum.inr 3417) = Sparse.eval nodeValue3417 (mixedVector B) := by
    change mixedMoment B node3417 node3417Labels = _
    exact sound3417 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3508 : mixedVector B (Sum.inr 3508) = Sparse.eval nodeValue3508 (mixedVector B) := by
    change mixedMoment B node3508 node3508Labels = _
    exact sound3508 B hB hF
  have h3509 : mixedVector B (Sum.inr 3509) = Sparse.eval nodeValue3509 (mixedVector B) := by
    change mixedMoment B node3509 node3509Labels = _
    exact sound3509 B hB hF
  have h3512 : mixedVector B (Sum.inr 3512) = Sparse.eval nodeValue3512 (mixedVector B) := by
    change mixedMoment B node3512 node3512Labels = _
    exact sound3512 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3555 : mixedVector B (Sum.inr 3555) = Sparse.eval nodeValue3555 (mixedVector B) := by
    change mixedMoment B node3555 node3555Labels = _
    exact sound3555 B hB hF
  have h3591 : mixedVector B (Sum.inr 3591) = Sparse.eval nodeValue3591 (mixedVector B) := by
    change mixedMoment B node3591 node3591Labels = _
    exact sound3591 B hB hF
  have h3754 : mixedVector B (Sum.inr 3754) = Sparse.eval nodeValue3754 (mixedVector B) := by
    change mixedMoment B node3754 node3754Labels = _
    exact sound3754 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h3760 : mixedVector B (Sum.inr 3760) = Sparse.eval nodeValue3760 (mixedVector B) := by
    change mixedMoment B node3760 node3760Labels = _
    exact sound3760 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3766 : mixedVector B (Sum.inr 3766) = Sparse.eval nodeValue3766 (mixedVector B) := by
    change mixedMoment B node3766 node3766Labels = _
    exact sound3766 B hB hF
  have h3771 : mixedVector B (Sum.inr 3771) = Sparse.eval nodeValue3771 (mixedVector B) := by
    change mixedMoment B node3771 node3771Labels = _
    exact sound3771 B hB hF
  have h3795 : mixedVector B (Sum.inr 3795) = Sparse.eval nodeValue3795 (mixedVector B) := by
    change mixedMoment B node3795 node3795Labels = _
    exact sound3795 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3811 : mixedVector B (Sum.inr 3811) = Sparse.eval nodeValue3811 (mixedVector B) := by
    change mixedMoment B node3811 node3811Labels = _
    exact sound3811 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3832 : mixedVector B (Sum.inr 3832) = Sparse.eval nodeValue3832 (mixedVector B) := by
    change mixedMoment B node3832 node3832Labels = _
    exact sound3832 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3868 : mixedVector B (Sum.inr 3868) = Sparse.eval nodeValue3868 (mixedVector B) := by
    change mixedMoment B node3868 node3868Labels = _
    exact sound3868 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  simpa only [sourceForm2534, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2154, h2155, h2158, h2164, h2274, h3406, h3415, h3417, h3478, h3508, h3509, h3512, h3522, h3538, h3555, h3591, h3754, h3757, h3760, h3761, h3766, h3771, h3795, h3807, h3811, h3813, h3832, h3845, h3868, h3884, reducedSource2041] using sourceEq2534 B hB

theorem rowSound2041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2041 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2041, numericCheck2041, reducedZero2041 B hB hF, mul_zero]

theorem reducedZero2042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2042 (mixedVector B) = 0 := by
  have h2348 : mixedVector B (Sum.inr 2348) = Sparse.eval nodeValue2348 (mixedVector B) := by
    change mixedMoment B node2348 node2348Labels = _
    exact sound2348 B hB hF
  have h3133 : mixedVector B (Sum.inr 3133) = Sparse.eval nodeValue3133 (mixedVector B) := by
    change mixedMoment B node3133 node3133Labels = _
    exact sound3133 B hB hF
  have h3671 : mixedVector B (Sum.inr 3671) = Sparse.eval nodeValue3671 (mixedVector B) := by
    change mixedMoment B node3671 node3671Labels = _
    exact sound3671 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h3720 : mixedVector B (Sum.inr 3720) = Sparse.eval nodeValue3720 (mixedVector B) := by
    change mixedMoment B node3720 node3720Labels = _
    exact sound3720 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2535, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2348, h3133, h3671, h3693, h3719, h3720, h4092, reducedSource2042] using sourceEq2535 B hB

theorem rowSound2042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2042 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2042, numericCheck2042, reducedZero2042 B hB hF, mul_zero]

theorem reducedZero2043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2043 (mixedVector B) = 0 := by
  have h2321 : mixedVector B (Sum.inr 2321) = Sparse.eval nodeValue2321 (mixedVector B) := by
    change mixedMoment B node2321 node2321Labels = _
    exact sound2321 B hB hF
  have h2798 : mixedVector B (Sum.inr 2798) = Sparse.eval nodeValue2798 (mixedVector B) := by
    change mixedMoment B node2798 node2798Labels = _
    exact sound2798 B hB hF
  have h3674 : mixedVector B (Sum.inr 3674) = Sparse.eval nodeValue3674 (mixedVector B) := by
    change mixedMoment B node3674 node3674Labels = _
    exact sound3674 B hB hF
  have h3689 : mixedVector B (Sum.inr 3689) = Sparse.eval nodeValue3689 (mixedVector B) := by
    change mixedMoment B node3689 node3689Labels = _
    exact sound3689 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2536, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2321, h2798, h3674, h3689, h3691, h3693, h4092, reducedSource2043] using sourceEq2536 B hB

theorem rowSound2043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2043 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2043, numericCheck2043, reducedZero2043 B hB hF, mul_zero]

theorem reducedZero2044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2044 (mixedVector B) = 0 := by
  have h2356 : mixedVector B (Sum.inr 2356) = Sparse.eval nodeValue2356 (mixedVector B) := by
    change mixedMoment B node2356 node2356Labels = _
    exact sound2356 B hB hF
  have h3138 : mixedVector B (Sum.inr 3138) = Sparse.eval nodeValue3138 (mixedVector B) := by
    change mixedMoment B node3138 node3138Labels = _
    exact sound3138 B hB hF
  have h3674 : mixedVector B (Sum.inr 3674) = Sparse.eval nodeValue3674 (mixedVector B) := by
    change mixedMoment B node3674 node3674Labels = _
    exact sound3674 B hB hF
  have h3693 : mixedVector B (Sum.inr 3693) = Sparse.eval nodeValue3693 (mixedVector B) := by
    change mixedMoment B node3693 node3693Labels = _
    exact sound3693 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3733 : mixedVector B (Sum.inr 3733) = Sparse.eval nodeValue3733 (mixedVector B) := by
    change mixedMoment B node3733 node3733Labels = _
    exact sound3733 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2537, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2356, h3138, h3674, h3693, h3732, h3733, h4092, reducedSource2044] using sourceEq2537 B hB

theorem rowSound2044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2044 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2044, numericCheck2044, reducedZero2044 B hB hF, mul_zero]

theorem reducedZero2045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2045 (mixedVector B) = 0 := by
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4692 : mixedVector B (Sum.inr 4692) = Sparse.eval nodeValue4692 (mixedVector B) := by
    change mixedMoment B node4692 node4692Labels = _
    exact sound4692 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4703 : mixedVector B (Sum.inr 4703) = Sparse.eval nodeValue4703 (mixedVector B) := by
    change mixedMoment B node4703 node4703Labels = _
    exact sound4703 B hB hF
  have h4704 : mixedVector B (Sum.inr 4704) = Sparse.eval nodeValue4704 (mixedVector B) := by
    change mixedMoment B node4704 node4704Labels = _
    exact sound4704 B hB hF
  have h4705 : mixedVector B (Sum.inr 4705) = Sparse.eval nodeValue4705 (mixedVector B) := by
    change mixedMoment B node4705 node4705Labels = _
    exact sound4705 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4884 : mixedVector B (Sum.inr 4884) = Sparse.eval nodeValue4884 (mixedVector B) := by
    change mixedMoment B node4884 node4884Labels = _
    exact sound4884 B hB hF
  have h4945 : mixedVector B (Sum.inr 4945) = Sparse.eval nodeValue4945 (mixedVector B) := by
    change mixedMoment B node4945 node4945Labels = _
    exact sound4945 B hB hF
  have h4976 : mixedVector B (Sum.inr 4976) = Sparse.eval nodeValue4976 (mixedVector B) := by
    change mixedMoment B node4976 node4976Labels = _
    exact sound4976 B hB hF
  have h5110 : mixedVector B (Sum.inr 5110) = Sparse.eval nodeValue5110 (mixedVector B) := by
    change mixedMoment B node5110 node5110Labels = _
    exact sound5110 B hB hF
  have h5206 : mixedVector B (Sum.inr 5206) = Sparse.eval nodeValue5206 (mixedVector B) := by
    change mixedMoment B node5206 node5206Labels = _
    exact sound5206 B hB hF
  have h5215 : mixedVector B (Sum.inr 5215) = Sparse.eval nodeValue5215 (mixedVector B) := by
    change mixedMoment B node5215 node5215Labels = _
    exact sound5215 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5229 : mixedVector B (Sum.inr 5229) = Sparse.eval nodeValue5229 (mixedVector B) := by
    change mixedMoment B node5229 node5229Labels = _
    exact sound5229 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5287 : mixedVector B (Sum.inr 5287) = Sparse.eval nodeValue5287 (mixedVector B) := by
    change mixedMoment B node5287 node5287Labels = _
    exact sound5287 B hB hF
  have h5300 : mixedVector B (Sum.inr 5300) = Sparse.eval nodeValue5300 (mixedVector B) := by
    change mixedMoment B node5300 node5300Labels = _
    exact sound5300 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  simpa only [sourceForm2545, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4684, h4692, h4693, h4703, h4704, h4705, h4846, h4884, h4945, h4976, h5110, h5206, h5215, h5228, h5229, h5248, h5274, h5275, h5287, h5300, h5302, reducedSource2045] using sourceEq2545 B hB

theorem rowSound2045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2045 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2045, numericCheck2045, reducedZero2045 B hB hF, mul_zero]

theorem reducedZero2047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2047 (mixedVector B) = 0 := by
  have h2152 : mixedVector B (Sum.inr 2152) = Sparse.eval nodeValue2152 (mixedVector B) := by
    change mixedMoment B node2152 node2152Labels = _
    exact sound2152 B hB hF
  have h2168 : mixedVector B (Sum.inr 2168) = Sparse.eval nodeValue2168 (mixedVector B) := by
    change mixedMoment B node2168 node2168Labels = _
    exact sound2168 B hB hF
  have h2169 : mixedVector B (Sum.inr 2169) = Sparse.eval nodeValue2169 (mixedVector B) := by
    change mixedMoment B node2169 node2169Labels = _
    exact sound2169 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h2272 : mixedVector B (Sum.inr 2272) = Sparse.eval nodeValue2272 (mixedVector B) := by
    change mixedMoment B node2272 node2272Labels = _
    exact sound2272 B hB hF
  have h2273 : mixedVector B (Sum.inr 2273) = Sparse.eval nodeValue2273 (mixedVector B) := by
    change mixedMoment B node2273 node2273Labels = _
    exact sound2273 B hB hF
  have h2280 : mixedVector B (Sum.inr 2280) = Sparse.eval nodeValue2280 (mixedVector B) := by
    change mixedMoment B node2280 node2280Labels = _
    exact sound2280 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h2653 : mixedVector B (Sum.inr 2653) = Sparse.eval nodeValue2653 (mixedVector B) := by
    change mixedMoment B node2653 node2653Labels = _
    exact sound2653 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2659 : mixedVector B (Sum.inr 2659) = Sparse.eval nodeValue2659 (mixedVector B) := by
    change mixedMoment B node2659 node2659Labels = _
    exact sound2659 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2673 : mixedVector B (Sum.inr 2673) = Sparse.eval nodeValue2673 (mixedVector B) := by
    change mixedMoment B node2673 node2673Labels = _
    exact sound2673 B hB hF
  have h2685 : mixedVector B (Sum.inr 2685) = Sparse.eval nodeValue2685 (mixedVector B) := by
    change mixedMoment B node2685 node2685Labels = _
    exact sound2685 B hB hF
  have h2687 : mixedVector B (Sum.inr 2687) = Sparse.eval nodeValue2687 (mixedVector B) := by
    change mixedMoment B node2687 node2687Labels = _
    exact sound2687 B hB hF
  have h2705 : mixedVector B (Sum.inr 2705) = Sparse.eval nodeValue2705 (mixedVector B) := by
    change mixedMoment B node2705 node2705Labels = _
    exact sound2705 B hB hF
  have h2742 : mixedVector B (Sum.inr 2742) = Sparse.eval nodeValue2742 (mixedVector B) := by
    change mixedMoment B node2742 node2742Labels = _
    exact sound2742 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h3025 : mixedVector B (Sum.inr 3025) = Sparse.eval nodeValue3025 (mixedVector B) := by
    change mixedMoment B node3025 node3025Labels = _
    exact sound3025 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  simpa only [sourceForm2547, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2152, h2168, h2169, h2229, h2272, h2273, h2280, h2286, h2653, h2658, h2659, h2672, h2673, h2685, h2687, h2705, h2742, h2743, h3025, h3054, h3055, reducedSource2047] using sourceEq2547 B hB

theorem rowSound2047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2047 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2047, numericCheck2047, reducedZero2047 B hB hF, mul_zero]

theorem sourceRowsAt2032 : MixedData.sourceRows (2032 : Fin 2425) =
    MixedData.row2032 := by decide +kernel

theorem sourceRowsAt2033 : MixedData.sourceRows (2033 : Fin 2425) =
    MixedData.row2033 := by decide +kernel

theorem sourceRowsAt2034 : MixedData.sourceRows (2034 : Fin 2425) =
    MixedData.row2034 := by decide +kernel

theorem sourceRowsAt2035 : MixedData.sourceRows (2035 : Fin 2425) =
    MixedData.row2035 := by decide +kernel

theorem sourceRowsAt2036 : MixedData.sourceRows (2036 : Fin 2425) =
    MixedData.row2036 := by decide +kernel

theorem sourceRowsAt2037 : MixedData.sourceRows (2037 : Fin 2425) =
    MixedData.row2037 := by decide +kernel

theorem sourceRowsAt2038 : MixedData.sourceRows (2038 : Fin 2425) =
    MixedData.row2038 := by decide +kernel

theorem sourceRowsAt2039 : MixedData.sourceRows (2039 : Fin 2425) =
    MixedData.row2039 := by decide +kernel

theorem sourceRowsAt2040 : MixedData.sourceRows (2040 : Fin 2425) =
    MixedData.row2040 := by decide +kernel

theorem sourceRowsAt2041 : MixedData.sourceRows (2041 : Fin 2425) =
    MixedData.row2041 := by decide +kernel

theorem sourceRowsAt2042 : MixedData.sourceRows (2042 : Fin 2425) =
    MixedData.row2042 := by decide +kernel

theorem sourceRowsAt2043 : MixedData.sourceRows (2043 : Fin 2425) =
    MixedData.row2043 := by decide +kernel

theorem sourceRowsAt2044 : MixedData.sourceRows (2044 : Fin 2425) =
    MixedData.row2044 := by decide +kernel

theorem sourceRowsAt2045 : MixedData.sourceRows (2045 : Fin 2425) =
    MixedData.row2045 := by decide +kernel

theorem sourceRowsAt2046 : MixedData.sourceRows (2046 : Fin 2425) =
    MixedData.row2046 := by decide +kernel

theorem sourceRowsAt2047 : MixedData.sourceRows (2047 : Fin 2425) =
    MixedData.row2047 := by decide +kernel

theorem chunkSound127_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 127) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 2032 ∨ k.val = 2033 ∨ k.val = 2034 ∨ k.val = 2035 ∨ k.val = 2036 ∨ k.val = 2037 ∨ k.val = 2038 ∨ k.val = 2039 ∨ k.val = 2040 ∨ k.val = 2041 ∨ k.val = 2042 ∨ k.val = 2043 ∨ k.val = 2044 ∨ k.val = 2045 ∨ k.val = 2046 ∨ k.val = 2047 := by omega
  rcases heq with h2032 | h2033 | h2034 | h2035 | h2036 | h2037 | h2038 | h2039 | h2040 | h2041 | h2042 | h2043 | h2044 | h2045 | h2046 | h2047
  · have he : k = (2032 : Fin 2425) := Fin.ext h2032
    subst k
    rw [sourceRowsAt2032]
    exact rowSound2032 B hB hF
  · have he : k = (2033 : Fin 2425) := Fin.ext h2033
    subst k
    rw [sourceRowsAt2033]
    exact rowSound2033_e B hB hF
  · have he : k = (2034 : Fin 2425) := Fin.ext h2034
    subst k
    rw [sourceRowsAt2034]
    exact rowSound2034_e B hB hF
  · have he : k = (2035 : Fin 2425) := Fin.ext h2035
    subst k
    rw [sourceRowsAt2035]
    exact rowSound2035_e B hB hF
  · have he : k = (2036 : Fin 2425) := Fin.ext h2036
    subst k
    rw [sourceRowsAt2036]
    exact rowSound2036_e B hB hF
  · have he : k = (2037 : Fin 2425) := Fin.ext h2037
    subst k
    rw [sourceRowsAt2037]
    exact rowSound2037_e B hB hF
  · have he : k = (2038 : Fin 2425) := Fin.ext h2038
    subst k
    rw [sourceRowsAt2038]
    exact rowSound2038_e B hB hF
  · have he : k = (2039 : Fin 2425) := Fin.ext h2039
    subst k
    rw [sourceRowsAt2039]
    exact rowSound2039_e B hB hF
  · have he : k = (2040 : Fin 2425) := Fin.ext h2040
    subst k
    rw [sourceRowsAt2040]
    exact rowSound2040_e B hB hF
  · have he : k = (2041 : Fin 2425) := Fin.ext h2041
    subst k
    rw [sourceRowsAt2041]
    exact rowSound2041 B hB hF
  · have he : k = (2042 : Fin 2425) := Fin.ext h2042
    subst k
    rw [sourceRowsAt2042]
    exact rowSound2042 B hB hF
  · have he : k = (2043 : Fin 2425) := Fin.ext h2043
    subst k
    rw [sourceRowsAt2043]
    exact rowSound2043 B hB hF
  · have he : k = (2044 : Fin 2425) := Fin.ext h2044
    subst k
    rw [sourceRowsAt2044]
    exact rowSound2044 B hB hF
  · have he : k = (2045 : Fin 2425) := Fin.ext h2045
    subst k
    rw [sourceRowsAt2045]
    exact rowSound2045 B hB hF
  · have he : k = (2046 : Fin 2425) := Fin.ext h2046
    subst k
    rw [sourceRowsAt2046]
    exact rowSound2046_e B hB hF
  · have he : k = (2047 : Fin 2425) := Fin.ext h2047
    subst k
    rw [sourceRowsAt2047]
    exact rowSound2047 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e_oai
